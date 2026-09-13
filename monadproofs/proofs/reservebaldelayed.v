(** * Coq model of reserve balance and proof of safety

    The guiding idea is simple:

    - *Consensus* computes a **worst-case, fee-only budget** (the “effective
      reserve”) for the yet-to-be-executed suffix and only proposes blocks when
      that budget stays non-negative for every **sender** that appears later.

    - *Execution* runs the actual EVM step and enforces that **no account dips
      below its protected reserve slice** (with a carefully fenced “emptying”
      exception). If a transaction would violate that, it is reverted in place.

    Below we define the two algorithms, followed by proofs.
    The consensus check is defined in [consensusAcceptableTxs], the execution check is in [execValidatedTx] (called by [execTx] after validation).

    **Delayed reserve-balance configuration.**
    Accounts can update their reserve balance by calling a stateful precompile; updates become
    effective only after [K] blocks. We model this via [delayedReserveBalOfAddr], which returns
    the latest update at or before block [n-K] when processing block [n]. Consensus therefore
    does not need to inspect transactions to track reserve-balance updates, and execution records
    pending updates in extra state. Reverted transactions discard reserve-balance updates.

    The main soundness theorem is [fullBlockStep]. Intuitively, it says that if any sequence of txs is accepted by consensus, execution of those txs cannot run into an error because of inability to pay gas fees.
    References to any Coq item are hyperlinked to its definition if the definition is in this file or in the Coq standard library.

    [consensusAcceptableTxs] is defined using idealized arithmetic ([Z], which is Coq's type of unbounded integers with no over/underflow in operations).
    To be sure that it can be implemented without over/underflow issues, at the end of this file, we define a variant that only uses [U256] operations and prove that variant equivalent to the one using [Z]. The proof essentially boils down to showing that it can be implemented in a way that avoids any over/underflows during the U256 operations involved in the computation.
*)

(* begin hide *)
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.misc.
Require Import monad.proofs.U256.
Require Import elpi.apps.derive.derive.
Require Import Lens.Elpi.Elpi.

(* Require Import skylabs.hw_models.utils. *)
Require Import Lens.Lens.
Import LensNotations.
Open Scope lens_scope.
Import miscPure.Forward.
Import miscPure. (* has a better version of forward_reason *)
Set Default Goal Selector "!".
Require Import skylabs.auto.cpp.tactics4.
Require Import elpi.apps.derive.derive.
Require Import Lens.Elpi.Elpi.
Open Scope N_scope.

(*TODO: move to misc.v *)
#[global] Hint Rewrite @orb_false_iff bool_decide_eq_false : iff.
#[global] Hint Rewrite andb_true_iff negb_true_iff negb_false_iff: iff.
(* end hide *)

(** * Preliminaries *)

(** This is the full EVM state that EVM execution takes as input and returns as output: *)
Definition StateOfAccounts : Type := EvmAddr -> AccountM.


(** Whether an address is currently delegated in the core state. *)
Definition addrDelegated  (s: StateOfAccounts) (a : EvmAddr) : bool :=
  match delegatedTo (s a) with
  | None => false
  | Some _ => true
  end.

Record EIP7702Authority := {
    del_from: option EvmAddr;
    (** ^ None means the signature was invalid *)
    del_to: EvmAddr;
    (** ^ address 0 means undelegate *)
  }.

(** Many of the EVM semantics definitions we use come from Yoichi's EVM semantics, developed several years ago. The definition of [Transaction] there lacks fields to support newer features like delegation. We extend the extra fields with a summary of reserve-balance configuration updates (if any) that occurred during execution; these updates are applied with a delayed effect after [K] blocks, so consensus does not need to inspect transactions to determine current reserve balances. *)
Record TxExtra :=
  {
    
    authorities: list EIP7702Authority;

    (** The fields above should ultimately come from EVM semantics. The fields below are monad-specific. *)
    
    indexInBlock: N;
    (** ^ index of this transaction in the block. monaddb stores when (blockindex, txindex) an account was born *)
    
    (** Reserve-balance updates are no longer summarized in [TxExtra]; they are
        emitted by the EVM core during execution and applied with a delayed effect. *)
  }.

(** for any decidable assertion/proposition P, [asbool P] is a boolean such that [(asbool P = true) <-> P], where
 [<->] means iff (if and only if)*)
Notation asbool := bool_decide.

Definition is_undelegation (a: EIP7702Authority) : bool :=
  asbool (del_to a = 0).

(** list of accounts requested to be delegated in transaction [txe] *)
Definition dels (txe: TxExtra) : list EvmAddr :=
  flat_map (fun a => match del_from a with
                     | Some addr => if is_undelegation a then [] else [addr]
                     | None => []
                     end ) (authorities txe).

(** list of accounts requested to be undelegated in transaction [txe] *)
Definition undels (txe: TxExtra) : list EvmAddr :=
  flat_map (fun a => match del_from a with
                     | Some addr => if is_undelegation a then [addr] else []
                     | None => []
                     end ) (authorities txe).

#[global] Opaque dels undels.

Definition Transaction: Type :=  block.transaction * TxExtra.
(** The type [A * B] in Coq can be thought of as [std::pair<A,B>]. The projections [.1] and [.2] can be used to obtain the first and second components of the pair, respectively. *)
Definition TxWithHdr : Type := Transaction * BlockHeader.

(** Our **fee upper bound** is intentionally pessimistic: the consensus rule
    reasons about [gas_limit × gas_price], not about *actual* gas used, which can be hard to efficiently estimate.
    This excludes storage fees, which are are separately handled below because storage fees are only accounted by consensus for transactions that are allowed to empty.
    The proofs in this file never unfold the definition of [maxTxFee], so nothing will break if this definition is changed. 
 *)
Definition maxTxFee (t: TxWithHdr) : N :=
  ((w256_to_N (block.tr_gas_price t.1.1)) * (w256_to_N (block.tr_gas_limit t.1.1))).

Opaque maxTxFee.

(** max storage fee. the exact definition does not matter for our proofs, so we keep it undefined, so our proofs would have to work for all possible definitions. one can choose the body as 0 to effectively disable storage fees *)
Definition maxStorageFee (t: TxWithHdr) : N. Admitted.



Section K.
(** Parameterization by the lookahead window [K]:
Consensus can be ahead of execution by at most K. The n+Kth block must have the state root hash after executing block n. The next two variables are parameters for the rest of the proofs.
 *)
Variable K: N.
Hypothesis K_pos : (0 < K)%N.

(** Next, we have some simple wrappers for brevity.

   sender of a transaction: *)
Definition sender (t: TxWithHdr): EvmAddr := tsender t.1.1.

(** balance of an account in a given state: *)
Definition balanceOfAc (s: StateOfAccounts) (a: EvmAddr) : N := balance (s a).

(** update the value of the key [updKey] in [oldMap] to [f (oldMap updKey)] ([f] applied to the old value of the key [updKey] in the map) *)
Definition updateKey  {T} `{c: EqDecision T} {V}  (oldmap: T -> V) (updKey: T) (f: V -> V) : T -> V :=
  fun k => if (asbool (k=updKey)) then f (oldmap updKey) else oldmap k.

(** update balance of the account [addr] such that the new value is [upd] applied to the old value *)
Definition updateBalanceOfAc (s: StateOfAccounts) (addr: EvmAddr) (upd: N -> N) : StateOfAccounts :=
  updateKey s addr (fun old => old &: _balance %= upd).

(** value transfer field of a of a transaction *)
Definition value (t: TxWithHdr): N := w256_to_N (block.tr_value t.1.1).

(** addresses delegated or undelegated by [tx] *)
Definition addrsDelUndelByTx  (tx: TxWithHdr) : list EvmAddr := (dels tx.1.2 ++undels tx.1.2).

(** block number of a transaction *)
Definition txBlockNum (t: TxWithHdr) : N := number t.2.

(** A transaction may emit multiple reserve-balance updates (e.g., via repeated
    precompile calls). Each entry targets a specific address. *)
Definition ReserveBalUpdate : Type := list (EvmAddr * N).

(** To implement reserve balance checks, execution needs to maintain some extra state (beyond the core EVM state) for each account:  *)
Record ExtraAcState :=
  {
    lastTxInBlockIndex : option N;
    (** ^ last block index where this account sent a transaction. In the implementation, we can just track the last 2K range, e.g. this can be None if the last tx was more than 2K block before. we do not need to store this information in the db as it can be easily computed *)
    lastDelUndelInBlockIndex : option N;
    (** ^ last block index where this address was delegated or undelegated. In the implementation, we can just track the last 2K range.*)
    settledReserveBal: N;
    (** ^ last *settled* reserve balance value for this account (defaults to [DefaultReserveBal]). *)
    pendingReserveBal: option (N * N);
    (** ^ pending reserve balance update (if any), as [(value, block)]. *)
  }.


#[only(lens)] derive ExtraAcState.

Definition ExtraAcStates := (EvmAddr -> ExtraAcState).

Definition settledReserveBalOfAddr (s: ExtraAcStates) (addr : EvmAddr) : N := settledReserveBal (s addr).
Definition pendingReserveBalOfAddr (s: ExtraAcStates) (addr : EvmAddr) : option (N * N) := pendingReserveBal (s addr).
Definition pendingReserveBalBlockOfAddr (s: ExtraAcStates) (addr : EvmAddr) : option N :=
  option_map snd (pendingReserveBal (s addr)).

(** The settled (non-delayed) configured reserve balance value. *)
Definition configuredReserveBalOfAddr (s: ExtraAcStates) (addr : EvmAddr) : N :=
  settledReserveBalOfAddr s addr.

(** Our modified execution function which does reserve balance checks will use the following type as input/output.*)
Definition AugmentedState : Type := StateOfAccounts * ExtraAcStates.

(** balance of an account in a given augmented state *)
Definition balanceOfAcA (s: AugmentedState) (ac: EvmAddr) := balanceOfAc  s.1 ac.

(** just an abstract helper used in the next two definitions, which choose different instantiations for the [proj] argument *)
Definition indexWithinK (proj: ExtraAcState -> option N) (state : ExtraAcStates)  (tx: TxWithHdr) : bool :=
  let startIndex :=  txBlockNum tx - (K-1)  in
  match proj (state (sender tx))  with
  | Some index =>
      asbool (startIndex <= index <= txBlockNum tx)
  | None => false
  end.

(** returns true if [sender tx] sent a transaction within the last K blocks of [txBlockNum tx]*)
Definition existsTxWithinK (state : AugmentedState)  (tx: TxWithHdr) : bool :=
  indexWithinK lastTxInBlockIndex (state.2) tx.

(** returns true if the account [sender tx] was delegated/undelegated within the last K blocks of [txBlockNum tx]*)
Definition existsDelUndelTxWithinK (state : AugmentedState)  (tx: TxWithHdr) : bool :=
  indexWithinK  lastDelUndelInBlockIndex (state.2) tx.


(* Cryptographic code hash (Keccak-256), modeled abstractly. *)
Axiom keccak256_program : evm.program -> N.
(* Keccak-256 of a non-empty program is never NULL_HASH. *)
Definition code_hash_of_program
           (pr: EVMOpSem.evm.program)
  : Corelib.Numbers.BinNums.N :=
  keccak256_program pr.

(* Delegation marker bytecode has fixed length 3 + 20. *)
Definition delegation_indicator_size : Z := 23%Z.
Parameter delegation_marker_prefix : evm.program -> bool.

Definition isDelegationMarker (p: evm.program) : bool :=
  (asbool (EVMOpSem.evm.program_length p = delegation_indicator_size))
    && delegation_marker_prefix p.

(** is an account a smart contract? *)
Definition isAcSC (os: option AccountM) : bool:=
  match os with
   | Some s =>
      (asbool (code_hash_of_program (block.block_account_code (coreAc s)) <> 0%N)) && (negb (isDelegationMarker (block.block_account_code (coreAc s))))
   | None => false
  end.

(** in state [s], is the account at address [addr] a smart contract? *)
Definition isSC (s: StateOfAccounts) (addr: EvmAddr): bool:=
  isAcSC (Some (s addr)).



(*
Disable Notation "!!!".
 *)

(** * Consensus Check (algo 1)
Below, we build up the definition of the consensus check [consensusAcceptableTxs]
 *)
(**  The “emptying” gate:

    [candidateTx] may “empty” the sender's balance
    iff all three are true about its sender:

    - it is *not* currently delegated,
    - it had no delegation change within the last [K] blocks (last K-1 blocks and the prev transactions in the current block),
    - it did not send a transaction in the last [K] blocks.

    This gate is what lets consensus handle fee-only budgets and still allows an EOA to empty their account under certain conditions.
    [preIntermediatesState] is the latest fully-executed state and [intermediates] is a list of all the transactions between [preIntermediatesState] and [candidateTx].

 *)
Definition isAllowedToEmpty
  (preIntermediatesState : AugmentedState) (intermediates: list TxWithHdr)  (candidateTx: TxWithHdr) : bool :=
  let consideredDelegated :=
    (addrDelegated (preIntermediatesState.1) (sender candidateTx))
      || existsDelUndelTxWithinK preIntermediatesState candidateTx
      || asbool  ((sender candidateTx) ∈ flat_map addrsDelUndelByTx (candidateTx::intermediates)) in
  let existsSameSenderTxInWindow :=
    (existsTxWithinK preIntermediatesState candidateTx)
    || asbool ((sender candidateTx) ∈ map sender intermediates) in
  (negb consideredDelegated) && (negb existsSameSenderTxInWindow).


(** Whether this is the first transaction from the sender within the last [K]
    blocks and without delegation/undelegation activity in that window. This is
    a slightly *weaker* condition than [isAllowedToEmpty] because it ignores
    delegation/undelegation activity that may appear in [candidateTx] itself.
    Hence [isAllowedToEmpty] implies [senderNoRecentActivity], but not conversely
    (e.g., a tx that contains a self-authorization can make [isAllowedToEmpty]
    false while [senderNoRecentActivity] remains true). A precise characterization
    of this gap is given later in Lemma [isAllowedToEmpty_false_senderNoRecentActivity].

 *)
Definition senderNoRecentActivity
  (preIntermediatesState : AugmentedState) (intermediates: list TxWithHdr) (candidateTx: TxWithHdr) : bool :=
  let senderAddr := sender candidateTx in
  let existsSameSenderTxInWindow :=
      (existsTxWithinK preIntermediatesState candidateTx)
      || asbool (senderAddr ∈ map sender intermediates) in
  let senderTouchedByDelUndel :=
      asbool (senderAddr ∈ flat_map addrsDelUndelByTx intermediates) in
  let consideredDelegated :=
      (addrDelegated preIntermediatesState.1 senderAddr)
        || existsDelUndelTxWithinK preIntermediatesState candidateTx
        || senderTouchedByDelUndel in
  (negb existsSameSenderTxInWindow) && (negb consideredDelegated).

(** The effective reserve map:

    Consensus reasons about *how much of the protected (reserve) slice of the balance
    can be consumed* by
    the yet-to-run suffix.  This is the “effective reserve” map:
    - It is initialized with [min(balance, userConfiguredReserve)].
    - Every transaction removes *at most* its fee from the sender’s entry,
      except for the “emptying” hole, where the pessimistic removal accounts
      for [value + fee] in one shot.

    Notice the type is [Z]: negative entries encode an *over-consumption* that
    should make the proposal unacceptable.

    Z is the type of mathematical numbers in Coq: unbounded, exact arithmetic (no over/under flows). At the end of this file, we implement in Coq the algorithm using just U256, while still avoiding over/underflows and thus prove equivalence *)
Definition EffReserveBals := EvmAddr -> Z.


(** delayed user reserve balance: latest update whose block index plus [K] is ≤ [n]. *)
Definition delayedReserveBal (es: ExtraAcState) (n: N) : N :=
  match pendingReserveBal es with
  | Some (v, blk) =>
      if asbool (blk + K <= n)
      then v
      else settledReserveBal es
  | None => settledReserveBal es
  end.

(** delayed user reserve balance at address [addr] in the state map. *)
Definition delayedReserveBalOfAddr (s: ExtraAcStates) (addr : EvmAddr) (n: N) : N :=
  delayedReserveBal (s addr) n.


Open Scope Z_scope.

(** initial effective reserve balances, before any proposed tx.
    For delayed URB, the initial value is a placeholder; the first time a sender
    appears, we recompute using the block number of that tx (via the
    [senderNoRecentActivity] and [advanceEffReserveBals] steps). For senders that
    never appear in the suffix, this placeholder is irrelevant.
 *)
Definition initialEffReserveBals (s: AugmentedState) : EffReserveBals :=
  fun addr =>  (balanceOfAc s.1 addr `min` delayedReserveBalOfAddr s.2 addr 0).

(** Advance the effective-reserve map to a block [b] by clamping each entry
    to the delayed reserve balance effective at [b]. *)
Definition advanceEffReserveBals (s: AugmentedState) (erbs: EffReserveBals) (b: N) : EffReserveBals :=
  fun addr => (erbs addr) `min` delayedReserveBalOfAddr s.2 addr b.

(** Consensus’ decrement step:

    The next defn is the algebraic heart of consensus check algorithm:
    fold this function left-to-right over the entire sequence of proposed txs, and you get the remaining
    worst-case protected reserve for every sender.

    Formally, this function conservatively estimates the remaining effective reserve balance of the sender of [candidateTx] after executing [candidateTx], assuming [prevErb] is the estimate of the reserve balance of the sender of [candidateTx] just before executing [candidateTx]. [preIntermediatesState] is the latest fully-executed state and [intermediates] is a list of all the transactions between [preIntermediatesState] and [candidateTx].

    In the definition of [newBal] (let binding), the subtraction is capped below at 0: the result is non-negative.
    So, if [sbal < maxTxFee candidateTx + value candidateTx] but  [maxTxFee next <= sbal], this transaction ([candidateTx]) will be accepted but all
    subsequent ones (with [maxTxFee > 0]) from the same sender will be rejected as the remaining effective reserve balance becomes 0.

   This function represents the check that consensus needs to do when adding [candidateTx] at the end of the already built/proposed valid sequence of txs [intermediates]. [candidateTx] will be accepted iff the returned value is non-negative.

   The [intermediates] list is used only for the [isAllowedToEmpty] check and to
   detect whether the sender already appeared in the last [K] blocks. So the Rust
   implementation can optimize it by instead just maintaining the necessary
   summaries (the set of senders and the set of addrs that are delegated or
   undelegated in those txs).
 *)

Definition remainingEffReserveBalOfSender (preIntermediatesState : AugmentedState) (prevErb: Z) (intermediates: list TxWithHdr) (candidateTx: TxWithHdr)
  : Z :=
  let s := preIntermediatesState in
  let senderAddr := sender candidateTx in
  let baseErb :=
      if senderNoRecentActivity s intermediates candidateTx
      then (balanceOfAc s.1 senderAddr `min`
              delayedReserveBalOfAddr s.2 senderAddr (txBlockNum candidateTx))
      else (prevErb `min`
              delayedReserveBalOfAddr s.2 senderAddr (txBlockNum candidateTx)) in
  if isAllowedToEmpty s intermediates candidateTx
  then
    let sbal := balanceOfAc s.1 senderAddr in
    let newBal:= (sbal - maxTxFee candidateTx - value candidateTx - maxStorageFee candidateTx) `max` 0 in
    if asbool (maxTxFee candidateTx <= sbal)
    then newBal `min` (delayedReserveBalOfAddr s.2 senderAddr (txBlockNum candidateTx))
    else -1
  else (baseErb - maxTxFee candidateTx). (* -ve =>  this tx cannot be accepted *)

(** The file also contains a finite-width (U256) variant of the consensus checks;
    see Section [U256Consensus] near the end. *)

(** Next, we just "fold" the above function over the entire sequence of proposed transactions, starting from the first one after the fully executed state. Note how in the recursive call, we add the processed head to the list of intermediate transactions.
   As with the function above, [postStateAccountedSuffix] is only used to track
   whether the sender already appeared in the suffix and for the [isAllowedToEmpty]
   check. An optimized implementation can maintain just the necessary summaries
   instead of the full list.

 *)
Fixpoint remainingEffReserveBalsL (latestState : AugmentedState) (preRestERBs: EffReserveBals) (postStateAccountedSuffix rest: list TxWithHdr)
  : EffReserveBals:=
  match rest with
  | [] => preRestERBs
  | hrest::tlrest =>
      let preRestERBs' := advanceEffReserveBals latestState preRestERBs (txBlockNum hrest) in
      let rem: Z :=
        remainingEffReserveBalOfSender latestState (preRestERBs' (sender hrest)) postStateAccountedSuffix hrest in
      let erbs: EffReserveBals := updateKey preRestERBs' (sender hrest) (fun _ => rem) in
      remainingEffReserveBalsL latestState erbs (postStateAccountedSuffix++[hrest]) tlrest
  end.

(** ** Algorithm 1 (consensus): acceptability of a suffix

    [postStateProposedTxs] is **consensus-acceptable** if, after pessimistically removing the
    head-then-tail debits, *every sender that appears later still has a
    non-negative effective reserve*.  This is exactly the safety condition
    proposers maintain as they build blocks up to [K] ahead.

    When evaluating a new tx at block number N to add at the end of [postStateProposedTxs],
    [latestState] must be the state after N-K block when proposing a new block.
    However, when the next pending (already proposed) block is executed, we need to derive that the remaining already proposed transactions are still valid on top of the more recent state: this is what the main soundness lemma [fullBlockStep] proves, in addition to proving that [postStateProposedTxs] will execute without running out of fees to pay.

   
 *)
Definition consensusAcceptableTxs (latestState : AugmentedState) (postStateProposedTxs: list TxWithHdr) : Prop :=
  forall addr,  addr ∈ map sender postStateProposedTxs ->
   0<= (remainingEffReserveBalsL latestState (initialEffReserveBals latestState) [] postStateProposedTxs) addr.


(** * Execution Check (algo 2)

 The execution logic is also tweaked to ensure that a transaction cannot dip too much into reserves so as to not have enough fees for a transaction already included by consensus. The main complication is that some EOAs may be delegated and thus transactions sent to them can make arbitrary debits that are hard to statically estimate without actually executing the transaction. Thus, we have a dynamic check at the end of execution, to check if some EOA account (possibly other than the sender) was debited too much.
First, some helpers for that.


[isAllowedToEmptyExec] is a trivial wrapper used in execution, where there are NO intermediate transactions between the current transaction and the last known fully executed state.
 *)

Definition isAllowedToEmptyExec
  (state : AugmentedState)  (tx: TxWithHdr) : bool :=
  isAllowedToEmpty state [] tx.

(** [updateExtraState] is the execution-time maintenance of the tiny history we
    need for emptiness checks and delayed reserve-config changes. It applies all
    reserve updates emitted during execution (possibly for multiple addresses)
    only on successful execution; [updateExtraStateNoReserve] is used on revert,
    and only promotes already-pending updates (it discards any new reserve
    updates from the reverted tx). *)
Definition promotePendingReserveBal (es: ExtraAcState) (n: N) : ExtraAcState :=
  match pendingReserveBal es with
  | Some (v, blk) =>
      if asbool (blk + K <= n)%N
      then {|
        lastTxInBlockIndex := lastTxInBlockIndex es;
        lastDelUndelInBlockIndex := lastDelUndelInBlockIndex es;
        settledReserveBal := v;
        pendingReserveBal := None;
      |}
      else es
  | None => es
  end.

Definition applyReserveBalUpdate (es: ExtraAcState) (n: N) (newRb: N) : ExtraAcState :=
  match pendingReserveBal es with
  | Some (_v, blk) =>
      (** if multiple updates are applied in a single block, the latest wins *)
      if asbool (blk = n)%N
      then {|
        lastTxInBlockIndex := lastTxInBlockIndex es;
        lastDelUndelInBlockIndex := lastDelUndelInBlockIndex es;
        settledReserveBal := settledReserveBal es;
        pendingReserveBal := Some (newRb, n)
      |}
      else es
  | None =>
      {|
        lastTxInBlockIndex := lastTxInBlockIndex es;
        lastDelUndelInBlockIndex := lastDelUndelInBlockIndex es;
        settledReserveBal := settledReserveBal es;
        pendingReserveBal := Some (newRb, n)
      |}
  end.

Definition applyReserveBalUpdatesForAddr (es: ExtraAcState) (n: N) (addr: EvmAddr)
           (updates: ReserveBalUpdate) : ExtraAcState :=
  fold_left (fun st '(a, newRb) =>
               if asbool (a = addr) then applyReserveBalUpdate st n newRb else st)
            updates es.

Definition updateExtraStateBase (a: ExtraAcStates) (tx: TxWithHdr) : ExtraAcStates :=
  (fun addr =>
     let oldes := a addr in
       {|
         lastTxInBlockIndex :=
           if asbool (sender tx = addr)
           then Some (txBlockNum tx)
           else lastTxInBlockIndex oldes;
         lastDelUndelInBlockIndex :=
           if asbool (addr ∈ addrsDelUndelByTx tx)
           then Some (txBlockNum tx)
           else lastDelUndelInBlockIndex oldes;
         settledReserveBal := settledReserveBal oldes;
         pendingReserveBal := pendingReserveBal oldes
       |}
    ).


Definition updateExtraState (a: ExtraAcStates) (tx: TxWithHdr) (rbUpdate: ReserveBalUpdate) : ExtraAcStates :=
  (fun addr =>
     let oldes := (updateExtraStateBase a tx) addr in
     let oldes' := promotePendingReserveBal oldes (txBlockNum tx) in
     applyReserveBalUpdatesForAddr oldes' (txBlockNum tx) addr rbUpdate
  ).

Definition updateExtraStateNoReserve (a: ExtraAcStates) (tx: TxWithHdr) : ExtraAcStates :=
  (fun addr =>
     let oldes := updateExtraStateBase a tx addr in
     promotePendingReserveBal oldes (txBlockNum tx)).

Open Scope N_scope.

Section EvmCore.
(** ** Abstract execution and revert

    We postulate a single-step EVM core ([evmExecTxCore]) that returns the new
    state, a transaction result (receipt), and the set of changed accounts; and
    the revert step for failed checks.
    This keeps the reserve logic orthogonal to the (much larger) EVM semantics.
    The list ([list EvmAddr]) returned by [evmExecTxCore] contains all the changed accounts.
 *)

Variable evmExecTxCore :
  StateOfAccounts -> TxWithHdr ->
  ((StateOfAccounts * TxResult) * (list EvmAddr)) * ReserveBalUpdate.
Variable revertTx : StateOfAccounts -> TxWithHdr -> (StateOfAccounts * TxResult).

Definition revertTxState (s: StateOfAccounts) (t: TxWithHdr) : StateOfAccounts :=
  (revertTx s t).1.

Definition evmExecTxCoreState (s: StateOfAccounts) (t: TxWithHdr) : StateOfAccounts :=
  (evmExecTxCore s t).1.1.1.

(*
Definition emptyTxResult : TxResult :=
  {| gas_used := 0; gas_refund := 0; logs := [] |}.
*)


(** ** Algorithm 2 (execution): execute a transaction

    Next, we define [execValidateTx], which assumes that [t] has already been validated to ensure that the sender has
    enough balance to cover [maxTxFee]. It uses a helper [allFinalBalSufficient], which we define first.

    Execution, as defined by [execValidateTx], proceeds as follows:

    - Run the core EVM step to obtain the *actual* post state.
    - For *changed* accounts, [allFinalBalSufficient] checks that the account was not debited too much, which may endanger the fee solvency of the later transactions already accepted by consensus.
    - If any check fails, revert the tx *and still* update the extra history
      (so K-window bookkeeping remains accurate). Reserve-balance updates are
      applied only on success. *)


(** [allFinalBalSufficient] captures the per-account reserve-balance postcondition for
    a transaction.  *)

Definition finalBalSufficient (preTxState: AugmentedState) (postTxState : StateOfAccounts)
    (t: TxWithHdr) (a: EvmAddr): bool :=
  let ReserveBal := delayedReserveBalOfAddr preTxState.2 a (txBlockNum t) in
  let erb:N := ReserveBal `min` (balanceOfAc preTxState.1 a) in
  if isSC postTxState a (* important that si is not s, making it more liberal: allow just deployed contracts to empty *)
  then true
  else
    if asbool (sender t =a)
    then if isAllowedToEmptyExec preTxState t then true else asbool ((erb  - maxTxFee t) <= balanceOfAc postTxState a)
    else asbool (erb <= balanceOfAc postTxState a).

Definition allFinalBalSufficient (preTxState: AugmentedState) (postTxState : StateOfAccounts)
    (changedAccounts: list EvmAddr) (t: TxWithHdr): bool:=
  forallb (finalBalSufficient preTxState postTxState t) changedAccounts.

(** Execute a validated tx and return the post-state plus the EVM receipt. *)
Definition execValidatedTx  (s: AugmentedState) (t: TxWithHdr)
  : AugmentedState * TxResult :=
  let '(((postTxState, txr), changedAccounts), rbUpdate) := evmExecTxCore (s.1) t in
  if (allFinalBalSufficient s postTxState changedAccounts t)
  then ((postTxState, updateExtraState s.2 t rbUpdate), txr)
  else
    let (revState, revRes) := revertTx s.1 t in
    ((revState, updateExtraStateNoReserve s.2 t), revRes).

(** Note that because the [isSC] check is done on [si] (the result of running the EVM blackbox to execute [t]), not [s] (the pre-exec state), the following scenario is allowed.

   - Before the tx, Alice sends money to some address addr2 (computed using keccak). Alice is EOA.
   - Alice sends tx foo to a smart contract address addr.
   - foo execution deploys code at addr2 and calls it, and the call empties addr2.
 *)


(** Execution check of tx validity:
    The implementation checks nonces as well, but here we are only concerned with tx fees.
 *)
Definition validateTx (preTxState: StateOfAccounts) (tx: TxWithHdr): bool :=
   asbool (maxTxFee tx  <= balanceOfAc preTxState (sender tx)).


(** Top-level execution wrapper that fails fast when validation fails.
    On success, it returns the post-state and receipt for [t].
   [None] means the execution of the whole block containing [t] aborts, which is what the consensus/execution checks must guarantee to never happen. *)
Definition execTx (s: AugmentedState) (t: TxWithHdr): option (AugmentedState * TxResult) :=
  if (negb (validateTx (s.1) t))
  then None
  else Some (execValidatedTx  s t).

(** execute a list of transactions one by one, returning the final state and receipts. Note that if the execution of any tx returns [None] (balance insufficient to cover fees), the entire execution (of the whole list of txs) returns [None]. *)
Fixpoint execTxs  (s: AugmentedState) (ts: list TxWithHdr): option (AugmentedState * list TxResult) :=
  match ts with
  | [] => Some (s, [])
  | t::tls =>
      match execTx s t with
      | None => None 
      | Some (si, r) =>
        match execTxs si tls with
        | Some (sf, rs) => Some (sf, r :: rs)
        | None => None
        end
      end
  end.



(** * Main correctness theorem *)
Open Scope Z_scope.
(** Our correctness property only holds when the set of proposed transactions is within K.
  This helps capture that assumption. *)
Fixpoint blockNumsInRange (ltx: list TxWithHdr) : Prop :=
  match ltx with
  | [] => True
  | htx::ttx =>
      (forall txext, txext ∈ ttx ->  txBlockNum txext - (K-1) ≤ txBlockNum htx ≤ txBlockNum txext)
      /\ blockNumsInRange ttx
  end.

Definition txCannotCreateContractAtAddrs tx (eoasWithPrivateKey: list EvmAddr) :=
  forall s, let sf := (execValidatedTx s tx).1 in
            forall addr,  addr ∈ eoasWithPrivateKey -> isSC s.1 addr = false -> isSC sf.1 addr = false.

(** The lemma below is probably what one would come up first as the main correctness theorem.
[blocks] represents the transactions in the blocks proposed after [latestState].
It says that consensus checks ([consensusAcceptableTxs latestState blocks]) implies
that the execution of all transactions [blocks] one by one, starting from the state [latestState] will succeed and not abort ([None]) due to preTx balance being less than [maxTxFee].

*)
Theorem fullBlockStep2  (latestState : AugmentedState) (blocks: list TxWithHdr) :
  (forall ac, ac ∈ (map sender blocks) -> isSC latestState.1 ac = false)
  -> (forall txext, txext ∈ blocks ->  txCannotCreateContractAtAddrs txext (map sender blocks))
  -> blockNumsInRange blocks
  -> consensusAcceptableTxs latestState blocks
  -> match execTxs latestState blocks with
     | None =>  False
     | Some (si, _) => True
     end. Abort.

(** ** main correctness theorem
We will prove the above correctness theorem below, but the actual correctness theorem we need is slightly stronger.
Suppose we split [blocks] in the theorem above into [firstblock] and [restblocks] such that [blocks=firstblock++blocksrest] and suppose these blocks together are all transactions from the K proposed blocks since the last consensus state. Now, consensus will wait for execution to catch up and compute the state after [firstblock], say [latestState'].
After that, consensus should check the next block after [blocksrest] w.r.t [latestState'].
At that time, it needs to know that [blocksrest] is already valid w.r.t [latestState'], i.e. [consensusAcceptableTxs latestState' blocksrest].  This is precisely what the main theorem, shown next does:
*)
Theorem fullBlockStep  (latestState : AugmentedState) (firstblock: list TxWithHdr) (restblocks: list TxWithHdr) :
  blockNumsInRange (firstblock++restblocks)
  -> consensusAcceptableTxs latestState (firstblock++restblocks)
  -> (forall txext, txext ∈ (firstblock++restblocks) -> txCannotCreateContractAtAddrs txext (map sender (firstblock++restblocks)))
  -> (forall ac, ac ∈ (map sender (firstblock++restblocks)) -> isSC latestState.1 ac = false)
  -> match execTxs latestState firstblock with
     | None =>  False
        (** ^ execution cannot abort (indicated by returning None) due to balance being insufficient to even pay fees *)
     | Some (si, _) =>
        (** in this case, we have enough conditions to guarantee fee-solvency of [restblocks], so that it can be extended and then this lemma reapplied: *)
         consensusAcceptableTxs si restblocks
         /\ blockNumsInRange restblocks
         /\ (forall ac, ac ∈ (map sender restblocks) -> isSC si.1 ac = false)
         /\ (forall txext, txext ∈ (restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (restblocks)))
     end.
Proof. Abort.

(** * Proof *)
Open Scope N_scope.
(** ** core execution assumptions
To prove the theorem [fullBlockStep], we needed to make the following assumptions about how the core EVM execution updates balances and delegated-ness. The names of these assumptions are fairly descriptive.

 *)

Class EVMAssupmtions :=
  {
    
balanceOfRevertSender: forall s tx,
  maxTxFee tx <= balanceOfAc s (sender tx)
  -> balanceOfAc (revertTxState s tx) (sender tx)
     = balanceOfAc s (sender tx) - maxTxFee tx;

balanceOfRevertOther: forall s tx ac,
  ac <> (sender tx)
  -> balanceOfAc (revertTxState s tx) ac
     = balanceOfAc s ac;


revertTxDelegationUpdCore: forall tx s,
  let sf :=  (revertTxState s tx) in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && asbool (ac ∉ (undels tx.1.2)))
                || asbool (ac ∈ (dels tx.1.2)));

execTxDelegationUpdCore: forall tx s,
  let sf :=  (evmExecTxCoreState s tx) in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && asbool (ac ∉ (undels tx.1.2)))
                || asbool (ac ∈ (dels tx.1.2)));

execTxSenderBalCore: forall tx s,
  maxTxFee tx <= balanceOfAc s (sender tx) ->
  let sf :=  (evmExecTxCoreState s tx) in
  addrDelegated sf (sender tx) = false
   ->   balanceOfAc s (sender tx) - ( maxTxFee tx + value tx + maxStorageFee tx) <= balanceOfAc sf (sender tx)
        \/  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - (maxTxFee tx);


(** One caveat in the assumption below is that it assumes that the account [ac] does not receive so much credit that it overflows 2^256. In practice, this should never happen, assuming the ETH supply is well below 2^256. Thus, we can assume that [evmExecTxCore] caps the balance at [2^256] should it overflow, instead of wrapping around, which may violate this assumption. *)
execTxCannotDebitNonDelegatedNonContractAccountsCore: forall tx s,
  let sf :=  (evmExecTxCoreState s tx) in
  forall ac, ac <> sender tx
              -> (addrDelegated sf ac || isSC sf ac) = false
                 ->  balanceOfAc s ac <= balanceOfAc sf ac;


changedAccountSetSound: forall tx s,
  let '(((sf, sf_res), changedAccounts), _) :=  (evmExecTxCore s tx) in
  (forall ac, ac ∉ changedAccounts -> sf ac = s ac);
}.

(** ** lemmas about execution
 *)

(* begin hide *)
Lemma delayedReserveBal_updateExtraStateBase s tx addr n :
  delayedReserveBal (updateExtraStateBase s tx addr) n = delayedReserveBal (s addr) n.
Proof.
  unfold updateExtraStateBase, delayedReserveBal. simpl. reflexivity.
Qed.

Lemma delayedReserveBalOfAddr_unfold s addr n :
  delayedReserveBalOfAddr s addr n = delayedReserveBal (s addr) n.
Proof. reflexivity. Qed.

Lemma lastTxInBlockIndex_promotePendingReserveBal es n :
  lastTxInBlockIndex (promotePendingReserveBal es n) = lastTxInBlockIndex es.
Proof using K K_pos.
  unfold promotePendingReserveBal.
  destruct (pendingReserveBal es) as [[v blk]|] ; simpl; auto.
  destruct (asbool (blk + K <= n)%N); simpl; auto.
Qed.

Lemma lastDelUndelInBlockIndex_promotePendingReserveBal es n :
  lastDelUndelInBlockIndex (promotePendingReserveBal es n) = lastDelUndelInBlockIndex es.
Proof using K K_pos.
  unfold promotePendingReserveBal.
  destruct (pendingReserveBal es) as [[v blk]|] ; simpl; auto.
  destruct (asbool (blk + K <= n)%N); simpl; auto.
Qed.

Lemma promotePendingReserveBal_idem es n :
  promotePendingReserveBal (promotePendingReserveBal es n) n =
  promotePendingReserveBal es n.
Proof using K K_pos.
  unfold promotePendingReserveBal.
  destruct (pendingReserveBal es) as [[v blk]|] eqn:Hpend.
  - destruct (asbool (blk + K <= n)%N) eqn:Hprom.
    + simpl. reflexivity.
    + rewrite Hpend. simpl. rewrite Hprom. reflexivity.
  - rewrite Hpend. simpl. reflexivity.
Qed.

Lemma delayedReserveBal_promoteWithinK es (n0 n: N) :
  (n0 <= n)%N ->
  (n < n0 + K)%N ->
  delayedReserveBal (promotePendingReserveBal es n0) n =
  delayedReserveBal es n.
Proof using K K_pos.
  intros Hle _Hlt.
  unfold delayedReserveBal, promotePendingReserveBal.
  destruct (pendingReserveBal es) as [[v blk]|] eqn:Hpend; simpl.
  - destruct (asbool (blk + K <= n0)%N) eqn:Hprom; simpl.
    + apply bool_decide_eq_true_1 in Hprom.
      assert (blk + K <= n)%N by (eapply N.le_trans; [exact Hprom|exact Hle]).
      rewrite bool_decide_true; [reflexivity|assumption].
    + rewrite Hpend. reflexivity.
  - rewrite Hpend. reflexivity.
Qed.

Lemma settledReserveBal_promote es n :
  settledReserveBal (promotePendingReserveBal es n) = delayedReserveBal es n.
Proof using K K_pos.
  unfold promotePendingReserveBal, delayedReserveBal.
  destruct (pendingReserveBal es) as [[v blk]|] eqn:Hpend; simpl; auto.
  destruct (asbool (blk + K <= n)%N); simpl; auto.
Qed.

Lemma settledReserveBal_applyReserveBalUpdate es n newRb :
  settledReserveBal (applyReserveBalUpdate es n newRb) = settledReserveBal es.
Proof using K K_pos.
  unfold applyReserveBalUpdate.
  destruct (pendingReserveBal es) as [[v blk]|] eqn:Hpend; simpl.
  - case_bool_decide; reflexivity.
  - reflexivity.
Qed.

Lemma lastTxInBlockIndex_applyReserveBalUpdate es n newRb :
  lastTxInBlockIndex (applyReserveBalUpdate es n newRb) = lastTxInBlockIndex es.
Proof using K K_pos.
  unfold applyReserveBalUpdate.
  destruct (pendingReserveBal es) as [[v blk]|] eqn:Hpend; simpl.
  - case_bool_decide; reflexivity.
  - reflexivity.
Qed.


Lemma lastDelUndelInBlockIndex_applyReserveBalUpdate es n newRb :
  lastDelUndelInBlockIndex (applyReserveBalUpdate es n newRb) = lastDelUndelInBlockIndex es.
Proof using K K_pos.
  unfold applyReserveBalUpdate.
  destruct (pendingReserveBal es) as [[v blk]|] eqn:Hpend; simpl.
  - case_bool_decide; reflexivity.
  - reflexivity.
Qed.

Lemma lastTxInBlockIndex_applyReserveBalUpdatesForAddr es n addr updates :
  lastTxInBlockIndex (applyReserveBalUpdatesForAddr es n addr updates) =
  lastTxInBlockIndex es.
Proof using K K_pos.
  revert es.
  induction updates as [|[a newRb] tl IH]; intros es; simpl; [reflexivity|].
  case_bool_decide; simpl.
  - specialize (IH (applyReserveBalUpdate es n newRb)).
    eapply transitivity; [exact IH|].
    apply lastTxInBlockIndex_applyReserveBalUpdate.
  - apply IH.
Qed.

Lemma lastDelUndelInBlockIndex_applyReserveBalUpdatesForAddr es n addr updates :
  lastDelUndelInBlockIndex (applyReserveBalUpdatesForAddr es n addr updates) =
  lastDelUndelInBlockIndex es.
Proof using K K_pos.
  revert es.
  induction updates as [|[a newRb] tl IH]; intros es; simpl; [reflexivity|].
  case_bool_decide; simpl.
  - specialize (IH (applyReserveBalUpdate es n newRb)).
    eapply transitivity; [exact IH|].
    apply lastDelUndelInBlockIndex_applyReserveBalUpdate.
  - apply IH.
Qed.

Lemma delayedReserveBal_applyReserveBalUpdate_ltK es (n0 n: N) newRb :
  (n < n0 + K)%N ->
  delayedReserveBal (applyReserveBalUpdate es n0 newRb) n = delayedReserveBal es n.
Proof using K K_pos.
  intros Hlt.
  unfold applyReserveBalUpdate.
  destruct (pendingReserveBal es) as [[v blk]|] eqn:Hpend; simpl.
  - destruct (decide (blk = n0)) as [Hblock|Hblock].
    + rewrite bool_decide_true; [|exact Hblock].
      unfold delayedReserveBal. simpl.
      rewrite bool_decide_false; [|lia].
      rewrite Hpend. simpl.
      rewrite Hblock.
      rewrite bool_decide_false; [reflexivity|lia].
    + rewrite bool_decide_false; [|exact Hblock].
      reflexivity.
  - unfold delayedReserveBal. simpl.
    rewrite bool_decide_false; [|lia].
    rewrite Hpend. simpl. reflexivity.
Qed.

Lemma delayedReserveBal_applyReserveBalUpdatesForAddr_ltK es (n0 n: N) addr updates :
  (n < n0 + K)%N ->
  delayedReserveBal (applyReserveBalUpdatesForAddr es n0 addr updates) n = delayedReserveBal es n.
Proof using K K_pos.
  revert es.
  induction updates as [|[a newRb] tl IH]; intros es Hlt; simpl; [reflexivity|].
  case_bool_decide; simpl.
  - specialize (IH (applyReserveBalUpdate es n0 newRb) Hlt).
    eapply transitivity; [exact IH|].
    apply delayedReserveBal_applyReserveBalUpdate_ltK; exact Hlt.
  - apply IH; exact Hlt.
Qed.

Lemma settledReserveBal_applyReserveBalUpdatesForAddr es n addr updates :
  settledReserveBal (applyReserveBalUpdatesForAddr es n addr updates) = settledReserveBal es.
Proof using K K_pos.
  revert es.
  induction updates as [|[a newRb] tl IH]; intros es; simpl; [reflexivity|].
  case_bool_decide; simpl.
  - specialize (IH (applyReserveBalUpdate es n newRb)).
    eapply transitivity; [exact IH|].
    apply settledReserveBal_applyReserveBalUpdate.
  - apply IH.
Qed.


(* TODO: remove *)
Lemma updateKeyLkp3  {T} `{c: EqDecision T} {V} (m: T -> V) (a b: T) (f: V -> V) :
  (updateKey m a f)  b = if (asbool (b=a)) then (f (m a)) else m  b.
Proof using K K_pos.
  reflexivity.
Qed.

Lemma addrDelegatedUnchangedByBalUpd s  f addr baladdr:
  addrDelegated (updateBalanceOfAc s baladdr f) addr = addrDelegated s addr.
Proof.
  unfold addrDelegated.
  simpl.
  Transparent updateBalanceOfAc.
  unfold updateBalanceOfAc.
  symmetry.
  unfold updateKey.
  case_bool_decide; subst; auto.
  simpl.
  destruct (s baladdr); simpl.
  reflexivity.
Qed.

Context {eas: EVMAssupmtions}.
Lemma execTxDelegationUpdCoreImpl tx s:
  let sf :=  (evmExecTxCoreState s tx) in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || asbool (ac ∈ (addrsDelUndelByTx tx))).
Proof using eas K K_pos.
  simpl.
  intros ?.
  rewrite execTxDelegationUpdCore; auto.
  repeat rewrite Is_true_true.
  intros Hp.
  autorewrite with iff in Hp.
  destruct Hp; forward_reason; rwHyps; auto;[].
  unfold addrsDelUndelByTx.
  simpl.
  resdec ltac:(set_solver).
  autorewrite with syntactic.
  reflexivity.
Qed.

Lemma revertTxDelegationUpdCoreImpl tx s:
  let sf :=  (revertTxState s tx) in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || asbool (ac ∈ (addrsDelUndelByTx tx))).
Proof using eas K K_pos.
  simpl.
  intros ?.
  rewrite revertTxDelegationUpdCore;auto.
  repeat rewrite Is_true_true.
  intros Hp.
  autorewrite with iff in Hp.
  destruct Hp; forward_reason; rwHyps; auto;[].
  unfold addrsDelUndelByTx.
  simpl.
  resdec ltac:(set_solver).
  autorewrite with syntactic.
  reflexivity.
Qed.

Lemma balanceOfUpd s ac f acp:
  balanceOfAc (updateBalanceOfAc s ac f) acp = if (asbool (ac=acp)) then f (balanceOfAc s ac) else (balanceOfAc s acp).
Proof using eas K K_pos.
  unfold updateBalanceOfAc, updateKey, balanceOfAc. simpl.
  case_bool_decide; simpl; subst; auto; resdec ltac:(congruence);[].
  destruct (s ac); auto.
Qed.

Lemma execTxOtherBalanceLB tx s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let sf := (execValidatedTx s tx).1 in
  (forall ac,
      let ReserveBal := delayedReserveBalOfAddr s.2 ac (txBlockNum tx) in
      (ac <> sender tx)
       -> if (isSC sf.1 ac)
          then True
          else ReserveBal `min` (balanceOfAcA s ac) <= (balanceOfAcA sf ac)).
Proof using eas K K_pos.
  intros Hfee sf ac ReserveBal Hneq.
  subst sf.
  unfold execValidatedTx in *.
  unfold allFinalBalSufficient in *.
  simpl in *.
  pose proof (changedAccountSetSound tx s.1) as Hsnd.
  rdestruct (evmExecTxCore s.1 tx) as [[[postTxState postTxRes] changed] rbUpdate].
  rememberForallb.
  unfold balanceOfAcA in *.
  destruct fb; simpl in *.
  - (* success *)
    remember (isSC postTxState ac) as sac.
    destruct sac; [exact I|].
    symmetry in Heqfb.
    rewrite forallb_spec in Heqfb.
    unfold finalBalSufficient in Heqfb.
    destruct (decide (ac ∈ changed)).
    + specialize (Heqfb ac ltac:(auto)).
      rewrite <- Heqsac in Heqfb.
      rewrite bool_decide_false in Heqfb; [|congruence].
      rewrite bool_decide_eq_true in Heqfb.
      exact Heqfb.
    + unfold balanceOfAc.
      rewrite Hsnd; auto. lia.
  - (* revert *)
    destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
    pose proof (balanceOfRevertOther s.1 tx ac ltac:(auto)) as Hrevbal.
    unfold revertTxState in Hrevbal.
    rewrite Hrev in Hrevbal. simpl in Hrevbal.
    rewrite Hrevbal.
    remember (isSC revState ac) as srev.
    destruct srev; [exact I|].
    resolveDecide congruence.
    destruct (decide (ReserveBal <= balanceOfAc s.1 ac)) as [Hle|Hgt].
    + rewrite N.min_l; [exact Hle|assumption].
    + assert (balanceOfAc s.1 ac <= ReserveBal) by lia.
      rewrite N.min_r; [apply N.le_refl|assumption].
Qed.


Lemma execTxSenderBal tx s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let ReserveBal := delayedReserveBalOfAddr s.2 (sender tx) (txBlockNum tx) in
  let sf := (execValidatedTx s tx).1 in
  isSC sf.1 (sender tx) = false->
  (if isAllowedToEmpty s [] tx
   then balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx + maxStorageFee tx) <= balanceOfAcA sf (sender tx)
        \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
  else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx))).
Proof using eas K K_pos.
  intros Hfee.
  cbn.
  intros Hsc.
  pose proof (execTxSenderBalCore tx s.1 Hfee) as Hc.
  simpl in Hc.
  unfold isAllowedToEmpty.
  unfold execValidatedTx.
  unfold allFinalBalSufficient in *.
  unfold finalBalSufficient in *.
  pose proof (changedAccountSetSound tx s.1) as Hsnd.
  pose proof (execTxDelegationUpdCore tx s.1 (sender tx)) as Hsf.
  destruct (evmExecTxCore s.1 tx) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl in Hsf.
  unfold isAllowedToEmptyExec. unfold isAllowedToEmpty.
  intros.
  unfold balanceOfAcA in *.
  rdestruct (addrDelegated s.1 (sender tx)); simpl in *.
  {
    rememberForallb.
    unfold balanceOfAcA in *.
    destruct fb; try lia.
    2:{
      simpl in *.
      destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
      pose proof (balanceOfRevertSender s.1 tx ltac:(auto)) as Hrevbal.
      unfold revertTxState in Hrevbal.
      rewrite Hrev in Hrevbal. simpl in Hrevbal.
      rewrite Hrevbal.
      resolveDecide congruence. lia.
    }
    symmetry in Heqfb.
    assert (Hallowed : isAllowedToEmptyExec s tx = false).
    { unfold isAllowedToEmptyExec, isAllowedToEmpty.
      rewrite <- Heqrd. simpl. reflexivity. }
    pose proof Heqfb as Hfb_all.
    assert (Hfb_true : forallb (finalBalSufficient s postTxState tx) changed = true).
    { unfold finalBalSufficient. rewrite Hallowed. exact Hfb_all. }
    assert (Hsfstate : (execValidatedTx s tx).1.1 = postTxState).
    { unfold execValidatedTx. rewrite Hcore. simpl.
      unfold allFinalBalSufficient.
      rewrite Hfb_true. reflexivity. }
    assert (Hsc_post : isSC postTxState (sender tx) = false).
    { rewrite <- Hsfstate. exact Hsc. }
    rewrite  forallb_spec in Heqfb.
    destruct (decide (sender tx ∈ changed));
      [| unfold balanceOfAc; simpl; rewrite Hsnd; auto; lia].
    specialize (Heqfb (sender tx) ltac:(auto)).
    resolveDecide congruence.
    simpl in *.
    rewrite Hsc_post in Heqfb.
    case_bool_decide; try lia.
  }
  {
    autorewrite with syntactic in *.
    rewrite Hsf in Hc.
    rememberForallb.
    remember (~~ (existsDelUndelTxWithinK s tx || asbool (sender tx ∈ addrsDelUndelByTx tx)) && ~~ existsTxWithinK s tx) as rd1; destruct rd1;
      simpl in *.
    {
      symmetry in Heqrd1.
      autorewrite with iff in *.
      unfold addrsDelUndelByTx in Heqrd1.
      forward_reason.
      specialize (Hc ltac:(set_solver)).
      destruct fb; simpl in *.
      - unfold evmExecTxCoreState in Hc.
        rewrite Hcore in Hc. simpl in Hc.
        exact Hc.
      - auto; try lia.
        destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
        pose proof (balanceOfRevertSender s.1 tx ltac:(auto)) as Hrevbal.
        unfold revertTxState in Hrevbal.
        rewrite Hrev in Hrevbal. simpl in Hrevbal.
        rewrite Hrevbal; auto.
    }
    {
      destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
      pose proof (balanceOfRevertSender s.1 tx ltac:(auto)) as Hrevbal.
      unfold revertTxState in Hrevbal.
      rewrite Hrev in Hrevbal. simpl in Hrevbal.
      destruct fb; simpl in *; orient_rwHyps; simpl in *;
        try (rewrite Hrevbal;[]);
        try resolveDecide congruence; try auto;
        try lia;[].
      assert (Hallowed : isAllowedToEmptyExec s tx = false).
      { unfold isAllowedToEmptyExec, isAllowedToEmpty.
        rewrite Heqrd. simpl.
        rewrite app_nil_r.
        resolveDecide congruence.
        rewrite orb_false_r.
        rewrite Heqrd1. reflexivity. }
      pose proof Heqfb as Hfb_all.
      unfold finalBalSufficient in Hfb_all.
      assert (Hsfstate : (execValidatedTx s tx).1.1 = postTxState).
      { unfold execValidatedTx. rewrite Hcore. simpl.
        unfold allFinalBalSufficient.
        unfold finalBalSufficient. rewrite Hallowed.
        rewrite Hfb_all. reflexivity. }
      assert (Hsc_post : isSC postTxState (sender tx) = false).
      { rewrite <- Hsfstate. exact Hsc. }
      rewrite  forallb_spec in Heqfb.
      destruct (decide (sender tx ∈ changed)).
      {
        specialize (Heqfb (sender tx) ltac:(auto)).
        destruct (bool_decide (sender tx = sender tx)) eqn:Hdec; [|].
        2:{
          apply (proj1 (bool_decide_eq_false _)) in Hdec.
          exfalso. apply Hdec. reflexivity.
        }
        simpl in Heqfb.
        rewrite Hsc_post in Heqfb.
        simpl in Heqfb.
        try (apply (proj1 (bool_decide_eq_true _)) in Heqfb);
        try (symmetry in Heqfb; apply (proj1 (bool_decide_eq_true _)) in Heqfb).
        exact Heqfb.
      }
      {
        unfold balanceOfAc in *.
        forward_reason.
        rewrite Hsnd; auto.
        lia.
      }

    }

  }
Qed.

Lemma execTxDelegationUpd tx s:
  let sf := (execValidatedTx s tx).1 in
  (forall ac, addrDelegated (sf.1) ac  -> addrDelegated (s.1) ac || asbool (ac ∈ (addrsDelUndelByTx tx))).
Proof using eas K K_pos.
  intros ? ? Hd.
  subst sf.
  unfold execValidatedTx in Hd.
  simpl in *.
  rewrite pairEta in Hd.
  destruct (evmExecTxCore s.1 tx) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl in *.
  case_match.
  {
    pose proof (execTxDelegationUpdCoreImpl tx s.1) as HcoreImpl.
    unfold evmExecTxCoreState in HcoreImpl.
    rewrite Hcore in HcoreImpl.
    simpl in HcoreImpl.
    apply HcoreImpl in Hd; auto.
  }
  {
    destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in Hd.
    pose proof (revertTxDelegationUpdCoreImpl tx s.1) as HrevImpl.
    unfold revertTxState in HrevImpl.
    rewrite Hrev in HrevImpl. simpl in HrevImpl.
    apply HrevImpl in Hd; auto.
  }
Qed.


Lemma execTxCannotDebitNonDelegatedNonContractAccounts tx s:
  let sf := (execValidatedTx s tx).1 in
  (forall ac, ac <> sender tx
              -> if (addrDelegated (sf.1) ac || isSC (sf.1) ac)
                 then True
                 else balanceOfAcA s ac <= balanceOfAcA sf ac).
Proof using eas K K_pos.
  intros. subst sf.
  pose proof (execTxCannotDebitNonDelegatedNonContractAccountsCore tx s.1 ac ltac:(auto)) as Htx.
  unfold execValidatedTx.
  simpl in *.
  case_match_concl; auto;[].
  unfold balanceOfAcA in *.
  destruct (evmExecTxCore s.1 tx) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl in *.
  unfold evmExecTxCoreState in Htx.
  rewrite Hcore in Htx.
  simpl in Htx.
  destruct (allFinalBalSufficient s postTxState changed tx) eqn:Hfb; simpl in *; try lia.
  {
    apply Htx; auto.
  }
  {
    destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
    pose proof (balanceOfRevertOther s.1 tx ac ltac:(auto)) as Hrevbal.
    unfold revertTxState in Hrevbal.
    rewrite Hrev in Hrevbal. simpl in Hrevbal.
    rewrite Hrevbal; auto.
  }
Qed.

Lemma execS2 s txlast:
  (execValidatedTx s txlast).1.2 =
    let '(((postTxState, _), changedAccounts), rbUpdate) := evmExecTxCore s.1 txlast in
    if allFinalBalSufficient s postTxState changedAccounts txlast
    then updateExtraState s.2 txlast rbUpdate
    else updateExtraStateNoReserve s.2 txlast.
Proof using K K_pos.
  unfold execValidatedTx.
  destruct (evmExecTxCore s.1 txlast) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl.
  destruct (allFinalBalSufficient s postTxState changed txlast); simpl.
  - reflexivity.
  - destruct (revertTx s.1 txlast) as [revState revRes]; simpl; reflexivity.
Qed.


Lemma lastTxInBlockIndexUpd s txlast:
  lastTxInBlockIndex ((execValidatedTx s txlast).1.2 (sender txlast))
  = Some (txBlockNum txlast).
Proof using K K_pos.
  rewrite execS2.
  destruct (evmExecTxCore s.1 txlast) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl.
  destruct (allFinalBalSufficient s postTxState changed txlast); simpl.
  - unfold updateExtraState. simpl.
    set (oldes := updateExtraStateBase s.2 txlast (sender txlast)).
    set (oldes' := promotePendingReserveBal oldes (txBlockNum txlast)).
    rewrite lastTxInBlockIndex_applyReserveBalUpdatesForAddr.
    rewrite lastTxInBlockIndex_promotePendingReserveBal.
    unfold oldes, updateExtraStateBase. simpl.
    case_bool_decide; [reflexivity|congruence].
  - unfold updateExtraStateNoReserve. simpl.
    rewrite lastTxInBlockIndex_promotePendingReserveBal.
    unfold updateExtraStateBase. simpl.
    case_bool_decide; [reflexivity|congruence].
Qed.

Lemma otherTxLstSenderLkp s addr txlast :
  addr <> sender txlast
  ->
    lastTxInBlockIndex ((execValidatedTx s txlast).1.2 addr)
    = lastTxInBlockIndex (s.2 addr).
Proof using K K_pos.
  rewrite execS2.
  destruct (evmExecTxCore s.1 txlast) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl. intros Hneq.
  destruct (allFinalBalSufficient s postTxState changed txlast); simpl.
  - unfold updateExtraState. simpl.
    rewrite lastTxInBlockIndex_applyReserveBalUpdatesForAddr.
    rewrite lastTxInBlockIndex_promotePendingReserveBal.
    unfold updateExtraStateBase. simpl.
    case_bool_decide; [congruence|reflexivity].
  - unfold updateExtraStateNoReserve. simpl.
    rewrite lastTxInBlockIndex_promotePendingReserveBal.
    unfold updateExtraStateBase. simpl.
    case_bool_decide; [congruence|reflexivity].
Qed.


Lemma delgUndelgUpdTx txlast s addr:
  addr ∈  addrsDelUndelByTx txlast
  -> lastDelUndelInBlockIndex ((execValidatedTx s txlast).1.2 addr) = Some (txBlockNum txlast).
Proof using eas K K_pos.
  rewrite execS2.
  destruct (evmExecTxCore s.1 txlast) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl. intros Hmem.
  destruct (allFinalBalSufficient s postTxState changed txlast); simpl.
  - unfold updateExtraState. simpl.
    rewrite lastDelUndelInBlockIndex_applyReserveBalUpdatesForAddr.
    rewrite lastDelUndelInBlockIndex_promotePendingReserveBal.
    unfold updateExtraStateBase. simpl.
    case_bool_decide; [reflexivity|exfalso; set_solver].
  - unfold updateExtraStateNoReserve. simpl.
    rewrite lastDelUndelInBlockIndex_promotePendingReserveBal.
    unfold updateExtraStateBase. simpl.
    case_bool_decide; [reflexivity|exfalso; set_solver].
Qed.

Lemma otherDelUndelLkp s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    lastDelUndelInBlockIndex ((execValidatedTx s txlast).1.2 addr)
    = lastDelUndelInBlockIndex (s.2  addr).
Proof using eas K K_pos.
  rewrite execS2.
  destruct (evmExecTxCore s.1 txlast) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl. intros Hnmem.
  destruct (allFinalBalSufficient s postTxState changed txlast); simpl.
  - unfold updateExtraState. simpl.
    rewrite lastDelUndelInBlockIndex_applyReserveBalUpdatesForAddr.
    rewrite lastDelUndelInBlockIndex_promotePendingReserveBal.
    unfold updateExtraStateBase. simpl.
    case_bool_decide; [exfalso; apply Hnmem; assumption|reflexivity].
  - unfold updateExtraStateNoReserve. simpl.
    rewrite lastDelUndelInBlockIndex_promotePendingReserveBal.
    unfold updateExtraStateBase. simpl.
    case_bool_decide; [exfalso; apply Hnmem; assumption|reflexivity].
Qed.

Lemma otherDelUndelDelegationStatusUnchanged s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    addrDelegated ((execValidatedTx s txlast).1.1) addr
    = addrDelegated s.1 addr.
Proof using eas K K_pos.
  intros Hn.
  unfold execValidatedTx.
  destruct (evmExecTxCore s.1 txlast) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl in *.
  case_match;
    simpl in *.
  2:{
    destruct (revertTx s.1 txlast) as [revState revRes] eqn:Hrev; simpl in *.
    pose proof (revertTxDelegationUpdCore txlast s.1) as HrevCore.
    unfold revertTxState in HrevCore.
    rewrite Hrev in HrevCore. simpl in HrevCore.
    rewrite HrevCore; auto;[].
    unfold addrsDelUndelByTx in *.
    rewrite bool_decide_true;[| set_solver].
    rewrite bool_decide_false;[|set_solver].
    autorewrite with syntactic.
    reflexivity.
  }
  {
    pose proof (execTxDelegationUpdCore txlast s.1 addr) as Hd.
    unfold evmExecTxCoreState in Hd.
    rewrite Hcore in Hd.
    simpl in Hd.
    rewrite Hd.
    clear Hd. revert Hn. clear.
    unfold addrsDelUndelByTx in *.
    intros.
    rewrite bool_decide_true; [| set_solver].
    rewrite bool_decide_false;[|set_solver].
    autorewrite with syntactic.
    reflexivity.
  }
Qed.

Set Nested Proofs Allowed.


Lemma isAllowedToEmptyImpl s tx inter a:
  isAllowedToEmpty s (tx::inter) a = true
  -> sender tx <> sender a
     /\ addrDelegated ((execValidatedTx s tx).1.1) (sender a) = false.
Proof using eas K K_pos.
  intros  Hae.
  unfold isAllowedToEmpty in *.
  simpl in *.
  destruct (decide (sender a = sender tx)).
  {
    assert (asbool (sender a ∈ sender tx :: map sender inter)= true) as Heq.
    { rewrite bool_decide_true; set_solver. }
    rewrite Heq in Hae.
    autorewrite with syntactic in Hae.
    congruence.
  }
  split_and; auto.
  rewrite <- not_true_iff_false.
  intros Hc.
  pose proof (execTxDelegationUpd tx s) as Hdel.
  simpl in Hdel.
  specialize (Hdel  (sender a)).
  repeat rewrite Is_true_true in Hdel.
  specialize (Hdel Hc).
  apply orb_prop in Hdel.
  destruct Hdel as [Hdel | Hdel].
  {
    rewrite Hdel in Hae.
    simpl.
    autorewrite with syntactic in Hae.
    congruence.
  }
  {
    rewrite bool_decide_eq_true in Hdel.
    case_bool_decide; try set_solver.
    autorewrite with syntactic in Hae.
    congruence.
  }
Qed.

Lemma delayedReserveBalOfAddrSame s tx a n:
  sender tx <> a
  -> txBlockNum tx <= n
  -> n < txBlockNum tx + K
  -> delayedReserveBalOfAddr ((execValidatedTx s tx).1.2) a n
     = delayedReserveBalOfAddr s.2 a n.
Proof using K K_pos.
  intros _Hn Hle Hlt.
  rewrite execS2.
  destruct (evmExecTxCore s.1 tx) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl.
  destruct (allFinalBalSufficient s postTxState changed tx); simpl.
  - unfold updateExtraState. simpl.
    unfold delayedReserveBalOfAddr. simpl.
    set (oldes := updateExtraStateBase s.2 tx a).
    set (oldes' := promotePendingReserveBal oldes (txBlockNum tx)).
    rewrite (delayedReserveBal_applyReserveBalUpdatesForAddr_ltK
               oldes' (txBlockNum tx) n a rbUpdate); [|exact Hlt].
    rewrite (delayedReserveBal_promoteWithinK oldes (txBlockNum tx) n);
      [|exact Hle|exact Hlt].
    rewrite <- (delayedReserveBal_updateExtraStateBase s.2 tx a n).
    reflexivity.
  - unfold updateExtraStateNoReserve. simpl.
    unfold delayedReserveBalOfAddr. simpl.
    set (oldes := updateExtraStateBase s.2 tx a).
    rewrite (delayedReserveBal_promoteWithinK oldes (txBlockNum tx) n);
      [|exact Hle|exact Hlt].
    rewrite (delayedReserveBal_updateExtraStateBase s.2 tx a n).
    reflexivity.
Qed.

Lemma delayedReserveBalOfAddrSenderWithinK s tx n:
  txBlockNum tx <= n ->
  n < txBlockNum tx + K ->
  delayedReserveBalOfAddr ((execValidatedTx s tx).1.2) (sender tx) n
     = delayedReserveBalOfAddr s.2 (sender tx) n.
Proof using K K_pos.
  intros Hle Hlt.
  rewrite execS2.
  destruct (evmExecTxCore s.1 tx) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl.
  destruct (allFinalBalSufficient s postTxState changed tx); simpl.
  - unfold updateExtraState, delayedReserveBalOfAddr. simpl.
    set (oldes := updateExtraStateBase s.2 tx (sender tx)).
    set (oldes' := promotePendingReserveBal oldes (txBlockNum tx)).
    change (delayedReserveBal (applyReserveBalUpdatesForAddr oldes' (txBlockNum tx) (sender tx) rbUpdate) n =
            delayedReserveBal (s.2 (sender tx)) n).
    rewrite (delayedReserveBal_applyReserveBalUpdatesForAddr_ltK oldes' (txBlockNum tx) n (sender tx) rbUpdate); [|exact Hlt].
    rewrite (delayedReserveBal_promoteWithinK oldes (txBlockNum tx) n); [|exact Hle|exact Hlt].
    unfold oldes, updateExtraStateBase. simpl. reflexivity.
  - (* revert *)
    unfold updateExtraStateNoReserve. simpl.
    rewrite delayedReserveBalOfAddr_unfold.
    rewrite delayedReserveBalOfAddr_unfold.
    set (oldes := updateExtraStateBase s.2 tx (sender tx)).
    change (delayedReserveBal (promotePendingReserveBal oldes (txBlockNum tx)) n =
            delayedReserveBal (s.2 (sender tx)) n).
    rewrite (delayedReserveBal_promoteWithinK oldes (txBlockNum tx) n); [|exact Hle|exact Hlt].
    unfold oldes, updateExtraStateBase. simpl. reflexivity.
Qed.

Lemma delayedReserveBalOfAddrWithinK s tx a n:
  txBlockNum tx <= n ->
  n < txBlockNum tx + K ->
  delayedReserveBalOfAddr ((execValidatedTx s tx).1.2) a n
     = delayedReserveBalOfAddr s.2 a n.
Proof using K K_pos.
  intros Hle Hlt.
  destruct (decide (a = sender tx)) as [->|Hneq].
  - apply delayedReserveBalOfAddrSenderWithinK; auto.
  - apply delayedReserveBalOfAddrSame; auto.
Qed.

Lemma settledReserveBal_after_exec_any s tx addr :
  settledReserveBal ((execValidatedTx s tx).1.2 addr) =
  delayedReserveBal (s.2 addr) (txBlockNum tx).
Proof using K K_pos.
  rewrite execS2.
  destruct (evmExecTxCore s.1 tx) as [[[postTxState postTxRes] changed] rbUpdate] eqn:Hcore.
  simpl.
  destruct (allFinalBalSufficient s postTxState changed tx); simpl.
  - unfold updateExtraState. simpl.
    set (oldes := updateExtraStateBase s.2 tx addr).
    set (oldes' := promotePendingReserveBal oldes (txBlockNum tx)).
    rewrite settledReserveBal_applyReserveBalUpdatesForAddr.
    rewrite settledReserveBal_promote.
    unfold oldes, updateExtraStateBase. simpl. reflexivity.
  - unfold updateExtraStateNoReserve. simpl.
    set (oldes := updateExtraStateBase s.2 tx addr).
    rewrite settledReserveBal_promote.
    unfold oldes, updateExtraStateBase. simpl. reflexivity.
Qed.

Lemma settledReserveBal_after_exec s tx :
  settledReserveBal ((execValidatedTx s tx).1.2 (sender tx)) =
  delayedReserveBal (s.2 (sender tx)) (txBlockNum tx).
Proof using K K_pos.
  apply settledReserveBal_after_exec_any.
Qed.

Lemma delayedReserveBalOfAddr_at0 s addr :
  delayedReserveBalOfAddr s addr 0 = settledReserveBal (s addr).
Proof using K_pos K.
  unfold delayedReserveBalOfAddr, delayedReserveBal.
  destruct (pendingReserveBal (s addr)) as [[v blk]|] eqn:Hpend; simpl.
  - destruct (asbool (blk + K <= 0)) eqn:Hle; simpl.
    + apply bool_decide_eq_true in Hle.
      have Hk_le : K <= blk + K := N.le_add_l _ _.
      have Hk0 : K <= 0 := N.le_trans _ _ _ Hk_le Hle.
      have Hcontra : (0 < 0)%N by (eapply N.lt_le_trans; [exact K_pos|exact Hk0]).
      exfalso; exact (N.lt_irrefl 0 Hcontra).
    + reflexivity.
  - reflexivity.
Qed.

Lemma delayedReserveBalOfAddr_after_exec0 s tx addr :
  delayedReserveBalOfAddr ((execValidatedTx s tx).1.2) addr 0 =
  delayedReserveBalOfAddr s.2 addr (txBlockNum tx).
Proof using K_pos K.
  rewrite delayedReserveBalOfAddr_at0.
  rewrite settledReserveBal_after_exec_any.
  reflexivity.
Qed.

Lemma delayedReserveBalOfAddrSender0 s tx :
  delayedReserveBalOfAddr ((execValidatedTx s tx).1.2) (sender tx) 0 =
  delayedReserveBalOfAddr s.2 (sender tx) (txBlockNum tx).
Proof using K_pos K.
  apply delayedReserveBalOfAddr_after_exec0.
Qed.


Lemma emptyBalanceUb s tx inter a:
  isSC ((execValidatedTx s tx).1.1) (sender a) = false
  -> isAllowedToEmpty s (tx :: inter) a = true
  -> balanceOfAc s.1 (sender a) ≤ balanceOfAc ((execValidatedTx s tx).1.1) (sender a).
Proof using eas K K_pos.
  intros Hsc Hae.
  pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s (sender a)) as Hs.
  simpl in Hs.
  apply isAllowedToEmptyImpl in Hae; auto.
  forward_reason.
  rewrite Haer in Hs.
  simpl in *.
  rewrite Hsc in Hs.
  unfold balanceOfAcA in *.
  simpl in *.
  lia.
Qed.

(*
Definition rbAfterTx s tx :=
  configuredReserveBalOfAddr (updateExtraState s tx) (sender tx).

Lemma configuredReserveBalOfAddrSpec s tx a:
  configuredReserveBalOfAddr ((execValidatedTx s tx).1.2) a
  = if asbool (a=sender tx)
    then rbAfterTx s.2 tx
    else configuredReserveBalOfAddr s.2 a.
Admitted.

Lemma configuredReserveBalOfAddrSame s tx  a:
  sender tx <> a
  -> (configuredReserveBalOfAddr ((execValidatedTx s tx).1.2) a
      =
        configuredReserveBalOfAddr s.2 a).
Admitted.

Lemma configuredReserveBalOfAddrSame2 s tx inter a:
  isAllowedToEmpty s (tx :: inter) a = true
  -> (configuredReserveBalOfAddr ((execValidatedTx s tx).1.2) (sender a)
      =
        configuredReserveBalOfAddr s.2 (sender a)).
Admitted.
*)


Lemma isSCFalsePresExec l s tx:
  (forall txext, txext ∈ (tx::l) ->  txCannotCreateContractAtAddrs txext (map sender (tx::l)))
  -> (forall ac, ac ∈ (map sender (tx::l)) -> isSC s.1 ac = false)
  -> (forall ac, ac ∈ (map sender (tx::l)) -> isSC ((execValidatedTx s tx).1.1) ac = false).
Proof using eas K K_pos.
  intros Heoac Hsc.
  intros.
  pose proof (Hsc ac ltac:(set_solver)).
  specialize (Heoac tx ltac:(set_solver) s ac ltac:(set_solver) ltac:(assumption)).
  auto.
Qed.


Lemma initResBal s addr:
  (initialEffReserveBals s)  addr =
    (balanceOfAcA s addr `min` delayedReserveBalOfAddr s.2 addr 0)%Z.
Proof.
  reflexivity.
Qed.

Lemma initResBal_le_balance s addr :
  (initialEffReserveBals s addr <= Z.of_N (balanceOfAc s.1 addr))%Z.
Proof.
  rewrite initResBal.
  unfold balanceOfAcA.
  apply Z.le_min_l.
Qed.

Lemma advanceEffReserveBals_le s irb b addr :
  (advanceEffReserveBals s irb b addr <= irb addr)%Z.
Proof.
  unfold advanceEffReserveBals.
  apply Z.le_min_l.
Qed.


(* end hide *)

(** This lemma combines the axioms above to build a
    lower bound of the balance of any account after executing a transaction.
*)
Lemma execBalLb ac s tx:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let sf := (execValidatedTx s tx).1 in
  let ReserveBal := delayedReserveBalOfAddr s.2 ac (txBlockNum tx) in
  if (asbool (ac=sender tx)) then
    isSC sf.1 (sender tx) = false->
    (if isAllowedToEmpty s [] tx
     then balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx + maxStorageFee tx) <= balanceOfAcA sf (sender tx)
          \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
     else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx)))
  else
    if (isSC sf.1 ac)
    then True
    else (if addrDelegated (sf.1) ac then ReserveBal `min` (balanceOfAcA s ac) else balanceOfAcA s ac)
         <= (balanceOfAcA sf ac).
Proof using eas K K_pos.
  simpl. intros.
  case_bool_decide; subst; auto; [apply execTxSenderBal; auto|].
  pose proof (execTxOtherBalanceLB tx s ltac:(auto) ac ltac:(auto)).
  pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s ac ltac:(auto)).
  destruct (isSC ((execValidatedTx s tx).1.1) ac); auto;[].
  autorewrite with syntactic in *.
  case_match; lia.
Qed.

Open Scope Z_scope.

(** **  [isAllowedToEmpty] lemmas

  Recall [isAllowedToEmpty s (txInterfirst :: rest) txnext]
  determines whether the transaction [txnext] is allowed to empty its balance,
  in the setting where [s] is the last available state and
  [(txInterfirst :: rest)] are the transactions between [s] and [txnext].

  This lemma proves that to be equivalent to executing [txInterfirst]
  at state [s] and considering the result as the latest available state
  and thereby removing [txInterfirst] from intermediates.

*)

Lemma execPreservesIsAllowedToEmpty s txInterfirst rest txnext:
  let sf := (execValidatedTx s txInterfirst).1 in
  txBlockNum txnext - (K-1) ≤ txBlockNum txInterfirst ≤ txBlockNum txnext
  -> isAllowedToEmpty s (txInterfirst :: rest) txnext = isAllowedToEmpty sf rest txnext.
Proof using eas K K_pos.
  intros ? Hr.
  symmetry.
  unfold isAllowedToEmpty.
  simpl.
  autorewrite with syntactic.
  destruct (decide (sender txnext = sender txInterfirst)).
  {
    assert ((asbool (sender txnext ∈ sender txInterfirst :: map sender rest)) = true) as Hf.
    {
      rewrite bool_decide_true; auto.
      set_solver.
    }

    rewrite Hf.
    autorewrite with syntactic.
    match goal with
    |  |-  _ && ?r = false =>
         assert (r=false) as Hrf
    end;
    [|  rewrite Hrf; autorewrite with syntactic; reflexivity].
    unfold existsTxWithinK.
    unfold indexWithinK.
    rwHyps.
    rewrite lastTxInBlockIndexUpd.
    rewrite bool_decide_true;[reflexivity|].
    split_and !; try lia.
  }
  {
    f_equiv.
    2:{
      f_equiv.
      f_equiv.
      2:{
        apply bool_decide_ext.
        autorewrite with syntactic.
        tauto.
      }
      {
        unfold existsTxWithinK.
        unfold indexWithinK.
        subst sf.
        rewrite otherTxLstSenderLkp; auto.
      }
    }
    {
      destruct (decide (sender txnext ∈ addrsDelUndelByTx txInterfirst)).
      {
        symmetry.
          Hint Rewrite @elem_of_app: iff.
        rewrite bool_decide_true;
          [ | autorewrite with iff; tauto].
        autorewrite with syntactic; simpl.
        unfold existsDelUndelTxWithinK.
        unfold indexWithinK.
        rewrite delgUndelgUpdTx; auto;[].
        resolveDecide lia.
        autorewrite with syntactic.
        rewrite bool_decide_true;[| lia].
        autorewrite with syntactic.
        reflexivity.
      }
      {
        f_equiv.
        f_equiv;[
            |apply bool_decide_ext;
             autorewrite with iff; tauto].
        unfold existsDelUndelTxWithinK.
        unfold indexWithinK.
        rewrite otherDelUndelLkp; auto.
        f_equiv.

        apply otherDelUndelDelegationStatusUnchanged; auto.
      }

    }
  }
Qed.

Lemma sender_in_flat_map_delundel_cons addr tx inter :
  asbool (addr ∈ flat_map addrsDelUndelByTx (tx :: inter)) =
  asbool (addr ∈ addrsDelUndelByTx tx) || asbool (addr ∈ flat_map addrsDelUndelByTx inter).
Proof.
  cbn [flat_map].
  destruct (decide (addr ∈ addrsDelUndelByTx tx)) as [Htx|Htx];
  destruct (decide (addr ∈ flat_map addrsDelUndelByTx inter)) as [Hinter|Hinter].
  - rewrite bool_decide_true; [|apply elem_of_app; left; exact Htx].
    rewrite bool_decide_true; [|exact Htx].
    rewrite bool_decide_true; [|exact Hinter]. simpl. reflexivity.
  - rewrite bool_decide_true; [|apply elem_of_app; left; exact Htx].
    rewrite bool_decide_true; [|exact Htx].
    rewrite bool_decide_false; [|exact Hinter]. simpl. reflexivity.
  - rewrite bool_decide_true; [|apply elem_of_app; right; exact Hinter].
    rewrite bool_decide_false; [|exact Htx].
    rewrite bool_decide_true; [|exact Hinter]. simpl. reflexivity.
  - assert (addr ∉ addrsDelUndelByTx tx ++ flat_map addrsDelUndelByTx inter) as Hnot.
    { intro Hin. apply elem_of_app in Hin. destruct Hin as [Hin|Hin]; contradiction. }
    rewrite bool_decide_false; [|exact Hnot].
    simpl. rewrite bool_decide_false; [|exact Htx].
    rewrite bool_decide_false; [|exact Hinter]. simpl. reflexivity.
Qed.

Lemma isAllowedToEmpty_false_senderNoRecentActivity s inter tx :
  senderNoRecentActivity s inter tx = true ->
  isAllowedToEmpty s inter tx = false <-> asbool (sender tx ∈ addrsDelUndelByTx tx) = true.
Proof using K K_pos.
  intros Hsnra.
  unfold senderNoRecentActivity in Hsnra.
  set (senderAddr := sender tx) in *.
  set (existsSameSenderTxInWindow :=
         (existsTxWithinK s tx) || asbool (senderAddr ∈ map sender inter)) in *.
  set (senderTouchedByDelUndel :=
         asbool (senderAddr ∈ flat_map addrsDelUndelByTx inter)) in *.
  set (consideredDelegated :=
         addrDelegated s.1 senderAddr
           || existsDelUndelTxWithinK s tx
           || senderTouchedByDelUndel) in *.
  apply andb_true_iff in Hsnra as [HnoSender HnoDeleg].
  apply negb_true_iff in HnoSender.
  apply negb_true_iff in HnoDeleg.
  apply orb_false_iff in HnoDeleg as [Htmp HsenderTouched].
  apply orb_false_iff in Htmp as [HaddrDel HexistsDel].
  unfold isAllowedToEmpty; simpl.
  change (sender tx) with senderAddr.
  replace ((existsTxWithinK s tx) || asbool (senderAddr ∈ map sender inter))
    with existsSameSenderTxInWindow by reflexivity.
  rewrite HnoSender.
  rewrite HaddrDel.
  rewrite HexistsDel.
  simpl.
  rewrite sender_in_flat_map_delundel_cons.
  replace (asbool (senderAddr ∈ flat_map addrsDelUndelByTx inter))
    with senderTouchedByDelUndel by reflexivity.
  rewrite HsenderTouched.
  simpl.
  rewrite orb_false_r.
  rewrite andb_true_r.
  destruct (asbool (senderAddr ∈ addrsDelUndelByTx tx)) eqn:Hb;
    simpl; split; intro H; [reflexivity|reflexivity|discriminate|discriminate].
Qed.

Hint Rewrite @updateKeyLkp3 : syntactic.

Definition rbLe (eoas: list EvmAddr) (rb1 rb2: EffReserveBals) :=
  forall addr, addr ∈ eoas -> rb1 addr <= rb2 addr.

(** ** lemmas about [remainingEffReserveBalOfSender]

    [remainingEffReserveBalOfSender] is monotone. proof is straightforward by analyzing cases
    and using Coq's arith automation [lia].
*)

(** Monotonicity helpers for [Z.min] and [Z.max]. *)
Lemma zmax_mono_l a b c : (a <= b)%Z -> (a `max` c) <= (b `max` c).
Proof using K K_pos.
  intros Hle.
  destruct (Z_le_dec a c), (Z_le_dec b c); lia.
Qed.

Lemma zmin_mono_l a b c : (a <= b)%Z -> (a `min` c) <= (b `min` c).
Proof using K K_pos.
  intros Hle.
  destruct (Z_le_dec a c), (Z_le_dec b c); lia.
Qed.

Lemma zmin_mono_r a b c : (a <= b)%Z -> (c `min` a) <= (c `min` b).
Proof using K K_pos.
  intros Hle.
  rewrite (Z.min_comm c a).
  rewrite (Z.min_comm c b).
  apply zmin_mono_l; exact Hle.
Qed.

Lemma zle_min a b c : (a <= b)%Z -> (a <= c)%Z -> (a <= b `min` c)%Z.
Proof using K K_pos.
  intros H1 H2.
  destruct (Z_le_dec b c); lia.
Qed.

Lemma nmin_le_l a b : N.min a b <= a.
Proof using K K_pos.
  destruct (N.le_dec a b); lia.
Qed.

Lemma nmin_le_r a b : N.min a b <= b.
Proof using K K_pos.
  destruct (N.le_dec a b); lia.
Qed.

Lemma nmin_mono_l a b c : (a <= b)%N -> N.min a c <= N.min b c.
Proof using K K_pos.
  intros Hle.
  destruct (N.le_dec a c), (N.le_dec b c); lia.
Qed.

Lemma nle_min a b c : (a <= b)%N -> (a <= c)%N -> (a <= N.min b c)%N.
Proof using K K_pos.
  intros H1 H2.
  destruct (N.le_dec b c); lia.
Qed.

Lemma Z_of_N_min a b :
  Z.of_N (N.min a b) = Z.min (Z.of_N a) (Z.of_N b).
Proof using K K_pos.
  destruct (N.le_dec a b).
  - rewrite N.min_l; [|assumption].
    rewrite Z.min_l; [reflexivity|].
    apply N2Z.inj_le; assumption.
  - rewrite N.min_r; [|lia].
    rewrite Z.min_r; [reflexivity|].
    apply N2Z.inj_le; lia.
Qed.

Lemma Z_of_N_sub_le a b :
  (Z.of_N a - Z.of_N b <= Z.of_N (a - b))%Z.
Proof using K K_pos.
  zify; lia.
Qed.

Lemma nsub_le a b : (a - b <= a)%N.
Proof using K K_pos.
  destruct (N.le_dec b a); lia.
Qed.

Lemma nsub_le_mono_l a b c : (a <= b)%N -> (a - c <= b - c)%N.
Proof using K K_pos.
  intros Hle.
  destruct (N.le_dec c a), (N.le_dec c b); lia.
Qed.

Lemma mono  s rb1 rb2 inter tx:
  rb1 <= rb2
  -> (remainingEffReserveBalOfSender s rb1 inter tx) <= (remainingEffReserveBalOfSender s rb2 inter tx).
Proof using K K_pos.
  intros Hrb.
  unfold remainingEffReserveBalOfSender.
  set (senderAddr := sender tx).
  set (firstFromSenderFlag := senderNoRecentActivity s inter tx).
  change (senderNoRecentActivity s inter tx) with firstFromSenderFlag.
  destruct (isAllowedToEmpty s inter tx) eqn:Hae; simpl.
  - destruct (asbool (maxTxFee tx <= balanceOfAc s.1 (sender tx))); lia.
  - destruct firstFromSenderFlag; simpl.
    + apply Z.le_refl.
    + set (drb := delayedReserveBalOfAddr s.2 senderAddr (txBlockNum tx)).
      assert (Hmin : (rb1 `min` drb) <= (rb2 `min` drb)) by (apply zmin_mono_l; lia).
      apply Z.sub_le_mono_r; exact Hmin.
Qed.

(** [remainingEffReserveBalOfSender] never exceeds the sender's balance, assuming [prevErb] doesn't. *)
Lemma remRb_le_balance s prevErb inter tx :
  prevErb <= balanceOfAc s.1 (sender tx) ->
  remainingEffReserveBalOfSender s prevErb inter tx
  <= balanceOfAc s.1 (sender tx).
Proof using K K_pos.
  intros Hprev.
  unfold remainingEffReserveBalOfSender.
  set (senderAddr := sender tx).
  set (firstFromSenderFlag := senderNoRecentActivity s inter tx).
  change (senderNoRecentActivity s inter tx) with firstFromSenderFlag.
  destruct (isAllowedToEmpty s inter tx) eqn:Hae; simpl.
  - set (sbal := balanceOfAc s.1 (sender tx)).
    set (drb := delayedReserveBalOfAddr s.2 senderAddr (txBlockNum tx)).
    change (balanceOfAc s.1 (sender tx)) with sbal.
    change (balanceOfAc s.1 senderAddr) with sbal.
    destruct (asbool (maxTxFee tx <= sbal)) eqn:Hfee; simpl.
    + assert (Hmax : (Z.max (sbal - maxTxFee tx - value tx - maxStorageFee tx) 0) <= sbal) by lia.
      assert (Hmin : (Z.min (Z.max (sbal - maxTxFee tx - value tx - maxStorageFee tx) 0) drb)
                      <= Z.max (sbal - maxTxFee tx - value tx - maxStorageFee tx) 0).
      { destruct (Z_le_dec (Z.max (sbal - maxTxFee tx - value tx - maxStorageFee tx) 0) drb) as [Hle|Hgt].
        - rewrite Z.min_l; [lia | exact Hle].
        - rewrite Z.min_r; [lia | lia].
      }
      apply (Z.le_trans _ (Z.max (sbal - maxTxFee tx - value tx - maxStorageFee tx) 0) sbal);
        [exact Hmin | exact Hmax].
    + lia.
  - destruct firstFromSenderFlag; simpl.
    + set (sbal := balanceOfAc s.1 senderAddr).
      set (drb := delayedReserveBalOfAddr s.2 senderAddr (txBlockNum tx)).
      assert (Hmin : (sbal `min` drb) <= sbal).
      { destruct (Z_le_dec sbal drb).
        - rewrite Z.min_l; lia.
        - rewrite Z.min_r; lia.
      }
      pose proof (N2Z.is_nonneg (maxTxFee tx)) as Hfee.
      assert (Hsub : (sbal `min` drb - maxTxFee tx) <= (sbal `min` drb)) by lia.
      apply (Z.le_trans _ (sbal `min` drb)); [exact Hsub | exact Hmin].
    + set (drb := delayedReserveBalOfAddr s.2 senderAddr (txBlockNum tx)).
      assert (Hmin : (prevErb `min` drb) <= balanceOfAc s.1 senderAddr).
      { destruct (Z_le_dec prevErb drb).
        - rewrite Z.min_l; [exact Hprev | exact l].
        - rewrite Z.min_r; [|lia].
          apply (Z.le_trans _ prevErb); [lia | exact Hprev].
      }
      pose proof (N2Z.is_nonneg (maxTxFee tx)) as Hfee.
      assert (Hsub : (prevErb `min` drb - maxTxFee tx) <= (prevErb `min` drb)) by lia.
      apply (Z.le_trans _ (prevErb `min` drb)); [exact Hsub | exact Hmin].
Qed.

(** In the proof of the main correctness theorem, we use a slightly different
variant of monotonicity, where in the RHS of [<=], remainingEffReserveBalOfSender starts
from the final state after executing [tx] from [s] and as a result, [tx]
is dropped from the list of intermediate transactions between the state
and the candidate transaction [txc].
The proof follows from the definition of [remainingEffReserveBalOfSender]
and the execution lemmas above.
*)
Lemma mono2 tx txc extension s (eoas: list EvmAddr) rb1 rb2 inter:
  (∀ ac : EvmAddr,
      ac ∈ sender tx :: sender txc :: map sender extension
      -> isSC ((execValidatedTx s tx).1.1) ac = false)
  -> (rb1 ≤ rb2)
  -> (rb2 <= balanceOfAc (execValidatedTx s tx).1.1 (sender txc))
  -> txBlockNum txc - (K-1) ≤ txBlockNum tx  ≤ txBlockNum txc
  -> ∀ addr : EvmAddr,
      addr ∈ eoas
      -> remainingEffReserveBalOfSender s rb1 (tx :: inter) txc
          <= remainingEffReserveBalOfSender ((execValidatedTx s tx).1) rb2 inter txc.
Proof using eas K K_pos.
  intros Hsc Hrb Hrb2bal Hrangel.
  intros addr Hin.
  unfold remainingEffReserveBalOfSender.
  rewrite <- execPreservesIsAllowedToEmpty; try lia.
  remember (isAllowedToEmpty s (tx :: inter) txc) as ia.
  destruct ia; simpl.
  - specialize (Hsc (sender txc) ltac:(set_solver)).
    symmetry in Heqia.
    pose proof (emptyBalanceUb _ _ _ _ Hsc Heqia) as Hle.
    pose proof (isAllowedToEmptyImpl _ _ _ _ Heqia) as Hneq.
    forward_reason.
    pose proof (delayedReserveBalOfAddrSame s tx (sender txc) (txBlockNum txc)
                  ltac:(auto) ltac:(lia) ltac:(lia)) as Hdrb.
    rewrite Hdrb.
    destruct (bool_decide (maxTxFee txc <= balanceOfAc s.1 (sender txc))) eqn:Hfee1; simpl.
    + apply bool_decide_eq_true_1 in Hfee1.
      set (bal1 := balanceOfAc s.1 (sender txc)).
      set (bal2 := balanceOfAc (execValidatedTx s tx).1.1 (sender txc)).
      set (drb := (delayedReserveBalOfAddr s.2 (sender txc) (txBlockNum txc) : Z)).
      assert (maxTxFee txc <= bal2)%N by lia.
      rewrite bool_decide_true; [|lia].
      set (x1 := (bal1 - maxTxFee txc - value txc - maxStorageFee txc) `max` 0).
      set (x2 := (bal2 - maxTxFee txc - value txc - maxStorageFee txc) `max` 0).
      assert (x1 <= x2)%Z by (unfold x1, x2; apply zmax_mono_l; lia).
      assert (Hmin : (x1 `min` drb) <= (x2 `min` drb)).
      { apply zmin_mono_l; exact H0. }
      exact Hmin.
    + apply bool_decide_eq_false_1 in Hfee1.
      destruct (bool_decide (maxTxFee txc <= balanceOfAc (execValidatedTx s tx).1.1 (sender txc))) eqn:Hfee2; simpl; lia.
  - assert (HdrbK :
              delayedReserveBalOfAddr (execValidatedTx s tx).1.2 (sender txc) (txBlockNum txc) =
              delayedReserveBalOfAddr s.2 (sender txc) (txBlockNum txc)).
    { apply delayedReserveBalOfAddrWithinK; lia. }
    rewrite HdrbK.
    set (senderAddr := sender txc).
    set (drb := delayedReserveBalOfAddr s.2 senderAddr (txBlockNum txc)).
    set (bal1 := balanceOfAc s.1 senderAddr).
    set (bal2 := balanceOfAc (execValidatedTx s tx).1.1 senderAddr).
    set (existsSameSenderTxInWindowL :=
           (existsTxWithinK s txc)
           || asbool (senderAddr ∈ sender tx :: map sender inter)).
    set (senderTouchedByDelUndelL :=
           asbool (senderAddr ∈ flat_map addrsDelUndelByTx (tx :: inter))).
    set (consideredDelegatedL :=
           addrDelegated s.1 senderAddr
           || existsDelUndelTxWithinK s txc
           || senderTouchedByDelUndelL).
    set (firstFromSenderL :=
           (negb existsSameSenderTxInWindowL) && (negb consideredDelegatedL)).
    set (existsSameSenderTxInWindowR :=
           (existsTxWithinK (execValidatedTx s tx).1 txc)
           || asbool (senderAddr ∈ map sender inter)).
    set (senderTouchedByDelUndelR :=
           asbool (senderAddr ∈ flat_map addrsDelUndelByTx inter)).
    set (consideredDelegatedR :=
           addrDelegated (execValidatedTx s tx).1.1 senderAddr
           || existsDelUndelTxWithinK (execValidatedTx s tx).1 txc
           || senderTouchedByDelUndelR).
    set (firstFromSenderR :=
           (negb existsSameSenderTxInWindowR) && (negb consideredDelegatedR)).
    change (senderNoRecentActivity s (tx :: inter) txc) with firstFromSenderL.
    change (senderNoRecentActivity (execValidatedTx s tx).1 inter txc) with firstFromSenderR.
    apply Z.sub_le_mono_r.
    destruct firstFromSenderL eqn:Hfl; destruct firstFromSenderR eqn:Hfr; simpl.
    + (* L true, R true *)
      pose proof Hfl as Hfl'.
      unfold firstFromSenderL in Hfl'.
      assert (Hfl1 : existsSameSenderTxInWindowL = false).
      { apply andb_true_iff in Hfl as [Hfl _].
        apply negb_true_iff in Hfl; exact Hfl. }
      assert (Hfl2 : consideredDelegatedL = false).
      { apply andb_true_iff in Hfl as [_ Hfl2].
        apply negb_true_iff in Hfl2; exact Hfl2. }
      assert (Hmem : asbool (senderAddr ∈ sender tx :: map sender inter) = false).
      { apply orb_false_iff in Hfl1 as [_ Hmem]; exact Hmem. }
      assert (Hneq : senderAddr <> sender tx).
      { apply bool_decide_eq_false in Hmem.
        set_solver. }
      pose proof Hfl2 as Hfl2'.
      unfold consideredDelegatedL in Hfl2'.
      apply orb_false_iff in Hfl2' as [Hdel_or Htouch].
      apply orb_false_iff in Hdel_or as [Hdel0 HexistsDel0].
      assert (Hnmem : senderAddr ∉ addrsDelUndelByTx tx).
      { apply bool_decide_eq_false in Htouch.
        set_solver. }
      assert (HexistsR : existsTxWithinK (execValidatedTx s tx).1 txc = false).
      { apply orb_false_iff in Hfl1 as [HexistsL _].
        unfold existsTxWithinK, indexWithinK.
        rewrite otherTxLstSenderLkp; [|exact Hneq].
        exact HexistsL. }
      assert (HmemR : asbool (senderAddr ∈ map sender inter) = false).
      { apply bool_decide_eq_false in Hmem.
        assert (senderAddr ∉ map sender inter) by set_solver.
        apply bool_decide_eq_false; auto. }
      assert (HtouchR : senderTouchedByDelUndelR = false).
      { apply bool_decide_eq_false in Htouch.
        assert (senderAddr ∉ flat_map addrsDelUndelByTx inter) by set_solver.
        apply bool_decide_eq_false; auto. }
      assert (HexistsDelR : existsDelUndelTxWithinK (execValidatedTx s tx).1 txc = false).
      { unfold existsDelUndelTxWithinK, indexWithinK.
        rewrite otherDelUndelLkp; [|exact Hnmem].
        exact HexistsDel0. }
      assert (HdelR : addrDelegated (execValidatedTx s tx).1.1 senderAddr = false).
      { pose proof (otherDelUndelDelegationStatusUnchanged s senderAddr tx Hnmem) as HdelEq.
        rewrite HdelEq. exact Hdel0. }
      assert (Hsc_txc : isSC (execValidatedTx s tx).1.1 senderAddr = false).
      { apply Hsc. set_solver. }
      pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s senderAddr) as Hbal.
      specialize (Hbal Hneq).
      rewrite HdelR in Hbal. rewrite Hsc_txc in Hbal. simpl in Hbal.
      assert (Hbal' : (balanceOfAc s.1 senderAddr <= balanceOfAc (execValidatedTx s tx).1.1 senderAddr)%Z).
      { unfold balanceOfAcA in Hbal. simpl in Hbal.
        apply N2Z.inj_le; exact Hbal. }
      apply zmin_mono_l; exact Hbal'.
    + (* L true, R false: impossible *)
      pose proof Hfl as Hfl'.
      unfold firstFromSenderL in Hfl'.
      assert (Hfl1 : existsSameSenderTxInWindowL = false).
      { apply andb_true_iff in Hfl as [Hfl _].
        apply negb_true_iff in Hfl; exact Hfl. }
      assert (Hfl2 : consideredDelegatedL = false).
      { apply andb_true_iff in Hfl as [_ Hfl2].
        apply negb_true_iff in Hfl2; exact Hfl2. }
      assert (Hmem : asbool (senderAddr ∈ sender tx :: map sender inter) = false).
      { apply orb_false_iff in Hfl1 as [_ Hmem]; exact Hmem. }
      assert (Hneq : senderAddr <> sender tx).
      { apply bool_decide_eq_false in Hmem.
        set_solver. }
      pose proof Hfl2 as Hfl2'.
      unfold consideredDelegatedL in Hfl2'.
      apply orb_false_iff in Hfl2' as [Hdel_or Htouch].
      apply orb_false_iff in Hdel_or as [Hdel0 HexistsDel0].
      assert (Hnmem : senderAddr ∉ addrsDelUndelByTx tx).
      { apply bool_decide_eq_false in Htouch.
        set_solver. }
      assert (HexistsR : existsTxWithinK (execValidatedTx s tx).1 txc = false).
      { apply orb_false_iff in Hfl1 as [HexistsL _].
        unfold existsTxWithinK, indexWithinK.
        rewrite otherTxLstSenderLkp; [|exact Hneq].
        exact HexistsL. }
      assert (HmemR : asbool (senderAddr ∈ map sender inter) = false).
      { apply bool_decide_eq_false in Hmem.
        assert (senderAddr ∉ map sender inter) by set_solver.
        apply bool_decide_eq_false; auto. }
      assert (HtouchR : senderTouchedByDelUndelR = false).
      { apply bool_decide_eq_false in Htouch.
        assert (senderAddr ∉ flat_map addrsDelUndelByTx inter) by set_solver.
        apply bool_decide_eq_false; auto. }
      assert (HexistsDelR : existsDelUndelTxWithinK (execValidatedTx s tx).1 txc = false).
      { unfold existsDelUndelTxWithinK, indexWithinK.
        rewrite otherDelUndelLkp; [|exact Hnmem].
        exact HexistsDel0. }
      assert (HdelR : addrDelegated (execValidatedTx s tx).1.1 senderAddr = false).
      { pose proof (otherDelUndelDelegationStatusUnchanged s senderAddr tx Hnmem) as HdelEq.
        rewrite HdelEq. exact Hdel0. }
      assert (HconsR : consideredDelegatedR = false).
      { unfold consideredDelegatedR.
        rewrite HdelR; rewrite HexistsDelR; rewrite HtouchR.
        reflexivity. }
      assert (HexistsSameR : existsSameSenderTxInWindowR = false).
      { unfold existsSameSenderTxInWindowR.
        rewrite HexistsR; rewrite HmemR.
        reflexivity. }
      assert (Hfr' : firstFromSenderR = true).
      { unfold firstFromSenderR.
        rewrite HexistsSameR; rewrite HconsR.
        reflexivity. }
      rewrite Hfr in Hfr'; discriminate.
    + (* L false, R true *)
      pose proof Hfl as Hfl'.
      unfold firstFromSenderL in Hfl'.
      apply zmin_mono_l.
      eapply Z.le_trans; [exact Hrb|exact Hrb2bal].
    + (* L false, R false *)
      pose proof Hfl as Hfl'.
      unfold firstFromSenderL in Hfl'.
      assert (Hmin : (rb1 `min` drb) <= (rb2 `min` drb)) by (apply zmin_mono_l; exact Hrb).
      exact Hmin.
Qed.


(*
(** lifts [mono] from [remainingEffReserveBals] to [remainingEffReserveBalsL]:
proof follows a straightforward induction on the list [extension],
using [mono] to fulfil the obligations of the induction hypothesis
 *)
Lemma monoL eoas s rb1 rb2 inter extension:
  map sender extension ⊆ eoas
  -> rbLe eoas rb1 rb2
  -> rbLe eoas (remainingEffReserveBalsL s rb1 inter extension)
          (remainingEffReserveBalsL s rb2 inter extension).
Proof using K K_pos.
  revert rb1 rb2 inter.
  induction extension; auto;[].
  unfold rbLe in *.
  intros ? ? ? Hs Hrb addr Hin. simpl in *.
  simpl.
  apply IHextension;[set_solver | | set_solver].
  apply mono.
  assumption.
Qed.
 *)

(** lifts [mono2] from [remainingEffReserveBalOfSender] to [remainingEffReserveBalsL]:
proof follows a straightforward induction on the list [extension],
using [mono2] to fulfil the obligations of the induction hypothesis.
 *)

Lemma monoL2 eoas s rb1 rb2 inter extension tx:
  (map sender extension) ⊆ eoas
  -> rbLe eoas rb1 rb2
  -> (forall txext, txext ∈ extension ->  txBlockNum txext - (K-1) ≤ txBlockNum tx ≤ txBlockNum txext)
  -> (∀ ac : EvmAddr, ac ∈ map sender (tx :: extension) → isSC ((execValidatedTx s tx).1.1) ac = false)
  -> (∀ addr : EvmAddr, addr ∈ eoas -> rb2 addr <= balanceOfAc (execValidatedTx s tx).1.1 addr)
  -> rbLe eoas (remainingEffReserveBalsL s rb1 (tx::inter) extension)
          (remainingEffReserveBalsL ((execValidatedTx s tx).1) rb2 inter extension).
Proof using eas K K_pos.
  revert rb1 rb2 inter.
  induction extension; auto;[].
  unfold rbLe in *.
  intros ? ? ? Hsub Hrb Hrange Hsc Hrb2bal addr Hin.
  simpl.
  apply forallCons in Hrange.
  simpl in Hsc.
  forward_reason.
  eapply IHextension.
  - set_solver.
  - (* rbLe after the head step *)
    intros addr0 Hin0.
    repeat rewrite updateKeyLkp3.
    case_bool_decide; subst.
    + eapply mono2.
      * exact Hsc.
      * (* rb1 <= rb2 for advanced maps *)
        unfold advanceEffReserveBals.
        set (b := txBlockNum a).
        assert (Hdrb :
          delayedReserveBalOfAddr (execValidatedTx s tx).1.2 (sender a) b =
          delayedReserveBalOfAddr s.2 (sender a) b).
        { apply delayedReserveBalOfAddrWithinK; lia. }
        rewrite Hdrb.
        apply zmin_mono_l. apply Hrb. set_solver.
      * (* rb2 <= balance *)
        eapply Z.le_trans;
          [apply advanceEffReserveBals_le
          | apply Hrb2bal; set_solver].
      * split; [exact Hrangell|exact Hrangelr].
      * exact Hin0.
    + (* monotone under [advanceEffReserveBals] with equal delayed reserve *)
      unfold advanceEffReserveBals.
      set (b := txBlockNum a).
      assert (Hdrb :
        delayedReserveBalOfAddr (execValidatedTx s tx).1.2 addr0 b =
        delayedReserveBalOfAddr s.2 addr0 b).
      { apply delayedReserveBalOfAddrWithinK; lia. }
      rewrite Hdrb.
      apply zmin_mono_l. apply Hrb. set_solver.
  - intros; apply Hranger; set_solver.
  - intros; apply Hsc; set_solver.
  - intros addr0 Hin0;
      rewrite updateKeyLkp3;
      case_bool_decide; subst;
        [apply remRb_le_balance;
         eapply Z.le_trans;
         [apply advanceEffReserveBals_le
         | apply Hrb2bal; set_solver]
        | eapply Z.le_trans;
          [apply advanceEffReserveBals_le
          | apply Hrb2bal; set_solver] ].
  - exact Hin.
Qed.


Print Assumptions monoL2.
Hint Rewrite initResBal: syntactic.

(** This lemma captures a key property of [remainingEffReserveBalOfSender]: it underapproximates
the resultant effective balance after execution of the transaction.
This is the heart of the proof of the top-level correctness theorem [fullBlockStep].
Proof follows by unfolding definitions and case analysis. uses [mono2], [execBalLb], and many other lemmas above
*)
Lemma exec1 tx extension s :
  let irb0 := advanceEffReserveBals s (initialEffReserveBals s) (txBlockNum tx) in
  let remf  := remainingEffReserveBalOfSender s (irb0 (sender tx)) [] tx in
  let remRbsf := updateKey irb0 (sender tx) (fun _ => remf) in
  let sf := (execValidatedTx s tx).1 in
  maxTxFee tx <= balanceOfAc s.1 (sender tx)
  -> (∀ ac : EvmAddr, ac ∈ sender tx :: map sender extension → isSC sf.1 ac = false)
     -> (∀ addr : EvmAddr,
            addr ∈ sender tx :: map sender extension
            -> remRbsf addr
              ≤ initialEffReserveBals sf addr).
(* Original proof (pre-delayed-URB update):
Proof using eas K K_pos.
  simpl.
  intros Hfee  Hscf.
  intros ? Hin.
  unfold remainingEffReserveBalOfSender.
  case_match_concl.
  { (* this tx updates the reserve balance *)
    rename n into nrb.
    case_match_concl;
          try rewrite updateKeyLkp3;
    repeat rewrite initResBal;
    rewrite configuredReserveBalOfAddrSpec;
    unfold execValidatedTx;
    rwHyps;
    simpl in *;
    unfold balanceOfAcA in *;
    rewrite balanceOfUpd;
    unfold rbAfterTx;
    rwHyps;
    case_bool_decide;
      resolveDecide congruence; simpl in *; try lia.
  }
  pose proof (execBalLb addr s tx ltac:(lia)) as Hlb.
  simpl in Hlb.
  rewrite Hscf in Hlb;[|set_solver].
  rewrite Hscf in Hlb;[|set_solver].
  case_match_concl.
  { (* isAllowedToEmpty *)
    match goal with
    | H: isAllowedToEmpty _ _ _ = _ |- _ => rename H into Hae
    end.
    autorewrite with syntactic in *.
      unfold balanceOfAcA in *.
      rwHyps.
      repeat case_match; try lia; try congruence.
      subst.
      destruct Hlb as [Hstorage|Hrevert].
      { case_bool_decide; try lia. }
      { subst. case_bool_decide; try lia. }
  }
  rewrite updateKeyLkp3.
  autorewrite with syntactic in *.
  unfold balanceOfAcA, rbAfterTx in *.
  rwHyps.
  case_bool_decide; subst; resolveDecide congruence; try lia.
  case_match; lia.
Qed.
*)
Proof using eas K K_pos.
  simpl.
  intros Hfee Hscf addr Hin.
  unfold remainingEffReserveBalOfSender.
  destruct (isAllowedToEmpty s [] tx) eqn:Hae.
  - (* isAllowedToEmpty = true *)
    repeat rewrite updateKeyLkp3.
    repeat rewrite initResBal.
    case_bool_decide; subst.
    + (* addr = sender tx *)
      pose proof (execBalLb (sender tx) s tx ltac:(lia)) as Hlb.
      simpl in Hlb.
      rewrite Hscf in Hlb; [|set_solver].
      rewrite Hae in Hlb.
      autorewrite with syntactic in *.
      unfold balanceOfAcA in *.
      rwHyps.
      rewrite delayedReserveBalOfAddrSender0.
      specialize (Hlb ltac:(auto)).
      subst.
      destruct Hlb as [Hstorage|Hrevert].
      * apply zmin_mono_l. lia.
      * subst. apply zmin_mono_l. lia.
    + (* addr ≠ sender tx *)
      pose proof (execBalLb addr s tx ltac:(lia)) as Hlb.
      simpl in Hlb.
      rewrite (Hscf addr ltac:(set_solver)) in Hlb.
      simpl in Hlb.
      rewrite bool_decide_false in Hlb; [|congruence].
      rwHyps.
      rewrite (delayedReserveBalOfAddr_after_exec0 s tx addr).
      unfold advanceEffReserveBals.
      rewrite initResBal.
      set (drb0 := delayedReserveBalOfAddr s.2 addr 0).
      set (drbtx := delayedReserveBalOfAddr s.2 addr (txBlockNum tx)).
      assert (Hirb_drb0 : ((balanceOfAc s.1 addr `min` drb0) `min` drbtx) <= drb0).
      { eapply Z.le_trans.
        - apply Z.le_min_l.
        - apply Z.le_min_r.
      }
      (* Use [execBalLb] to lower-bound balance, then clamp by [drb0]. *)
      destruct (addrDelegated (execValidatedTx s tx).1.1 addr) eqn:Hdel.
      * pose proof (proj1 (N2Z.inj_le _ _) Hlb) as Hlbz.
        simpl in Hlbz. rewrite Z_of_N_min in Hlbz.
        assert (Hirb_le_lb :
          ((balanceOfAc s.1 addr `min` drb0) `min` drbtx)
          <= drbtx `min` balanceOfAc s.1 addr) by lia.
        assert (Hbal :
          ((balanceOfAc s.1 addr `min` drb0) `min` drbtx)
          <= balanceOfAc (execValidatedTx s tx).1.1 addr).
        { etransitivity; [exact Hirb_le_lb| exact Hlbz]. }
        apply zle_min; [exact Hbal| apply Z.le_min_r].
      * pose proof (proj1 (N2Z.inj_le _ _) Hlb) as Hlbz.
        simpl in Hlbz.
        assert (Hirb_le_lb :
          ((balanceOfAc s.1 addr `min` drb0) `min` drbtx)
          <= balanceOfAc s.1 addr) by lia.
        assert (Hbal :
          ((balanceOfAc s.1 addr `min` drb0) `min` drbtx)
          <= balanceOfAc (execValidatedTx s tx).1.1 addr).
        { etransitivity; [exact Hirb_le_lb| exact Hlbz]. }
        apply zle_min; [exact Hbal| apply Z.le_min_r].
  - (* isAllowedToEmpty = false *)
    repeat rewrite updateKeyLkp3.
    repeat rewrite initResBal.
    case_bool_decide; subst.
    + (* addr = sender tx *)
      pose proof (execBalLb (sender tx) s tx ltac:(lia)) as Hlb.
      simpl in Hlb.
      rewrite Hscf in Hlb; [|set_solver].
      rewrite Hae in Hlb.
      rewrite bool_decide_true in Hlb; [|reflexivity].
      autorewrite with syntactic in *.
      unfold balanceOfAcA in *.
      rwHyps.
      rewrite delayedReserveBalOfAddrSender0.
      specialize (Hlb eq_refl).
      unfold advanceEffReserveBals.
      rewrite initResBal.
      set (drb0 := delayedReserveBalOfAddr s.2 (sender tx) 0).
      set (drb := delayedReserveBalOfAddr s.2 (sender tx) (txBlockNum tx)).
      set (prev := (balanceOfAc s.1 (sender tx) `min` drb0) `min` drb).
      assert (Hprev_le_drb : prev <= drb) by (unfold prev; apply Z.le_min_r).
      assert (Hprev_le_bal : prev <= balanceOfAc s.1 (sender tx)).
      { unfold prev.
        eapply Z.le_trans.
        - apply Z.le_min_l.
        - apply Z.le_min_l.
      }
      rewrite (Z.min_l prev drb Hprev_le_drb).
      pose proof (proj1 (N2Z.inj_le _ _) Hlb) as Hlbz.
      set (mN := N.min drb (balanceOfAc s.1 (sender tx))).
      assert (Hprev_le_min : prev <= drb `min` balanceOfAc s.1 (sender tx)).
      { apply zle_min; [exact Hprev_le_drb|exact Hprev_le_bal]. }
      assert (Hprev_le_m : prev <= Z.of_N mN).
      { rewrite Z_of_N_min. exact Hprev_le_min. }
      assert (Hlhs_le_m : prev - maxTxFee tx <= Z.of_N mN - maxTxFee tx).
      { apply Z.sub_le_mono_r. exact Hprev_le_m. }
      assert (Hlhs_le_sub : prev - maxTxFee tx <= Z.of_N (mN - maxTxFee tx)).
      { eapply Z.le_trans; [exact Hlhs_le_m|].
        apply Z_of_N_sub_le. }
      assert (Hbal : prev - maxTxFee tx <= balanceOfAc (execValidatedTx s tx).1.1 (sender tx)).
      { etransitivity; [exact Hlhs_le_sub|exact Hlbz]. }
      set (firstFromSenderFlag := senderNoRecentActivity s [] tx).
      change (senderNoRecentActivity s [] tx) with firstFromSenderFlag.
      destruct firstFromSenderFlag; simpl.
      * (* firstFromSender = true: baseErb = balance `min` drb *)
        assert (Hbase_le_sub :
          balanceOfAc s.1 (sender tx) `min` drb - maxTxFee tx
          <= Z.of_N (mN - maxTxFee tx)).
        { rewrite Z.min_comm.
          rewrite <- Z_of_N_min.
          apply Z_of_N_sub_le. }
        assert (Hbal' :
          balanceOfAc s.1 (sender tx) `min` drb - maxTxFee tx
          <= balanceOfAc (execValidatedTx s tx).1.1 (sender tx)).
        { etransitivity; [exact Hbase_le_sub|exact Hlbz]. }
        apply zle_min; [exact Hbal'|lia].
      * (* firstFromSender = false: baseErb = prev *)
        apply zle_min; [exact Hbal|lia].
    + (* addr ≠ sender tx *)
      pose proof (execBalLb addr s tx ltac:(lia)) as Hlb.
      simpl in Hlb.
      pose proof (Hscf addr Hin) as Hscf_addr.
      rewrite Hscf_addr in Hlb.
      rewrite bool_decide_false in Hlb; [|congruence].
      rwHyps.
      rewrite (delayedReserveBalOfAddr_after_exec0 s tx addr).
      unfold advanceEffReserveBals.
      rewrite initResBal.
      set (drb0 := delayedReserveBalOfAddr s.2 addr 0).
      set (drbtx := delayedReserveBalOfAddr s.2 addr (txBlockNum tx)).
      assert (Hirb_drb0 : ((balanceOfAc s.1 addr `min` drb0) `min` drbtx) <= drb0).
      { eapply Z.le_trans.
        - apply Z.le_min_l.
        - apply Z.le_min_r.
      }
      destruct (addrDelegated (execValidatedTx s tx).1.1 addr) eqn:Hdel.
      * pose proof (proj1 (N2Z.inj_le _ _) Hlb) as Hlbz.
        simpl in Hlbz. rewrite Z_of_N_min in Hlbz.
        assert (Hirb_le_lb :
          ((balanceOfAc s.1 addr `min` drb0) `min` drbtx)
          <= drbtx `min` balanceOfAc s.1 addr) by lia.
        assert (Hbal :
          ((balanceOfAc s.1 addr `min` drb0) `min` drbtx)
          <= balanceOfAc (execValidatedTx s tx).1.1 addr).
        { etransitivity; [exact Hirb_le_lb| exact Hlbz]. }
        apply zle_min; [exact Hbal| apply Z.le_min_r].
      * pose proof (proj1 (N2Z.inj_le _ _) Hlb) as Hlbz.
        simpl in Hlbz.
        assert (Hirb_le_lb :
          ((balanceOfAc s.1 addr `min` drb0) `min` drbtx)
          <= balanceOfAc s.1 addr) by lia.
        assert (Hbal :
          ((balanceOfAc s.1 addr `min` drb0) `min` drbtx)
          <= balanceOfAc (execValidatedTx s tx).1.1 addr).
        { etransitivity; [exact Hirb_le_lb| exact Hlbz]. }
        apply zle_min; [exact Hbal| apply Z.le_min_r].
Qed.

  Definition remainingEffReserveBals s irb inter txc:=
  let irb' := advanceEffReserveBals s irb (txBlockNum txc) in
  let rem  := remainingEffReserveBalOfSender s (irb' (sender txc)) inter txc in
  updateKey irb' (sender txc) (fun _ => rem).

Lemma decreasingRemTxSender s irb proc tx txc:
  let remRbs := remainingEffReserveBals s irb (tx :: proc) txc in
  remRbs (sender tx) ≤ irb (sender tx).
Proof using eas K K_pos.
  simpl.
  unfold remainingEffReserveBals.
  set (irb' := advanceEffReserveBals s irb (txBlockNum txc)).
  repeat rewrite updateKeyLkp3.
  case_bool_decide; subst; simpl.
  - (* sender tx = sender txc *)
    unfold remainingEffReserveBalOfSender.
    destruct (isAllowedToEmpty s (tx :: proc) txc) eqn:Hae; simpl.
    + apply isAllowedToEmptyImpl in Hae. forward_reason. congruence.
    + set (drb := delayedReserveBalOfAddr s.2 (sender txc) (txBlockNum txc)).
      set (base := (irb' (sender txc) `min` drb)).
      set (fee := (Z.of_N (maxTxFee txc))).
      assert (Hsender_in : sender txc ∈ map sender (tx :: proc)).
      { simpl. set_solver. }
      set (firstFromSenderFlag := senderNoRecentActivity s (tx :: proc) txc).
      change (senderNoRecentActivity s (tx :: proc) txc) with firstFromSenderFlag.
      assert (Hfirst_false : firstFromSenderFlag = false).
      { unfold firstFromSenderFlag, senderNoRecentActivity.
        rewrite (bool_decide_true _ Hsender_in). simpl.
        rewrite orb_true_r. simpl. reflexivity. }
      rewrite Hfirst_false. simpl.
      assert (Hsub : (base - fee <= base)%Z) by lia.
      assert (Hmin : base <= irb' (sender txc)) by (apply Z.le_min_l).
      assert (Hle_irb : irb' (sender txc) <= irb (sender txc)).
      { apply advanceEffReserveBals_le. }
      eapply Z.le_trans; [exact Hsub|].
      eapply Z.le_trans; [exact Hmin|].
      rewrite H. exact Hle_irb.
  - (* sender tx <> sender txc *)
    apply advanceEffReserveBals_le.
Qed.


(** lifts the previous lemma from [remainingEffReserveBalOfSender] to [remainingEffReserveBalsL]. induction on [nextL] *)
Lemma decreasingRemL s irb proc (nextL: list TxWithHdr) tx:
  (remainingEffReserveBalsL s irb (tx::proc) nextL) (sender tx) <=  (irb (sender tx)).
Proof using eas K K_pos.
  revert proc irb.
  induction nextL; simpl; [lia|].
  intros.
  pose proof (IHnextL (proc++[a]) (remainingEffReserveBals s irb (tx::proc) a)).
  etransitivity;[apply H|].
  apply decreasingRemTxSender.
Qed.

(** Here is a component of the main theorem: it says that
    the consensus checks guarantee that execution of the first transaction
    will pass validation during execution, i.e. the balance would be sufficient to cover
    [maxTxFee].

    This doesn't say anything about whether the execution of the later transactions ([extension]) will also pass the check. That is where the next lemma comes in handy.
 *)
Lemma execValidate tx extension s:
  consensusAcceptableTxs s (tx::extension)
  -> validateTx s.1 tx = true.
Proof using eas K K_pos.
  intros Hc.
  unfold consensusAcceptableTxs in *.
  specialize (Hc (sender tx)).
  simpl in *.
  specialize (Hc ltac:(set_solver)).

  unfold validateTx.
  autorewrite with iff.
  simpl in Hc.
  unfold remainingEffReserveBalsL in Hc; simpl in Hc.
  set (irb0 := advanceEffReserveBals s (initialEffReserveBals s) (txBlockNum tx)) in Hc.
  set (rem := remainingEffReserveBalOfSender s (irb0 (sender tx)) [] tx) in Hc.
  set (erbs := updateKey irb0 (sender tx) (fun _ => rem)) in Hc.
  pose proof (decreasingRemL s erbs [] extension tx) as Hdec.
  assert (0 <= erbs (sender tx)) as Hr.
  { etransitivity; [exact Hc|exact Hdec]. }
  unfold erbs in Hr.
  rewrite updateKeyLkp3 in Hr.
  case_bool_decide; [|congruence]. simpl in Hr.
  unfold rem in Hr.
  unfold remainingEffReserveBalOfSender in Hr.
  set (sbal := balanceOfAc s.1 (sender tx)) in *.
  destruct (isAllowedToEmpty s [] tx) eqn:Hae; simpl in Hr.
  - destruct (asbool (maxTxFee tx <= sbal)) eqn:Hfee; simpl in Hr.
    + apply bool_decide_eq_true_1 in Hfee.
      change (Z.of_N (maxTxFee tx) <= Z.of_N sbal)%Z in Hfee.
      apply (proj2 (N2Z.inj_le _ _)) in Hfee.
      exact Hfee.
    + lia.
  - set (drb := delayedReserveBalOfAddr s.2 (sender tx) (txBlockNum tx)).
    set (firstFromSenderFlag := senderNoRecentActivity s [] tx).
    change (senderNoRecentActivity s [] tx) with firstFromSenderFlag.
    change (senderNoRecentActivity s [] tx) with firstFromSenderFlag in Hr.
    destruct firstFromSenderFlag; simpl in *.
    + (* firstFromSender = true *)
      repeat rewrite orb_false_r in Hr.
      assert (Hfee_le :
        (Z.of_N (maxTxFee tx)
         <= balanceOfAc s.1 (sender tx) `min` drb)%Z) by lia.
      assert (Hbase_le_bal :
        (balanceOfAc s.1 (sender tx) `min` drb <= Z.of_N sbal)%Z) by (apply Z.le_min_l).
      assert (Hfee_le_bal : (Z.of_N (maxTxFee tx) <= Z.of_N sbal)%Z).
      { eapply Z.le_trans; [exact Hfee_le|exact Hbase_le_bal]. }
      apply (proj2 (N2Z.inj_le _ _)) in Hfee_le_bal. exact Hfee_le_bal.
    + (* firstFromSender = false *)
      repeat rewrite orb_false_r in Hr.
      set (base := (irb0 (sender tx) `min` drb)).
      assert (Hfee_le : (Z.of_N (maxTxFee tx) <= base)%Z) by lia.
      assert (Hbase_le_irb0 : base <= irb0 (sender tx)) by (apply Z.le_min_l).
      assert (Hirb0_le_init : irb0 (sender tx) <= initialEffReserveBals s (sender tx)).
      { apply advanceEffReserveBals_le. }
      assert (Hinit_le_bal : (initialEffReserveBals s (sender tx) <= Z.of_N sbal)%Z).
      { apply initResBal_le_balance. }
      assert (Hfee_le_bal : (Z.of_N (maxTxFee tx) <= Z.of_N sbal)%Z).
      { eapply Z.le_trans; [exact Hfee_le|].
        eapply Z.le_trans; [exact Hbase_le_irb0|].
        eapply Z.le_trans; [exact Hirb0_le_init|exact Hinit_le_bal]. }
      apply (proj2 (N2Z.inj_le _ _)) in Hfee_le_bal. exact Hfee_le_bal.
Qed.


(** This lemma says that you can execute the first tx in the proposed extension and the consensus checks would
    still hold on the resultant state for the remaining transactions in the proposal.
    This follows from [exec1] and [monoL2]
*)
Lemma execPreservesConsensusChecks tx extension s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  (forall txext, txext ∈ extension ->  txBlockNum txext - (K-1) ≤ txBlockNum tx ≤ txBlockNum txext)   -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtAddrs txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> isSC s.1 ac = false)
  -> consensusAcceptableTxs s (tx::extension)
  -> consensusAcceptableTxs ((execValidatedTx s tx).1) extension.
Proof using eas K K_pos.
  intros Hfee Hext Heoac Hsc.
  pose proof (isSCFalsePresExec _ _ _ Heoac Hsc) as Hscf.
  clear Heoac.
  set (sf:= (execValidatedTx s tx).1.1).
  intros Hc.
  simpl in *.
  intros ac Hin.
  specialize (Hc ac).
  eapply Z.le_trans.
  - apply Hc. simpl. right. exact Hin.
  - pose proof (monoL2 (map sender (tx::extension))) as Hm.
    unfold rbLe in Hm.
    apply (Hm s
             (updateKey
                (advanceEffReserveBals s (initialEffReserveBals s) (txBlockNum tx))
                (sender tx)
                (λ _ : Z,
                   remainingEffReserveBalOfSender s
                     (advanceEffReserveBals s (initialEffReserveBals s)
                        (txBlockNum tx) (sender tx))
                     [] tx))
             (initialEffReserveBals (execValidatedTx s tx).1)
             [] extension tx).
    + set_solver.
    + hnf. intros addr Hinaddr.
      simpl in Hinaddr.
      eapply (exec1 tx extension s).
      * exact Hfee.
      * exact Hscf.
      * exact Hinaddr.
    + exact Hext.
    + exact Hscf.
    + intros addr Hinaddr. apply initResBal_le_balance.
    + simpl. right. exact Hin.
Qed.

(** The above 2 lemmas are used to yield the following: *)
Lemma inductiveStep  (latestState : AugmentedState) (tx: TxWithHdr) (extension: list TxWithHdr) :
  maxTxFee tx <= balanceOfAc latestState.1 (sender tx)
  -> (forall txext, txext ∈ extension ->  txBlockNum txext - (K-1) ≤ txBlockNum tx ≤ txBlockNum txext)
  -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtAddrs txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> isSC latestState.1 ac = false)
 ->  consensusAcceptableTxs latestState (tx::extension)
  -> match execTx latestState tx with
     | None =>  False
     | Some (si,_) =>
         consensusAcceptableTxs si extension
     end.
Proof using eas K K_pos.
  intros Hext Heoac Hsc Hc.
  unfold execTx.
  intros.
  rewrite -> (execValidate tx extension) by assumption.
  simpl. case_match.
  apply execPreservesConsensusChecks in Hc; auto.
  unfold execValidatedTx in *.
  revert Hc. rwHyps. auto.
Qed.

Set Printing Coercions.

Fixpoint blockNumsInRange2 (ltx: list TxWithHdr) : Prop :=
  match ltx with
  | [] => True
  | htx::ttx =>
      (forall txext, txext ∈ ttx ->  txBlockNum txext ≤ txBlockNum htx + (K-1)  /\ txBlockNum htx ≤ txBlockNum txext)
      /\ blockNumsInRange2 ttx
  end.

Lemma bnequiv ltx: blockNumsInRange2 ltx -> blockNumsInRange ltx .
Proof using K K_pos.
  induction ltx; auto;[].
  simpl.
  intros Hyp.
  forward_reason.
  split_and; auto.
  intros.
  pose proof (Hypl txext ltac:(assumption)).
  lia.
Qed.


Lemma bnequiv2 ltx: blockNumsInRange ltx -> blockNumsInRange2 ltx .
Proof using K K_pos.
  induction ltx; auto;[].
  simpl.
  intros Hyp.
  forward_reason.
  split_and; auto.
  intros.
  pose proof (Hypl txext ltac:(assumption)).
  lia.
Qed.


Lemma  txCannotCreateContractAtAddrsMono tx l1 l2:
  l1 ⊆ l2
  -> txCannotCreateContractAtAddrs tx l2
  -> txCannotCreateContractAtAddrs tx l1.
Proof using K K_pos.
  unfold txCannotCreateContractAtAddrs.
  intros Hs Hp.
  intros.
  apply Hp; auto.
Qed.

Lemma  txCannotCreateContractAtAddrsTrimHead tx h l:
  txCannotCreateContractAtAddrs tx (h::l)
  -> txCannotCreateContractAtAddrs tx l.
Proof using eas K K_pos.
  apply txCannotCreateContractAtAddrsMono.
  set_solver.
Qed.

(** * Proof of main theorem:
    Straightforward induction on [firstblock],
    with [inductiveStep] used in the inductive step.
*)

Lemma fullBlockStep  (latestState : AugmentedState) (firstblock restblocks: list TxWithHdr) :
  blockNumsInRange (firstblock++restblocks)
  -> consensusAcceptableTxs latestState (firstblock++restblocks)
  -> (forall txext, txext ∈ (firstblock++restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (firstblock++restblocks)))
  -> (forall ac, ac ∈ (map sender (firstblock++restblocks)) -> isSC latestState.1 ac = false)
  -> match execTxs latestState firstblock with
     | None =>  False
     | Some (si, _) =>
         consensusAcceptableTxs si restblocks
         /\ blockNumsInRange restblocks
         /\ (forall ac, ac ∈ (map sender restblocks) -> isSC si.1 ac = false)
         /\ (forall txext, txext ∈ (restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (restblocks)))
     end.
Proof using eas K K_pos.
  intros Hrange Hacc.
  induction firstblock as [|hb1 firstblock IH] in latestState, Hrange, Hacc |- *; simpl in *; auto.
  intros Heoa Hsc.
  change  ((hb1 :: firstblock) ++ restblocks) with (hb1::(firstblock++restblocks)) in Hacc.
  forward_reason.
  pose proof (execValidate _ _ _ Hacc) as Hv.
  unfold validateTx in Hv.
  autorewrite with iff in Hv.
  eapply inductiveStep in Hacc;  auto;[| lia].
  unfold execTx in *.
  destruct (validateTx latestState.1 hb1) eqn:Hval; simpl in *; try contradiction;[].
  pose proof (isSCFalsePresExec _ _ _ Heoa Hsc) as Hsci.
  remember (execValidatedTx latestState hb1) as si.
  destruct si as [si result].
  simpl in *.
  pose proof (fun txext (p : txext ∈ firstblock ++ restblocks) => txCannotCreateContractAtAddrsTrimHead _ _ _
                               (Heoa txext (ltac:(set_solver)))) as Hcannot_tail.
  specialize (IH si ltac:(auto) ltac:(auto) Hcannot_tail).
  simplify_eq.
  destruct (execValidatedTx latestState hb1) as [si0 r0] eqn:Hvr.
  simpl.
  pose proof (f_equal fst Hvr) as Hsi0.
  simpl in Hsi0.
  simplify_eq.
  specialize (IH (fun ac Hac => Hsci ac (ltac:(set_solver)))).
  simpl in *.
  match goal with
    |- context[execTxs ?a ?b] => destruct (execTxs a b)  as [[sf rs] | ] eqn:Htxs
  end.
  - simpl in *; exact IH.
  - simpl in *; exact IH.
Qed.
Corollary fullBlockStep2  (latestState : AugmentedState) (blocks: list TxWithHdr) :
  (forall ac, ac ∈ (map sender (blocks)) -> isSC latestState.1 ac = false)
  -> (forall txext, txext ∈ (blocks) ->  txCannotCreateContractAtAddrs txext (map sender (blocks)))
  -> blockNumsInRange (blocks)
  -> consensusAcceptableTxs latestState (blocks)
  -> match execTxs latestState blocks with
     | None =>  False
     | Some (si, _) => True
     end.
Proof using eas K K_pos.
  intros.
  pose proof (fullBlockStep latestState blocks []) as Hf.
  autorewrite with syntactic in Hf.
  specialize (Hf ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
  destruct (execTxs latestState blocks) as [[si rs] | ] eqn:Hexec.
  - exact I.
  - exact Hf.
Qed.


Lemma acceptableNil lastConsensedState:
  consensusAcceptableTxs lastConsensedState [].
Proof using K K_pos.
  unfold consensusAcceptableTxs.
  intros.
  simpl.
  rewrite initResBal.
  lia.
Qed.


(** If an account's balance did not decrease, the reserve-balance check cannot fail for that account.
    [finalBalSufficient preTxState postTxState t a] is the condition that is checked at the end of a transaction [t] for every changed account [a].
    If the check returns false for any changed account, the transaction is reverted: see [execValidatedTx] above *)
Lemma finalBalSufficient_if_balance_not_decreased:
  forall preTxState postTxState t a, 
    balanceOfAc preTxState.1 a <= balanceOfAc postTxState a
    -> finalBalSufficient preTxState postTxState t a = true.
Proof using K K_pos.
  intros ? ? ? ? Hbal.
  unfold finalBalSufficient.
  destruct (isSC postTxState a) eqn:Hsc; [reflexivity|].
  destruct (decide (sender t = a)) as [Hsender|Hsender].
  - rewrite bool_decide_true; [|exact Hsender].
    destruct (isAllowedToEmptyExec preTxState t) eqn:Hallow; [reflexivity|].
    apply bool_decide_true. lia.
  - rewrite bool_decide_false; [|exact Hsender].
    apply bool_decide_true.
    lia.
Qed.

(* Consensus Invariant and how its steps preserve the invariant
At any given time, consensus has some [latestConsensedState] and a list of transactions/blocks (say [ltx]) proposed on top of that.
The main invariant is that it maintains [consensusAcceptableTxs latestConsensedState ltx].
There are also side conditions like [blockNumsInRange ltx] and that the transactions in [ltx] are not sent to an address that has code: the latter is just a formal assumption in Coq but is guaranteed by cryptographic hardness of generating private keys.

This invariant needs to be preserved in the two main steps of consensus:
- extend ltx with a new block of transactions.
- once execution catches up to the next block remove a prefix of ltx that corresponds to the block whose execution results are now available.

The lemma [fullBlockStep] is exactly what is needed to preserve the invariant at the latter step.
To preserve the invariant at the first step, the proposed new txs (e.g. grabbed from mempool) need to be checked so that they satisfy the [consensusAcceptableTxs] property.

 *)

(*
Below is an illustration of how the blockchain evolves starting from the genesis block b0.
It assumes an oracle nextBlockPicker that picks the next block while satisfying the conditions.

 *)

(* begin hide *)
Section consensusInvariantsAndPreservation.
  Variable b0: list TxWithHdr.
  Variable sb0 : AugmentedState. (* state after b0 *)
  Hypothesis b0range: blockNumsInRange b0.
  Definition cannotCreateCodeAtSenderAddrs ltx := ∀ txext : TxWithHdr,
   txext ∈ ltx
   → txCannotCreateContractAtAddrs txext (map sender ltx).
  Hypothesis b0csa: cannotCreateCodeAtSenderAddrs b0.

  Hypothesis nextBlockPicker:
    forall (lastConsensedState: AugmentedState) (proposedTxs: (list TxWithHdr)),
      consensusAcceptableTxs lastConsensedState proposedTxs
      -> blockNumsInRange proposedTxs
      -> cannotCreateCodeAtSenderAddrs proposedTxs
      -> (∀ ac : EvmAddr, ac ∈ map sender proposedTxs → isSC lastConsensedState.1 ac = false)
      -> exists nextBlock,
          consensusAcceptableTxs lastConsensedState (proposedTxs++nextBlock)
          /\ blockNumsInRange (proposedTxs++nextBlock)
          /\ cannotCreateCodeAtSenderAddrs (proposedTxs++nextBlock)
          /\ (∀ ac : EvmAddr, ac ∈ map sender (proposedTxs++nextBlock) → isSC lastConsensedState.1 ac = false).
  Open Scope N_scope.

  (** The statement below is of course unprovable. But the proof script below illustrates how the state of the consensus module evolves from the genesis block b0, showing how the two steps are taken and how they preserve the invariants. At every time, the proof context (hypotheses) has the assertion that the invariants are satisfied for the latest consensus block and the proposal so far. The proof script itself is not useful to see: the Coq goal at every step is illuminating.
   *)

  Lemma operation  : False.
    intros.
    revert nextBlockPicker.
    rwHyps.
    intros.
    (** now we invoke the oracle to pick the next block after b0 *)
    pose proof (nextBlockPicker sb0 []  (acceptableNil _) I ltac:(set_solver) ltac:(set_solver)) as b1.
    destruct b1 as [b1 b1ok].
    simpl in b1ok.
    forward_reason.
    (** now we invoke the oracle to pick the next block after b1 *)
    pose proof (nextBlockPicker sb0 b1 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b2.
    destruct b2 as [b2 b2ok].
    forward_reason.
    unfold cannotCreateCodeAtSenderAddrs in *.
    apply fullBlockStep in b2okl; auto.
    (** assuming K=2, we wait for execution to execute b1 and give us the new state sb1  *)
    destruct (execTxs sb0 b1) as [[sb1 ?]|]; auto.
    forward_reason.
    (** now we pick the new block b3, but with the latestConsensedState of sb1 rather than sb0 *)
    pose proof (nextBlockPicker sb1 b2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b3.
    destruct b3 as [b3 b3ok].
    forward_reason.
    apply fullBlockStep in b3okl; auto.
    (** we wait for execution to execute b2 and give us the new state sb2  *)
    destruct (execTxs sb1 b2) as [[sb2 ?]|]; auto;[].
    forward_reason.
    (** now we pick the new block b3, but with the latestConsensedState of sb2 rather than sb1 *)
    pose proof (nextBlockPicker sb2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b4.
 Abort.
End consensusInvariantsAndPreservation.
(* end hide *)
End EvmCore.
End K.

(** * Consensus checks using finite-width arithmetic (U256).

Below we define [remainingEffReserveBalOfSenderF], which is equivalent to [remainingEffReserveBalOfSender],
but only uses finite-width arithmetic ([U256]), instead of the unbounded/exact [Z], where one does not need to worry
about over/underflows.

The main idea is to represent a [Z] by [option U256] where [None] represents all the negative numbers.
All negative values of remaining effective reserve balance are useless anyway.
The definition of [remainingEffReserveBalOfSenderF] will look almost exactly like [remainingEffReserveBalOfSender]
except that it uses variants of arithmetic operations (like [-], [`min`], [`max`]) that work on [option U256] instead of [Z].
 *)

Section U256Consensus.
  Context (K: N).

  Definition u256_to_Z (u: U256): Z := Z.of_N (u256_to_N u).

  Open Scope Z_scope.
  (** below, we define precisely what it means for an [o:option U256] is equivalent to a [z:Z] *)
  Definition u256z_equiv (o: option U256) (z: Z) : Prop :=
    (z < 2^256) /\
      match o with
    | None => (z < 0)
    | Some u => z = u256_to_Z u
    end.
  
  (** Below, we define variants of previous definitions where Z is substituted in by [U256].
      The suffix F stands for finite width numbers.
   *)
  Definition EffReserveBalsF := EvmAddr -> U256.

  (** Helper projections relying on the invariant that balances already fit in 256 bits. *)
  Definition balanceOfAcF (s : AugmentedState) (addr : EvmAddr) : U256 :=
    u256_of_N (balanceOfAc s.1 addr).
  
  Definition delayedReserveBalF (s : AugmentedState) (addr : EvmAddr) (n: N) : U256 :=
    u256_of_N (delayedReserveBalOfAddr K s.2 addr n).

  Definition valueF (t: TxWithHdr) : U256 := u256_of_N (value t).
  Definition maxTxFeeF (t: TxWithHdr) : U256 := u256_of_N (maxTxFee t).
  Definition maxStorageFeeF (t: TxWithHdr) : U256 := u256_of_N (maxStorageFee t).


  (** The definition of [remainingEffReserveBalOfSenderF] will look almost exactly like [remainingEffReserveBalOfSender] except that it uses variants of arithmetic operations (like [-], [`min`], [`max`]) that work on [option U256] instead of [Z]. So, we define those operations on [option 256] and prove that they respect the equivalence [u256z_equiv].

      The first one is the [min] operation:

   *)
  Definition u256_opt_min (lhs rhs : option U256) : option U256 :=
    match lhs, rhs with
    | Some l, Some r => Some (u256_min l r)
    | _, _ => None
     (** ^ the min of 2 negative numbers is always a negative number *)          end.

  (* begin hide *)
  Hint Unfold u256z_equiv u256_sub
    u256_min 
    u256_wrap 
    u256_to_Z 
    u256_to_N
    u256_of_N
    U256_modulus
    : unfoldu.
  
  Ltac unfolds := autounfold with unfoldu in *; simpl in *.
  (* end hide *)

  (** We easily prove that our min operation on [option U256] respects the
      [u256z_equiv] relation: on inputs that are equivalent,
      the outputs of [u256_opt_min] and [Z.min] are equivalent *)
  Lemma u256z_equiv_mino (x y : option U256) (zx zy : Z) :
    u256z_equiv x zx ->
    u256z_equiv y zy ->
    u256z_equiv (u256_opt_min x y) (Z.min zx zy).
  Proof.
    destruct x, y; simpl in *; unfolds; try Arith.arith_solve.
  Qed.

  (** max operation on [option U256] *)
  Definition u256_opt_max (lhs rhs : option U256) : option U256 :=
    match lhs, rhs with
    | Some l, Some r =>
        Some (u256_wrap ((u256_to_N l) `max` (u256_to_N r)))
    | Some l, None => Some l
    | None, Some r => Some r
    | None, None => None
    end.


  Lemma u256z_equiv_maxo (x y : option U256) (zx zy : Z) :
    u256z_equiv x zx ->
    u256z_equiv y zy ->
    u256z_equiv (u256_opt_max x y) (Z.max zx zy).
  Proof.
    destruct x, y; simpl in *; unfolds; try Arith.arith_solve.
  Qed.
  
  (** Subtraction is tricky. if [a] and [b] are negative numbers, the result may be negative or positive. But as we represent both [a] and [b] by [None], we do not have enough information to determine that. Fortunately, in [remainingEffReserveBalOfSender], the RHS of subtraction was always known to be non-negative. So it suffices to just define for that case: *)
  Definition u256_opt_sub (lhs : option U256) (rhs: U256) : option U256 :=
    match lhs with
    | Some l =>
        if  (asbool (u256_to_N l < u256_to_N rhs)) then None else Some (u256_sub l rhs)
    | None =>  None
    (** ^ subtracting a non-negative number from a negative number is always negative *)
    end.

  Lemma u256z_equiv_sub (x : option U256) (y : U256) (zx zy : Z) :
    u256z_equiv x zx ->
    u256z_equiv (Some y) zy ->
    u256z_equiv (u256_opt_sub x y) (zx - zy).
  Proof.
    unfolds.
    simpl. intros.
    destruct x as [| x].
    {
      simpl.
      unfolds.
      case_bool_decide; try Arith.arith_solve.
    }
    {
      simpl.
      unfolds. Arith.arith_solve.
    }
  Qed.

  (** We define some notations to make our definition of [remainingEffReserveBalOfSenderF] look similar *)
  Declare Scope u256opt_scope.
  Delimit Scope u256opt_scope with u256opt.
  (** the line below tells Coq to parse [x ⊖  y] as [u256_opt_sub x y] *)
  Notation "x ⊖  y" := (u256_opt_sub x y) (at level 50, left associativity) : u256opt_scope.
  Notation "x `mino` y" := (u256_opt_min x y) (at level 35, y at next level) : u256opt_scope.
  Notation "x `maxo` y" := (u256_opt_max x y) (at level 35, y at next level) : u256opt_scope.

  (*
  Notation "x `minf` y" := (u256_min x y) (at level 35, y at next level) : u256opt_scope. *)
  Notation "0f" := (Some u256_zero) : u256opt_scope.

  (* begin hide *)
  Local Open Scope u256opt_scope.

    Definition z_to_u256_option (z: Z) : option U256 :=
    if asbool ((0 <= z) /\ (z < 2^256))
    then Some (u256_of_N (Z.to_N z))
    else None.
 

  Hint Unfold u256z_equiv u256_sub z_to_u256_option
    u256_min 
    u256_wrap 
    u256_to_Z 
    u256_to_N
    u256_of_N
    U256_modulus
    u256_opt_sub
    : unfoldu.
  
  Lemma iffeq r z:
    (z < 2^256)->
      match r with
    | None => (z < 0)
    | Some u => z = u256_to_Z u
      end <-> z_to_u256_option z = r.
  Proof.
    unfolds.
    split.
    - destruct r; intros; subst.
      {
        case_bool_decide; try Arith.arith_solve.
        destruct u.
        do 2 f_equal. Arith.remove_useless_mod_a.
        simpl. lia.
      }
      {
        case_bool_decide; try Arith.arith_solve.
      }
    - intros.
      subst.
      case_bool_decide; try lia.
      simpl.
      Arith.arith_solve.
  Qed.
  
    
  

  Lemma u256z_equiv_minf (x y : U256) (zx zy : Z) :
    u256z_equiv (Some x) zx ->
    u256z_equiv (Some y) zy ->
    u256z_equiv (Some (u256_min x y)) (Z.min zx zy).
  Proof.
    simpl.
    unfolds. Arith.arith_solve.
  Qed.
  Hint Unfold balanceOfAcF balanceOfAcF z_to_u256_option u256_opt_min u256_of_N u256_wrap : unfoldu.

  (* end hide *)


  (** Finally, below is the U256 version of [remainingEffReserveBalOfSender] *)
  Definition remainingEffReserveBalOfSenderF
    (preIntermediatesState : AugmentedState)
    (prevErb : U256)
    (intermediates : list TxWithHdr)
    (candidateTx : TxWithHdr) : option U256 :=
    let s := preIntermediatesState in
    let senderAddr := sender candidateTx in
    let senderBal := Some (balanceOfAcF preIntermediatesState senderAddr) in
    let delayedRb := Some (delayedReserveBalF preIntermediatesState senderAddr (txBlockNum candidateTx)) in
    let baseErb :=
      if senderNoRecentActivity K s intermediates candidateTx
      then senderBal `mino` delayedRb
      else (Some prevErb) `mino` delayedRb in
    if isAllowedToEmpty K preIntermediatesState intermediates candidateTx
    then
      let newBal := (((senderBal ⊖ (maxTxFeeF candidateTx)) ⊖ (valueF candidateTx)) ⊖ (maxStorageFeeF candidateTx)) `maxo` 0f in
      (** ^ pay attention to the bracketing. If we instead first add up [maxTxFeeF candidateTx], [valueF candidateTx], and [maxStorageFeeF candidateTx], and only then subtract from [senderBal], the result of addition may overflow, although only a malicious person would probably send such a transaction *)
      if asbool (maxTxFee candidateTx <= balanceOfAc (preIntermediatesState.1) senderAddr)
      then newBal `mino` delayedRb
      else None
    else baseErb ⊖ (maxTxFeeF candidateTx).

  (*
  Definition initialEffReserveBalsF (s : AugmentedState) : EffReserveBalsF :=
    fun addr => ((balanceOfAcF s addr)) `minf` ((configuredReserveBalF s addr)).
  
  Fixpoint remainingEffReserveBalsLF
    (latestState : AugmentedState)
    (preRestResBalances : EffReserveBalsF)
    (postStateAccountedSuffix rest : list TxWithHdr) : option EffReserveBalsF :=
    match rest with
    | [] => Some preRestResBalances
    | hrest :: tlrest =>
        let rem :=
            remainingEffReserveBalOfSenderF latestState
              (preRestResBalances (sender hrest)) postStateAccountedSuffix hrest in
        match rem with
        | None => None
        | Some remp => 
            let erbs := updateKey preRestResBalances (sender hrest) (fun _ => remp) in
            remainingEffReserveBalsLF latestState erbs (postStateAccountedSuffix ++ [hrest]) tlrest
        end
    end.

  Definition consensusAcceptableTxsF (latestState : AugmentedState) (postStateProposedTxs : list TxWithHdr) : bool :=
    match remainingEffReserveBalsLF latestState
            (initialEffReserveBalsF latestState) [] postStateProposedTxs with
    | None => false
    | Some _ => true
    end.
  Definition txsReserveUpdatesWithinBounds (ltx : list TxWithHdr) : Prop :=
    forall tx, tx ∈ ltx -> txReserveUpdateWithinBounds tx.
   *)

  (** Next we prove equivalence: for that, we need to assume that the balances, configured reserve balance thresholds of all accounts, [value], [maxTxFee], etc. are within bounds of U256. These are trivial invariants because the EVM datatypes already enforce that
      *)
  Definition stateWithinBounds (s : AugmentedState) : Prop :=
    forall addr,
      ((balanceOfAc s.1 addr) < 2^256) /\
      ((settledReserveBalOfAddr s.2 addr) < 2^256) /\
      match pendingReserveBalOfAddr s.2 addr with
      | Some (rb, _) => rb < 2^256
      | None => True
      end.

  Definition txReserveUpdateWithinBounds (tx : TxWithHdr) : Prop :=
    maxTxFee tx < 2^256 /\
    value tx < 2^256 /\
    maxStorageFee tx < 2^256.

  (** we can now use the above 2 definitions to state the equivalence theorem. The proof is mainly just unfolding definitions and using an arithmetic solver that understands Z.modulo *)
  Lemma remainingEffReserveBalOfSender_equivF
    (preIntermediatesState : AugmentedState)
    (prevErbF : U256)
    (intermediates : list TxWithHdr)
    (candidateTx : TxWithHdr) :
    stateWithinBounds preIntermediatesState ->
    txReserveUpdateWithinBounds candidateTx ->
    u256_val prevErbF < 2^256 ->
    u256z_equiv
      (remainingEffReserveBalOfSenderF preIntermediatesState prevErbF intermediates candidateTx)
      (remainingEffReserveBalOfSender K preIntermediatesState (u256_to_N prevErbF) intermediates candidateTx).
  Proof.
    intros Hb Ht Hr.
    unfold remainingEffReserveBalOfSender, remainingEffReserveBalOfSenderF.
    destruct (Hb (sender candidateTx)) as [Hbal [Hsettled Hpend]].
    hnf in Ht.
    unfold balanceOfAcF, delayedReserveBalF in *.
    set (drb := delayedReserveBalOfAddr K preIntermediatesState.2 (sender candidateTx)
                (txBlockNum candidateTx)).
    assert (Hdrb : drb < 2^256).
    {
      unfold drb, delayedReserveBalOfAddr, delayedReserveBal.
      destruct (pendingReserveBal (preIntermediatesState.2 (sender candidateTx))) as [[v blk]|] eqn:Hpend';
        simpl.
      - unfold pendingReserveBalOfAddr in Hpend.
        rewrite Hpend' in Hpend; simpl in Hpend.
        destruct (asbool (blk + K <= txBlockNum candidateTx)%N) eqn:Hle; simpl; [exact Hpend|exact Hsettled].
      - exact Hsettled.
    }
    unfolds.
    destruct (isAllowedToEmpty K preIntermediatesState intermediates candidateTx) eqn:Hallow; simpl.
    - destruct (asbool (maxTxFee candidateTx <= balanceOfAc (preIntermediatesState.1) (sender candidateTx))) eqn:Hfee; simpl.
      all: autounfold with unfoldu in *.
      all: repeat (
        case_bool_decide;
        forward_reason; simpl in *;
        try (resolveDecide lia);
        try (Arith.remove_useless_mod_a; try lia; try Arith.arith_solve)
      ).
    - destruct (senderNoRecentActivity K preIntermediatesState intermediates candidateTx) eqn:Hsnra; simpl.
      all: autounfold with unfoldu in *.
      all: repeat (
        case_bool_decide;
        forward_reason; simpl in *;
        try (resolveDecide lia);
        try (Arith.remove_useless_mod_a; try lia; try Arith.arith_solve)
      ).
   Qed.

    (*
  Theorem consensusAcceptableTxs_equiv_U256
    (latestState : AugmentedState) (postStateProposedTxs : list TxWithHdr) :
    stateWithinBounds latestState ->
    txsReserveUpdatesWithinBounds postStateProposedTxs ->
    consensusAcceptableTxs K latestState postStateProposedTxs <->
    consensusAcceptableTxsF latestState postStateProposedTxs = true.
  Proof. Abort.

  Theorem consensusAcceptableTxs_equiv_U256
    (latestState : AugmentedState) (postStateProposedTxs : list TxWithHdr) :
    stateWithinBounds latestState ->
    txsReserveUpdatesWithinBounds postStateProposedTxs ->
    consensusAcceptableTxsF latestState postStateProposedTxs = true ->
    consensusAcceptableTxs K latestState postStateProposedTxs.
  Proof.
    induction postStateProposedTxs;
      unfold consensusAcceptableTxs, consensusAcceptableTxsF; simpl in *;
      [intros; rewrite initResBal; lia|].
    intros. Abort.
1 goal (ID 110)
  
  K, DefaultReserveBal : N
  latestState : AugmentedState
  a : TxWithHdr
  postStateProposedTxs : list TxWithHdr
  IHpostStateProposedTxs :
    stateWithinBounds latestState
    → txsReserveUpdatesWithinBounds postStateProposedTxs
      → consensusAcceptableTxsF latestState postStateProposedTxs = true
        → consensusAcceptableTxs K latestState postStateProposedTxs
  H : stateWithinBounds latestState
  H0 : txsReserveUpdatesWithinBounds (a :: postStateProposedTxs)
  H1 :
    match
      match remainingEffReserveBalOfSenderU256 latestState (initialEffReserveBalsF latestState (sender a)) [] a with
      | Some _ =>
          remainingEffReserveBalsLF latestState
            (updateKey (initialEffReserveBalsF latestState) (sender a)
               (λ _ : option U256,
                  remainingEffReserveBalOfSenderU256 latestState (initialEffReserveBalsF latestState (sender a)) [] a))
            [a] postStateProposedTxs
      | None => None
      end
    with
    | Some _ => true
    | None => false
    end = true
  addr : EvmAddr
  H2 : addr ∈ sender a :: map sender postStateProposedTxs
  ============================
  (0
   ≤ remainingEffReserveBalsL K latestState
       (updateKey (initialEffReserveBals latestState) (sender a)
          (λ _ : Z, remainingEffReserveBalOfSender K latestState (initialEffReserveBals latestState (sender a)) [] a))
       [a] postStateProposedTxs addr)
     *)
End U256Consensus.

(** * RBTests: small “test case” lemmas by unfolding and rewriting *)
Section RBTests.
  Context (K: N) (K_pos: (0 < K)%N).

  Variable s0 : AugmentedState.
  Variables A B : EvmAddr.
  Variable tx1 : TxWithHdr.
  Let n1 : N := txBlockNum tx1.
  Let rb10 : N := 10.

  (** Example setup: A is delegated and its settled reserve is 0 in the pre‑state.
      A can recover by having another EOA [B] call into A’s delegated code to
      set the reserve to 10, which yields a reserve‑balance update for [A]
      during execution. *)
  Hypothesis Hdeleg : addrDelegated s0.1 A = true.
  Hypothesis Hsettled0 : settledReserveBal (s0.2 A) = 0.
  Hypothesis Hpend0 : pendingReserveBal (s0.2 A) = None.
  Hypothesis Hsender1 : sender tx1 = B.

  Let rbUpdate1 : ReserveBalUpdate := [(A, rb10)].
  Let es1 : ExtraAcStates := @updateExtraState K s0.2 tx1 rbUpdate1.

  (** In the pre‑state, A’s delayed reserve is 0. *)
  Lemma RBTest_pre_rb0 :
    delayedReserveBalOfAddr K s0.2 A n1 = 0.
  Proof using A Hpend0 Hsettled0 K K_pos n1 s0 tx1.
    unfold delayedReserveBalOfAddr, delayedReserveBal. simpl.
    rewrite Hpend0. simpl. rewrite Hsettled0. reflexivity.
  Qed.

  (** After the sponsor update, A’s delayed reserve becomes 10 at [n1+K]. *)
  Lemma RBTest_delegate_raise_with_sponsor :
    delayedReserveBalOfAddr K es1 A (n1 + K) = rb10.
  Proof using A B Hpend0 Hsender1 Hsettled0 K K_pos es1 n1 rb10 rbUpdate1 s0 tx1.
    unfold es1.
    unfold rbUpdate1.
    unfold updateExtraState, updateExtraStateBase.
    unfold delayedReserveBalOfAddr, delayedReserveBal.
    simpl.
    rewrite Hpend0. simpl.
    unfold promotePendingReserveBal. simpl.
    unfold applyReserveBalUpdate. simpl.
    case_bool_decide; [|contradiction].
    simpl.
    case_bool_decide; [reflexivity|lia].
  Qed.

  (** Consensus acceptability for the sponsor tx (sender = [B]). *)
  Hypothesis HnotDelegB : addrDelegated s0.1 B = false.
  Hypothesis HnoDelWindow1B : @existsDelUndelTxWithinK K s0 tx1 = false.
  Hypothesis HnoDelTx1B :
    asbool (B ∈ flat_map addrsDelUndelByTx [tx1]) = false.
  Hypothesis HnoTxWindow1B : @existsTxWithinK K s0 tx1 = false.
  Hypothesis Hbal1B :
    (maxTxFee tx1 + value tx1 + maxStorageFee tx1 <= balanceOfAc s0.1 B)%N.

  Lemma RBTest_consensus_accepts_sponsor :
    consensusAcceptableTxs K s0 [tx1].
  Proof using A B Hbal1B HnoDelTx1B HnoDelWindow1B HnoTxWindow1B HnotDelegB
    Hdeleg Hpend0 Hsender1 Hsettled0 K K_pos n1 s0 tx1.
    intros addr Haddr.
    assert (addr = B) as ->.
    { simpl in Haddr. rewrite Hsender1 in Haddr. set_solver. }
    unfold remainingEffReserveBalsL. simpl.
    set (pre := @initialEffReserveBals K s0).
    set (pre1 := @advanceEffReserveBals K s0 pre (txBlockNum tx1)).
    unfold remainingEffReserveBalOfSender. simpl.
    unfold isAllowedToEmpty.
    rewrite Hsender1.
    rewrite HnotDelegB.
    rewrite HnoDelWindow1B.
    rewrite HnoDelTx1B.
    rewrite HnoTxWindow1B.
    simpl.
    unfold updateKey.
    simpl.
    rewrite bool_decide_true; [|reflexivity].
    simpl.
    assert (Hfee_le : (maxTxFee tx1 <= balanceOfAc s0.1 B)%N).
    {
      apply (N.le_trans _ (maxTxFee tx1 + value tx1)).
      - apply N.le_add_r.
      - apply (N.le_trans _ (maxTxFee tx1 + value tx1 + maxStorageFee tx1)).
        + apply N.le_add_r.
        + exact Hbal1B.
    }
    match goal with
    | |- context[asbool ?P] =>
        (assert (Hfee_ok : asbool P = true) by
           (apply bool_decide_true; lia);
         rewrite Hfee_ok; simpl)
    end.
    apply Z.min_glb; [apply Z.le_max_r|apply N2Z.is_nonneg].
  Qed.

  (** Putting the pieces together: although A’s reserve is 0 in the pre‑state,
      a sponsor tx from [B] can be accepted by consensus and raise A’s delayed
      reserve back to 10 after [K] blocks. *)
  Lemma RBTest_recover_from_zero :
    delayedReserveBalOfAddr K s0.2 A n1 = 0 /\
    consensusAcceptableTxs K s0 [tx1] /\
    delayedReserveBalOfAddr K es1 A (n1 + K) = rb10.
  Proof using A B Hbal1B HnoDelTx1B HnoDelWindow1B HnoTxWindow1B HnotDelegB
    Hdeleg Hpend0 Hsender1 Hsettled0 K K_pos n1 rb10 s0 es1 tx1.
    split.
    - apply RBTest_pre_rb0.
    - split.
      + apply RBTest_consensus_accepts_sponsor.
      + apply RBTest_delegate_raise_with_sponsor.
  Qed.

  (** Execution success for a concrete two‑tx suffix: just unfold. *)
  Variables evmExecTxCore :
    StateOfAccounts -> TxWithHdr -> ((StateOfAccounts * TxResult) * (list EvmAddr)) * ReserveBalUpdate.
  Variables revertTx : StateOfAccounts -> TxWithHdr -> (StateOfAccounts * TxResult).
  Variables post1 : StateOfAccounts.
  Variable changed1 : list EvmAddr.
  Variable rbUpdate1' : ReserveBalUpdate.
  Variable r1 : TxResult.
  Hypothesis Hcore1 :
    evmExecTxCore s0.1 tx1 = (((post1, r1), changed1), rbUpdate1').
  Hypothesis Hsufficient1 :
    @allFinalBalSufficient K s0 post1 changed1 tx1 = true.

  Lemma RBTest_validateTx :
    validateTx s0.1 tx1 = true.
  Proof using Hbal1B Hsender1 s0 tx1.
    unfold validateTx.
    rewrite Hsender1.
    apply bool_decide_true.
    apply (N.le_trans _ (maxTxFee tx1 + value tx1)).
    - apply N.le_add_r.
    - apply (N.le_trans _ (maxTxFee tx1 + value tx1 + maxStorageFee tx1)).
      + apply N.le_add_r.
      + exact Hbal1B.
  Qed.

  Lemma RBTest_execTx_no_revert :
    @execTx K evmExecTxCore revertTx s0 tx1 =
      Some ((post1, @updateExtraState K s0.2 tx1 rbUpdate1'), r1).
  Proof using B Hcore1 Hsufficient1 Hbal1B Hsender1 K evmExecTxCore rbUpdate1' r1 revertTx s0 post1 tx1 changed1.
    unfold execTx. rewrite RBTest_validateTx. simpl.
    unfold execValidatedTx.
    rewrite Hcore1. simpl.
    rewrite Hsufficient1. reflexivity.
  Qed.

  Lemma RBTest_execTxs_one :
    @execTxs K evmExecTxCore revertTx s0 [tx1] =
      Some ((post1, @updateExtraState K s0.2 tx1 rbUpdate1'), [r1]).
  Proof using B Hcore1 Hsufficient1 Hbal1B Hsender1 K evmExecTxCore rbUpdate1' r1 revertTx s0 post1 tx1 changed1.
    simpl. rewrite RBTest_execTx_no_revert. reflexivity.
  Qed.
End RBTests.
