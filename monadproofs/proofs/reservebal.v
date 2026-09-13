(** * Coq model of reserve balance and proof of safety

    The guiding idea is simple:

    - *Consensus* computes a **worst-case, mostly fee-only budget** (the “effective
      reserve”) for the yet-to-be-executed suffix and only proposes blocks when
      that budget stays non-negative for every **sender** that appears later.

    - *Execution* runs the actual EVM step and enforces that **no account dips
      below its protected reserve slice** (with a carefully fenced “emptying”
      exception). If a transaction would violate that, it is reverted in place.

    Below we define the two algorithms, followed by proofs.
    The consensus check is defined in [consensusAcceptableTxs], the execution check is in [execValidatedTx] (called by [execTx] after validation).

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

(** Many of the EVM semantics definitions we use come from Yoichi's EVM semantics, developed several years ago. The definition of [Transaction] there lacks fields to support newer features like delegation. Also, the last field is to support user-configurable reserve balances in Monad. There is a new transaction type which can update the configured reserve balance of the sender. Such transactions do nothing else. *)
Record TxExtra :=
  {
    
    authorities: list EIP7702Authority;

    (** The fields above should ultimately come from EVM semantics. The fields below are monad-specific. *)
    
    indexInBlock: N;
    (** ^ index of this transaction in the block. monaddb stores when (blockindex, txindex) an account was born *)
    
    reserveBalUpdate: option N
    (** ^ updates the reserve balance of the sender if [Some]. In that case, the transaction does nothing else, e.g., no smart contract invocation or transfer. It must be [None] for regular transactions (which do not reconfigure the reserve balance). [option N] in Coq can be thought of as std::optional<N> in C++. [None] in Coq corresponds to std::nullopt in C++.
Transactions to update reserve balance will be implemented as a call to a special precompile:

A stateful precompile at address 0xRESERVES maintains a mapping from account addresses to their configured
reserve balance values. The precompile exposes an update(uint256) function that allows accounts to set
their reserve balance. Any internal call (from a smart contract) to the update function of 0xRESERVES causes
the transaction to revert. Only EOA accounts may call the precompile’s update function directly.
A transaction t is a reconfiguring transaction if it calls the update(uint256) function of the 0xRESERVES
precompile (inspectable by the to and calldata field). A reconfiguring transaction is required to have value
field set as 0.
Behavior of the precompile: When a reconfiguring transaction is executed, the precompile only updates
the reserve balance mapping for t.sender to the specified value. The precompile performs no other operations:
no balance transfers, no state changes beyond updating the single mapping entry. As a result, a reconfiguring
transaction never reverts. This simplicity is assumed for proving the correctness of the reserve balance
mechanism.

     *)
  }.

(** for any decidable assertion/proposition P, [asbool P] is a boolean such that [(asbool P = true) <-> P], where
 [<->] means iff (if and only if)*)
Notation asbool := bool_decide.

Definition is_undelegation (a: EIP7702Authority) : bool :=
  asbool (del_to a = 0).

(** EIP-7702 applies only the last valid authorization per authority.
    We canonicalize by scanning right-to-left and keeping only the last valid
    occurrence per [del_from]. *)
Fixpoint canonicalAuthorities
    (l: list EIP7702Authority) : list EIP7702Authority :=
  match l with
  | [] => []
  | a :: tl =>
      let tl' := canonicalAuthorities tl in
      match del_from a with
      | None => tl'
      | Some addr =>
          if asbool (addr ∈ flat_map (fun x =>
                         match del_from x with
                         | Some addr' => [addr']
                         | None => []
                         end) tl')
          then tl'
          else a :: tl'
      end
  end.

(** list of accounts requested to be delegated in transaction [txe] *)
Definition dels (txe: TxExtra) : list EvmAddr :=
  flat_map (fun a => match del_from a with
                     | Some addr => if is_undelegation a then [] else [addr]
                     | None => []
                     end ) (canonicalAuthorities (authorities txe)).

(** list of accounts requested to be undelegated in transaction [txe] *)
Definition undels (txe: TxExtra) : list EvmAddr :=
  flat_map (fun a => match del_from a with
                     | Some addr => if is_undelegation a then [addr] else []
                     | None => []
                     end ) (canonicalAuthorities (authorities txe)).

#[global] Opaque dels undels.

Definition Transaction: Type :=  block.transaction * TxExtra.
(** The type [A * B] in Coq can be thought of as [std::pair<A,B>]. The projections [.1] and [.2] can be used to obtain the first and second components of the pair, respectively. *)
Definition TxWithHdr : Type := Transaction * BlockHeader.

(** Our **fee upper bound** is intentionally pessimistic: the consensus rule
    reasons about [gas_limit × gas_price], not about *actual* gas used, which can be hard to efficiently estimate.
    This excludes storage fees, which are separately handled below because storage fees are only accounted by consensus for transactions that are allowed to empty.
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

(** Next, we have some simple wrappers for brevity.

   sender of a transaction: *)
Definition sender (t: TxWithHdr): EvmAddr := tsender t.1.1.

(** value transfer field of a of a transaction *)
Definition value (t: TxWithHdr): N := w256_to_N (block.tr_value t.1.1).

(** addresses delegated or undelegated by [tx] *)
Definition addrsDelUndelByTx  (tx: TxWithHdr) : list EvmAddr := (dels tx.1.2 ++undels tx.1.2).

(** block number of a transaction *)
Definition txBlockNum (t: TxWithHdr) : N := number t.2.

(** returns [None] if this tx is not a reserve-balance-reconfig tx. Else it returns [Some newRb], where [newRb] will become the new reserve balance threshold of the sender if/when t is executed. *)
Definition reserveBalUpdateOfTx (t: TxWithHdr) : option N :=
  reserveBalUpdate t.1.2.

(** To implement reserve balance checks, execution needs to maintain some extra state (beyond the core EVM state) for each account:  *)
Record ExtraAcState :=
  {
    lastTxInBlockIndex : option N;
    (** ^ last block index where this account sent a transaction. In the implementation, we can just track the last 2K range, e.g. this can be None if the last tx was more than 2K block before. we do not need to store this information in the db as it can be easily computed *)
    lastDelUndelInBlockIndex : option N;
    (** ^ last block index where this address was delegated or undelegated. In the implementation, we can just track the last 2K range.*)
    configuredReserveBal: N;
    (** ^ the current configured reserve balance of the account. will either be [DefaultReserveBal] or something else if the account sent a transaction where [reserveBalUpdate] is not [None] *)
  }.

(*
#[only(lens)] derive ExtraAcState.
*)

Definition ExtraAcStates := (EvmAddr -> ExtraAcState).

(** Our modified execution function which does reserve balance checks will use the following type as input/output.*)
Definition AugmentedState : Type := StateOfAccounts * ExtraAcStates.

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


(** update the value of the key [updKey] in [oldMap] to [f (oldMap updKey)] ([f] applied to the old value of the key [updKey] in the map) *)
Definition updateKey  {T} `{c: EqDecision T} {V}  (oldmap: T -> V) (updKey: T) (f: V -> V) : T -> V :=
  fun k => if (asbool (k=updKey)) then f (oldmap updKey) else oldmap k.

(*
Disable Notation "!!!".
 *)

(* TODO: remove *)
Lemma updateKeyLkp3  {T} `{c: EqDecision T} {V} (m: T -> V) (a b: T) (f: V -> V) :
  (updateKey m a f)  b = if (asbool (b=a)) then (f (m a)) else m  b.
Proof using.
  reflexivity.
Qed.

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

(** some more wrappers: *)
Definition configuredReserveBalOfAddr (s: ExtraAcStates) (addr : EvmAddr) : N := configuredReserveBal (s addr).

(* begin hide *)
Open Scope Z_scope.
(* end hide *)

(** balance of an account in a given state: *)
Definition balanceOfAc (s: StateOfAccounts) (a: EvmAddr) : N := balance (s a).

(** update balance of the account [addr] such that the new value is [upd] applied to the old value *)
Definition updateBalanceOfAc (s: StateOfAccounts) (addr: EvmAddr) (upd: N -> N) : StateOfAccounts :=
  updateKey s addr (fun old => old &: _balance %= upd).

(** balance of an account in a given augmented state *)
Definition balanceOfAcA (s: AugmentedState) (ac: EvmAddr) := balanceOfAc  s.1 ac.

(** initial effective reserve balances, before any proposed tx  *)
Definition initialEffReserveBals (s: AugmentedState) : EffReserveBals :=
  fun addr =>  (balanceOfAc s.1 addr `min` configuredReserveBalOfAddr s.2 addr).

(** Consensus’ decrement step:

    The next defn is the algebraic heart of consensus check algorithm:
    fold this function left-to-right over the entire sequence of proposed txs, and you get the remaining
    worst-case protected reserve for every sender.

    Formally, this function conservatively estimates the remaining effective reserve balance of the sender of [candidateTx] after executing [candidateTx], assuming [prevErb] is the estimate of the reserve balance of the sender of [candidateTx] just before executing [candidateTx]. [preIntermediatesState] is the latest fully-executed state and [intermediates] is a list of all the transactions between [preIntermediatesState] and [candidateTx].

    In the definition of [newBal] (let binding), the subtraction is capped below at 0: the result is non-negative.
    So, if [sbal < maxTxFee candidateTx + value candidateTx + maxStorageFee candidateTx] but  [maxTxFee next <= sbal], this transaction ([candidateTx]) will be accepted but all
    subsequent ones (with [maxTxFee > 0]) from the same sender will be rejected as the remaining effective reserve balance becomes 0.

   This function represents the check that consensus needs to do when adding [candidateTx] at the end of the already built/proposed valid sequence of txs [intermediates]. [candidateTx] will be accepted iff the returned value is non-negative.

   The [intermediates] list is only used for the [isAllowedToEmpty] check: so the Rust implementation can optimize it by instead just maintaining the 2 pieces of info [isAllowedToEmpty] needs from [intermediates]: the set of senders, the set of addrs that are delegated or undelegated in those txs.
 *)

Definition remainingEffReserveBalOfSender (preIntermediatesState : AugmentedState) (prevErb: Z) (intermediates: list TxWithHdr) (candidateTx: TxWithHdr)
  : Z :=
  let s := preIntermediatesState in
  let senderAddr := sender candidateTx in
  match reserveBalUpdateOfTx candidateTx with
  | Some newRb =>
      if isAllowedToEmpty s intermediates candidateTx
      then (balanceOfAc s.1 senderAddr - maxTxFee candidateTx) `min` newRb
      else (prevErb - maxTxFee candidateTx) `min` newRb
  | None  =>
      (** regular tx, not one that sets reserve balance: *)
      if isAllowedToEmpty s intermediates candidateTx
      then
        let sbal := balanceOfAc s.1 senderAddr in
        let newBal:= (sbal - maxTxFee candidateTx - value candidateTx - maxStorageFee candidateTx) `max` 0 in
        if asbool (maxTxFee candidateTx <= sbal)
        then newBal `min` (configuredReserveBalOfAddr s.2 senderAddr)
        else -1

      else (prevErb - maxTxFee candidateTx) (* -ve =>  this tx cannot be accepted *)
  end.

(** At the end of this file, we have defined [remainingEffReserveBalOfSenderF] which is analogous to [remainingEffReserveBalOfSender] but instead of [Z] arithmetic (idealized, unbounded), only uses U256 aritmetic. Instead of returning Z, it returns an [option U256], where negative numbers are represented by [None]. In that version, [candidateTx] is accepted iff the result is not [None]. We proved that [remainingEffReserveBalOfSenderF] and [remainingEffReserveBalOfSender] are equivalent.
*)

(** Next, we just "fold" the above function over the entire sequence of proposed transactions, starting from the first one after the fully executed state. Note how in the recursive call, we add the processed head to the list of intermediate transactions.
   As with the function above, the [intermediates] list is only used for the [isAllowedToEmpty] check: so the Rust implementation can optimize it by instead just maintaining the 2 pieces of info [isAllowedToEmpty] needs from [intermediates]: the set of senders, the set of addrs that are delegated or undelegated in those txs.

 *)
Fixpoint remainingEffReserveBalsL (latestState : AugmentedState) (preRestERBs: EffReserveBals) (postStateAccountedSuffix rest: list TxWithHdr)
  : EffReserveBals:=
  match rest with
  | [] => preRestERBs
  | hrest::tlrest =>
      let rem: Z :=
        remainingEffReserveBalOfSender latestState (preRestERBs (sender hrest)) postStateAccountedSuffix hrest in
      let erbs: EffReserveBals := updateKey preRestERBs (sender hrest) (fun _ => rem) in
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

(** Counterexample pattern: consensus can accept a tx whose [maxTxFee] is above
    the default reserve threshold (here fixed to 10), as long as the tx is
    allowed to empty and can pay its own fee. *)
Definition DefaultReserveBalCounterexample : N := 10.

Lemma consensusAcceptable_singleton_fee_above_default_counterexample :
  forall (s: AugmentedState) (tx: TxWithHdr),
    (forall addr, configuredReserveBalOfAddr s.2 addr = DefaultReserveBalCounterexample) ->
    reserveBalUpdateOfTx tx = None ->
    isAllowedToEmpty s [] tx = true ->
    maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
    value tx = 0%N ->
    maxStorageFee tx = 0%N ->
    DefaultReserveBalCounterexample < maxTxFee tx ->
    consensusAcceptableTxs s [tx].
Proof.
  intros s tx Hdefault Hrb Hallow Hfee Hvalue Hstorage _.
  unfold consensusAcceptableTxs.
  intros addr Hin.
  simpl in Hin.
  apply list_elem_of_singleton in Hin.
  subst addr.
  cbn [remainingEffReserveBalsL].
  rewrite updateKeyLkp3.
  rewrite (bool_decide_eq_true_2 (sender tx = sender tx)); [|reflexivity].
  unfold remainingEffReserveBalOfSender.
  rewrite Hrb.
  rewrite Hallow.
  assert (HfeeZ : asbool (maxTxFee tx <= balanceOfAc (s.1) (sender tx)) = true).
  { apply bool_decide_eq_true_2. exact Hfee. }
  rewrite HfeeZ.
  rewrite Hvalue.
  rewrite Hstorage.
  apply Z.min_glb.
  - apply Z.le_max_r.
  - rewrite Hdefault.
    apply N2Z.is_nonneg.
Qed.


(** * Execution Check (algo 2)

 The execution logic is also tweaked to ensure that a transaction cannot dip too much into reserves so as to not have enough fees for a transaction already included by consensus. The main complication is that some EOAs may be delegated and thus transactions sent to them can make arbitrary debits that are hard to statically estimate without actually executing the transaction. Thus, we have a dynamic check at the end of execution, to check if some EOA account (possibly other than the sender) was debited too much.
First, some helpers for that.


[isAllowedToEmptyExec] is a trivial wrapper used in execution, where there are NO intermediate transactions between the current transaction and the last known fully executed state.
 *)

Definition isAllowedToEmptyExec
  (state : AugmentedState)  (tx: TxWithHdr) : bool :=
  isAllowedToEmpty state [] tx.


(** [updateExtraState] is the execution-time maintenance of the tiny history we
    need for emptiness checks and reserve-config changes.  *)

Definition updateExtraState (a: ExtraAcStates) (tx: TxWithHdr) : ExtraAcStates :=
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
         configuredReserveBal:=
           if asbool (sender tx = addr)
           then
             match reserveBalUpdateOfTx tx with
             | Some newRb => newRb
             | None => configuredReserveBal oldes
             end
           else configuredReserveBal oldes
       |}
    ).

Open Scope N_scope.

Section EvmCore.
(** ** Abstract execution and revert

    We postulate a single-step EVM core ([evmExecTxCore]) that returns the new
    state, a transaction result (receipt), the set of changed accounts, and the
    set of accounts that executed code (including delegated
    EOAs running delegated code, and newly created-and-selfdestructed contracts).
    The revert step is for failed checks.
    For reserve-balance reasoning we also use the derived set
    [codeExecSCAccountsOfResult], which excludes delegated accounts.
    This keeps the reserve logic orthogonal to the (much larger) EVM semantics.
    For a result [r], [changedAccounts r] is the list of changed accounts, and
    [codeExecAccounts r] is the list of accounts that executed code.
 *)

Record EvmExecResult := {
  postState : StateOfAccounts;
  receipt : TxResult;
  changedAccounts : list EvmAddr;
  (** Accounts that executed code (possibly delegated EOAs). *)
  codeExecAccounts : list EvmAddr;
  }.

Variable evmExecTxCore :
  StateOfAccounts -> TxWithHdr -> EvmExecResult.
Variable revertTx : StateOfAccounts -> TxWithHdr -> (StateOfAccounts * TxResult).

Definition revertTxState (s: StateOfAccounts) (t: TxWithHdr) : StateOfAccounts :=
  (revertTx s t).1.


Definition emptyTxResult : TxResult :=
  {| gas_used := 0; gas_refund := 0; logs := [] |}.

Definition codeExecSCAccountsOfResult (r: EvmExecResult) : list EvmAddr :=
  filter (fun addr => negb (addrDelegated (postState r) addr)) (codeExecAccounts r).



(** ** Algorithm 2 (execution): execute a transaction

    Next, we define [execValidatedTx], which assumes that [t] has already been validated to ensure that the sender has
    enough balance to cover [maxTxFee]. It uses a helper [allFinalBalSufficient], which we define first.

    Execution, as defined by [execValidatedTx], proceeds as follows:

    - Special “reserve update” tx: pay fee; set new configured reserve.
    - Otherwise, run the core EVM step to obtain the *actual* post state.
    - For *changed* accounts, [allFinalBalSufficient] checks that the account was not debited too much, which may endanger the fee solvency of the later transactions already accepted by consensus.
    - If any check fails, revert the tx *and still* update the extra history
      (so K-window bookkeeping remains accurate). *)


(** The staking contract lives at 0x1000.
Its balance can decrease even if it is neither the sender, never ran code, nor is delegated.
 *)
Definition StakingContractAddr : N := 4096.

(** [allFinalBalSufficient] captures the per-account reserve-balance postcondition for
    a transaction.  *)

Definition finalBalSufficient (preTxState: AugmentedState) (postTxState : StateOfAccounts) (nonDelegatedCodeExecAccounts: list EvmAddr)
    (t: TxWithHdr) (a: EvmAddr): bool :=
  let ReserveBal := configuredReserveBalOfAddr preTxState.2 a in
  let erb:N := ReserveBal `min` (balanceOfAc preTxState.1 a) in
  if isSC postTxState a || asbool (a ∈ nonDelegatedCodeExecAccounts) || asbool (a=StakingContractAddr)
  then true
  else
    if asbool (sender t =a)
    then if isAllowedToEmptyExec preTxState t then true else asbool ((erb  - maxTxFee t) <= balanceOfAc postTxState a)
    else asbool (erb <= balanceOfAc postTxState a).

Definition allFinalBalSufficient (preTxState: AugmentedState) (postTxState : StateOfAccounts)
    (changedAccounts nonDelegatedCodeExecAccounts: list EvmAddr) (t: TxWithHdr): bool:=
  forallb (finalBalSufficient preTxState postTxState nonDelegatedCodeExecAccounts t) changedAccounts.

(** Execute a validated tx and return the post-state plus the EVM receipt. *)
Definition execValidatedTx  (s: AugmentedState) (t: TxWithHdr)
  : AugmentedState * TxResult :=
  match reserveBalUpdateOfTx t with
  | Some n =>
      ((updateBalanceOfAc s.1  (sender t) (fun b => b - maxTxFee t),
        updateExtraState s.2 t), emptyTxResult)
  | None =>
      let r := evmExecTxCore (s.1) t in
      let postTxState := postState r in
      let txr := receipt r in
      let changedAccounts := changedAccounts r in
      let codeExecSCAccounts := codeExecSCAccountsOfResult r in
      if (allFinalBalSufficient s postTxState changedAccounts codeExecSCAccounts t)
      then ((postTxState, updateExtraState s.2 t), txr)
      else
        let (revState, revRes) := revertTx s.1 t in
        ((revState, updateExtraState s.2 t), revRes)
  end.

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

Definition execCodeAccounts (s: StateOfAccounts) (tx: TxWithHdr) : list EvmAddr :=
  match reserveBalUpdateOfTx tx with
  | Some _ => []
  | None => codeExecAccounts (evmExecTxCore s tx)
  end.

Definition execCodeSCAccounts (s: StateOfAccounts) (tx: TxWithHdr) : list EvmAddr :=
  match reserveBalUpdateOfTx tx with
  | Some _ => []
  | None => codeExecSCAccountsOfResult (evmExecTxCore s tx)
  end.


(** this is a cryptographic hardness assumption: transactions cannot create contracts or run code (except when delegated) as EOAs with private keys *)
Definition txCannotCreateContractAtAddrs tx (eoasWithPrivateKey: list EvmAddr) :=
  forall s, let sf := (execValidatedTx s tx).1 in
            forall addr,  addr ∈ eoasWithPrivateKey -> isSC s.1 addr = false ->
              isSC sf.1 addr = false /\ addr ∉ execCodeSCAccounts s.1 tx.

Definition noTxnsFromStakingAddr (ltx: list TxWithHdr) : Prop :=
  forall ac, ac ∈ map sender ltx -> ac <> StakingContractAddr.

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
Lemma fullBlockStep  (latestState : AugmentedState) (firstblock restblocks: list TxWithHdr) :
  blockNumsInRange (firstblock++restblocks)
  -> consensusAcceptableTxs latestState (firstblock++restblocks)
  -> (forall txext, txext ∈ (firstblock++restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (firstblock++restblocks)))
  -> noTxnsFromStakingAddr (firstblock++restblocks)
  -> (forall ac, ac ∈ (map sender (firstblock++restblocks)) -> isSC latestState.1 ac = false)
  -> match execTxs latestState firstblock with
     | None =>  False
     | Some (si, _) =>
         consensusAcceptableTxs si restblocks
         /\ blockNumsInRange restblocks
         /\ noTxnsFromStakingAddr restblocks
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
  -> reserveBalUpdateOfTx tx = None
  -> balanceOfAc (revertTxState s tx) (sender tx)
     = balanceOfAc s (sender tx) - maxTxFee tx;

balanceOfRevertOther: forall s tx ac,
  reserveBalUpdateOfTx tx = None
  -> ac <> (sender tx)
  -> balanceOfAc (revertTxState s tx) ac
     = balanceOfAc s ac;


revertTxCoreDelegationUpd: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (revertTxState s tx) in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && asbool (ac ∉ (undels tx.1.2)))
                || asbool (ac ∈ (dels tx.1.2)));

execTxCoreDelegationUpd: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (postState (evmExecTxCore s tx)) in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && asbool (ac ∉ (undels tx.1.2)))
                || asbool (ac ∈ (dels tx.1.2)));
    
(** Sender's balance lower bound: when sender is not delegated after exec,
either it paid only fee (revert-like path) or it paid fee+value+storage.
In the non-revert case, there can be credits as well so we use [<=] instead of [=].  *)
execTxCoreBalanceSender: forall tx s,
  maxTxFee tx <= balanceOfAc s (sender tx) ->
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (postState (evmExecTxCore s tx)) in
  addrDelegated sf (sender tx) = false
   ->   balanceOfAc s (sender tx) - ( maxTxFee tx + value tx + maxStorageFee tx) <= balanceOfAc sf (sender tx)
        \/  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - (maxTxFee tx);


(** balance lower bounds for non-senders.
One caveat in the assumption below is that it assumes that the account [ac] does not receive so much credit that it overflows 2^256. In practice, this should never happen, assuming the ETH supply is well below 2^256. Thus, we can assume that [evmExecTxCore] caps the balance at [2^256] should it overflow, instead of wrapping around, which may violate this assumption. *)
execTxCoreBalanceNonSender: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let result := evmExecTxCore s tx in
  let sf := postState result in
  let execAccounts := codeExecSCAccountsOfResult result in
  forall (ac: EvmAddr), ac <> sender tx
              -> (addrDelegated sf ac || isSC sf ac || asbool (ac ∈ execAccounts) || asbool (ac=StakingContractAddr)) = false
              ->  balanceOfAc s ac <= balanceOfAc sf ac;


changedAccountSetSound: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let r := (evmExecTxCore s tx) in
  let sf := postState r in
  let changedAccounts := changedAccounts r in
  (forall ac, ac ∉ changedAccounts -> sf ac = s ac);
}.

(** ** lemmas about execution
 *)

(* begin hide *)
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
Lemma execTxCoreDelegationUpdImpl tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (postState (evmExecTxCore s tx)) in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || asbool (ac ∈ (addrsDelUndelByTx tx))).
Proof using eas.
  simpl.
  intros ? ?.
  rewrite execTxCoreDelegationUpd; auto.
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

Lemma revertTxCoreDelegationUpdImpl tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (revertTxState s tx) in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || asbool (ac ∈ (addrsDelUndelByTx tx))).
Proof using eas.
  simpl.
  intros ? ?.
  rewrite revertTxCoreDelegationUpd;auto.
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
Proof using eas.
  unfold updateBalanceOfAc, updateKey, balanceOfAc. simpl.
  case_bool_decide; simpl; subst; auto; resdec ltac:(congruence);[].
  destruct (s ac); auto.
Qed.

Lemma execTxOtherBalanceLB tx s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let sf := (execValidatedTx s tx).1 in
  (forall ac,
      let ReserveBal := configuredReserveBalOfAddr s.2 ac in
      (ac <> sender tx)
       -> if (isSC sf.1 ac)
          then True
          else if (asbool (ac ∈ execCodeSCAccounts s.1 tx))
               then True
               else if (asbool (ac = StakingContractAddr))
                    then True
                    else ReserveBal `min` (balanceOfAcA s ac) <= (balanceOfAcA sf ac)).
Proof using eas.
  intros.
  subst ReserveBal.
  unfold execValidatedTx in *.
  unfold allFinalBalSufficient in *.
  unfold finalBalSufficient in *.
  simpl in *.

  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *.
  1:{
      subst sf. unfold balanceOfAcA. simpl.
      assert (HexecEmpty : execCodeSCAccounts s.1 tx = []).
      { unfold execCodeSCAccounts. rewrite <- Heqrb. reflexivity. }
      rewrite HexecEmpty. simpl.
      rewrite balanceOfUpd.
      destruct (decide (sender tx = ac)) as [Hsac|Hsac].
      { exfalso. auto. }
      rewrite (bool_decide_eq_false_2 (sender tx = ac)); [|exact Hsac].
      destruct (isSC (updateBalanceOfAc s.1 (sender tx) (fun b => b - maxTxFee tx)) ac); [exact I|].
      destruct (decide (ac = StakingContractAddr)) as [Hstake|Hstake].
      { subst ac. rewrite bool_decide_true; [exact I|reflexivity]. }
      rewrite (bool_decide_eq_false_2 (ac = StakingContractAddr)); [|exact Hstake].
      lia.
  }
  pose proof (changedAccountSetSound tx s.1 ltac:(auto)) as Hsnd.
  rdestruct (evmExecTxCore s.1 tx) as [si si_res changed rawExecAccounts].
  set (execAccounts := filter (fun addr => negb (addrDelegated si addr)) rawExecAccounts).
  assert (Hexec : execCodeSCAccounts s.1 tx = execAccounts).
  { unfold execCodeSCAccounts. rewrite <- Heqrb. simpl. rewrite <- Heqrd.
    unfold codeExecSCAccountsOfResult. simpl. unfold execAccounts. reflexivity. }
  rewrite Hexec.
  remember (isSC sf.1 ac) as sac.
  destruct sac; auto.
  destruct (decide (ac ∈ execAccounts)) as [Hin|Hnin].
  {
    simpl.
    rewrite (bool_decide_eq_true_2 (ac ∈ execAccounts)); [exact I|exact Hin].
  }
  destruct (decide (ac = StakingContractAddr)) as [Hstake|Hstake].
  {
    subst ac. simpl.
    rewrite (bool_decide_eq_false_2 (StakingContractAddr ∈ execAccounts)); [|exact Hnin].
    destruct (isSC sf.1 StakingContractAddr); exact I.
  }
  assert (Hsbool : asbool (ac = StakingContractAddr) = false).
  { apply bool_decide_eq_false_2. exact Hstake. }
  rememberForallb.
  unfold balanceOfAcA in *.
  destruct fb; simpl in *.
  2:{ subst sf.
      destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
      pose proof (balanceOfRevertOther s.1 tx ac ltac:(auto) ltac:(auto)) as Hrevbal.
      unfold revertTxState in Hrevbal.
      rewrite Hrev in Hrevbal. simpl in Hrevbal.
      rewrite <- Hrevbal.
      resolveDecide congruence.
      lia.
  }
  symmetry in Heqfb.
  rewrite  forallb_spec in Heqfb.
  destruct (decide (ac ∈ changed)).
  {
    specialize (Heqfb ac ltac:(auto)).
    rewrite <- Heqsac in Heqfb.
    rewrite (bool_decide_eq_false_2 (ac ∈ execAccounts)) in Heqfb; [|exact Hnin].
    rewrite Hsbool in Heqfb.
    rewrite (bool_decide_eq_false_2 (sender tx = ac)) in Heqfb; [|congruence].
    simpl in Heqfb.
    autorewrite with iff in Heqfb.
    rewrite (bool_decide_eq_false_2 (ac ∈ execAccounts)); [|exact Hnin].
    rewrite Hsbool.
    exact Heqfb.
  }
  {
    unfold balanceOfAc.
    rewrite Hsnd; auto.
    rewrite (bool_decide_eq_false_2 (ac ∈ execAccounts)); [|exact Hnin].
    rewrite Hsbool.
    lia.
  }

Qed.


Lemma execTxSenderBal tx s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  sender tx ∉ execCodeSCAccounts s.1 tx ->
  sender tx <> StakingContractAddr ->
  let ReserveBal := configuredReserveBalOfAddr s.2 (sender tx) in
  let sf := (execValidatedTx s tx).1 in
  isSC sf.1 (sender tx) = false->
  (if isAllowedToEmpty s [] tx
   then balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx + maxStorageFee tx) <= balanceOfAcA sf (sender tx)
        \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
  else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx))).
Proof using eas.
  intros Hfee Hnoexec Hnostaking ? ? Hsc.
  subst ReserveBal.
  pose proof (execTxCoreBalanceSender tx s.1) as Hc.
  simpl in Hc.
  unfold isAllowedToEmpty.
  subst sf.
  revert Hsc.
  unfold execValidatedTx.
  unfold allFinalBalSufficient in *.
  unfold finalBalSufficient in *.
  remember ((reserveBalUpdateOfTx tx)) as rb.
  destruct rb; simpl in *.
  1:{  unfold balanceOfAcA. simpl in *.  intros.
       repeat rewrite balanceOfUpd.
       resolveDecide congruence.
       case_match_concl; auto; try lia.
  }
  specialize (Hc ltac:(auto)).
  pose proof (changedAccountSetSound tx s.1 ltac:(auto)) as Hsnd.
  pose proof (execTxCoreDelegationUpd tx s.1 ltac:(auto) (sender tx) ) as Hsf.
  rdestruct (evmExecTxCore s.1 tx) as [si si_res changed rawExecAccounts].
  set (execAccounts := filter (fun addr => negb (addrDelegated si addr)) rawExecAccounts).
  assert (Hexec : execCodeSCAccounts s.1 tx = execAccounts).
  { unfold execCodeSCAccounts. rewrite <- Heqrb. simpl. rewrite <- Heqrd.
    unfold codeExecSCAccountsOfResult. simpl. unfold execAccounts. reflexivity. }
  assert (Hnoexec' : sender tx ∉ execAccounts).
  { rewrite <- Hexec. exact Hnoexec. }
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
      pose proof (balanceOfRevertSender s.1 tx ltac:(auto) ltac:(auto)) as Hrevbal.
      unfold revertTxState in Hrevbal.
      rewrite Hrev in Hrevbal. simpl in Hrevbal.
      rewrite Hrevbal.
      resolveDecide congruence. lia.
    }
    symmetry in Heqfb.
    rewrite  forallb_spec in Heqfb.
    destruct (decide (sender tx ∈ changed));
      [| unfold balanceOfAc; simpl; rewrite Hsnd; auto; lia].
    specialize (Heqfb (sender tx) ltac:(auto)).
    resolveDecide congruence.
    simpl in *.
    rewrite -> Hsc in Heqfb.
    destruct (asbool (sender tx ∈ execAccounts)) eqn:Hexecb.
    { apply bool_decide_eq_true_1 in Hexecb. exfalso. exact (Hnoexec' Hexecb). }
    destruct (asbool (sender tx = StakingContractAddr)) eqn:Hstakeb.
    { apply bool_decide_eq_true_1 in Hstakeb. exfalso. exact (Hnostaking Hstakeb). }
    try rewrite Hexecb in Heqfb.
    try rewrite Hstakeb in Heqfb.
    simpl in Heqfb.
    autorewrite with iff in Heqfb.
    lia.
  }
  {
    autorewrite with syntactic in *.
    rewrite Hsf in Hc.
      rememberForallb.
    specialize (Hc ltac:(auto)).
    remember (~~ (existsDelUndelTxWithinK s tx || asbool (sender tx ∈ addrsDelUndelByTx tx)) && ~~ existsTxWithinK s tx) as rd1; destruct rd1;
      simpl in *.
    {
      symmetry in Heqrd1.
      
      autorewrite with iff in *.
      unfold addrsDelUndelByTx in Heqrd1.
      forward_reason.
      specialize (Hc ltac:(set_solver)).
      destruct fb; simpl in *.
      - exact Hc.
      - auto; try lia.
        destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
        pose proof (balanceOfRevertSender s.1 tx ltac:(auto) ltac:(auto)) as Hrevbal.
        unfold revertTxState in Hrevbal.
        rewrite Hrev in Hrevbal. simpl in Hrevbal.
        rewrite Hrevbal; auto.
    }
    {
      destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
      pose proof (balanceOfRevertSender s.1 tx ltac:(auto) ltac:(auto)) as Hrevbal.
      unfold revertTxState in Hrevbal.
      rewrite Hrev in Hrevbal. simpl in Hrevbal.
      destruct fb; simpl in *; orient_rwHyps; simpl in *;
        try (rewrite Hrevbal;[]);
        try resolveDecide congruence; try auto;
        try lia;[].
      rewrite  forallb_spec in Heqfb.
      destruct (decide (sender tx ∈ changed)).
      {
        specialize (Heqfb (sender tx) ltac:(auto)).
        rewrite Hsc in Heqfb.
        destruct (asbool (sender tx ∈ execAccounts)) eqn:Hexecb.
        { apply bool_decide_eq_true_1 in Hexecb. exfalso. exact (Hnoexec' Hexecb). }
        destruct (asbool (sender tx = StakingContractAddr)) eqn:Hstakeb.
        { apply bool_decide_eq_true_1 in Hstakeb. exfalso. exact (Hnostaking Hstakeb). }
        try rewrite Hexecb in Heqfb.
        try rewrite Hstakeb in Heqfb.
        resolveDecide congruence.
        simpl in *.
        simpl in Heqfb.
        autorewrite with iff in Heqfb.
        lia.
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
Proof using eas.
  intros ? ? Hd.
  subst sf.
  unfold execValidatedTx in Hd.
  simpl in *.
  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *.
  1:{  unfold balanceOfAcA. simpl in *.  intros.
       repeat rewrite addrDelegatedUnchangedByBalUpd in Hd.
       auto.
  }
  rewrite pairEta in Hd.
  destruct (evmExecTxCore s.1 tx) as [postTxState postTxRes changed execAccounts] eqn:Hcore.
  simpl in *.
  case_match.
  {
    pose proof (execTxCoreDelegationUpdImpl tx s.1 ltac:(auto)) as HcoreImpl.
    (* inline evmExecCorePostState after rewrite *)
    rewrite Hcore in HcoreImpl.
    simpl in HcoreImpl.
    apply HcoreImpl in Hd; auto.
  }
  {
    destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in Hd.
    pose proof (revertTxCoreDelegationUpdImpl tx s.1 ltac:(auto)) as HrevImpl.
    unfold revertTxState in HrevImpl.
    rewrite Hrev in HrevImpl. simpl in HrevImpl.
    apply HrevImpl in Hd; auto.
  }
Qed.


Lemma execTxCannotDebitNonDelegatedNonContractAccounts tx s:
  let sf := (execValidatedTx s tx).1 in
  (forall ac, ac <> sender tx
              -> if (addrDelegated (sf.1) ac || isSC (sf.1) ac
                     || asbool (ac ∈ execCodeSCAccounts s.1 tx)
                     || asbool (ac = StakingContractAddr))
                 then True
                 else balanceOfAcA s ac <= balanceOfAcA sf ac).
Proof using eas.
  intros sf ac Hneq. subst sf.
  pose proof (fun p => execTxCoreBalanceNonSender tx s.1 p ac ltac:(auto)) as Htx.
  unfold execValidatedTx.
  simpl in *.
  case_match_concl;  auto;[].
  unfold balanceOfAcA in *.
  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *.
  - simpl in *.
    rewrite balanceOfUpd.
    destruct (decide (sender tx = ac)) as [Heq|Hneq']; [subst; exfalso; apply Hneq; reflexivity|].
    simpl.
    assert (Hfalse : asbool (sender tx = ac) = false).
    { apply bool_decide_eq_false_2. exact Hneq'. }
    rewrite Hfalse.
    lia.
  - specialize (Htx ltac:(auto)).
  destruct (evmExecTxCore s.1 tx) as [postTxState postTxRes changed rawExecAccounts] eqn:Hcore.
    simpl in *.
    destruct
      (allFinalBalSufficient s postTxState changed
         (codeExecSCAccountsOfResult
            {| postState := postTxState;
               receipt := postTxRes;
               changedAccounts := changed;
               codeExecAccounts := rawExecAccounts |}) tx) eqn:Hfb;
      simpl in *.
    + apply Htx.
      unfold execCodeSCAccounts in Heqb.
      rewrite <- Heqrb in Heqb.
      simpl in Heqb.
      rewrite Hcore in Heqb. simpl in Heqb.
      exact Heqb.
    + destruct (revertTx s.1 tx) as [revState revRes] eqn:Hrev; simpl in *.
      pose proof (balanceOfRevertOther s.1 tx ac ltac:(auto) ltac:(auto)) as Hrevbal.
      unfold revertTxState in Hrevbal.
      rewrite Hrev in Hrevbal. simpl in Hrevbal.
      rewrite Hrevbal; auto.
Qed.

Lemma execS2 s txlast:
  (execValidatedTx s txlast).1.2 = updateExtraState s.2 txlast.
Proof using eas.
  unfold execValidatedTx.
  destruct (reserveBalUpdateOfTx txlast) as [n|]; simpl; auto.
  destruct (evmExecTxCore s.1 txlast) as [postTxState postTxRes changed rawExecAccounts] eqn:Hcore.
  simpl.
  destruct
    (allFinalBalSufficient s postTxState changed
       (codeExecSCAccountsOfResult
          {| postState := postTxState;
             receipt := postTxRes;
             changedAccounts := changed;
             codeExecAccounts := rawExecAccounts |}) txlast);
    simpl; auto.
  destruct (revertTx s.1 txlast) as [revState revRes] eqn:Hrev; simpl; auto.
Qed.


Lemma lastTxInBlockIndexUpd s txlast:
  lastTxInBlockIndex ((execValidatedTx s txlast).1.2 (sender txlast))
  = Some (txBlockNum txlast).
Proof using eas evmExecTxCore revertTx.
  rewrite execS2.
  unfold updateExtraState.
  simpl.
  resdec congruence.
Qed.

Lemma otherTxLstSenderLkp s addr txlast :
  addr <> sender txlast
  ->
    lastTxInBlockIndex ((execValidatedTx s txlast).1.2 addr)
    = lastTxInBlockIndex (s.2 addr).
Proof using eas.
  rewrite execS2.
  unfold updateExtraState.
  simpl. intros.
  resdec congruence.
Qed.


Lemma delgUndelgUpdTx txlast s addr:
  addr ∈  addrsDelUndelByTx txlast
  -> lastDelUndelInBlockIndex ((execValidatedTx s txlast).1.2 addr) = Some (txBlockNum txlast).
Proof using eas evmExecTxCore revertTx.
  rewrite execS2.
  unfold updateExtraState.
  simpl. intros.
  resdec congruence.
Qed.

Lemma otherDelUndelLkp s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    lastDelUndelInBlockIndex ((execValidatedTx s txlast).1.2 addr)
    = lastDelUndelInBlockIndex (s.2  addr).
Proof using eas.
  rewrite execS2.
  unfold updateExtraState.
  simpl. intros.
  resdec congruence.
Qed.

Lemma otherDelUndelDelegationStatusUnchanged s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    addrDelegated ((execValidatedTx s txlast).1.1) addr
    = addrDelegated s.1 addr.
  Proof using eas.
  intros Hn.
  unfold execValidatedTx.
  case_match; auto.
  {
    simpl.
    rewrite addrDelegatedUnchangedByBalUpd. reflexivity.
  }
  rewrite pairEta. simpl in *.
  destruct (evmExecTxCore s.1 txlast) as [postTxState postTxRes changed execAccounts] eqn:Hcore.
  simpl in *.
  case_match;
    simpl in *.
  2:{
    destruct (revertTx s.1 txlast) as [revState revRes] eqn:Hrev; simpl in *.
    pose proof (revertTxCoreDelegationUpd txlast s.1 ltac:(auto)) as HrevCore.
    unfold revertTxState in HrevCore.
    rewrite Hrev in HrevCore. simpl in HrevCore.
    rewrite HrevCore; auto;[].
    unfold addrsDelUndelByTx in *.
    (*
    resdec ltac:(set_solver). *)
    rewrite bool_decide_true;[| set_solver].
    rewrite bool_decide_false;[|set_solver].
    autorewrite with syntactic.
    reflexivity.
  }
  {
    pose proof (execTxCoreDelegationUpd txlast s.1 ltac:(auto )addr) as Hd.
    (* inline evmExecCorePostState after rewrite *)
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
Proof using eas.
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


Lemma emptyBalanceUb s tx inter a:
  isSC ((execValidatedTx s tx).1.1) (sender a) = false
  -> isAllowedToEmpty s (tx :: inter) a = true
  -> sender a ∉ execCodeSCAccounts s.1 tx
  -> sender a <> StakingContractAddr
  -> balanceOfAc s.1 (sender a) ≤ balanceOfAc ((execValidatedTx s tx).1.1) (sender a).
Proof using eas.
  intros Hsc Hae Hnoexec Hnostaking.
  pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s (sender a)) as Hs.
  simpl in Hs.
  apply isAllowedToEmptyImpl in Hae; auto.
  forward_reason.
  rewrite Haer in Hs.
  simpl in *.
  rewrite Hsc in Hs.
  rewrite (bool_decide_eq_false_2 (sender a ∈ execCodeSCAccounts s.1 tx)) in Hs; [|exact Hnoexec].
  rewrite (bool_decide_eq_false_2 (sender a = StakingContractAddr)) in Hs; [|exact Hnostaking].
  unfold balanceOfAcA in *.
  simpl in *.
  lia.
Qed.

Definition rbAfterTx s tx :=
  match reserveBalUpdateOfTx tx with
  | Some rb => rb
  | None => configuredReserveBalOfAddr s (sender tx)
  end.


Lemma configuredReserveBalOfAddrSpec s tx a:
  configuredReserveBalOfAddr ((execValidatedTx s tx).1.2) a
  = if asbool (a=sender tx)
    then rbAfterTx s.2 tx
    else configuredReserveBalOfAddr s.2 a.
Proof using eas.
  unfold configuredReserveBalOfAddr.
  rewrite execS2.
  unfold updateExtraState.
  simpl. intros.
  unfold rbAfterTx.
  resdec solver.
  case_bool_decide;  resdec congruence; subst; auto.
Qed.

Lemma configuredReserveBalOfAddrSame s tx  a:
  sender tx <> a
  -> (configuredReserveBalOfAddr ((execValidatedTx s tx).1.2) a
      =
        configuredReserveBalOfAddr s.2 a).
Proof using eas.
  intros Hn.
  rewrite configuredReserveBalOfAddrSpec.
  case_bool_decide; try congruence.
Qed.

Lemma configuredReserveBalOfAddrSame2 s tx inter a:
  isAllowedToEmpty s (tx :: inter) a = true
  -> (configuredReserveBalOfAddr ((execValidatedTx s tx).1.2) (sender a)
      =
        configuredReserveBalOfAddr s.2 (sender a)).
Proof using eas.
  intros Hae.
  apply configuredReserveBalOfAddrSame.
  apply isAllowedToEmptyImpl in Hae; auto.
  tauto.
Qed.


Lemma isSCFalsePresExec l s tx:
  (forall txext, txext ∈ (tx::l) ->  txCannotCreateContractAtAddrs txext (map sender (tx::l)))
  -> (forall ac, ac ∈ (map sender (tx::l)) -> isSC s.1 ac = false)
  -> (forall ac, ac ∈ (map sender (tx::l)) -> isSC ((execValidatedTx s tx).1.1) ac = false).
Proof using eas.
  intros Heoac Hsc.
  intros.
  pose proof (Hsc ac ltac:(set_solver)).
  specialize (Heoac tx ltac:(set_solver) s ac ltac:(set_solver) ltac:(assumption)).
  forward_reason; auto.
Qed.


Lemma initResBal s addr:
  (initialEffReserveBals s)  addr =
    (balanceOfAcA s addr `min` configuredReserveBalOfAddr s.2 addr)%Z.
Proof.
  reflexivity.
Qed.


(* end hide *)

(** This lemma combines the axioms above to build a
    lower bound of the balance of any account after executing a transaction.
*)
Lemma execBalLb ac s tx:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  sender tx ∉ execCodeSCAccounts s.1 tx ->
  sender tx <> StakingContractAddr ->
  let sf := (execValidatedTx s tx).1 in
  let ReserveBal := configuredReserveBalOfAddr s.2 ac in
  if (asbool (ac=sender tx)) then
    isSC sf.1 (sender tx) = false->
    (if isAllowedToEmpty s [] tx
     then balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx + maxStorageFee tx) <= balanceOfAcA sf (sender tx)
          \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
     else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx)))
  else
    if (isSC sf.1 ac)
    then True
    else if (asbool (ac ∈ execCodeSCAccounts s.1 tx))
         then True
         else if (asbool (ac = StakingContractAddr))
              then True
              else (if addrDelegated (sf.1) ac then ReserveBal `min` (balanceOfAcA s ac) else balanceOfAcA s ac)
                   <= (balanceOfAcA sf ac).
Proof using eas.
  simpl. intros.
  case_bool_decide.
  - subst. apply execTxSenderBal; auto.
  - pose proof (execTxOtherBalanceLB tx s ltac:(auto) ac ltac:(auto)) as Hother.
    pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s ac ltac:(auto)) as Hnodebit.
    destruct (isSC ((execValidatedTx s tx).1.1) ac) eqn:Hsc; auto.
    destruct (decide (ac ∈ execCodeSCAccounts s.1 tx)) as [Hin|Hnin].
    + simpl.
      assert (Htrue : asbool (ac ∈ execCodeSCAccounts s.1 tx) = true).
      { apply bool_decide_eq_true_2. exact Hin. }
      rewrite Htrue. exact I.
    + simpl.
      autorewrite with syntactic in *.
      destruct (decide (ac = StakingContractAddr)) as [Hstake|Hstake].
      * subst ac. simpl. exact I.
      * assert (Hsbool : asbool (ac = StakingContractAddr) = false).
        { apply bool_decide_eq_false_2. exact Hstake. }
        rewrite Hsbool.
        rewrite Hsbool in Hother.
        rewrite Hsbool in Hnodebit.
        destruct (addrDelegated ((execValidatedTx s tx).1.1) ac) eqn:Hdel.
        -- exact Hother.
        -- exact Hnodebit.
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
Proof using eas.
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

Hint Rewrite @updateKeyLkp3 : syntactic.

Definition rbLe (eoas: list EvmAddr) (rb1 rb2: EffReserveBals) :=
  forall addr, addr ∈ eoas -> rb1 addr <= rb2 addr.

(** ** lemmas about [remainingEffReserveBalOfSender]

    [remainingEffReserveBalOfSender] is monotone. proof is straightforward by analyzing cases
    and using Coq's arith automation [lia].
*)

Lemma mono  s rb1 rb2 inter tx:
  rb1 <= rb2
  -> (remainingEffReserveBalOfSender s rb1 inter tx) <= (remainingEffReserveBalOfSender s rb2 inter tx).
Proof using.
  intros Hrb.
  unfold remainingEffReserveBalOfSender.
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  {
      case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
        fold EffReserveBals in *; try lia.
  }
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  {case_bool_decide; subst; try lia. }
  lia.
Qed.

(** In the proof of the main correctness theorem, we use a slightly different
variant of monotonicity, where in the RHS of [<=], remainingEffReserveBalOfSender starts
from the final state after executing [tx] from [s] and as a result, [tx]
is dropped from the list of intermediate transactions between the state
and the candidate transaction [txc].
The proof follows from the definition of [remainingEffReserveBalOfSender]
and the execution lemmas above.
*)
Lemma mono2 tx txc s (eoas: list EvmAddr) rb1 rb2 inter:
  (∀ ac : EvmAddr, ac ∈ eoas -> isSC s.1 ac = false)
  -> txCannotCreateContractAtAddrs tx eoas
  -> (∀ ac : EvmAddr, ac ∈ eoas -> ac <> StakingContractAddr)
  -> (rb1 ≤ rb2)
  -> txBlockNum txc - (K-1) ≤ txBlockNum tx  ≤ txBlockNum txc
  -> sender txc ∈ eoas
  -> ∀ addr : EvmAddr,
      addr ∈ eoas
      -> remainingEffReserveBalOfSender s rb1 (tx :: inter) txc
          <= remainingEffReserveBalOfSender ((execValidatedTx s tx).1) rb2 inter txc.
Proof using eas.
  intros HscPre Hnoexec HnostakePre Hrb Hrangel Hsender.
  intros addr Hin.
  simpl.
  unfold remainingEffReserveBalOfSender.
  rewrite <- execPreservesIsAllowedToEmpty; try lia.
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  {
    remember (isAllowedToEmpty s (tx :: inter) txc) as ia.
    destruct ia; simpl;
      repeat rewrite updateKeyLkp3; try lia.
    specialize (HscPre (sender txc) Hsender).
    pose proof (HnostakePre (sender txc) Hsender) as Hnostaking.
    pose proof (Hnoexec s (sender txc) Hsender HscPre) as Hnoexec_tx.
    destruct Hnoexec_tx as [Hsc_post Hnoexec_addr].
    symmetry in Heqia.
    pose proof (emptyBalanceUb _ _ _ _ Hsc_post Heqia Hnoexec_addr Hnostaking) as Hle.
    lia.
  }
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *;[| lia].
  specialize (HscPre (sender txc) Hsender).
  pose proof (HnostakePre (sender txc) Hsender) as Hnostaking.
  pose proof (Hnoexec s (sender txc) Hsender HscPre) as Hnoexec_tx.
  destruct Hnoexec_tx as [Hsc_post Hnoexec_addr].
  pose proof (emptyBalanceUb _ _ _ _ Hsc_post Heqb Hnoexec_addr Hnostaking) as Hle.
  case_bool_decide.
  {
    rewrite bool_decide_true; [|lia].
    repeat rewrite updateKeyLkp3;
      fold EffReserveBals in *; try lia.
    pose proof (configuredReserveBalOfAddrSame2 _ _ _ _ Heqb) as Hlle.
    rewrite Hlle.
    lia.
  }
  case_bool_decide;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *; lia.
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
Proof using.
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
  -> (∀ ac : EvmAddr, ac ∈ eoas → isSC s.1 ac = false)
  -> txCannotCreateContractAtAddrs tx eoas
  -> (∀ ac : EvmAddr, ac ∈ eoas -> ac <> StakingContractAddr)
  -> rbLe eoas (remainingEffReserveBalsL s rb1 (tx::inter) extension)
          (remainingEffReserveBalsL ((execValidatedTx s tx).1) rb2 inter extension).
Proof using eas.
  revert rb1 rb2 inter.
  induction extension as [|a extension IH]; intros rb1 rb2 inter Hsub Hrb Hrange HscPre Hnoexec HnostakePre addr Hin; simpl in *.
  - unfold rbLe in *.
    apply Hrb. exact Hin.
  - unfold rbLe in *.
    apply forallCons in Hrange as [Hrange_head Hrange_tail].
    apply IH.
    + set_solver.
    + clear Hin addr.
      intros.
      repeat rewrite updateKeyLkp3.
      destruct (decide (addr = sender a)) as [H0|Hneq].
      * assert (Htrue : asbool (addr = sender a) = true).
        { apply bool_decide_eq_true_2. exact H0. }
        rewrite Htrue.
        eapply mono2; [exact HscPre | exact Hnoexec | exact HnostakePre | | exact Hrange_head | | exact H].
        { apply Hrb. rewrite <- H0. exact H. }
        { apply Hsub. simpl. set_solver. }
      * assert (Hfalse : asbool (addr = sender a) = false).
        { apply bool_decide_eq_false_2. exact Hneq. }
        rewrite Hfalse.
        apply Hrb; assumption.
    + exact Hrange_tail.
    + intros. apply HscPre. set_solver.
    + exact Hnoexec.
    + exact HnostakePre.
    + exact Hin.
Qed.


Hint Rewrite initResBal configuredReserveBalOfAddrSpec: syntactic.

(** This lemma captures a key property of [remainingEffReserveBalOfSender]: it underapproximates
the resultant effective balance after execution of the transaction.
This is the heart of the proof of the top-level correctness theorem [fullBlockStep].
Proof follows by unfolding definitions and case analysis. uses [mono2], [execBalLb], and many other lemmas above
*)
Lemma exec1 tx extension s :
  let remf  := remainingEffReserveBalOfSender s (initialEffReserveBals s (sender tx)) [] tx in
  let remRbsf := updateKey (initialEffReserveBals s) (sender tx) (fun _ => remf) in
  let sf := (execValidatedTx s tx).1 in
  maxTxFee tx <= balanceOfAc s.1 (sender tx)
  -> (∀ ac : EvmAddr, ac ∈ sender tx :: map sender extension → isSC sf.1 ac = false)
  -> (∀ ac : EvmAddr, ac ∈ sender tx :: map sender extension
                      → ac ∉ execCodeSCAccounts s.1 tx /\ ac <> StakingContractAddr)
     -> (∀ addr : EvmAddr,
            addr ∈ sender tx :: map sender extension
            -> remRbsf addr
              ≤ initialEffReserveBals sf addr).
Proof using eas.
  simpl.
  intros Hfee  Hscf Hacc.
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
  case_match_concl.
  { (* isAllowedToEmpty *)
    match goal with
    | H: isAllowedToEmpty _ _ _ = _ |- _ => rename H into Hae
    end.
    autorewrite with syntactic in *.
      unfold balanceOfAcA, rbAfterTx in *.
      rwHyps.
      destruct (decide (addr = sender tx)) as [Hsender|Hneq].
      - subst addr.
        assert (Hsender_in : sender tx ∈ sender tx :: map sender extension).
        { apply elem_of_cons. left. reflexivity. }
        pose proof (Hacc (sender tx) Hsender_in) as Hsender_safe.
        pose proof (execBalLb (sender tx) s tx ltac:(lia)
                      (proj1 Hsender_safe) (proj2 Hsender_safe)) as Hlb.
        simpl in Hlb.
        pose proof (Hscf (sender tx) Hsender_in) as Hsc_sender.
        rewrite Hsc_sender in Hlb.
        rewrite Hae in Hlb.
        rewrite (bool_decide_eq_true_2 (sender tx = sender tx)) in Hlb; [|reflexivity].
        rewrite (bool_decide_eq_true_2 (sender tx = sender tx)); [|reflexivity].
        specialize (Hlb ltac:(auto)).
        destruct Hlb as [Hstorage|Hrevert].
        { rewrite (bool_decide_eq_true_2 (maxTxFee tx <= balanceOfAc s.1 (sender tx))); [|exact Hfee].
          apply Z.min_le_compat_r.
          set (sbal := balanceOfAc s.1 (sender tx)) in *.
          set (sfbal := balanceOfAc (execValidatedTx s tx).1.1 (sender tx)) in *.
          set (feesN := (maxTxFee tx + value tx + maxStorageFee tx)%N) in *.
          pose proof (proj1 (N2Z.inj_le _ _) Hstorage) as HstorageZ.
          assert (Hfees :
            Z.of_N feesN =
              Z.of_N (maxTxFee tx) + Z.of_N (value tx) + Z.of_N (maxStorageFee tx)).
          { unfold feesN. repeat rewrite N2Z.inj_add. lia. }
          replace (Z.of_N sbal - Z.of_N (maxTxFee tx) - Z.of_N (value tx) - Z.of_N (maxStorageFee tx))
             with (Z.of_N sbal - Z.of_N feesN) by (rewrite Hfees; lia).
          rewrite Z.max_comm.
          rewrite <- N2Z.inj_sub_max.
          exact HstorageZ. }
        { rewrite (bool_decide_eq_true_2 (maxTxFee tx <= balanceOfAc s.1 (sender tx))); [|exact Hfee].
          unfold balanceOfAcA in Hrevert.
          rewrite Hrevert.
          apply Z.min_le_compat_r.
          set (sbal := balanceOfAc s.1 (sender tx)) in *.
          set (sfbal := balanceOfAc (execValidatedTx s tx).1.1 (sender tx)) in *.
          apply Z.max_lub.
          - lia.
          - pose proof Hfee as HfeeZ.
            lia. }
      - assert (Hsender_in : sender tx ∈ sender tx :: map sender extension).
        { apply elem_of_cons. left. reflexivity. }
        pose proof (Hacc (sender tx) Hsender_in) as Hsender_safe.
        pose proof (execBalLb addr s tx ltac:(lia)
                      (proj1 Hsender_safe) (proj2 Hsender_safe)) as Hlb.
        simpl in Hlb.
        assert (Haddr_in : addr ∈ sender tx :: map sender extension).
        { apply elem_of_cons. exact Hin. }
        pose proof (Hscf addr Haddr_in) as Hsc_addr.
        rewrite Hsc_addr in Hlb.
        rewrite (bool_decide_eq_false_2 (addr = sender tx)) in Hlb; [|exact Hneq].
        rewrite (bool_decide_eq_false_2 (addr = sender tx)); [|exact Hneq].
        rewrite (bool_decide_eq_false_2 (addr ∈ execCodeSCAccounts s.1 tx)) in Hlb;
          [|exact (proj1 (Hacc _ Haddr_in))].
        rewrite (bool_decide_eq_false_2 (addr = StakingContractAddr)) in Hlb;
          [|exact (proj2 (Hacc _ Haddr_in))].
        destruct (addrDelegated (execValidatedTx s tx).1.1 addr) eqn:Hdel.
        + simpl in Hlb.
          pose proof
            (proj1 (N2Z.inj_le
                      (configuredReserveBalOfAddr s.2 addr `min` balanceOfAcA s addr)
                      (balanceOfAcA (execValidatedTx s tx).1 addr)) Hlb) as HlbZ.
          rewrite N2Z.inj_min in HlbZ.
          apply Z.min_glb.
          * rewrite Z.min_comm. exact HlbZ.
          * apply Z.le_min_r.
        + simpl in Hlb.
          pose proof
            (proj1 (N2Z.inj_le
                      (balanceOfAcA s addr)
                      (balanceOfAcA (execValidatedTx s tx).1 addr)) Hlb) as HlbZ.
          apply Z.min_le_compat_r.
          exact HlbZ.
  }
  rewrite updateKeyLkp3.
  autorewrite with syntactic in *.
  unfold balanceOfAcA, rbAfterTx in *.
  rwHyps.
  case_bool_decide; subst; resolveDecide congruence; try lia.
- assert (Hsender_in : sender tx ∈ sender tx :: map sender extension).
    { apply elem_of_cons. left. reflexivity. }
    pose proof (Hacc (sender tx) Hsender_in) as Hsender_safe.
    pose proof (execBalLb (sender tx) s tx ltac:(lia)
                  (proj1 Hsender_safe) (proj2 Hsender_safe)) as Hlb.
    simpl in Hlb.
    pose proof (Hscf (sender tx) Hsender_in) as Hsc_sender.
    rewrite Hsc_sender in Hlb.
    rewrite Heqb in Hlb.
    rewrite (bool_decide_eq_true_2 (sender tx = sender tx)) in Hlb; [|reflexivity].
    specialize (Hlb ltac:(auto)).
    pose proof
      (proj1 (N2Z.inj_le
                (configuredReserveBalOfAddr s.2 (sender tx) `min` balanceOfAcA s (sender tx) - maxTxFee tx)
                (balanceOfAcA (execValidatedTx s tx).1 (sender tx))) Hlb) as HlbZ.
    rewrite N2Z.inj_sub_max in HlbZ.
    rewrite N2Z.inj_min in HlbZ.
    rewrite Z.min_comm in HlbZ.
    apply Z.min_glb.
    + eapply Z.le_trans.
      * apply Z.le_max_r.
      * exact HlbZ.
    + apply (Z.le_trans _ (Z.min (balanceOfAc s.1 (sender tx))
                                  (configuredReserveBalOfAddr s.2 (sender tx)))).
      * pose proof (N2Z.is_nonneg (maxTxFee tx)) as Hfee0.
        lia.
      * apply Z.le_min_r.
  - assert (Hsender_in : sender tx ∈ sender tx :: map sender extension).
    { apply elem_of_cons. left. reflexivity. }
    pose proof (Hacc (sender tx) Hsender_in) as Hsender_safe.
    pose proof (execBalLb addr s tx ltac:(lia)
                  (proj1 Hsender_safe) (proj2 Hsender_safe)) as Hlb.
    simpl in Hlb.
    assert (Haddr_in : addr ∈ sender tx :: map sender extension).
    { apply elem_of_cons. exact Hin. }
    pose proof (Hscf addr Haddr_in) as Hsc_addr.
    rewrite Hsc_addr in Hlb.
    rewrite (bool_decide_eq_false_2 (addr = sender tx)) in Hlb; [|exact H].
    rewrite (bool_decide_eq_false_2 (addr ∈ execCodeSCAccounts s.1 tx)) in Hlb;
      [|exact (proj1 (Hacc _ Haddr_in))].
    rewrite (bool_decide_eq_false_2 (addr = StakingContractAddr)) in Hlb;
      [|exact (proj2 (Hacc _ Haddr_in))].
    destruct (addrDelegated (execValidatedTx s tx).1.1 addr) eqn:Hdel.
    + simpl in Hlb.
      pose proof
        (proj1 (N2Z.inj_le
                  (configuredReserveBalOfAddr s.2 addr `min` balanceOfAcA s addr)
                  (balanceOfAcA (execValidatedTx s tx).1 addr)) Hlb) as HlbZ.
      rewrite N2Z.inj_min in HlbZ.
      apply Z.min_glb.
      * rewrite Z.min_comm. exact HlbZ.
      * apply Z.le_min_r.
    + simpl in Hlb.
      pose proof
        (proj1 (N2Z.inj_le
                  (balanceOfAcA s addr)
                  (balanceOfAcA (execValidatedTx s tx).1 addr)) Hlb) as HlbZ.
      apply Z.min_le_compat_r.
      exact HlbZ.
Qed.

  Definition remainingEffReserveBals s irb inter txc:=
  let rem  := remainingEffReserveBalOfSender s (irb (sender txc)) inter txc in
  updateKey irb (sender txc) (fun _ => rem).

Lemma decreasingRemTxSender s irb proc tx txc:
  let rem  := remainingEffReserveBalOfSender s (irb (sender txc)) (tx :: proc) txc in
  let remRbs := updateKey irb (sender txc) (fun _ => rem) in
  remRbs (sender tx) ≤ irb (sender tx).
Proof using eas.
  simpl.
  unfold remainingEffReserveBalOfSender.
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  { case_bool_decide; rwHyps; try lia; try case_match_concl; repeat rewrite updateKeyLkp3;
      fold EffReserveBals in *;  try lia;
    try applyToSomeHyp isAllowedToEmptyImpl; forward_reason; try congruence; try lia.
  }
  case_bool_decide; try lia.
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *; rwHyps; try lia.
  apply isAllowedToEmptyImpl in Heqb.
  forward_reason. congruence.
Qed.


(** lifts the previous lemma from [remainingEffReserveBalOfSender] to [remainingEffReserveBalsL]. induction on [nextL] *)
Lemma decreasingRemL s irb proc (nextL: list TxWithHdr) tx:
  (remainingEffReserveBalsL s irb (tx::proc) nextL) (sender tx) <=  (irb (sender tx)).
Proof using eas.
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
Proof using eas.
  intros Hc.
  unfold consensusAcceptableTxs in *.
  specialize (Hc (sender tx)).
  simpl in *.
  specialize (Hc ltac:(set_solver)).

  unfold validateTx.
  autorewrite with iff.
  match type of Hc with
    context[ remainingEffReserveBalsL _ ?irb _ _ ]
    => assert (0<= irb (sender tx)) as Hr
  end.
  {
    etransitivity;[ apply Hc|].
    apply decreasingRemL.
  }
  clear Hc.
  unfold remainingEffReserveBals in Hr.
  unfold remainingEffReserveBalOfSender in Hr.
  case_match; auto; case_match;
    repeat rewrite updateKeyLkp3 in Hr;
    autorewrite with syntactic in Hr;
    fold EffReserveBals balanceOfAcA in *; unfold balanceOfAcA in *; simpl in *; try lia;[].
  case_bool_decide; auto;
    repeat rewrite updateKeyLkp3 in Hr;
    autorewrite with syntactic in Hr;
    fold EffReserveBals balanceOfAcA in *; unfold balanceOfAcA in *; simpl in *; try lia.
Qed.


(** This lemma says that you can execute the first tx in the proposed extension and the consensus checks would
    still hold on the resultant state for the remaining transactions in the proposal.
    This follows from [exec1] and [monoL2]
*)
Lemma execPreservesConsensusChecks tx extension s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  (forall txext, txext ∈ extension ->  txBlockNum txext - (K-1) ≤ txBlockNum tx ≤ txBlockNum txext)   -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtAddrs txext (map sender (tx::extension)))
  -> noTxnsFromStakingAddr (tx::extension)
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> isSC s.1 ac = false)
  -> consensusAcceptableTxs s (tx::extension)
  -> consensusAcceptableTxs ((execValidatedTx s tx).1) extension.
Proof using eas.
  intros Hfee Hext Heoac Hnostake Hsc.
  pose proof (isSCFalsePresExec _ _ _ Heoac Hsc) as Hscf.
  assert (Hnoexec :
            forall ac, ac ∈ sender tx :: map sender extension ->
              ac ∉ execCodeSCAccounts s.1 tx /\ ac <> StakingContractAddr).
  { intros ac Hin.
    specialize (Heoac tx ltac:(set_solver) s ac Hin).
    specialize (Heoac ltac:(apply Hsc; set_solver)).
    destruct Heoac as [_ Hnoexec].
    split; [exact Hnoexec|].
    apply Hnostake.
    set_solver.
  }
  set (sf:= (execValidatedTx s tx).1.1).
  intros Hc.
  simpl in *.
  intros ac Hin.
  specialize (Hc ac).
  forward_reason.
  simpl in *.
  specialize (Hc ltac:(set_solver)).
  etransitivity.
  { apply Hc. }
  pose proof (monoL2 (map sender (tx::extension))) as Hm.
  unfold rbLe in Hm.
  simpl in *.
  apply Hm.
  all: try (intros a Ha; simpl; right; exact Ha);
       try (apply exec1; [exact Hfee | exact Hscf | exact Hnoexec]);
       try exact Hext;
       try exact Hsc;
       try (intros a Ha; apply Hnostake; set_solver);
       try (apply Heoac; simpl; left; reflexivity);
       try set_solver.
Qed.

(** The above 2 lemmas are used to yield the following: *)
Lemma inductiveStep  (latestState : AugmentedState) (tx: TxWithHdr) (extension: list TxWithHdr) :
  maxTxFee tx <= balanceOfAc latestState.1 (sender tx)
  -> (forall txext, txext ∈ extension ->  txBlockNum txext - (K-1) ≤ txBlockNum tx ≤ txBlockNum txext)
  -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtAddrs txext (map sender (tx::extension)))
  -> noTxnsFromStakingAddr (tx::extension)
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> isSC latestState.1 ac = false)
 ->  consensusAcceptableTxs latestState (tx::extension)
  -> match execTx latestState tx with
     | None =>  False
     | Some (si,_) =>
         consensusAcceptableTxs si extension
     end.
Proof using eas.
  intros Hext Heoac Hnostake Hsc Hc.
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
Proof using.
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
Proof using.
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
Proof using.
  unfold txCannotCreateContractAtAddrs.
  intros Hs Hp.
  intros.
  apply Hp; auto.
Qed.

Lemma  txCannotCreateContractAtAddrsTrimHead tx h l:
  txCannotCreateContractAtAddrs tx (h::l)
  -> txCannotCreateContractAtAddrs tx l.
Proof using eas.
  apply txCannotCreateContractAtAddrsMono.
  set_solver.
Qed.

Lemma noTxnsFromStakingAddrMono l1 l2:
  l1 ⊆ l2
  -> noTxnsFromStakingAddr l2
  -> noTxnsFromStakingAddr l1.
Proof using eas evmExecTxCore revertTx.
  unfold noTxnsFromStakingAddr.
  intros Hs Hp ac Hin.
  apply Hp.
  set_solver.
Qed.

Lemma noTxnsFromStakingAddrTrimHead h l:
  noTxnsFromStakingAddr (h::l)
  -> noTxnsFromStakingAddr l.
Proof using eas evmExecTxCore revertTx.
  apply noTxnsFromStakingAddrMono.
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
  -> noTxnsFromStakingAddr (firstblock++restblocks)
  -> (forall ac, ac ∈ (map sender (firstblock++restblocks)) -> isSC latestState.1 ac = false)
  -> match execTxs latestState firstblock with
     | None =>  False
     | Some (si, _) =>
         consensusAcceptableTxs si restblocks
         /\ blockNumsInRange restblocks
         /\ noTxnsFromStakingAddr restblocks
         /\ (forall ac, ac ∈ (map sender restblocks) -> isSC si.1 ac = false)
         /\ (forall txext, txext ∈ (restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (restblocks)))
     end.
Proof using eas.
  intros Hrange Hacc.
  induction firstblock as [|hb1 firstblock IH] in latestState, Hrange, Hacc |- *; simpl in *; auto.
  intros Heoa Hnostake Hsc.
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
  pose proof (noTxnsFromStakingAddrTrimHead hb1 (firstblock ++ restblocks) Hnostake) as Hnostake_tail.
  specialize (IH si ltac:(auto) ltac:(auto) Hcannot_tail Hnostake_tail).
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

Print Assumptions fullBlockStep.
(** All assumptions of the proof:
[[
Section Variables:
revertTx
: StateOfAccounts → TxWithHdr → StateOfAccounts * TxResult
evmExecTxCore
: StateOfAccounts → TxWithHdr → EvmExecResult
eas
: EVMAssupmtions
K
: N
Axioms:
maxStorageFee : TxWithHdr → N
keccak256_program : evm.program → N
delegation_marker_prefix : evm.program → bool
]]
 *)


Corollary fullBlockStep2  (latestState : AugmentedState) (blocks: list TxWithHdr) :
  (forall ac, ac ∈ (map sender (blocks)) -> isSC latestState.1 ac = false)
  -> (forall txext, txext ∈ (blocks) ->  txCannotCreateContractAtAddrs txext (map sender (blocks)))
  -> noTxnsFromStakingAddr blocks
  -> blockNumsInRange (blocks)
  -> consensusAcceptableTxs latestState (blocks)
  -> match execTxs latestState blocks with
     | None =>  False
     | Some (si, _) => True
     end.
Proof using eas.
  intros.
  pose proof (fullBlockStep latestState blocks []) as Hf.
  autorewrite with syntactic in Hf.
  specialize (Hf ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
  destruct (execTxs latestState blocks) as [[si rs] | ] eqn:Hexec.
  - exact I.
  - exact Hf.
Qed.


Lemma acceptableNil lastConsensedState:
  consensusAcceptableTxs lastConsensedState [].
Proof using.
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
  forall preTxState postTxState execAs t a,
    balanceOfAc preTxState.1 a <= balanceOfAc postTxState a
    -> finalBalSufficient preTxState postTxState execAs t a = true.
Proof.
  intros ? ? ? ? ? Hbal.
  unfold finalBalSufficient.
  destruct (isSC postTxState a
            || asbool (a ∈ execAs)
            || asbool (a = StakingContractAddr)) eqn:Hsc; [reflexivity|].
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
  Hypothesis b0nostaking: noTxnsFromStakingAddr b0.

  Hypothesis nextBlockPicker:
    forall (lastConsensedState: AugmentedState) (proposedTxs: (list TxWithHdr)),
      consensusAcceptableTxs lastConsensedState proposedTxs
      -> blockNumsInRange proposedTxs
      -> cannotCreateCodeAtSenderAddrs proposedTxs
      -> noTxnsFromStakingAddr proposedTxs
      -> (∀ ac : EvmAddr, ac ∈ map sender proposedTxs → isSC lastConsensedState.1 ac = false)
      -> exists nextBlock,
          consensusAcceptableTxs lastConsensedState (proposedTxs++nextBlock)
          /\ blockNumsInRange (proposedTxs++nextBlock)
          /\ cannotCreateCodeAtSenderAddrs (proposedTxs++nextBlock)
          /\ noTxnsFromStakingAddr (proposedTxs++nextBlock)
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
    pose proof (nextBlockPicker sb0 []  (acceptableNil _) I ltac:(set_solver) ltac:(set_solver) ltac:(set_solver)) as b1.
    destruct b1 as [b1 b1ok].
    simpl in b1ok.
    forward_reason.
    (** now we invoke the oracle to pick the next block after b1 *)
    pose proof (nextBlockPicker sb0 b1 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b2.
    destruct b2 as [b2 b2ok].
    forward_reason.
    unfold cannotCreateCodeAtSenderAddrs in *.
    apply fullBlockStep in b2okl; auto.
    (** assuming K=2, we wait for execution to execute b1 and give us the new state sb1  *)
    destruct (execTxs sb0 b1) as [[sb1 ?]|]; auto.
    forward_reason.
    (** now we pick the new block b3, but with the latestConsensedState of sb1 rather than sb0 *)
    pose proof (nextBlockPicker sb1 b2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b3.
    destruct b3 as [b3 b3ok].
    forward_reason.
    apply fullBlockStep in b3okl; auto.
    (** we wait for execution to execute b2 and give us the new state sb2  *)
    destruct (execTxs sb1 b2) as [[sb2 ?]|]; auto;[].
    forward_reason.
    (** now we pick the new block b3, but with the latestConsensedState of sb2 rather than sb1 *)
    pose proof (nextBlockPicker sb2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b4.
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
  
  Definition configuredReserveBalF (s : AugmentedState) (addr : EvmAddr) : U256 :=
    u256_of_N (configuredReserveBalOfAddr s.2 addr).

  Definition valueF (t: TxWithHdr) : U256 := u256_of_N (value t).
  Definition maxTxFeeF (t: TxWithHdr) : U256 := u256_of_N (maxTxFee t).
  Definition maxStorageFeeF (t: TxWithHdr) : U256 := u256_of_N (maxStorageFee t).
  Definition reserveBalUpdateOfTxF (t: TxWithHdr) : option U256 := option_map u256_of_N (reserveBalUpdateOfTx t).


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
  Proof using.
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
    let configuredRb := Some (configuredReserveBalF preIntermediatesState senderAddr) in
    match reserveBalUpdateOfTxF candidateTx with
    | Some newRb =>
        if isAllowedToEmpty K preIntermediatesState intermediates candidateTx
        then (senderBal ⊖ maxTxFeeF candidateTx) `mino` (Some newRb)
        else (Some prevErb ⊖ maxTxFeeF candidateTx) `mino` (Some newRb)
    | None =>
        if isAllowedToEmpty K preIntermediatesState intermediates candidateTx
        then
          let newBal := (((senderBal ⊖ (maxTxFeeF candidateTx)) ⊖ (valueF candidateTx)) ⊖ (maxStorageFeeF candidateTx)) `maxo` 0f in
          (** ^ pay attention to the bracketing. If we instead first add up [maxTxFeeF candidateTx], [valueF candidateTx], and [maxStorageFeeF candidateTx], and only then subtract from [senderBal], the result of addition may overflow, although only a malicious person would probably send such a transaction *)
          if asbool (maxTxFee candidateTx <= balanceOfAc (preIntermediatesState.1) senderAddr)
          then newBal `mino` configuredRb
          else None
        else Some prevErb ⊖ (maxTxFeeF candidateTx)
    end.

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
      ((configuredReserveBalOfAddr s.2 addr) < 2^256).

  Definition txReserveUpdateWithinBounds (tx : TxWithHdr) : Prop :=
    maxTxFee tx < 2^256 /\
    value tx < 2^256 /\
    maxStorageFee tx < 2^256 /\
    match reserveBalUpdateOfTx tx with
    | Some rb => (rb < 2^256)
    | None => True
    end.

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
    unfold reserveBalUpdateOfTxF.
    pose proof (Hb (sender candidateTx)).
    hnf in Ht.
    unfolds. 
    forward_reason.
    case_match_concl.
    { simpl.
      case_match_concl.
      {
        autounfold with unfoldu in *.
        case_bool_decide;
          forward_reason; simpl in *; 
        Arith.remove_useless_mod_a; try lia.
      }
      {
        autounfold with unfoldu in *.
        case_bool_decide;
          forward_reason; simpl in *; 
        Arith.remove_useless_mod_a; try lia.
      }
    }
    {
      case_match_concl; simpl in *.
      2:      {
        autounfold with unfoldu in *.
        case_bool_decide;
          forward_reason; simpl in *; 
        Arith.remove_useless_mod_a; try lia.
      }

      {
        autounfold with unfoldu in *.
        simpl in *.
        repeat (
          case_bool_decide;
          simpl in *;
          try (resolveDecide lia);
          try auto;
          try (Arith.remove_useless_mod_a; try lia; try Arith.arith_solve)
        ).
        all: autounfold with unfoldu in *;
            subst; simpl in *;
            Arith.remove_useless_mod_a; try Arith.arith_solve; try lia.
      }
    }
    
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
  Proof using.
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
