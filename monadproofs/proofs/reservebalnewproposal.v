(** * Coq model of reserve balance and proof of safety

    This is a new proposal for reserve balance checks.
    It is drastically simpler and much easier to implement/maintain than the one currently implemented in Monad, and yet has the same safety theorems proved in Coq.
    This document does not assume that you understand the old one, except mentioning the differences at some places, which you can safely ignore. This document uses the same names for analogous definitions, so that you can compare and judge the simplifications in this new proposal. Whenever we say “old design” below, we mean the reserve-balance mechanism currently implemented in Monad.

    Main advantages of this proposal:
    - No need to maintain history of previous 2K transactions. Any *currently* undelegated sender is allowed to empty, even if it sent many other transactions in the same block or was delegated earlier in the same block. There can be many emptying transactions.
    - The execution check is *strictly* more liberal, so transactions are less likely to revert. The only execution change is the new (more permissive) definition of [isAllowedToEmpty].
    - The definitions and proofs are much shorter (< 1/2 the size in Coq).
    - Consensus checks are more liberal in some ways and less liberal in others. They are more liberal because several emptying transactions in the same block are allowed, as long as the balance lower-bound estimates allow it. They are less liberal in the sense that they may reject some sequences that the previous design allowed, but those transactions would have reverted during execution anyway unless there was an intervening credit. A concrete example:

[[
Alice: balance = 100, reserve = 5, undelegated  
tx1: sent by Alice, fee 6, value 1        (balance ≈ 93 after tx1)  
tx2: some tx from Bob that does not change any account's delegation status  
tx3: sent by Alice, fee 2, value 91       (needs ≈93 total, fully consuming the budget)  
tx4: sent by Alice, fee 1, value 0
]]

This sequence would be allowed by the old consensus check algorithm: tx1 is allowed to empty, so Alice's effective reserve balance after tx1 becomes 5, which the old logic treats as enough to pay the fees of the remaining transactions from Alice (because they are deemed not allowed to empty). During execution, tx3 would revert unless tx2 credited Alice's account.

In the new proposal, tx4 will not be accepted and tx3 will not revert during execution. Consensus lowers the balance estimate for Alice to 0 after tx3, so tx4 is rejected. Tx3 is also allowed to empty because it is not delegated. If tx2 indeed credited Alice, tx4 can be accepted by the new consensus check in the Kth block after the credit, because by that time the full execution result of the block containing the credit is available.


It can be argued that minimizing tx reverts is more important for a good user experience because reverts cost the user, and delaying transaction inclusion to a later block when there is revert risk may be a fair price to pay for it. The simplicity and ease of implementation are other pros for this new proposal.

Next, we give a very brief overview of the design in the new proposal and then look at several examples illustrating the difference in consensus/execution behavior. Only then do we present the Coq definitions of the new design.
*)


(** * Design Overview:


The model has two cooperating pieces:

    - **Consensus** does a very shallow execution of transactions to only compute 3 pieces of info for each account (the implementation can be sparse):
      - whether the account is delegated after the tx
      - the current configured reserve balance
      - a lower bound on the balance of the account. a tx is accepted if its sender's pre-tx lowerbound is enough to cover the max fee.

    - **Execution**: exactly the same as before, except for the simpler (and more liberal) definition of [isAllowedToEmpty]: execute the core EVM step and then check each changed delegated/non-code account to ensure it did not dip too far into the reserve; otherwise revert. *)
        

(** * Examples illustrating the difference 

Below are more examples contrasting the consensus and execution behavior difference between the old design and the new proposal: *)

(** ** Example 2:

[[
Alice: bal 100, reserve 5, undelegated
tx1: alice, fee 6, value 10
tx2: alice, fee 6, value 10
]]
- consensus: the new design accepts this sequence of 2 txs but the old one rejects tx2 because the estimate of remaining reserve balance after tx1 is less than the fee of 6. Because Alice remains undelegated throughout, its balance lower bound can be more precisely computed by tracking the value transfers, so the new design of consensus checks knows that tx2 has enough balance to cover the fee.
- execution: the new design will not revert tx2 because it is allowed to empty because it is undelegated.
 *)


(** ** Example 3:
[[
Alice 100, undelegated, reservebal =5
tx1: sender Alice, delegates Alice, value 10, fee 1
tx2: Bob sends to Alice, and a delegated smart-contract execution debits her by 20
tx3: sender Alice, undelegates Alice, value 0, fee 1
tx4: sender Alice, value 10, fee 1
]]
- consensus: both new and old designs will accept. In the new proposal, consensus maintains a lower bound on every account's balance and ensures that the lower bound is enough to cover the fees. Once an account is delegated, its lower bound drops to the min of the previous lower bound and configured reserve balance. After tx4, in the new design, the balance lower bound estimate becomes negative for Alice and thus no more transactions from Alice will be accepted for the next K blocks.
- execution: only the old design will unnecessarily revert tx4. In the new proposal, tx4 will be considered emptying because it is not delegated and will NOT revert.

*)


(** * Main artifacts:

    - Consensus check: [consensusAcceptableTxs].
    - Execution step (with its check): [execValidatedTx] (called by [execTx]).
    - Main “safety” theorem: [fullBlockStep], says that if a sequence of txs is accepted by consensus, the execution of that sequence cannot run into an error due to inability to pay the fee.

    References to any Coq item are hyperlinked to its definition if the definition is in this file or in the Coq standard library.

    [consensusAcceptableTxs] is defined using idealized arithmetic ([Z], which is Coq's type of unbounded integers with no over/underflow in operations). If this proposal is adopted, we can write a U256 (finite-width arithmetic) version and prove it equivalent, ideally under no additional assumptions.
*)

(* begin hide *)
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.misc.
Require Import Lens.Lens.
Import LensNotations.
Open Scope lens_scope.
Import miscPure.Forward.
Import miscPure. (* has a better version of forward_reason *)
Set Default Goal Selector "!".
Require Import skylabs.auto.cpp.tactics4.
Open Scope N_scope.

Require Import elpi.apps.derive.derive.
Require Import Lens.Lens.
Require Import Lens.Elpi.Elpi.

Import LensNotations.
#[local] Open Scope lens_scope.
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

(** Many of the EVM semantics definitions we use come from Yoichi's EVM semantics, developed several years ago. The definition of [block.transaction] there lacks fields to support newer features like delegation. Also, the last field is to support user-configurable reserve balances in Monad. There is a new transaction type which can update the configured reserve balance of the sender. Such transactions do nothing else. *)
Record TxExtra :=
  {
    dels: list EvmAddr;
    undels: list EvmAddr;
    (** The fields above should ultimately come from EVM semantics and not here. The fields below are monad-specific. *)
    reserveBalUpdate': option N
   (** ^ updates the reserve balance of the sender if [Some]. In that case, the transaction does nothing else, e.g., no smart contract invocation or transfer. It must be [None] for regular transactions (which do not reconfigure the reserve balance). [option N] in Coq can be thought of as std::optional<N> in C++. [None] in Coq corresponds to std::nullopt in C++.
Transactions to uodate reserve balance will be implemented as a call to a special precompile:

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

Definition isEmpty {T} (t:list T) : bool :=
  match t with
  | [] => true
  | _ => false
  end.

(** A transaction that reconfigures a user's reserve balance cannot also change any delegation status.
    In the implementation, the data-structure design probably will not allow both.
    Here, we simply ignore the reserve-balance update of a transaction if the transaction delegates or undelegates.
 *)
Definition reserveBalUpdate (t: TxExtra) : option N :=
  if isEmpty (dels t ++ undels t) then reserveBalUpdate' t else None.

(** The type [A * B] in Coq can be thought of as [std::pair<A,B>]. The projections [.1] and [.2] can be used to obtain the first and second components of the pair, respectively. *)
Definition TxWithHdr : Type := (BlockHeader * TxExtra) * (block.transaction).

(** Our **fee upper bound** is intentionally pessimistic: the consensus rule
    reasons about [gas_limit × gas_price], not about *actual* gas used, which can be hard to efficiently estimate.
 *)
Definition maxTxFee (t: TxWithHdr) : N :=
  ((w256_to_N (block.tr_gas_price t.2)) * (w256_to_N (block.tr_gas_limit t.2))).

(** The proofs in this file never unfold the definition of [maxTxFee], so nothing will break if this definition is changed.  *)
Opaque maxTxFee.

(** for any decidable assertion/proposition P, [asbool P] is a boolean such that [(asbool P = true) <-> P], where
 [<->] means iff (if and only if)*)
Notation asbool := bool_decide.

(** Next, we have some simple wrappers for brevity.

   sender of a transaction: *)
Definition sender (t: TxWithHdr): EvmAddr := tsender t.2.

(** value transfer field of a of a transaction *)
Definition value (t: TxWithHdr): N := w256_to_N (block.tr_value t.2).

(** addresses delegated or undelegated by [tx] *)
Definition addrsDelUndelByTx (tx: TxWithHdr) : list EvmAddr := (dels tx.1.2 ++ undels tx.1.2).

(** Does [tx] delegate/undelegate [addr]? *)
Definition txDelUndelAddr (addr: EvmAddr) (tx: TxWithHdr) : bool :=
  asbool (addr ∈ addrsDelUndelByTx tx).

(** block number of a transaction *)
Definition txBlockNum (t: TxWithHdr) : N := number t.1.1.

(** returns [None] if this tx is not a reserve-balance-reconfig tx. Else it returns [Some newRb], where [newRb] will become the new reserve balance threshold of the sender if/when t is executed. *)
Definition reserveBalUpdateOfTx (t: TxWithHdr) : option N := reserveBalUpdate t.1.2.

(** The extra (non-EVM) state needed to be maintained by execution to implement reserve balance checks. Note that this had many more (history) fields in the old design *)
Record ExtraAcState :=
  {
    configuredReserveBal: N;
    (** ^ current configured reserve balance of the account (defaults to the global reserve if it never reconfigured). *)
  }.

Definition ExtraAcStates := (EvmAddr -> ExtraAcState).

(** We thread the EVM state with this metadata. This “augmented state” is the
    substrate both consensus and execution read from and update. *)
Definition AugmentedState : Type := StateOfAccounts * ExtraAcStates.

(** Whether an address currently has code. excludes cases where the code is just a delegation marker  *)
Definition isSC (s: StateOfAccounts) (addr: EvmAddr): bool. Admitted.

(** update the value of the key [updKey] in [oldMap] to [f (oldMap updKey)] ([f] applied to the old value of the key [updKey] in the map) *)
Definition updateKey  {T} `{c: EqDecision T} {V}  (oldmap: T -> V) (updKey: T) (f: V -> V) : T -> V :=
  fun k => if (asbool (k=updKey)) then f (oldmap updKey) else oldmap k.

(* TODO: remove *)
Lemma updateKeyLkp3  {T} `{c: EqDecision T} {V} (m: T -> V) (a b: T) (f: V -> V) :
  (updateKey m a f)  b = if (asbool (b=a)) then (f (m a)) else m  b.
Proof using. reflexivity. Qed.

(** * Consensus (Algorithm 1)

    Consensus maintains **shallow execution summary** per account that is
    deliberately lossy but safe: it pessimistically lowers a “balance lower
    bound” and threads the configured reserve cap and delegation flag. This is
    sufficient to enforce fee‑solvency for any yet‑to‑run suffix.
*)

(** Shallow summary for a single account after shallow execution of a sequence of transactions from a fully executed state: *)
Record ShallowExecRes : Type := mkNotDelCase
  {
    (** Pessimistic **lower bound** on the account’s balance: *)
    balanceLb: Z;

    (** the account's configured reserve balance:  *)
    configuredRB: N;

    (** is the account delegated? : *)
    delegated: bool;

  }.

(** Shallow execution results of all accounts. It is a pair containing:
- a bool indicating whether the sequence of proposed txs is fee-solvent so far, and
- each account's shallow state after shallow execution.
 *)

Definition ShallowExecResults : Type := bool * (EvmAddr -> ShallowExecRes).

(** some more wrappers: *)
Definition configuredReserveBalOfAddr (s: ExtraAcStates) addr := configuredReserveBal (s addr).

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

(** Initial shallow execution result, before executing any proposed transactions. [s] will typically be the last fully executed/finalized state. If an account is not delegated, its balance lower bound is the entire balance in [s]. Otherwise, we take the minimum of its balance and the configured reserve balance of the account. The fee-solvency bool (first element of the pair) is true because we are starting with an empty proposal. *)
Definition initialShallowExecResults (s: AugmentedState) : ShallowExecResults :=
  (true, 
    fun addr =>
      let crb := configuredReserveBalOfAddr s.2 addr in
      let del := addrDelegated s.1 addr in
      let bal := balanceOfAc s.1 addr in
      {|
        balanceLb := if del then bal `min` crb else bal;
        configuredRB := crb;
        delegated := del;
      |}).

(** the new delegation status of an account after executing [tx] *)
Definition delegatedAfterTx (prevDelegated: bool) (tx: TxWithHdr) (addr: EvmAddr) : bool :=
      (prevDelegated && asbool (addr ∉ undels tx.1.2))
      || asbool (addr ∈ dels tx.1.2).

(** ** Shallow execution of a transaction

    The next defn is the algebraic heart of consensus check algorithm:
    fold this function left-to-right over the entire sequence of proposed txs, and you get the final result of shallow execution. The first component of the result indicates fee solvency.


    Formally, this function conservatively estimates the [ShallowExecResults] after executing [candTx] (cand is just short for candidate), assuming [prevRes] is the shallow execution result just before [candTx]. A few things to note:
    - it is monotone (proven in the lemma [mono] below)
    - if the account is delegated, the balance lower bound drops to the min of the previous lower bound and the configured reserve balance
    - updates the shallow account state ([ShallowExecRes]) of not just the sender but also every account that got delegated in [candTx]
    - the fee-solvency bool is [true] iff the previous result itself was solvent and the previous lower bound on balance was greater than or equal to [maxTxFee candTx]
*)
Definition shallowExecTx (preRes: ShallowExecResults) (candTx: TxWithHdr)
  : ShallowExecResults :=
  let feeSolvent : bool :=
    let previouslySolvent := preRes.1 in 
    previouslySolvent && asbool (maxTxFee candTx <= balanceLb (preRes.2 (sender candTx))) in
  let shallowRes (addr: EvmAddr) :=
    let prev := preRes.2 addr in
    let newCrb :=
      if asbool (sender candTx <> addr)
      then configuredRB prev
      else
        match reserveBalUpdateOfTx candTx with
        | Some newRb => newRb
        | None => configuredRB prev
        end in
    let newDelegated := delegatedAfterTx (delegated prev) candTx addr in
    let isNotSender := asbool (sender candTx <> addr) in
    let startingRb := balanceLb prev `min` newCrb in
    {|
      balanceLb :=
        if newDelegated
        then (if isNotSender then startingRb else startingRb - maxTxFee candTx)
        else if isNotSender
             then balanceLb prev
             else balanceLb prev - maxTxFee candTx - value candTx;
      configuredRB := newCrb ;
      delegated := newDelegated;
    |} in
  (feeSolvent, shallowRes)
.

(** We can fold the function above over the entire list of proposed transactions, chaining the results. *)
Fixpoint shallowExecTxL (preProposalRes: ShallowExecResults) (proposal: list TxWithHdr)
  : ShallowExecResults:=
  match proposal with
  | [] => preProposalRes
  | htx::tltx =>
      shallowExecTxL (shallowExecTx preProposalRes htx) tltx
  end.

(** ** Consensus acceptability.
    A suffix [proposedTxs] is **acceptable** if the fee-solvency bool is true in the final result. *)
Definition consensusAcceptableTxs (latestState : AugmentedState) (proposedTxs: list TxWithHdr) : Prop :=
   (shallowExecTxL
      (initialShallowExecResults latestState) proposedTxs).1 = true.

(** * Execution Check (algo 2)

The execution logic is also tweaked to ensure that a transaction cannot dip too much into reserves and thereby fail to cover the fees for a transaction already included by consensus. The main complication is that some EOAs may be delegated and thus transactions sent to them can make arbitrary debits that are hard to statically estimate without actually executing the transaction. Thus, we have a dynamic check at the end of execution to see if some delegated EOA account (possibly other than the sender) was debited too much. Consensus carries a more precise balance lower-bounding for non-delegated accounts, so execution can let non-delegated accounts empty.
*)

(** Trivial wrapper defining whether the sender is delegated after executing [tx] in state [s]. *)
Definition senderDelegatedAfterTx (s: StateOfAccounts) (tx: TxWithHdr) :=
  delegatedAfterTx (addrDelegated s (sender tx)) tx (sender tx).

(** Notice that we did not need any “isAllowedToEmpty” concept in defining consensus checks.
The execution check is the same as in the old design, except that the definition of “is allowed to empty” is radically simplified: it does not need any history of previous transactions and is equivalent to the sender being not delegated *after* executing the transaction.
 *)
Definition isAllowedToEmpty
  (s : AugmentedState)  (t: TxWithHdr) : bool :=
  negb (senderDelegatedAfterTx s.1 t).

(** Helper to update the extra metadata (just the configured reserve balance of each account). *)
Definition updateExtraState (a: ExtraAcStates) (tx: TxWithHdr) : ExtraAcStates :=
  (fun addr =>
     let oldes := a addr in
       {|
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

(* begin hide *)
Open Scope N_scope.
(* end hide *)

(** ** Abstract execution and revert

    We postulate a single-step EVM core ([evmExecTxCore]) that returns the new
    state and the set of changed accounts; and the revert step for failed checks.
    This keeps the reserve logic orthogonal to the (much larger) EVM semantics.
    The list ([list EvmAddr]) returned by [evmExecTxCore] contains all the changed accounts.
 *)
Axiom evmExecTxCore : StateOfAccounts -> TxWithHdr -> StateOfAccounts * (list EvmAddr) (* the list contains all the changed accounts *).
Axiom revertTx : StateOfAccounts -> TxWithHdr -> StateOfAccounts.

(** ** Algorithm 2 (execution): execute a transaction

    Next, we define [execValidateTx], which assumes that [t] has already been validated to ensure that the sender has
    enough balance to cover [maxTxFee]. It uses a helper [allFinalBalSufficient], which we define first.

    Execution, as defined by [execValidateTx], proceeds as follows:

    - Special “reserve update” tx: pay fee; set new configured reserve.
    - Otherwise, run the core EVM step to obtain the *actual* post state.
    - For *changed* accounts, [allFinalBalSufficient] checks that the account was not debited too much, which may endanger the fee solvency of the later transactions already accepted by consensus. Note that the checks are trivial for accounts that have code or are not delegated after executing t.
    - If any check fails, revert the tx. *)

(** [allFinalBalSufficient] captures the per-account reserve-balance postcondition for
    a transaction.  *)

Definition allFinalBalSufficient (preTxState: AugmentedState) (postTxState : StateOfAccounts) (changedAccounts: list EvmAddr) (t: TxWithHdr): bool:=
       let finalBalSufficient (a: EvmAddr) :=
       let ReserveBal := configuredReserveBalOfAddr preTxState.2 a in
       let erb:N := ReserveBal `min` (balanceOfAc preTxState.1 a) in
       if isSC postTxState a
       then true
       else
         if asbool (sender t = a)
         then if isAllowedToEmpty preTxState t
              then true
              else asbool ((erb  - maxTxFee t) <= balanceOfAc postTxState a)
         else asbool (erb <= balanceOfAc postTxState a) in
     (forallb finalBalSufficient changedAccounts).

Definition execValidatedTx  (s: AugmentedState) (t: TxWithHdr)
  : AugmentedState :=
  match reserveBalUpdateOfTx t with
  | Some n => (updateBalanceOfAc s.1  (sender t) (fun b => b - maxTxFee t)
                 , updateExtraState s.2 t)
  | None =>

     let (postTxState, changedAccounts) := evmExecTxCore (fst s) t in
     if (allFinalBalSufficient s postTxState changedAccounts t) 
     then (postTxState, updateExtraState s.2 t)
     else (revertTx s.1 t, updateExtraState s.2 t)
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
   [None] means the execution of the whole block containing [t] aborts, which is what the consensus/execution checks must guarantee to never happen. *)
Definition execTx (s: AugmentedState) (t: TxWithHdr): option (AugmentedState) :=
  if (negb (validateTx (fst s) t)) then None
  else Some (execValidatedTx  s t).

(** execute a list of transactions one by one. Note that if the execution of any tx returns [None] (balance insufficient to cover fees), the entire execution (of the whole list of txs) returns [None]. *)
Fixpoint execTxs  (s: AugmentedState) (ts: list TxWithHdr): option AugmentedState :=
  match ts with
  | [] => Some s
  | t::tls =>
      match execTx s t with
      | Some si => execTxs si tls
      | None => None
      end
  end.

(** * Main correctness theorem *)

Open Scope Z_scope.

(** Cryptographic difficulty assumption: *)
Definition txCannotCreateContractAtAddrs tx (eoasWithPrivateKey: list EvmAddr) :=
  forall s, let sf := (execValidatedTx  s tx) in
            forall addr,  addr ∈ eoasWithPrivateKey -> isSC s.1 addr = false -> isSC sf.1 addr = false.

(** The lemma below is probably what one would come up first as the main correctness theorem.
[blocks] represents the transactions in the blocks proposed after [latestState].
It says that consensus checks ([consensusAcceptableTxs latestState blocks]) implies
that the execution of all transactions [blocks] one by one, starting from the state [latestState] will succeed and not abort ([None]) due to preTx balance being less than [maxTxFee].

*)
Theorem fullBlockStep2  (latestState : AugmentedState) (blocks: list TxWithHdr) :
  (forall ac, ac ∈ (map sender blocks) -> isSC latestState.1 ac = false)
  -> (forall txext, txext ∈ blocks ->  txCannotCreateContractAtAddrs txext (map sender blocks))
  -> consensusAcceptableTxs latestState blocks
  -> match execTxs latestState blocks with
     | None =>  False
     | Some si => True
     end. Abort.

(** ** main correctness theorem
We will prove the above correctness theorem below, but the actual correctness theorem we need is slightly stronger.
Suppose we split [blocks] in the theorem above into [firstblock] and [restblocks] such that [blocks=firstblock++blocksrest] and suppose these blocks together are all transactions from the K proposed blocks since the last consensus state. Now, consensus will wait for execution to catch up and compute the state after [firstblock], say [latestState'].
After that, consensus should check the next block after [blocksrest] w.r.t [latestState'].
At that time, it needs to know that [blocksrest] is already valid w.r.t [latestState'], i.e. [consensusAcceptableTxs latestState' blocksrest].  This is precisely what the main theorem, shown next does:
*)
Theorem fullBlockStep  (latestState : AugmentedState) (firstblock: list TxWithHdr) (restblocks: list TxWithHdr) :
  consensusAcceptableTxs latestState (firstblock++restblocks)
  -> (forall txext, txext ∈ (firstblock++restblocks) -> txCannotCreateContractAtAddrs txext (map sender (firstblock++restblocks)))
  -> (forall ac, ac ∈ (map sender (firstblock++restblocks)) -> isSC latestState.1 ac = false)
  -> match execTxs latestState firstblock with
     | None =>  False
        (** ^ Execution cannot abort because a head tx lacks enough fee balance. *)
     | Some si =>
        (** ^ Moreover, the tail remains fee‑solvent (and keeps the hygiene side
            conditions), enabling induction over blocks. *)
         consensusAcceptableTxs si restblocks
         /\ (forall ac, ac ∈ (map sender restblocks) -> isSC si.1 ac = false)
         /\ (forall txext, txext ∈ (restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (restblocks)))
     end.
Proof. Abort.


(** * Proof *)
Open Scope N_scope.
(** ** Core execution assumptions
To prove the theorem [fullBlockStep], we need to make some assumptions about how the core EVM execution updates balances and delegated-ness. The names of these axioms are fairly descriptive.

 *)

Axiom balanceOfRevertSender: forall s tx,
  maxTxFee tx <= balanceOfAc s (sender tx)
  -> reserveBalUpdateOfTx tx = None
  -> balanceOfAc (revertTx s tx) (sender tx)
     = balanceOfAc s (sender tx) - maxTxFee tx.

Axiom balanceOfRevertOther: forall s tx ac,
  reserveBalUpdateOfTx tx = None
  -> ac <> (sender tx)
  -> balanceOfAc (revertTx s tx) ac
     = balanceOfAc s ac.


Axiom revertTxDelegationUpdCore: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (revertTx s tx) in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && asbool (ac ∉ (undels tx.1.2)))
                || asbool (ac ∈ (dels tx.1.2))).

Axiom execTxDelegationUpdCore: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && asbool (ac ∉ (undels tx.1.2)))
                || asbool (ac ∈ (dels tx.1.2))).


Axiom execTxSenderBalCore: forall tx s,
  maxTxFee tx <= balanceOfAc s (sender tx) ->
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  senderDelegatedAfterTx s tx = false
   ->  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - ( maxTxFee tx + value tx)
        \/  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - (maxTxFee tx).


(** One caveat in the assumption below is that it assumes that the account [ac] does not receive so much credit that it overflows 2^256. In practice, this should never happen, assuming the ETH supply is well below 2^256. Thus, we can assume that [evmExecTxCore] caps the balance at [2^256] should it overflow, instead of wrapping around, which may violate this assumption. *)
Axiom execTxCannotDebitNonDelegatedNonContractAccountsCore: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  forall ac, ac <> sender tx
              -> (addrDelegated sf ac || isSC sf ac) = false
                 ->  balanceOfAc s ac <= balanceOfAc sf ac.


Axiom changedAccountSetSound: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let (sf, changedAccounts) :=  (evmExecTxCore s tx) in
  (forall ac, ac ∉ changedAccounts -> sf ac = s ac).


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


    

Lemma execTxDelegationUpdCoreImpl tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || asbool (ac ∈ (addrsDelUndelByTx tx))).
Proof.
  simpl.
  intros ? ?.
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
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (revertTx s tx) in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || asbool (ac ∈ (addrsDelUndelByTx tx))).
Proof.
  simpl.
  intros ? ?.
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
Proof.
  unfold updateBalanceOfAc, updateKey, balanceOfAc. simpl.
  case_bool_decide; simpl; subst; auto; resdec ltac:(congruence);[].
  destruct (s ac); auto.
Qed.

Lemma execTxOtherBalanceLB tx s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let sf :=  (execValidatedTx s tx) in
  (forall ac,
      let ReserveBal := configuredReserveBalOfAddr s.2 ac in
      (ac <> sender tx)
       -> if (isSC sf.1 ac)
          then True
          else ReserveBal `min` (balanceOfAcA s ac) <= (balanceOfAcA sf ac)).
Proof using.
  intros.
  subst ReserveBal.
  unfold execValidatedTx in *.
  unfold allFinalBalSufficient in *.
  simpl in *.

  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *.
  1:{  subst sf. unfold balanceOfAcA.  simpl.
       rewrite balanceOfUpd. case_match; auto. try lia.
       case_bool_decide; try lia.
  }
  pose proof (changedAccountSetSound tx s.1 ltac:(auto)) as Hsnd.
  rdestruct (evmExecTxCore s.1 tx) as [si changed].
  remember (isSC sf.1 ac) as sac.
  destruct sac; auto.
  rememberForallb.
  unfold balanceOfAcA in *.
  destruct fb; simpl in *.
  2:{ subst sf.
      rewrite balanceOfRevertOther; auto;[].
      resolveDecide congruence.
      lia.
  }
  symmetry in Heqfb.
  rewrite  forallb_spec in Heqfb.
  destruct (decide (ac ∈ changed)).
  {
    specialize (Heqfb ac ltac:(auto)).
    rewrite <- Heqsac in Heqfb.
    resolveDecide congruence.
    case_bool_decide; try lia.
  }
  {
    unfold balanceOfAc.
    rewrite Hsnd; auto. lia.
  }

Qed.

Lemma execTxSenderBal tx s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let ReserveBal := configuredReserveBalOfAddr s.2 (sender tx) in
  let sf :=  (execValidatedTx s tx) in
  isSC sf.1 (sender tx) = false->
  (if isAllowedToEmpty s tx
   then balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx)
        \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
  else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx))).
Proof.
  intros ? ? ? Hsc.
  subst ReserveBal.
  pose proof (execTxSenderBalCore tx s.1) as Hc.
  simpl in Hc.
  subst sf.
  revert Hsc.
  unfold execValidatedTx.
  unfold allFinalBalSufficient in *.
  remember ((reserveBalUpdateOfTx tx)) as rb.
  destruct rb; simpl in *.
  1:{  unfold balanceOfAcA. simpl in *.  intros.
       repeat rewrite balanceOfUpd.
       resolveDecide congruence.
       case_match_concl; auto; try lia.
  }
  specialize (Hc ltac:(auto)).
  pose proof (changedAccountSetSound tx s.1 ltac:(auto)) as Hsnd.
  rdestruct (evmExecTxCore s.1 tx) as [si changed].
  unfold isAllowedToEmpty, delegatedAfterTx.
  intros.
  unfold balanceOfAcA in *.
  destruct (senderDelegatedAfterTx s.1 tx); simpl in *.
  {
    rememberForallb.
    unfold balanceOfAcA in *.
    destruct fb; try lia.
    2:{
      simpl in *. rewrite balanceOfRevertSender; auto.
      resolveDecide congruence. lia.
    }
    symmetry in Heqfb.
    rewrite  forallb_spec in Heqfb.
    rwHyps.
    destruct (decide (sender tx ∈ changed));
      [| unfold balanceOfAc; simpl; rewrite Hsnd;try sauto].
    specialize (Heqfb (sender tx) ltac:(auto)).
    resolveDecide congruence.
    simpl in *.
    rewrite -> Hsc in Heqfb.
    case_bool_decide; try lia.
  }
  {
    autorewrite with syntactic in *.
    rememberForallb.
    forward_reason.
    destruct fb; destruct Hc; simpl in *; orient_rwHyps; simpl in *;
      repeat (rewrite balanceOfRevertSender;sauto);
        try resolveDecide congruence; try auto;
      try lia.
  }
Qed.

Lemma isEmptyImpl {T} (t:list T) :
  isEmpty t = true -> t=[].
Proof using.
  unfold isEmpty.
  destruct t; sauto.
Qed.
  
Lemma execTxDelegationUpd tx s:
  let sf :=  (execValidatedTx s tx) in
  (forall ac, addrDelegated (fst sf) ac  -> addrDelegated (fst s) ac || asbool (ac ∈ (addrsDelUndelByTx tx))).
Proof.
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
  case_match.
  {
    apply execTxDelegationUpdCoreImpl in Hd; auto.
  }
  {
    apply revertTxDelegationUpdCoreImpl in Hd; auto.
  }
Qed.

Hint Rewrite @app_nil : iff.
Lemma execTxDelegationUpdDerived: forall tx s,
  let sf :=  (execValidatedTx s tx).1 in
  forall ac, addrDelegated sf ac  =
                delegatedAfterTx (addrDelegated s.1 ac) tx ac.
Proof using.
  intros ? ? ? ?.
  subst sf.
  unfold execValidatedTx, delegatedAfterTx.
  simpl in *.
  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *; try congruence.
  1:{  unfold balanceOfAcA. simpl in *.  intros.
       repeat rewrite addrDelegatedUnchangedByBalUpd.
       unfold reserveBalUpdateOfTx in Heqrb.
       unfold reserveBalUpdate in Heqrb.
       case_match; try 
                     congruence.
       applyToSomeHyp @isEmptyImpl.
       autorewrite with iff in *.
       sauto.
  }
  rewrite pairEta. simpl.
  case_match.
  {
    rewrite execTxDelegationUpdCore; auto.
  }
  {
    rewrite revertTxDelegationUpdCore; auto.
  }
Qed.

Lemma execTxCannotDebitNonDelegatedNonContractAccounts tx s:
  let sf :=  (execValidatedTx s tx) in
  (forall ac, ac <> sender tx
              -> if (addrDelegated (fst sf) ac || isSC (fst sf) ac)
                 then True
                 else balanceOfAcA s ac <= balanceOfAcA sf ac).
Proof using.
  intros. subst sf.
  pose proof (fun p => execTxCannotDebitNonDelegatedNonContractAccountsCore tx s.1 p ac ltac:(auto)) as Htx.
  unfold execValidatedTx.
  simpl in *.
  case_match_concl;  auto;[].
  unfold balanceOfAcA in *.
  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *.
  1:{  simpl in *.
       rewrite balanceOfUpd.
       case_bool_decide; try lia.
  }
  specialize (Htx ltac:(auto)).
  rewrite pairEta.
  rewrite pairEta in Heqb. simpl in *.
  case_match_concl; simpl in *; try lia.
  {
    rewrite Heqb in Htx.
    lia.
  }
  {
    rewrite balanceOfRevertOther;auto.
  }
Qed.


Lemma execS2 s txlast:
  ((execValidatedTx s txlast)).2 = updateExtraState s.2 txlast.
Proof using.
  unfold execValidatedTx.
  repeat (case_match; try reflexivity).
Qed.


Lemma otherDelUndelDelegationStatusUnchanged s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    addrDelegated ((execValidatedTx s txlast)).1 addr
    = addrDelegated s.1 addr.
Proof.
  intros Hn.
  unfold execValidatedTx.
  case_match; auto.
  {
    simpl.
    rewrite addrDelegatedUnchangedByBalUpd. reflexivity.
  }
  rewrite pairEta. simpl in *.
  case_match;
    simpl in *.
  2:{
    rewrite revertTxDelegationUpdCore;auto;[].
    unfold addrsDelUndelByTx in *.
    (*
    resdec ltac:(set_solver). *)
    rewrite bool_decide_true;[| set_solver].
    rewrite bool_decide_false;[|set_solver].
    autorewrite with syntactic.
    reflexivity.
  }
  {
    pose proof (execTxDelegationUpdCore txlast s.1 ltac:(auto )addr) as Hd.
    revert Hd. rwHyps.
    simpl.
    intros.
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


Definition rbAfterTx s tx :=
  match reserveBalUpdateOfTx tx with
  | Some rb => rb
  | None => configuredReserveBalOfAddr s (sender tx)
  end.


Lemma configuredReserveBalOfAddrSpec s tx a:
  configuredReserveBalOfAddr (execValidatedTx s tx).2 a
  = if asbool (a=sender tx)
    then rbAfterTx s.2 tx
    else configuredReserveBalOfAddr s.2 a.
Proof.
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
  -> (configuredReserveBalOfAddr (execValidatedTx s tx).2 a
      =
        configuredReserveBalOfAddr s.2 a).
Proof using.
  intros Hn.
  rewrite configuredReserveBalOfAddrSpec.
  case_bool_decide; try congruence.
Qed.

Lemma isSCFalsePresExec l s tx:
  (forall txext, txext ∈ (tx::l) ->  txCannotCreateContractAtAddrs txext (map sender (tx::l)))
  -> (forall ac, ac ∈ (map sender (tx::l)) -> isSC s.1 ac = false)
  -> (forall ac, ac ∈ (map sender (tx::l)) -> isSC (execValidatedTx s tx).1 ac = false).
Proof using.
  intros Heoac Hsc.
  intros.
  pose proof (Hsc ac ltac:(set_solver)).
  specialize (Heoac tx ltac:(set_solver) s ac ltac:(set_solver) ltac:(assumption)).
  auto.
Qed.

(* end hide *)




(** This lemma combines many of the execution lemmas above to build a
    lower bound of the balance of any account after executing a transaction.
*)
Lemma execBalLb ac s tx:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let sf :=  (execValidatedTx s tx) in
  let ReserveBal := configuredReserveBalOfAddr s.2 ac in
  if (asbool (ac=sender tx)) then
    isSC sf.1 (sender tx) = false->
    (if isAllowedToEmpty s tx
     then balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx)
          \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
     else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx)))
  else
    if (isSC sf.1 ac)
    then True
    else (if addrDelegated (fst sf) ac then ReserveBal `min` (balanceOfAcA s ac) else balanceOfAcA s ac)
         <= (balanceOfAcA sf ac).
Proof using.
  simpl. intros.
  case_bool_decide; subst; auto; [apply execTxSenderBal; auto|].
  pose proof (execTxOtherBalanceLB tx s ltac:(auto) ac ltac:(auto)).
  pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s ac ltac:(auto)).
  destruct (isSC (execValidatedTx s tx).1 ac); auto;[].
  autorewrite with syntactic in *.
  case_match; lia.
Qed.

Open Scope Z_scope.

Hint Rewrite @updateKeyLkp3 : syntactic.


(** ** Order and monotonicity for [shallowExecTx] *)

(** We define a “≤” ordering relation on [ShallowExecRes] values of an account:
balances must be ≤ and the other fields must be equal. *)
Definition sresLe (r1 r2: ShallowExecRes) :=
  delegated r1 = delegated r2
  /\ balanceLb r1 <= balanceLb r2
  /\ configuredRB r1 = configuredRB r2.

(** this tells Coq to parse [l ≼ r] as [(sresLe l r)]*)
Notation "l ≼ r" := (sresLe l r) (at level 70).

(** Now we lift the above pointwise order to all accounts to define a “≤” relation on full results (of all accounts). Recall that the results are a pair where the first component is the fee-solvency boolean and the second component is the [ShallowExecRes] of each account. We only enforce the ≼ relation for the accounts that are in a given set of EOAs. [eoas] will later be instantiated to the list of all senders in the proposed sequence of transactions. *)
Definition resLe (eoas: list EvmAddr) (rb1 rb2: ShallowExecResults) :=
  (rb1.1 = true -> rb2.1= true) /\
  forall addr, addr ∈ eoas -> (rb1.2 addr) ≼ (rb2.2 addr).

(** * Reasoning principles for the shallow execution 

    Two generic themes appear repeatedly:

    - **Monotonicity.** If you start from a pointwise larger shallow map, one
      shallow step (and therefore the whole fold) keeps you pointwise larger.
      This is the heart of the “execute head, refine the budget, and the tail
      still passes” argument.

    - **Under‑approximation.** A single shallow step *under‑approximates* the
      effect of the real execution step on the quantities we guard in the
      execution check. This bridges Algorithm 1 (consensus) and 2 (execution).
*)

(** The helper relations above (e.g., [resLe]/[sresLe]) capture the
    pointwise orderings the monotonicity results use. *)
(*
Lemma rbLeImpl a b :
  a ≼ b ->
   a.1 = true
   -> b.1 = true.
Proof.
  intros Hr.
  hnf in Hr.
  tauto.
Qed.
 *)

(** One‑step monotonicity for the shallow execution of a transaction. Proof by unfolding definitions, case analysis, and arithmetic reasoning *)
Lemma mono (eoas: list EvmAddr) (rb1 rb2: ShallowExecResults) (tx: TxWithHdr) :
  sender tx ∈ eoas 
  -> resLe eoas rb1 rb2
  -> resLe eoas (shallowExecTx rb1 tx) (shallowExecTx rb2 tx).
Proof using.
  intros Hs Hrb.
  destruct Hrb as [Hrbl Hrb].
  unfold shallowExecTx.
  simpl.
  split.
  {
    simpl.
    intros Hand.
    autorewrite with iff in *.
    forward_reason.
    split; auto;[].
    specialize (Hrb _ Hs).
    hnf in Hrb.
    lia.
  }
  intros addr Hin.
  simpl.
  pose proof (Hrb addr Hin) as Hrba.
  unfold sresLe in Hrba.
  forward_reason.
  unfold sresLe. simpl.
  autorewrite with iff in *.
  split_and !; try sauto;[].
  rwHyps.
  case_match_concl; case_bool_decide_concl; sauto.
Qed.

(** monotonicity of shallow executing a list of transactions. proof by induction on [extension], using [mono]. *)
Lemma monoL (eoas: list EvmAddr) (rb1 rb2: ShallowExecResults) (extension: list TxWithHdr):
  map sender extension ⊆ eoas
  -> resLe eoas rb1 rb2
  -> resLe eoas (shallowExecTxL rb1 extension)
          (shallowExecTxL rb2 extension).
Proof using.
  revert rb1 rb2.
  induction extension; auto;[].
  unfold resLe in *.
  intros ? ?  Hs.
  simpl in *.
  split.
  {
    simpl.
    apply IHextension; auto;[set_solver | ].
    apply mono; auto. set_solver.
  }
  intros  addr Hin. simpl in *.
  apply IHextension;[set_solver | | set_solver].
  apply mono; auto.
  set_solver.
Qed.

Hint Rewrite configuredReserveBalOfAddrSpec addrDelegatedUnchangedByBalUpd: syntactic.

(** ** Under‑approximation for one head step.**

    [exec1] formalizes the intuition that one shallow step from the initial
    summary **under‑approximates** (w.r.t. balance) the effect of the real execution step on the
    quantities Algorithm 2 guards (protected slice for non‑senders and fee
    budget for the sender). This is the key bridge from consensus to execution.
*)
Lemma exec1 (tx: TxWithHdr) (extension: list TxWithHdr) (s: AugmentedState) :
  let sf := (execValidatedTx s tx) in
  maxTxFee tx <= balanceOfAc s.1 (sender tx)
  -> (∀ ac : EvmAddr, ac ∈ sender tx :: map sender extension → isSC sf.1 ac = false)
  -> resLe (map sender (tx::extension))
       (shallowExecTx (initialShallowExecResults s) tx)
       (initialShallowExecResults sf).
Proof using.
  intros ? Hfee Hscf.
  unfold initialShallowExecResults.
  split;[simpl; auto; fail|].
  intros ? Hin.
  unfold shallowExecTx, sresLe. simpl in *.
  split_and !; try sauto.
  { subst sf. simpl.
    rewrite execTxDelegationUpdDerived.
    reflexivity.
  }

  2:{
    rewrite configuredReserveBalOfAddrSpec.
    case_bool_decide; resdec congruence;[].
    subst. reflexivity.
  }

  (* core balanceLb goal *)
  pose proof (execBalLb addr s tx ltac:(lia)) as Hlb.
  rewrite execTxDelegationUpdDerived.
  simpl in Hlb. fold sf in Hlb.
  unfold isAllowedToEmpty, senderDelegatedAfterTx in Hlb.
  repeat rewrite execTxDelegationUpdDerived in Hlb.
  rewrite Hscf in Hlb;[|set_solver].
  rewrite Hscf in Hlb;[|set_solver].
  unfold balanceOfAcA in *.
  rewrite configuredReserveBalOfAddrSpec.
  autorewrite with syntactic.
  case_match_concl.
  { (*  delegatedAfterTx (addrDelegated s.1 addr) tx addr = true *)
    case_bool_decide_concl; resdec congruence; try lia.
    { (* addr <> sendr *)
      case_match; try lia.
    }
    {
      forward_reason.
      subst.
      rewrite Heqb in Hlb.
      simpl in *.
      unfold rbAfterTx.
      case_match_concl; try lia;[].
      (* addrDelegated s.1 (sender tx) = false *)
      assert (reserveBalUpdateOfTx tx = None) as Hn.
      {
        unfold reserveBalUpdateOfTx.
        unfold reserveBalUpdate.
        unfold delegatedAfterTx in *.
        simpl in *.
        autorewrite with iff in *.
        case_match; auto.
        applyToSomeHyp @isEmptyImpl.
        autorewrite with iff in *.
        forward_reason.
        rewrite autogenhypl in Heqb.
        set_solver.
      }
      rewrite Hn.
      lia.
    }

  }
  { (* delegatedAfterTx (addrDelegated s.1 addr) tx addr = false *)
    case_bool_decide_concl; resdec congruence; try lia.
    { case_match; try sauto. }
    subst. rewrite  Heqb in Hlb.
    simpl in *.
    forward_reason.
    case_match; lia.
  }
Qed.

(** * From one step to many

    Two small lemmas express that fee‑solvency of a *tail* implies fee‑solvency
    of a *prefix* (decreasingness), and lift that from one step to lists.
*)
Lemma decreasingRemTxSender (irb: ShallowExecResults) (txc: TxWithHdr):
  (shallowExecTx irb txc).1 = true
  -> irb.1 = true.
Proof using.
  simpl.
  intros Hp.
  autorewrite with iff in Hp.
  tauto.
Qed.

Lemma decreasingRemL irb  (nextL: list TxWithHdr):
  (shallowExecTxL irb nextL).1 = true
  -> irb.1 = true.
Proof using.
  revert  irb.
  induction nextL; simpl; [ auto; fail|].
  intros.
  pose proof (IHnextL (shallowExecTx irb a)).
  forward_reason.
  eapply decreasingRemTxSender; eauto.
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
Proof using.
  intros Hc.
  unfold consensusAcceptableTxs in *.
  simpl in *.
  unfold validateTx.
  autorewrite with iff.
  apply decreasingRemL in Hc.
  simpl in Hc.
  autorewrite with iff in Hc.
  case_match; try lia.
Qed.

(** This lemma says that you can execute the first tx in the proposed extension and the consensus checks would
    still hold on the resultant state for the remaining transactions in the proposal.
    This follows from [exec1] and [monoL]
*)
Lemma execPreservesConsensusChecks tx extension s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtAddrs txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> isSC s.1 ac = false)
  -> consensusAcceptableTxs s (tx::extension)
  -> consensusAcceptableTxs (execValidatedTx s tx) extension.
Proof using.
  intros Hfee Heoac Hsc.
  pose proof (isSCFalsePresExec _ _ _ Heoac Hsc) as Hscf.
  clear Heoac.
  set (sf:=(execValidatedTx s tx).1).
  intros Hc.
  simpl in *.
  hnf.
  hnf in Hc.
  forward_reason.
  simpl in *.
  revert Hc.
  pose proof (monoL (map sender (tx::extension))) as Hm.
  apply Hm; simpl in *;[set_solver |].
  clear Hm.
  apply exec1 with (extension := extension); auto.
Qed.

(** The two lemmas above combine to yield the following: *)
Lemma inductiveStep  (latestState : AugmentedState) (tx: TxWithHdr) (extension: list TxWithHdr) :
  maxTxFee tx <= balanceOfAc latestState.1 (sender tx)
  -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtAddrs txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> isSC latestState.1 ac = false)
 ->  consensusAcceptableTxs latestState (tx::extension)
  -> match execTx latestState tx with
     | None =>  False
     | Some si =>
         consensusAcceptableTxs si extension
     end.
Proof.
  intros Hext Heoac Hsc Hc.
  unfold execTx.
  intros.
  rewrite -> (execValidate tx extension) by assumption.
  simpl.
  apply execPreservesConsensusChecks in Hc; auto.
Qed.

Set Printing Coercions.

Lemma txCannotCreateContractAtAddrsMono tx l1 l2:
  l1 ⊆ l2
  -> txCannotCreateContractAtAddrs tx l2
  -> txCannotCreateContractAtAddrs tx l1.
Proof using.
  unfold txCannotCreateContractAtAddrs.
  intros Hs Hp.
  intros.
  apply Hp; auto.
Qed.

Lemma txCannotCreateContractAtAddrsTrimHead tx h l:
  txCannotCreateContractAtAddrs tx (h::l)
  -> txCannotCreateContractAtAddrs tx l.
Proof using.
  apply txCannotCreateContractAtAddrsMono.
  set_solver.
Qed.

(** * Proof of main theorem:
    Straightforward induction on [firstblock],
    with [inductiveStep] used in the inductive step.
*)

Lemma fullBlockStep  (latestState : AugmentedState) (firstblock restblocks: list TxWithHdr) :
  consensusAcceptableTxs latestState (firstblock++restblocks)
  -> (forall txext, txext ∈ (firstblock++restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (firstblock++restblocks)))
  -> (forall ac, ac ∈ (map sender (firstblock++restblocks)) -> isSC latestState.1 ac = false)
  -> match execTxs latestState firstblock with
     | None =>  False
     | Some si =>
         (* enough conditions to guarantee fee-solvency of block2, so that it can be extended and then this lemma reapplied *)
         consensusAcceptableTxs si restblocks
         /\ (forall ac, ac ∈ (map sender restblocks) -> isSC si.1 ac = false)
         /\ (forall txext, txext ∈ (restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (restblocks)))
     end.
Proof.
  intros Hacc.
  induction firstblock as [|hb1 firstblock IH] in latestState, Hacc |- *; simpl in *; auto.
  intros Heoa Hsc.
  change  ((hb1 :: firstblock) ++ restblocks) with (hb1::(firstblock++restblocks)) in Hacc.
  forward_reason.
  pose proof (execValidate _ _ _ Hacc) as Hv.
  unfold validateTx in Hv.
  autorewrite with iff in Hv.
  eapply inductiveStep in Hacc;  auto;[| lia].
  unfold execTx in *.
  destruct (validateTx latestState.1 hb1); simpl in *; try contradiction;[].
  pose proof (isSCFalsePresExec _ _ _ Heoa Hsc) as Hsci.
  remember (execValidatedTx latestState hb1) as si.
  simpl in *.
  pose proof (fun txext (p : txext ∈ firstblock ++ restblocks) =>
    txCannotCreateContractAtAddrsTrimHead _ _ _
      (Heoa txext (ltac:(set_solver)))) as Hcannot_tail.
  specialize (IH si Hacc Hcannot_tail).
  lapply IH; auto;[].
  intros.
  apply Hsci. set_solver.
Qed.

Print Assumptions fullBlockStep.
(** All assumptions of the proof:
[[

Section Variables:
K
: N
Axioms:
revertTxDelegationUpdCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := revertTx s tx) (ac : EvmAddr),
        addrDelegated sf ac =
        addrDelegated s ac && asbool (ac ∉ undels tx.1.2) || asbool (ac ∈ dels tx.1.2)
revertTx : StateOfAccounts → TxWithHdr → StateOfAccounts
execTxSenderBalCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    (maxTxFee tx ≤ balanceOfAc s (sender tx))%N
    → reserveBalUpdateOfTx tx = None
      → let sf := (evmExecTxCore s tx).1 in
        senderDelegatedAfterTx s tx = false
        → balanceOfAc sf (sender tx) = (balanceOfAc s (sender tx) - (maxTxFee tx + value tx))%N
          ∨ balanceOfAc sf (sender tx) = (balanceOfAc s (sender tx) - maxTxFee tx)%N
execTxDelegationUpdCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := (evmExecTxCore s tx).1) (ac : EvmAddr),
        addrDelegated sf ac =
        addrDelegated s ac && asbool (ac ∉ undels tx.1.2) || asbool (ac ∈ dels tx.1.2)
execTxCannotDebitNonDelegatedNonContractAccountsCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := (evmExecTxCore s tx).1) (ac : EvmAddr),
        ac ≠ sender tx
        → addrDelegated sf ac || isSC sf ac = false
          → (balanceOfAc s ac ≤ balanceOfAc sf ac)%N
evmExecTxCore : StateOfAccounts → TxWithHdr → StateOfAccounts * list EvmAddr
changedAccountSetSound :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → let (sf, changedAccounts) := evmExecTxCore s tx in
      ∀ ac : EvmAddr, ac ∉ changedAccounts → sf ac = s ac
balanceOfRevertSender :
  ∀ (s : StateOfAccounts) (tx : TxWithHdr),
    (maxTxFee tx ≤ balanceOfAc s (sender tx))%N
    → reserveBalUpdateOfTx tx = None
      → balanceOfAc (revertTx s tx) (sender tx) = (balanceOfAc s (sender tx) - maxTxFee tx)%N
balanceOfRevertOther :
  ∀ (s : StateOfAccounts) (tx : TxWithHdr) (ac : EvmAddr),
    reserveBalUpdateOfTx tx = None
    → ac ≠ sender tx → balanceOfAc (revertTx s tx) ac = balanceOfAc s ac


]]
 *)


Corollary fullBlockStep2  (latestState : AugmentedState) (blocks: list TxWithHdr) :
  (forall ac, ac ∈ (map sender (blocks)) -> isSC latestState.1 ac = false)
  -> (forall txext, txext ∈ (blocks) ->  txCannotCreateContractAtAddrs txext (map sender (blocks)))
  -> consensusAcceptableTxs latestState (blocks)
  -> match execTxs latestState blocks with
     | None =>  False
     | Some si => True
     end.
Proof.
  intros.
  pose proof (fullBlockStep latestState blocks []) as Hf.
  autorewrite with syntactic in Hf.
  specialize (Hf ltac:(auto) ltac:(auto) ltac:(auto)).
  case_match; auto.
Qed.


Lemma acceptableNil lastConsensedState:
  consensusAcceptableTxs lastConsensedState [].
Proof using.
  unfold consensusAcceptableTxs.
  intros.
  simpl.
  reflexivity.
Qed.

(* Consensus invariant and how its steps preserve the invariant.
At any given time, consensus has some [latestConsensedState] and a list of transactions/blocks (say [ltx]) proposed on top of that.
The main invariant it maintains is [consensusAcceptableTxs latestConsensedState ltx].
There are also side conditions like [blockNumsInRange ltx] and that the transactions in [ltx] are not sent to an address that has code: the latter is just a formal assumption in Coq but is guaranteed by the cryptographic hardness of generating private keys.

This invariant needs to be preserved on the two main steps of consensus:
- extend [ltx] with a new block of transactions, and
- once execution catches up to the next block, remove a prefix of [ltx] that corresponds to the block whose execution results are now available.

The lemma [fullBlockStep] is exactly what is needed to preserve the invariant at the latter step.
To preserve the invariant at the first step, the proposed new txs (e.g., grabbed from the mempool) need to be checked so that they satisfy the [consensusAcceptableTxs] property.

 *)

(*
Below is an illustration of how the blockchain evolves starting from the genesis block b0.
It assumes an oracle nextBlockPicker that picks the next block while satisfying the conditions.

 *)

(* begin hide *)
Section consensusInvariantsAndPreservation.
  Variable b0: list TxWithHdr.
  Variable sb0 : AugmentedState. (* state after b0 *)
  Definition cannotCreateCodeAtSenderAddrs ltx := ∀ txext : TxWithHdr,
   txext ∈ ltx
   → txCannotCreateContractAtAddrs txext (map sender ltx).
  Hypothesis b0csa: cannotCreateCodeAtSenderAddrs b0.

  Hypothesis nextBlockPicker:
    forall (lastConsensedState: AugmentedState) (proposedTxs: (list TxWithHdr)),
      consensusAcceptableTxs lastConsensedState proposedTxs
      -> cannotCreateCodeAtSenderAddrs proposedTxs
      -> (∀ ac : EvmAddr, ac ∈ map sender proposedTxs → isSC lastConsensedState.1 ac = false)
      -> exists nextBlock,
          consensusAcceptableTxs lastConsensedState (proposedTxs++nextBlock)
          /\ cannotCreateCodeAtSenderAddrs (proposedTxs++nextBlock)
          /\ (∀ ac : EvmAddr, ac ∈ map sender (proposedTxs++nextBlock) → isSC lastConsensedState.1 ac = false).
  Open Scope N_scope.

  (** The statement below is of course unprovable. But the proof script illustrates how the state of the consensus module evolves from the genesis block b0, showing how the two steps are taken and how they preserve the invariants. At every point, the proof context (hypotheses) asserts that the invariants are satisfied for the latest consensed block and the proposal so far. The script itself is not useful to see; the Coq goal at every step is the illuminating part.
   *)

  Lemma operation  : False.
    intros.
    revert nextBlockPicker.
    rwHyps.
    intros.
    (** now we invoke the oracle to pick the next block after b0 *)
    pose proof (nextBlockPicker sb0 []  (acceptableNil _) ltac:(set_solver) ltac:(set_solver)) as b1.
    destruct b1 as [b1 b1ok].
    simpl in b1ok.
    forward_reason.
    (** now we invoke the oracle to pick the next block after b1 *)
    pose proof (nextBlockPicker sb0 b1 ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b2.
    destruct b2 as [b2 b2ok].
    forward_reason.
    unfold cannotCreateCodeAtSenderAddrs in *.
    apply fullBlockStep in b2okl; auto.
    (** assuming K=2, we wait for execution to execute b1 and give us the new state sb1  *)
    destruct (execTxs sb0 b1) as [sb1 ?|]; auto.
    forward_reason.
    (** now we pick the new block b3, but with the latestConsensedState of sb1 rather than sb0 *)
    pose proof (nextBlockPicker sb1 b2 ltac:(assumption) ltac:(assumption) ltac:(assumption) )  as b3.
    destruct b3 as [b3 b3ok].
    forward_reason.
    apply fullBlockStep in b3okl; auto.
    (** we wait for execution to execute b2 and give us the new state sb2  *)
    destruct (execTxs sb1 b2) as [sb2 ?|]; auto;[].
    forward_reason.
    (** now we pick the new block b3, but with the latestConsensedState of sb2 rather than sb1 *)
    pose proof (nextBlockPicker sb2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b4.
 Abort.
End consensusInvariantsAndPreservation.
(* end hide *)

(* consensus: both new and old will accept
   execution: only old will unnecessarily revert tx4

Alice 100, undelegated, reservebal =5
tx1: sender Alice, delegates Alice, value 10, fee 1
tx2: Bob sends to Alice, Alice balance debited by 20.
tx3: sender Alice, undelegates Alice, value 0, fee 1
tx4: sender Alice, value 67, fee 1
*)

(*
AA: balance 10
reservebal:=5
newtx: value 1, fee 6
undelegated: accepted
delegated: rejected
*)

(* accepted in new, not in old
Alice: bal 100, reserve 5, undelegated
tx1: alice, fee 6, value 1
tx2: alice, fee 6, value 1
 *)


(* old consensus accept, new reject
   old execution: unexpected revert possible,  
Alice: bal 100, reserve 5, undelegated
tx1: alice, fee 6, value 1
93 min 5=5
balanceLb := 93
tx2: alice, fee 2, value 92
balanceLb := 0
 *)


(* 
Alice: bal 100, reserve 5, undelegated
tx1: alice, fee 6, value 1
93 min 5=5
balanceLb := 93
tx2: alice, fee 6, value 1
balanceLb := 0
 *)
