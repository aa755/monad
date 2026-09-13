Require Import EVMOpSem.block.
Require Import stdpp.gmap.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.reservebalold.
Require Import Lens.Elpi.Elpi.
Require Import Lens.Lens.
#[local] Open Scope lens_scope.

Module evm.
  Definition log_entry: Type := EVMOpSem.evm.log_entry.
  Definition address: Type := EvmAddr.
  Definition account_state: Type (* TODO: investigate why Set doesnt work here *) := AccountM.

  (*
  #[global] Instance : EqDecision address. Proof. Admitted.
   #[global] Instance : Countable address. Proof. Admitted.
*)
  
  Definition GlobalState := gmap address account_state. (* EVMOpSem defines it as a function type which can cause hassles for computation and for separation logic reasoning *)
End evm.

(* delete and inline? 
Definition sender (t:Transaction) : evm.address:= (tr_from t.1).
 *)
Definition execTxCore'  (s: StateOfAccounts) (t: TxWithHdr): EvmExecResult.
Admitted. (* To be provided by an appropriate EVM semantics *)

(* similar to what execute_final does *)
Definition applyGasRefundsAndRewards (hdr: BlockHeader) (s: StateOfAccounts) (t: TxResult): StateOfAccounts. Admitted.

(* txindex can be used to store incarnation numbers *)
Definition execTxCore (s: StateOfAccounts) (t: TxWithHdr): EvmExecResult :=
  let r := execTxCore' s t in
  {|
    postState :=  applyGasRefundsAndRewards t.2 (postState r) (receipt r);
    receipt := receipt r;
    changedAccounts := changedAccounts r;
    codeExecAccounts := codeExecAccounts r
  |}.

Definition revertTx  (s: StateOfAccounts) (t: TxWithHdr): (StateOfAccounts * TxResult).
Admitted. (* To be provided by an appropriate EVM semantics *)

Definition ConsensusLookahead : N := 3.
Definition execTxs := execTxs ConsensusLookahead execTxCore revertTx.
Definition execTx := execTx ConsensusLookahead execTxCore revertTx.

(*
      Lemma stateAfterTransactionsC' (hdr: BlockHeader) (s: StateOfAccounts) (c: Transaction) (ts: list Transaction) (start:nat) (prevResults: list TxResult):
        stateAfterTransactions' hdr s (ts++[c]) start prevResults
        = let '(sf, prevs) := stateAfterTransactions' hdr s (ts) start prevResults in
          let '(sff, res) := stateAfterTransaction hdr (length ts+start) sf c in
          (sff, prevs ++ [res]).
      Proof using.
        revert s.
        revert start.
        revert prevResults.
        induction ts;[reflexivity|].
        intros. simpl.
        destruct (stateAfterTransaction hdr start s a).
        simpl.
        rewrite IHts.
        repeat f_equiv.
        rewrite <- Nat.add_succ_r.
        reflexivity.
      Qed.

      
      Lemma stateAfterTransactionsC (hdr: BlockHeader) (s: StateOfAccounts) (c: Transaction) (ts: list Transaction):
        stateAfterTransactions hdr s (ts++[c])
        = let '(sf, prevs) := stateAfterTransactions hdr s (ts) in
          let '(sff, res) := stateAfterTransaction hdr (length ts) sf c in
          (sff, prevs ++ [res]).
      Proof using.
        setoid_rewrite stateAfterTransactionsC'.
        repeat rewrite <- plus_n_O.
        reflexivity.
      Qed.
      Lemma  rect_len g l lt h bs : (g, l) = stateAfterTransactions h bs lt ->
                                    length l = length lt.
      Proof using. Admitted. (* easy *)
      *)
Record Withdrawal:=
  {
    recipient: evm.address;
    value_wei: N;
  }.

Record Block :=
  {
    transactions: list Transaction;
    header: BlockHeader;
    ommers: list BlockHeader;
    withdrawals: option (list Withdrawal);
  }.

Definition applyWithdrawals (s: AugmentedState) (ws: option (list Withdrawal)): AugmentedState.
Proof. Admitted.

Definition applyBlockReward (s: AugmentedState) (num_omsers: nat): AugmentedState.
Proof. Admitted.

(*
Definition stateAfterBlock (b: Block) (s: StateOfAccounts): StateOfAccounts * list TxResult :=
  let '(s, tr) := execTxs (header b) s (transactions b) in
  let s:= applyWithdrawals s (withdrawals b) in
  (applyBlockReward s (length (ommers b)), tr).
 *)

(* Coq model of the Chain type in C++ *)
Record Chain := {
    chainid: N
  }.
Inductive Revision := Shanghai | Frontier.

Definition dummyEvmState: evm.GlobalState. Proof. Admitted.
Definition stateRoot (b: evm.GlobalState) : N. Proof. Admitted.
Definition receiptRoot (b: list TxResult) : N. Proof. Admitted.
Definition transactionsRoot (b: Block) : N. Proof. Admitted.
Definition withdrawalsRoot (b: Block) : N. Proof. Admitted.



(** [ConsensusBlockHeader] is a model type of the C++ struct `MonadConsensusBlockHeader`.
This struct has many fields and the Db probably stores all of them.
But one struct field: `uint64_t round` is special as the Db uses round numbers to make decisions
For now we just model this field. 
 *)
Record ConsensusBlockHeader :=
  {
    roundNum: N; (* models `uint64_t round` *)
    (* TODO: add more fields, to model the following C++ fields
       uint64_t epoch{0};
       MonadQuorumCertificate qc{};
       byte_string_fixed<33> author{};
       uint64_t seqno{0};
       uint128_t timestamp_ns{0};
       byte_string_fixed<96> round_signature{};
       std::vector<BlockHeader> delayed_execution_results{};
       BlockHeader execution_inputs{};
     *)
  }.


(*
Definition txMaxFee (t: Transaction) : N. Proof. Admitted.
*)


Opaque Zdigits.binary_value Zdigits.Z_to_binary.
Opaque w256_to_Z.
Opaque Z_to_w256.

(*
Definition balanceOfAc (s: evm.GlobalState) (a: evm.address) : N (* 0 if account does not exist *) :=
  match s !! a with
  | Some ac => balance ac
  | None => 0
  end.
  *)  

Definition txsWithHdr (b: Block) : list TxWithHdr :=
  map (fun t => (t, header b)) (transactions b).
  
Definition stateAfterBlockV (b: Block) (s: AugmentedState): option (AugmentedState * list TxResult) :=
  match execTxs s (txsWithHdr b) with
  | None => None
  | Some (s, tr) =>
      let s:= applyWithdrawals s (withdrawals b) in
      Some (applyBlockReward s (length (ommers b)), tr)
  end.

(*
Open Scope N_scope.
Fixpoint totalTxFees (lt: list Transaction): gmap evm.address N :=
  match lt with
  | t::tl => 
      let r:= totalTxFees tl in
      let feesr := r !!!  (sender t) in 
      <[ sender t := feesr + txMaxFee t]> r
  | [] => ∅
  end.
*)



Open Scope N_scope.

Definition defaultW160: word160.word160.
  constructor; auto.
  exact false. exact [].
Defined.

Definition progDefault: program :=
   {| program_content := λ _ : Z, None; program_length := 0 |}.

Definition block_account_default :=
{|
  block_account_address := defaultW160;
  block_account_storage := storage_default;
  block_account_code := progDefault;
  block_account_balance := w256_default;
  block_account_nonce := w256_default;
  block_account_exists := coqharness.bool_default;
  block_account_hascode := coqharness.bool_default
|}.

Definition dummyAc : AccountM
  := Build_AccountM block_account_default (Build_Indices 0 0) [] 0.

(*
Print Assumptions dummyAc. (* closed under global context *)
*)
