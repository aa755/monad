Require Import skylabs.auto.cpp.proof.
Require Import stdpp.gmap.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.

Import linearity.
Set Warnings "+sl-impossible-patterns".
Unset SsrIdents.
Import evmmisc.
Import exec_specs.

#[local] Open Scope N_scope.

(* Generic sender-side rewrite lemmas used by the reserve-balance proofs. *)
Lemma update_assum_exactness_at_id
  (addr : evm.address)
  (m : MapModel evm.address AssumedPreTxAccountState) :
  update_assum_exactness_at addr (fun ex => ex) m = m.
Proof.
  induction m as [|[addr' [loc aps]] tl IH]; simpl; [reflexivity|].
  unfold update_assum_exactness_at in *; simpl in *.
  destruct (bool_decide (addr' = addr)); simpl.
  - destruct aps; simpl. now rewrite IH.
  - now rewrite IH.
Qed.

Lemma check_min_original_balance_update_eq_update_assum_exactness_map_insert
  (m : MapModel evm.address AssumedPreTxAccountState)
  (updates : gmap evm.address AssumptionExactness)
  (addr : evm.address)
  (max_reserve : N)
  (loc : ptr)
  (aps : AssumedPreTxAccountState) :
  NoDup (map fst (update_assum_exactness_map m updates)) ->
  mapModelLookup (update_assum_exactness_map m updates) addr = Some (loc, aps) ->
  check_min_original_balance_update (update_assum_exactness_map m updates) addr max_reserve =
  update_assum_exactness_map m
    (<[addr := min_balance_update (assumExactness aps)
                 (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                 (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                 max_reserve]> updates).
Proof.
  intros Hnodup Hlookup.
  pose proof
    (update_assum_exactness_at_check_min_original_balance_update_to_map
       m updates addr max_reserve (fun ex => ex) loc aps Hnodup Hlookup) as Hmap.
  rewrite update_assum_exactness_at_id in Hmap.
  simpl in Hmap.
  exact Hmap.
Qed.

Lemma state_original_payloads_check_min_rewrite
  (thread_info : biIndex)
  (_Σ : gFunctors)
  (Sigma : cpp_logic thread_info _Σ)
  (CU : genv)
  (statep : ptr)
  (tykey tyval : type)
  (krep : Qp -> evm.address -> Rep)
  (vrep : Qp -> AssumedPreTxAccountState -> Rep)
  (m : MapModel evm.address AssumedPreTxAccountState)
  (updates : gmap evm.address AssumptionExactness)
  (addr : evm.address)
  (max_reserve : N)
  (loc : ptr)
  (aps : AssumedPreTxAccountState) :
  NoDup (map fst (update_assum_exactness_map m updates)) ->
  mapModelLookup (update_assum_exactness_map m updates) addr = Some (loc, aps) ->
  (statep ,, o_field CU "monad::State::original_"
   |-> AnkerMapPayloadsR tykey tyval krep vrep 1
         (check_min_original_balance_update (update_assum_exactness_map m updates) addr max_reserve)) =
  (statep ,, o_field CU "monad::State::original_"
   |-> AnkerMapPayloadsR tykey tyval krep vrep 1
         (update_assum_exactness_map m
            (<[addr := min_balance_update (assumExactness aps)
                         (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                         (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                         max_reserve]> updates))).
Proof.
  intros Hnodup Hlookup.
  rewrite
    (check_min_original_balance_update_eq_update_assum_exactness_map_insert
       m updates addr max_reserve loc aps Hnodup Hlookup).
  reflexivity.
Qed.

Lemma state_original_spine_check_min_rewrite
  (thread_info : biIndex)
  (_Σ : gFunctors)
  (Sigma : cpp_logic thread_info _Σ)
  (CU : genv)
  (statep : ptr)
  (tykey tyval : type)
  (khash : evm.address -> N)
  (krep : Qp -> evm.address -> Rep)
  (m : MapModel evm.address AssumedPreTxAccountState)
  (updates : gmap evm.address AssumptionExactness)
  (addr : evm.address)
  (max_reserve : N)
  (loc : ptr)
  (aps : AssumedPreTxAccountState) :
  NoDup (map fst (update_assum_exactness_map m updates)) ->
  mapModelLookup (update_assum_exactness_map m updates) addr = Some (loc, aps) ->
  (statep ,, o_field CU "monad::State::original_"
   |-> AnkerMapSpineR tykey tyval khash krep 1
         (map (fun '(a, (b3, _)) => (a, b3))
            (check_min_original_balance_update (update_assum_exactness_map m updates) addr max_reserve))) =
  (statep ,, o_field CU "monad::State::original_"
   |-> AnkerMapSpineR tykey tyval khash krep 1
         (map (fun '(a, (b3, _)) => (a, b3))
            (update_assum_exactness_map m
               (<[addr := min_balance_update (assumExactness aps)
                            (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                            (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                            max_reserve]> updates)))).
Proof.
  intros Hnodup Hlookup.
  rewrite
    (check_min_original_balance_update_eq_update_assum_exactness_map_insert
       m updates addr max_reserve loc aps Hnodup Hlookup).
  reflexivity.
Qed.

Lemma state_original_check_min_rewrite_both_from_ctx
  (thread_info : biIndex)
  (_Σ : gFunctors)
  (Sigma : cpp_logic thread_info _Σ)
  (CU : genv)
  (statep : ptr)
  (tykey tyval : type)
  (khash : evm.address -> N)
  (krep : Qp -> evm.address -> Rep)
  (vrep : Qp -> AssumedPreTxAccountState -> Rep)
  (m : MapModel evm.address AssumedPreTxAccountState)
  (updates : gmap evm.address AssumptionExactness)
  (addr : evm.address)
  (max_reserve : N) :
  NoDup
    (map (fun x : evm.address * (ptr * AssumedPreTxAccountState) =>
            (let '(a, (b, _)) := x in (a, b)).1)
         (update_assum_exactness_map m updates)) ->
  is_Some (mapModelLookup (update_assum_exactness_map m updates) addr) ->
  exists (loc : ptr) (aps : AssumedPreTxAccountState),
    mapModelLookup (update_assum_exactness_map m updates) addr = Some (loc, aps) /\
    let updates' :=
      <[addr := min_balance_update (assumExactness aps)
                   (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                   (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                   max_reserve]> updates in
    (statep ,, o_field CU "monad::State::original_"
     |-> AnkerMapPayloadsR tykey tyval krep vrep 1
           (check_min_original_balance_update (update_assum_exactness_map m updates) addr max_reserve)) =
    (statep ,, o_field CU "monad::State::original_"
     |-> AnkerMapPayloadsR tykey tyval krep vrep 1
           (update_assum_exactness_map m updates')) /\
    (statep ,, o_field CU "monad::State::original_"
     |-> AnkerMapSpineR tykey tyval khash krep 1
           (map (fun '(a, (b3, _)) => (a, b3))
              (check_min_original_balance_update (update_assum_exactness_map m updates) addr max_reserve))) =
    (statep ,, o_field CU "monad::State::original_"
     |-> AnkerMapSpineR tykey tyval khash krep 1
           (map (fun '(a, (b3, _)) => (a, b3))
              (update_assum_exactness_map m updates'))).
Proof.
  intros Hnodup_ctx Hsome.
  destruct Hsome as [[loc aps] Hlookup].
  exists loc, aps.
  split; [exact Hlookup|].
  set (updates' :=
    <[addr := min_balance_update (assumExactness aps)
                 (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                 (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
                 max_reserve]> updates).
  assert (Hnodup_fst : NoDup (map fst (update_assum_exactness_map m updates))).
  {
    eapply nodup_map_fst_update_assum_exactness_map.
    exact Hnodup_ctx.
  }
  split.
  - subst updates'.
    eapply state_original_payloads_check_min_rewrite; eauto.
  - subst updates'.
    eapply state_original_spine_check_min_rewrite; eauto.
Qed.

Lemma map_key_ptr_check_min_to_insert_sender
  (ctx : MonadChainContext)
  (stm : StateM)
  (tx : TxWithHdr)
  (updates : _)
  (nthElemVstackTop : UpdatedAccountState)
  (x0 : AssumedPreTxAccountState) :
  update_assum_exactness_at (sender tx)
    (fun ex : AssumptionExactness =>
       min_balance_update ex
         (original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
         (balanceOfAccount (postTxState nthElemVstackTop))
         (DefReserve
          `min`
          original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
          (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (base_fee_per_gas (cblock ctx)))
            `mod` 2 ^ 256))
    (check_min_original_balance_update
       (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve) =
  update_assum_exactness_map (preTxAssumedState stm)
    (<[sender tx :=
        (fun ex : AssumptionExactness =>
           min_balance_update ex
             (original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
             (balanceOfAccount (postTxState nthElemVstackTop))
             (DefReserve
              `min`
              original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
              (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (base_fee_per_gas (cblock ctx)))
                `mod` 2 ^ 256))
         (min_balance_update (assumExactness x0)
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            DefReserve)]> updates) ->
  map (fun p => let '(a, (b, _)) := p in (a, b))
    (check_min_original_balance_update
       (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve) =
  map (fun p => let '(a, (b, _)) := p in (a, b))
    (update_assum_exactness_map (preTxAssumedState stm)
       (<[sender tx :=
           min_balance_update
             (min_balance_update (assumExactness x0)
                (original_balance_pessimistic_model_map
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                (original_balance_pessimistic_model_map
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                DefReserve)
             (original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
             (balanceOfAccount (postTxState nthElemVstackTop))
             (DefReserve
              `min`
              original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
              (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (base_fee_per_gas (cblock ctx)))
                `mod` 2 ^ 256)]> updates)).
Proof.
  intro H1.
  rewrite <- (map_key_ptr_update_assum_exactness_at
                (check_min_original_balance_update
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve)
                (sender tx)
                (fun ex : AssumptionExactness =>
                   min_balance_update ex
                     (original_balance_pessimistic_model_map
                        (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                     (balanceOfAccount (postTxState nthElemVstackTop))
                     (DefReserve
                      `min`
                      original_balance_pessimistic_model_map
                        (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
                      (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (base_fee_per_gas (cblock ctx)))
                        `mod` 2 ^ 256))).
  rewrite H1.
  reflexivity.
Qed.

Lemma mapModelLookup_match_preTxState_update_assum_exactness_at
  (m : _)
  (addr : _)
  (f : AssumptionExactness -> AssumptionExactness)
  (P : _ -> Prop) :
  (match mapModelLookup m addr with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end) ->
  (match mapModelLookup (update_assum_exactness_at addr f m) addr with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end).
Proof.
  revert P.
  induction m as [|[addr' [loc aps]] tl IH]; intros P H; simpl in *.
  { exact H. }
  {
    destruct (decide (addr' = addr)) as [Heq|Hneq].
    {
      subst addr'.
      assert (Hlookup0 :
        mapModelLookup ((addr, (loc, aps)) :: tl) addr = Some (loc, aps)).
      {
        unfold mapModelLookup; simpl.
        rewrite lookup_insert.
        cbn.
        destruct (decide (addr = addr)) as [_ | Hcontra].
        2:{ contradiction Hcontra; reflexivity. }
        reflexivity.
      }
      rewrite Hlookup0 in H.
      simpl in H.
      assert (Hlookup1 :
        mapModelLookup (update_assum_exactness_at addr f ((addr, (loc, aps)) :: tl)) addr =
        Some (loc, {| preTxState := preTxState aps;
                      preTxStorage := preTxStorage aps;
                      assumExactness := f (assumExactness aps) |})).
      {
        unfold mapModelLookup, update_assum_exactness_at; simpl.
        rewrite (bool_decide_eq_true_2 (addr = addr)).
        2:{ reflexivity. }
        simpl.
        rewrite lookup_insert.
        cbn.
        destruct (decide (addr = addr)) as [_ | Hcontra].
        2:{ contradiction Hcontra; reflexivity. }
        reflexivity.
      }
      rewrite Hlookup1.
      simpl.
      exact H.
    }
    {
      assert (Hlookup0 :
        mapModelLookup ((addr', (loc, aps)) :: tl) addr = mapModelLookup tl addr).
      {
        unfold mapModelLookup; simpl.
        rewrite lookup_insert_ne.
        { reflexivity. }
        { intro Heq. apply Hneq. exact Heq. }
      }
      rewrite Hlookup0 in H.
      assert (Hlookup1 :
        mapModelLookup (update_assum_exactness_at addr f ((addr', (loc, aps)) :: tl)) addr =
        mapModelLookup (update_assum_exactness_at addr f tl) addr).
      {
        unfold mapModelLookup, update_assum_exactness_at; simpl.
        rewrite (bool_decide_eq_false_2 (addr' = addr)).
        2:{ exact Hneq. }
        simpl.
        rewrite lookup_insert_ne.
        { reflexivity. }
        { intro Heq. apply Hneq. exact Heq. }
      }
      rewrite Hlookup1.
      eapply IH.
      exact H.
    }
  }
Qed.

Lemma mapModelLookup_match_preTxState_update_assum_exactness_at_rw
  (m : _)
  (addr : _)
  (f : AssumptionExactness -> AssumptionExactness)
  (P : _ -> Prop) :
  (match mapModelLookup (update_assum_exactness_at addr f m) addr with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end) =
  (match mapModelLookup m addr with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end).
Proof.
  induction m as [|[addr' [loc aps]] tl IH]; simpl.
  { reflexivity. }
  {
    destruct (decide (addr' = addr)) as [Heq|Hneq].
    {
      subst addr'.
      unfold mapModelLookup; simpl.
      rewrite lookup_insert.
      unfold update_assum_exactness_at; simpl.
      rewrite (bool_decide_eq_true_2 (addr = addr)).
      2:{ reflexivity. }
      simpl.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_ | Hcontra].
      2:{ contradiction Hcontra; reflexivity. }
      reflexivity.
    }
    {
      unfold mapModelLookup; simpl.
      unfold update_assum_exactness_at; simpl.
      rewrite (bool_decide_eq_false_2 (addr' = addr)).
      2:{ exact Hneq. }
      simpl.
      rewrite lookup_insert_ne.
      2:{ intro Heq. apply Hneq. exact Heq. }
      rewrite lookup_insert_ne.
      2:{ intro Heq. apply Hneq. exact Heq. }
      exact IH.
    }
  }
Qed.

Lemma mapModelLookup_update_assum_exactness_at_eq
  (m : _)
  (addr : _)
  (f : AssumptionExactness -> AssumptionExactness) :
  mapModelLookup (update_assum_exactness_at addr f m) addr =
  match mapModelLookup m addr with
  | Some (loc, aps) =>
      Some (loc, {| preTxState := preTxState aps;
                    preTxStorage := preTxStorage aps;
                    assumExactness := f (assumExactness aps) |})
  | None => None
  end.
Proof.
  induction m as [|[addr' [loc aps]] tl IH]; simpl.
  { reflexivity. }
  {
    destruct (decide (addr' = addr)) as [Heq|Hneq].
    {
      subst addr'.
      unfold mapModelLookup; simpl.
      rewrite lookup_insert.
      unfold update_assum_exactness_at; simpl.
      rewrite (bool_decide_eq_true_2 (addr = addr)).
      2:{ reflexivity. }
      simpl.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_ | Hcontra].
      2:{ contradiction Hcontra; reflexivity. }
      reflexivity.
    }
    {
      unfold mapModelLookup; simpl.
      unfold update_assum_exactness_at; simpl.
      rewrite (bool_decide_eq_false_2 (addr' = addr)).
      2:{ exact Hneq. }
      simpl.
      rewrite lookup_insert_ne.
      2:{ intro Heq. apply Hneq. exact Heq. }
      rewrite lookup_insert_ne.
      2:{ intro Heq. apply Hneq. exact Heq. }
      exact IH.
    }
  }
Qed.

Lemma sender_match_after_insert
  (ctx : MonadChainContext)
  (stm : StateM)
  (tx : TxWithHdr)
  (updates : _)
  (nthElemVstackTop : UpdatedAccountState)
  (x0 : AssumedPreTxAccountState)
  (P : _ -> Prop) :
  update_assum_exactness_at (sender tx)
    (fun ex : AssumptionExactness =>
       min_balance_update ex
         (original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
         (balanceOfAccount (postTxState nthElemVstackTop))
         (DefReserve
          `min`
          original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
          (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
            `mod` 2 ^ 256))
    (check_min_original_balance_update
       (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve) =
  update_assum_exactness_map (preTxAssumedState stm)
    (<[sender tx :=
        (fun ex : AssumptionExactness =>
           min_balance_update ex
             (original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
             (balanceOfAccount (postTxState nthElemVstackTop))
             (DefReserve
              `min`
              original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
              (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
                `mod` 2 ^ 256))
         (min_balance_update (assumExactness x0)
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            DefReserve)]> updates) ->
  (match
     mapModelLookup
       (check_min_original_balance_update
          (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve)
       (sender tx)
   with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end) ->
  (match
     mapModelLookup
       (update_assum_exactness_map (preTxAssumedState stm)
          (<[sender tx :=
              min_balance_update
                (min_balance_update (assumExactness x0)
                   (original_balance_pessimistic_model_map
                      (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                   (original_balance_pessimistic_model_map
                      (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                   DefReserve)
                (original_balance_pessimistic_model_map
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                (balanceOfAccount (postTxState nthElemVstackTop))
                (DefReserve
                 `min`
                 original_balance_pessimistic_model_map
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
                 (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
                   `mod` 2 ^ 256)]> updates))
       (sender tx)
   with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end).
Proof.
  intros H1 Hpreadd.
  rewrite <- H1.
  eapply mapModelLookup_match_preTxState_update_assum_exactness_at.
  exact Hpreadd.
Qed.

Lemma sender_lookup_after_insert_rewrite
  (ctx : MonadChainContext)
  (stm : StateM)
  (tx : TxWithHdr)
  (updates : gmap evm.address AssumptionExactness)
  (nthElemVstackTop : UpdatedAccountState)
  (x0 : AssumedPreTxAccountState) :
  update_assum_exactness_at (sender tx)
    (fun ex : AssumptionExactness =>
       min_balance_update ex
         (original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
         (balanceOfAccount (postTxState nthElemVstackTop))
         (DefReserve
          `min`
          original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
          (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
            `mod` 2 ^ 256))
    (check_min_original_balance_update
       (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve) =
  update_assum_exactness_map (preTxAssumedState stm)
    (<[sender tx :=
        (fun ex : AssumptionExactness =>
           min_balance_update ex
             (original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
             (balanceOfAccount (postTxState nthElemVstackTop))
             (DefReserve
              `min`
              original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
              (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
                `mod` 2 ^ 256))
         (min_balance_update (assumExactness x0)
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            DefReserve)]> updates) ->
  mapModelLookup
    (update_assum_exactness_map (preTxAssumedState stm)
       (<[sender tx :=
           min_balance_update
             (min_balance_update (assumExactness x0)
                (original_balance_pessimistic_model_map
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                (original_balance_pessimistic_model_map
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                DefReserve)
             (original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
             (balanceOfAccount (postTxState nthElemVstackTop))
             (DefReserve
              `min`
              original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
              (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
                `mod` 2 ^ 256)]> updates))
    (sender tx) =
  mapModelLookup
    (update_assum_exactness_at (sender tx)
       (fun ex : AssumptionExactness =>
          min_balance_update ex
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            (balanceOfAccount (postTxState nthElemVstackTop))
            (DefReserve
             `min`
             original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
             (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
               `mod` 2 ^ 256))
       (check_min_original_balance_update
          (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve))
    (sender tx).
Proof.
  intro H1.
  rewrite <- H1.
  reflexivity.
Qed.

Lemma sender_match_after_insert_prop
  (ctx : MonadChainContext)
  (stm : StateM)
  (tx : TxWithHdr)
  (updates : gmap evm.address AssumptionExactness)
  (nthElemVstackTop : UpdatedAccountState)
  (x0 : AssumedPreTxAccountState)
  (Q : _ -> Prop) :
  update_assum_exactness_at (sender tx)
    (fun ex : AssumptionExactness =>
       min_balance_update ex
         (original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
         (balanceOfAccount (postTxState nthElemVstackTop))
         (DefReserve
          `min`
          original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
          (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
            `mod` 2 ^ 256))
    (check_min_original_balance_update
       (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve) =
  update_assum_exactness_map (preTxAssumedState stm)
    (<[sender tx :=
        (fun ex : AssumptionExactness =>
           min_balance_update ex
             (original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
             (balanceOfAccount (postTxState nthElemVstackTop))
             (DefReserve
              `min`
              original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
              (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
                `mod` 2 ^ 256))
         (min_balance_update (assumExactness x0)
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
            DefReserve)]> updates) ->
  (match
     mapModelLookup
       (check_min_original_balance_update
          (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) DefReserve)
       (sender tx)
   with
   | Some (_, aps) => Q (preTxState aps)
   | None => False
   end) ->
  (match
     mapModelLookup
       (update_assum_exactness_map (preTxAssumedState stm)
          (<[sender tx :=
              min_balance_update
                (min_balance_update (assumExactness x0)
                   (original_balance_pessimistic_model_map
                      (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                   (original_balance_pessimistic_model_map
                      (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                   DefReserve)
                (original_balance_pessimistic_model_map
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx))
                (balanceOfAccount (postTxState nthElemVstackTop))
                (DefReserve
                 `min`
                 original_balance_pessimistic_model_map
                   (update_assum_exactness_map (preTxAssumedState stm) updates) (sender tx) -
                 (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))
                   `mod` 2 ^ 256)]> updates))
       (sender tx)
   with
   | Some (_, aps) => Q (preTxState aps)
   | None => False
   end).
Proof.
  intros H1 HQ.
  eapply (sender_match_after_insert
            ctx stm tx updates nthElemVstackTop x0 Q); eauto.
Qed.

Lemma rwlem2
  (ctx : MonadChainContext)
  (stm : StateM)
  (nthElemVstackTop : UpdatedAccountState)
  (_t_ : gmap evm.address AssumptionExactness)
  (tx : TxWithHdr)
  (x0 : AssumedPreTxAccountState) :
  update_assum_exactness_at (sender tx)
    (λ ex : AssumptionExactness,
       min_balance_update ex
         (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
         (balanceOfAccount (postTxState nthElemVstackTop))
         (DefReserve
          `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) -
          (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256))
    (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) DefReserve) =
  update_assum_exactness_map (preTxAssumedState stm)
    (<[sender tx:=(λ ex : AssumptionExactness,
                     min_balance_update ex
                       (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                       (balanceOfAccount (postTxState nthElemVstackTop))
                       (DefReserve
                        `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_)
                                (sender tx) -
                        (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256))
                    (min_balance_update (assumExactness x0)
                       (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                       (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                       DefReserve)]>
       _t_) ->
  (match
     mapModelLookup
       (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) DefReserve)
       (sender tx)
   with
   | Some (_, aps) =>
       match postTxState nthElemVstackTop with
       | Some am => isDelegationMarker (block.block_account_code (coreAc am))
       | None => false
       end =
       match preTxState aps with
       | Some am => isDelegationMarker (block.block_account_code (coreAc am))
       | None => false
       end && asbool (sender tx ∉ undels tx.1.2) || asbool (sender tx ∈ dels tx.1.2)
   | None => False
   end) ->
  match
    mapModelLookup
      (update_assum_exactness_map (preTxAssumedState stm)
         (<[sender tx:=min_balance_update
                         (min_balance_update (assumExactness x0)
                            (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                            (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                            DefReserve)
                         (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                         (balanceOfAccount (postTxState nthElemVstackTop))
                         (DefReserve
                          `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_)
                                  (sender tx) -
                          (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256)]>
            _t_))
      (sender tx)
  with
  | Some (_, aps) =>
      match postTxState nthElemVstackTop with
      | Some am => isDelegationMarker (block.block_account_code (coreAc am))
      | None => false
      end =
      match preTxState aps with
      | Some am => isDelegationMarker (block.block_account_code (coreAc am))
      | None => false
      end && asbool (sender tx ∉ undels tx.1.2) || asbool (sender tx ∈ dels tx.1.2)
  | None => False
  end.
Proof.
  intros H1 Hpreadd.
  rewrite <- H1.
  rewrite mapModelLookup_update_assum_exactness_at_eq.
  set (m :=
    mapModelLookup
      (check_min_original_balance_update
         (update_assum_exactness_map (preTxAssumedState stm) _t_)
         (sender tx) DefReserve)
      (sender tx)).
  destruct m as [[loc aps]|] eqn:Hm.
  {
    unfold m in Hm.
    rewrite Hm in Hpreadd.
    simpl in Hpreadd.
    simpl.
    exact Hpreadd.
  }
  {
    unfold m in Hm.
    rewrite Hm in Hpreadd.
    simpl in Hpreadd.
    exact Hpreadd.
  }
Qed.

(* Thin rewrite wrapper over [rwlem2] plus
   [mapModelLookup_match_preTxState_update_assum_exactness_at_rw].
   Candidate to inline at call sites later. *)
Lemma rwlem2_rewrite
  (ctx : MonadChainContext)
  (stm : StateM)
  (nthElemVstackTop : UpdatedAccountState)
  (_t_ : gmap evm.address AssumptionExactness)
  (tx : TxWithHdr)
  (x0 : AssumedPreTxAccountState) :
  update_assum_exactness_at (sender tx)
    (λ ex : AssumptionExactness,
       min_balance_update ex
         (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
         (balanceOfAccount (postTxState nthElemVstackTop))
         (DefReserve
          `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) -
          (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256))
    (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) DefReserve) =
  update_assum_exactness_map (preTxAssumedState stm)
    (<[sender tx:=(λ ex : AssumptionExactness,
                     min_balance_update ex
                       (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                       (balanceOfAccount (postTxState nthElemVstackTop))
                       (DefReserve
                        `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_)
                                (sender tx) -
                        (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256))
                    (min_balance_update (assumExactness x0)
                       (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                       (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                       DefReserve)]>
       _t_) ->
  (match
     mapModelLookup
       (update_assum_exactness_map (preTxAssumedState stm)
          (<[sender tx:=min_balance_update
                          (min_balance_update (assumExactness x0)
                             (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                             (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                             DefReserve)
                          (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                          (balanceOfAccount (postTxState nthElemVstackTop))
                          (DefReserve
                           `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_)
                                   (sender tx) -
                           (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256)]>
             _t_))
       (sender tx)
   with
   | Some (_, aps) =>
       match postTxState nthElemVstackTop with
       | Some am => isDelegationMarker (block.block_account_code (coreAc am))
       | None => false
       end =
       match preTxState aps with
       | Some am => isDelegationMarker (block.block_account_code (coreAc am))
       | None => false
       end && asbool (sender tx ∉ undels tx.1.2) || asbool (sender tx ∈ dels tx.1.2)
   | None => False
   end) =
  (match
     mapModelLookup
       (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) DefReserve)
       (sender tx)
   with
   | Some (_, aps) =>
       match postTxState nthElemVstackTop with
       | Some am => isDelegationMarker (block.block_account_code (coreAc am))
       | None => false
       end =
       match preTxState aps with
       | Some am => isDelegationMarker (block.block_account_code (coreAc am))
       | None => false
       end && asbool (sender tx ∉ undels tx.1.2) || asbool (sender tx ∈ dels tx.1.2)
   | None => False
   end).
Proof.
  intros H1.
  rewrite <- H1.
  set (P :=
    fun s =>
      match postTxState nthElemVstackTop with
      | Some am => isDelegationMarker (block.block_account_code (coreAc am))
      | None => false
      end =
      match s with
      | Some am => isDelegationMarker (block.block_account_code (coreAc am))
      | None => false
      end && asbool (sender tx ∉ undels tx.1.2) || asbool (sender tx ∈ dels tx.1.2)).
  exact
    (mapModelLookup_match_preTxState_update_assum_exactness_at_rw
       (check_min_original_balance_update
          (update_assum_exactness_map (preTxAssumedState stm) _t_)
          (sender tx) DefReserve)
       (sender tx)
       (λ ex : AssumptionExactness,
          min_balance_update ex
            (original_balance_pessimistic_model_map
               (update_assum_exactness_map (preTxAssumedState stm) _t_)
               (sender tx))
            (balanceOfAccount (postTxState nthElemVstackTop))
            (DefReserve
             `min` original_balance_pessimistic_model_map
                     (update_assum_exactness_map (preTxAssumedState stm) _t_)
                     (sender tx) -
             (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))
               `mod` 2 ^ 256))
       P).
Qed.

Lemma mapModelLookup_match_preTxState_update_assum_exactness_map
    (m : MapModel evm.address AssumedPreTxAccountState)
    (updates : gmap evm.address AssumptionExactness)
    (addr : evm.address)
    (P : option AccountM -> Prop) :
  (match mapModelLookup m addr with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end) ->
  (match mapModelLookup (update_assum_exactness_map m updates) addr with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end).
Proof.
  intros H.
  rewrite mapModelLookup_update_assum_exactness_map.
  destruct (mapModelLookup m addr) as [[loc aps0]|] eqn:Hlookup; simpl in *.
  { destruct (updates !! addr); simpl; exact H. }
  { exact H. }
Qed.

Lemma check_min_original_balance_update_match_preTxState_update_assum_exactness_map
    (m : MapModel evm.address AssumedPreTxAccountState)
    (updates : gmap evm.address AssumptionExactness)
    (addr : evm.address)
    (max_reserve : N)
    (P : option AccountM -> Prop) :
  (match mapModelLookup (check_min_original_balance_update m addr max_reserve) addr with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end) ->
  (match mapModelLookup
           (check_min_original_balance_update (update_assum_exactness_map m updates) addr max_reserve)
           addr
   with
   | Some (_, aps) => P (preTxState aps)
   | None => False
   end).
Proof.
  intros H.
  unfold check_min_original_balance_update in *.
  rewrite mapModelLookup_match_preTxState_update_assum_exactness_at_rw in H.
  rewrite mapModelLookup_match_preTxState_update_assum_exactness_at_rw.
  eapply mapModelLookup_match_preTxState_update_assum_exactness_map.
  exact H.
Qed.
