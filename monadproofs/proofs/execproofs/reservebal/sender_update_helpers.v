Require Import skylabs.auto.cpp.proof.
Require Import stdpp.gmap.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_rewrite_lemmas.

Import linearity.
Set Warnings "+sl-impossible-patterns".
Unset SsrIdents.
Import evmmisc.
Import exec_specs.

#[local] Open Scope N_scope.

Lemma gas_fee_model_mod_small
  (ctx : MonadChainContext)
  (tx : TxWithHdr) :
  (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx) < 2 ^ 256)%N ->
  ((tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx)) `mod` 2 ^ 256)%N =
  tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx).
Proof.
  intro Hlt.
  apply N.mod_small.
  exact Hlt.
Qed.

Lemma gas_fee_model_lt_2_256_of_validTx
  (tx : TxWithHdr) :
  validTx tx ->
  (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx) < 2 ^ 256)%N.
Proof.
  intros Hvalid.
  destruct Hvalid as [_ [Hgas_limit [Hgas_price _]]].
  apply N2Z.inj_lt.
  zify.
  nia.
Qed.

Lemma tx_base_fee_per_gas_eq_of_txidx
  (ctx : MonadChainContext)
  (i : nat)
  (tx : TxWithHdr) :
  option_map
    (fun t0 : Transaction => (t0, header (currentBlock (blocks ctx))))
    (nth_error (transactions (currentBlock (blocks ctx))) i) = Some tx ->
  tx_base_fee_per_gas tx = base_fee_per_gas (cblock ctx).
Proof.
  intros Htxidx.
  unfold cblock in *.
  destruct (nth_error (transactions (currentBlock (blocks ctx))) i) as [tx0|] eqn:Hnthtx.
  {
    simpl in Htxidx.
    inversion Htxidx; subst.
    unfold tx_base_fee_per_gas.
    simpl.
    reflexivity.
  }
  {
    simpl in Htxidx.
    discriminate.
  }
Qed.

Lemma gas_fee_model_lt_2_256_of_validTx_ctx
  (ctx : MonadChainContext)
  (tx : TxWithHdr) :
  validTx tx ->
  tx_base_fee_per_gas tx = base_fee_per_gas (cblock ctx) ->
  (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)) < 2 ^ 256)%N.
Proof.
  intros Hvalid Hfee_base.
  pose proof (gas_fee_model_lt_2_256_of_validTx tx Hvalid) as Hlt.
  unfold gas_price_model.
  rewrite <- Hfee_base.
  exact Hlt.
Qed.

Lemma maxTxFee_eq_fee_raw_of_validTx_ctx
  (ctx : MonadChainContext)
  (tx : TxWithHdr) :
  validTx tx ->
  tx_base_fee_per_gas tx = base_fee_per_gas (cblock ctx) ->
  maxTxFee tx =
    (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))%N.
Proof.
  intros Hvalid Hfee_base.
  destruct Hvalid as [_ [_ [_ Hraw]]].
  unfold gas_price_model.
  rewrite <- Hfee_base.
  exact Hraw.
Qed.

Lemma maxTxFee_eq_fee_mod_of_validTx_ctx
  (ctx : MonadChainContext)
  (tx : TxWithHdr) :
  validTx tx ->
  tx_base_fee_per_gas tx = base_fee_per_gas (cblock ctx) ->
  maxTxFee tx =
    ((tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))
      `mod` 2 ^ 256)%N.
Proof.
  intros Hvalid Hfee_base.
  pose proof (maxTxFee_eq_fee_raw_of_validTx_ctx ctx tx Hvalid Hfee_base) as Hraw.
  rewrite Hraw.
  rewrite N.mod_small.
  {
    reflexivity.
  }
  {
    exact (gas_fee_model_lt_2_256_of_validTx_ctx ctx tx Hvalid Hfee_base).
  }
Qed.

Lemma sender_insert_validModel_twice
  (stm : StateM)
  (_t_ : gmap evm.address AssumptionExactness)
  (tx : TxWithHdr)
  (x : ptr)
  (x0 : AssumedPreTxAccountState)
  (cur debit : N) :
  validModel (update_assum_exactness_state stm _t_) ->
  mapModelLookup
    (update_assum_exactness_map (preTxAssumedState stm) _t_)
    (sender tx) = Some (x, x0) ->
  let orig :=
    original_balance_pessimistic_model_map
      (update_assum_exactness_map (preTxAssumedState stm) _t_)
      (sender tx) in
  let ex0 := min_balance_update (assumExactness x0) orig orig DefReserve in
  let ex := min_balance_update ex0 orig cur debit in
  validModel (update_assum_exactness_state stm (<[sender tx := ex]> _t_)).
Proof.
  intros Hvalid_update Hlookup orig ex0 ex.
  assert (HvalidState_update : validStateM (update_assum_exactness_state stm _t_)).
  {
    apply validModel_validStateM.
    exact Hvalid_update.
  }
  assert (Hbound :
    match preTxState x0 with
    | Some cs =>
        if isSome (min_balance ex)
        then (min_balanceN ex <= cs .^ _balance)%N
        else True
    | None => True
    end).
  {
    eapply (min_balance_update_twice_bound_of_validStateM
              stm _t_ (sender tx) x x0 cur debit DefReserve); eauto.
  }
  assert (Hstr_ex : assumption_exactness_stricter (assumExactness x0) ex).
  {
    unfold ex, ex0.
    apply assumption_exactness_stricter_min_balance_update_twice.
  }
  exact
    (validModel_update_assum_exactness_state_insert_map_fst
       stm _t_ (sender tx) ex x x0
       Hvalid_update Hlookup Hstr_ex Hbound).
Qed.

Lemma sender_insert_validModel_once
  (stm : StateM)
  (_t_ : gmap evm.address AssumptionExactness)
  (tx : TxWithHdr)
  (loc : ptr)
  (aps : AssumedPreTxAccountState) :
  validModel (update_assum_exactness_state stm _t_) ->
  mapModelLookup
    (update_assum_exactness_map (preTxAssumedState stm) _t_)
    (sender tx) = Some (loc, aps) ->
  let orig :=
    original_balance_pessimistic_model_map
      (update_assum_exactness_map (preTxAssumedState stm) _t_)
      (sender tx) in
  let ex0 := min_balance_update (assumExactness aps) orig orig DefReserve in
  validModel (update_assum_exactness_state stm (<[sender tx := ex0]> _t_)).
Proof.
  intros Hvalid_update Hlookup orig ex0.
  assert (HvalidState_update : validStateM (update_assum_exactness_state stm _t_)).
  {
    apply validModel_validStateM.
    exact Hvalid_update.
  }
  assert (Hstr_ex0 : assumption_exactness_stricter (assumExactness aps) ex0).
  {
    unfold ex0.
    apply assumption_exactness_stricter_min_balance_update.
  }
  assert (Hbound_ex0 :
    match exec_specs.preTxState aps with
    | Some cs =>
        if isSome (min_balance ex0)
        then (min_balanceN ex0 <= cs .^ _balance)%N
        else True
    | None => True
    end).
  {
    pose proof
      (validStateM_bound_of_lookup
         (update_assum_exactness_state stm _t_)
         (sender tx) loc aps HvalidState_update Hlookup) as Hbound_old.
    destruct (exec_specs.preTxState aps) as [cs|] eqn:Hpre_aps; simpl; [|exact I].
    set (orig0 :=
           original_balance_pessimistic_model_map
             (update_assum_exactness_map (preTxAssumedState stm) _t_)
             (sender tx)) in *.
    assert (Horig_cs : orig0 = cs .^ _balance).
    {
      unfold orig0, original_balance_pessimistic_model_map, preTxAccountOf_map.
      rewrite Hlookup. simpl. rewrite Hpre_aps. reflexivity.
    }
    destruct (isSome (min_balance ex0)) eqn:Hsome; [|exact I].
    destruct (min_balance ex0) as [m|] eqn:Hmb; [|discriminate].
    simpl.
    assert (Hold :
      match min_balance (assumExactness aps) with
      | Some m0 => (m0 <= orig0)%N
      | None => True
      end).
    {
      destruct (min_balance (assumExactness aps)) as [m0|] eqn:Hmb_old.
      {
        simpl in Hbound_old.
        unfold min_balanceN in Hbound_old.
        rewrite Hmb_old in Hbound_old.
        simpl in Hbound_old.
        rewrite Horig_cs.
        exact Hbound_old.
      }
      {
        exact I.
      }
    }
    pose proof
      (min_balance_update_upper_bound (assumExactness aps) orig0 orig0 DefReserve Hold)
      as Hup.
    rewrite /ex0 in Hmb.
    rewrite Hmb in Hup. simpl in Hup.
    unfold min_balanceN.
    rewrite Hmb.
    simpl.
    rewrite Horig_cs in Hup.
    exact Hup.
  }
  exact
    (validModel_update_assum_exactness_state_insert_map_fst
       stm _t_ (sender tx) ex0 loc aps
       Hvalid_update Hlookup Hstr_ex0 Hbound_ex0).
Qed.

Lemma sender_insert_updates_stricter_once
  (stm : StateM)
  (_t_ : gmap evm.address AssumptionExactness)
  (tx : TxWithHdr)
  (loc : ptr)
  (aps : AssumedPreTxAccountState) :
  updates_stricter stm _t_ ->
  mapModelLookup
    (update_assum_exactness_map (preTxAssumedState stm) _t_)
    (sender tx) = Some (loc, aps) ->
  let orig :=
    original_balance_pessimistic_model_map
      (update_assum_exactness_map (preTxAssumedState stm) _t_)
      (sender tx) in
  let ex0 := min_balance_update (assumExactness aps) orig orig DefReserve in
  updates_stricter stm (<[sender tx := ex0]> _t_).
Proof.
  intros Hstr_updates Hlookup orig ex0.
  assert (Hex0_id : min_balance_update ex0 0 0 0 = ex0).
  {
    unfold min_balance_update, check_min_balance_ok.
    destruct ex0 as [mb ne].
    simpl.
    destruct (bool_decide (0 <= 0)%N) eqn:Hok; simpl.
    {
      destruct mb as [m|]; simpl.
      {
        destruct (N.ltb (0 - 0) 0) eqn:Hlt; simpl; reflexivity.
      }
      {
        reflexivity.
      }
    }
    {
      apply bool_decide_eq_false_1 in Hok.
      lia.
    }
  }
  pose proof
    (updates_stricter_insert
       stm _t_ (sender tx) loc aps
       orig orig DefReserve 0 0 0
       Hstr_updates Hlookup) as Hstr2.
  simpl in Hstr2.
  rewrite Hex0_id in Hstr2.
  exact Hstr2.
Qed.

Lemma sender_check_min_eq_of_lookup
  (stm : StateM)
  (_t_ : gmap evm.address AssumptionExactness)
  (tx : TxWithHdr)
  (loc : ptr)
  (aps : AssumedPreTxAccountState)
  (ex0 : AssumptionExactness) :
  NoDup (map fst (update_assum_exactness_map (preTxAssumedState stm) _t_)) ->
  mapModelLookup
    (update_assum_exactness_map (preTxAssumedState stm) _t_)
    (sender tx) = Some (loc, aps) ->
  ex0 =
    min_balance_update
      (assumExactness aps)
      (original_balance_pessimistic_model_map
         (update_assum_exactness_map (preTxAssumedState stm) _t_)
         (sender tx))
      (original_balance_pessimistic_model_map
         (update_assum_exactness_map (preTxAssumedState stm) _t_)
         (sender tx))
      DefReserve ->
  check_min_original_balance_update
    (update_assum_exactness_map (preTxAssumedState stm) _t_)
    (sender tx) DefReserve =
  update_assum_exactness_map (preTxAssumedState stm)
    (<[sender tx := ex0]> _t_).
Proof.
  intros Hnodup_update_fst Hlookup Hex0.
  subst ex0.
  eapply (check_min_original_balance_update_eq_update_assum_exactness_map_insert
            (preTxAssumedState stm) _t_ (sender tx) DefReserve loc aps); eauto.
Qed.
