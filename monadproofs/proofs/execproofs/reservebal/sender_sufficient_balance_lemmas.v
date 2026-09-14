Require Import skylabs.auto.cpp.proof.
Require Import stdpp.gmap.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import monad.proofs.execproofs.reservebal.non_sender_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_update_helpers.

Import linearity.
Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".
Unset SsrIdents.
Import evmmisc.
Import exec_specs.

#[local] Open Scope N_scope.

Lemma sender_suff_arith
  (pre ass upd fee d : N) :
  let debit := (d `min` ass - fee)%N in
  (Z.of_N debit <= Z.of_N pre + (Z.of_N upd - Z.of_N ass))%Z ->
  (debit <= upd)%N ->
  (Z.of_N (d `min` pre - fee) <= Z.of_N pre + (Z.of_N upd - Z.of_N ass))%Z.
Proof.
  intros debit Hdeb_post Hdeb_upd.
  nia.
Qed.

Lemma min_balance_update_twice_some_ge_min_orig
  (old : AssumptionExactness) (orig cur fee m : N) :
  min_balance
    (min_balance_update
       (min_balance_update old orig orig DefReserve)
       orig cur (DefReserve `min` orig - fee)) = Some m ->
  (DefReserve `min` orig <= m)%N.
Proof.
  intros Hm.
  unfold min_balance_update, check_min_balance_ok in Hm.
  destruct (bool_decide ((DefReserve `min` orig - fee <= cur)%N)) eqn:Hok2.
  {
    simpl in Hm.
    destruct (min_balance (min_balance_update old orig orig DefReserve)) as [m0|] eqn:Hm0.
    {
      simpl in Hm.
      assert (Hbase : (DefReserve `min` orig <= m0)%N).
      {
        assert (Hok1 : check_min_balance_ok orig DefReserve = true).
        {
          unfold min_balance_update in Hm0.
          destruct (check_min_balance_ok orig DefReserve) eqn:Hok1.
          {
            reflexivity.
          }
          {
            destruct old as [mb ne].
            destruct mb; simpl in Hm0; discriminate.
          }
        }
        pose proof (min_balance_update_lower_bound old orig orig DefReserve Hok1) as Hlb.
        rewrite Hm0 in Hlb; simpl in Hlb.
        unfold check_min_balance_ok in Hok1.
        apply bool_decide_eq_true_1 in Hok1.
        rewrite N.min_l; [|exact Hok1].
        assert (Hsub : (orig - (orig - DefReserve) = DefReserve)%N).
        {
          apply N2Z.inj.
          rewrite N2Z.inj_sub.
          {
            rewrite N2Z.inj_sub.
            {
              nia.
            }
            {
              exact Hok1.
            }
          }
          {
            nia.
          }
        }
        rewrite <- Hsub.
        exact Hlb.
      }
      destruct (N.ltb (cur - (DefReserve `min` orig - fee)) orig) eqn:Hlt.
      {
        rewrite Hm0 in Hm.
        simpl in Hm.
        inversion Hm as [Heq]; clear Hm.
        eapply N.le_trans with (m := m0).
        {
          exact Hbase.
        }
        {
          try rewrite <- Heq.
          apply N.le_max_l.
        }
      }
      {
        rewrite Hm0 in Hm.
        simpl in Hm.
        inversion Hm; subst; clear Hm.
        exact Hbase.
      }
    }
    {
      pose proof Hm0 as Hm0u.
      unfold min_balance_update, check_min_balance_ok in Hm0u.
      rewrite Hm0u in Hm.
      simpl in Hm.
      rewrite Hm0u in Hm.
      simpl in Hm.
      discriminate Hm.
    }
  }
  {
    simpl in Hm.
    discriminate Hm.
  }
Qed.

Lemma senderSuffBal :
  ∀ (thread_info : biIndex) (_Σ : gFunctors) (Sigma : cpp_logic thread_info _Σ) (CU : genv)
    (ctx : MonadChainContext) (_i_ : nat) (hist : ExtraAcStates) (statep : ptr) (stm : StateM),
    validTx (nth _i_ (map (λ t : Transaction, (t, header (cblock ctx))) (transactions (cblock ctx))) dummyTx) ->
    (∀ addr : EvmAddr, configuredReserveBal (hist addr) = DefReserve) ->
    ∀ (nthElemPtr nthElemVstackTopPtr : ptr) (nthElemVstackTop : UpdatedAccountState)
      (nthElemVstackTl : list (ptr * UpdatedAccountState))
      (_t_ : gmap evm.address AssumptionExactness)
      (tx := nth _i_ (map (λ t : Transaction, (t, header (cblock ctx))) (transactions (cblock ctx))) dummyTx)
      (x0 : AssumedPreTxAccountState) (i : N),
      nth_error (newStates stm) (N.to_nat i) =
        Some (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
      (∀ preTxState : StateOfAccounts,
          satisfiesAssumptions (update_assum_exactness_state stm _t_) preTxState ->
          historyConsistent ctx hist ->
          true = allFinalBalSufficient 3 (preTxState, hist)
                   (applyUpdates (update_assum_exactness_state stm _t_) preTxState)
                   (map fst (takeN i (newStates stm))) tx) ->
      map fst (newStates stm) ⊆ map fst (preTxAssumedState stm) ->
      validStateM (update_assum_exactness_state stm _t_) ->
      validPostNone (update_assum_exactness_state stm _t_) ->
      validSliceInvariants (update_assum_exactness_state stm _t_) ->
      option_map (λ t0 : Transaction, (t0, header (currentBlock (blocks ctx))))
        (nth_error (transactions (currentBlock (blocks ctx))) _i_) =
      Some (nth _i_
              (map (λ t0 : Transaction, (t0, header (currentBlock (blocks ctx))))
                 (transactions (currentBlock (blocks ctx))))
              dummyTx) ->
      ¬ DefReserve
        `min` original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) _t_)
                (sender tx) <
        (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256 ->
      ∀ x : ptr,
        mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) = Some (x, x0) ->
        (DefReserve
         `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) -
         (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256 ≤
         balanceOfAccount (postTxState nthElemVstackTop))%N ->
        NoDup (map fst (map (λ '(a, (b, _)), (a, b)) (newStates stm))) ->
        let orig :=
          original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) in
        let ex :=
          min_balance_update
            (min_balance_update (assumExactness x0) orig orig DefReserve)
            orig
            (balanceOfAccount (postTxState nthElemVstackTop))
            (DefReserve `min` orig -
             (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256) in
        let stf := update_assum_exactness_state stm (<[sender tx:=ex]> _t_) in
        validModel stf ∧
        ∀ preTxState : StateOfAccounts,
          satisfiesAssumptions stf preTxState ->
          historyConsistent ctx hist ->
          true =
          allFinalBalSufficient 3 (preTxState, hist)
            (applyUpdates stf preTxState)
            (map fst (takeN (1 + i) (newStates stm))) tx.
Proof.
  intros thread_info _Σ Sigma CU ctx _i_ hist statep stm.
  intros HvalidTx Hreserve_hist.
  intros nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl _t_ tx x0.
  intros i Hnth Hall_i Hmapfst HvalidState_update HvalidPost_update.
  intros HvalidSlice_update Htxidx n x Hlookup Hdebit_le Hnodup_new_fst.
  cbn in *.
  set (orig :=
         original_balance_pessimistic_model_map
           (update_assum_exactness_map (preTxAssumedState stm) _t_)
           (sender tx)).
  set (fee_mod :=
         ((tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))
            `mod` 2 ^ 256)%N).
  set (debit := (DefReserve `min` orig - fee_mod)%N).
  set (cur := balanceOfAccount (postTxState nthElemVstackTop)).
  set (ex0 := min_balance_update (assumExactness x0) orig orig DefReserve).
  set (ex := min_balance_update ex0 orig cur debit).
  set (stf := update_assum_exactness_state stm (<[sender tx := ex]> _t_)).
  assert (Hfee_base : tx_base_fee_per_gas tx = base_fee_per_gas (cblock ctx)).
  {
    exact (tx_base_fee_per_gas_eq_of_txidx ctx _i_ tx Htxidx).
  }
  assert (HmaxTxFee_eq : maxTxFee tx = fee_mod).
  {
    unfold fee_mod.
    exact (maxTxFee_eq_fee_mod_of_validTx_ctx ctx tx HvalidTx Hfee_base).
  }
  assert (Hvalid_update : validModel (update_assum_exactness_state stm _t_)).
  {
    eapply (validModel_of_components_update_assum_exactness_state stm _t_); eauto.
  }
  assert (Hstr_ex : assumption_exactness_stricter (assumExactness x0) ex).
  {
    unfold ex, ex0.
    apply assumption_exactness_stricter_min_balance_update_twice.
  }
  assert (Hnth_stf :
      nth_error (newStates stf) (N.to_nat i) =
        Some (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl))).
  {
    unfold stf, update_assum_exactness_state.
    simpl.
    exact Hnth.
  }
  split.
  {
    unfold stf, ex, ex0, orig.
    exact (sender_insert_validModel_twice stm _t_ tx x x0 cur debit Hvalid_update Hlookup).
  }
  {
    intros preTxState Hsat Hhist'.
    refine
      (allFinalBalSufficient_takeN_succ
         stf ctx hist tx i (sender tx) nthElemPtr
         ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)
         _ _ _ preTxState Hsat).
    {
      intros preTxState0 Hsat0.
      exact
        (allFinalBalSufficient_takeN_i_update_assum_exactness_state_insert
           stm ctx hist tx i (sender tx) nthElemPtr
           ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)
           _t_ ex preTxState0 x x0
           Hnodup_new_fst
           Hnth
           (fun preTxState1 Hsat1 => Hall_i preTxState1 Hsat1 Hhist')
           Hvalid_update
           Hlookup
           Hstr_ex
           Hsat0).
    }
    { exact Hnth_stf. }
    {
      intros preTxState0 Hsat0.
      unfold finalBalSufficient.
      destruct (isSC (applyUpdates stf preTxState0) (sender tx)); [reflexivity|].
      rewrite bool_decide_true; [|reflexivity].
      destruct (isAllowedToEmptyExec 3 (preTxState0, hist) tx); [reflexivity|].
      apply andb_true_intro.
      split.
      {
        apply bool_decide_eq_true_2.
        assert (Hlookup_upd0 :
            mapModelLookup
              (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_))
              (sender tx) =
            Some (x, {| preTxState := exec_specs.preTxState x0;
                        preTxStorage := exec_specs.preTxStorage x0;
                        assumExactness := ex |})).
        {
          pose proof (mapModelLookup_update_assum_exactness_map_Some
                        (preTxAssumedState stm) _t_ (sender tx) x x0 Hlookup)
            as (aps0 & Horig_lookup0 & Hpre_lookup0 & Hstorage_lookup0 & _Hassum_lookup0).
          rewrite mapModelLookup_update_assum_exactness_map.
          rewrite Horig_lookup0. simpl.
          rewrite lookup_insert. simpl.
          rewrite decide_True.
          2: {
            reflexivity.
          }
          simpl.
          rewrite <- Hpre_lookup0.
          rewrite <- Hstorage_lookup0.
          reflexivity.
        }
        pose proof (Hsat0 (sender tx)) as Hsat_sender0.
        unfold satisfiesAssumptions', satAccountAssumptions in Hsat_sender0.
        unfold assumptionOfAddr in Hsat_sender0.
        unfold stf, update_assum_exactness_state in Hsat_sender0; simpl in Hsat_sender0.
        change
          ((update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex]> _t_)) !! sender tx)
          with
            (mapModelLookup
               (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex]> _t_))
               (sender tx)) in Hsat_sender0.
        rewrite Hlookup_upd0 in Hsat_sender0.
        simpl in Hsat_sender0.
        destruct Hsat_sender0 as [Hnon0 _Hstor0].
        unfold satAccountNonStorageAssumptions in Hnon0.
        simpl in Hnon0.
        assert (Hpre_some0 : exists csAssumed, exec_specs.preTxState x0 = Some csAssumed).
        {
          destruct (exec_specs.preTxState x0) as [csAssumed|] eqn:Hprex0.
          {
            exists csAssumed.
            reflexivity.
          }
          {
            exfalso.
            destruct Hnon0.
          }
        }
        destruct Hpre_some0 as [csAssumed Hprex0].
        assert (Horig_eq0 : orig = csAssumed .^ _balance).
        {
          unfold orig, original_balance_pessimistic_model_map, preTxAccountOf_map.
          rewrite Hlookup.
          simpl.
          rewrite Hprex0.
          reflexivity.
        }
        assert (Hminorig_le_actual :
            (DefReserve `min` orig <= balanceOfAc preTxState0 (sender tx))%N).
        {
          destruct (relaxedValidation stm) eqn:Hrel0.
          {
            destruct (isNone (min_balance ex)) eqn:Hnone0.
            {
              rewrite Hprex0 in Hnon0.
              simpl in Hnon0.
              destruct Hnon0 as [Hbal_eq0 _].
              unfold balanceOfAc.
              rewrite Horig_eq0.
              simpl.
              first [rewrite Hbal_eq0 | rewrite <- Hbal_eq0].
              apply N.le_min_r.
            }
            {
              rewrite Hprex0 in Hnon0.
              simpl in Hnon0.
              destruct (min_balance ex) as [m0|] eqn:Hmb0.
              {
                destruct Hnon0 as [Hmin_ok0 _].
                unfold min_balanceN in Hmin_ok0.
                rewrite Hmb0 in Hmin_ok0.
                simpl in Hmin_ok0.
                pose proof
                  (min_balance_update_twice_some_ge_min_orig
                     (assumExactness x0) orig cur fee_mod m0) as Hlb0.
                unfold ex, ex0, debit in Hlb0.
                specialize (Hlb0 Hmb0).
                unfold balanceOfAc.
                simpl.
                eapply N.le_trans.
                { exact Hlb0. }
                { exact Hmin_ok0. }
              }
              {
                simpl in Hnone0.
                discriminate.
              }
            }
          }
          {
            rewrite Hprex0 in Hnon0.
            simpl in Hnon0.
            destruct Hnon0 as [[Hbal_eq0 _] _].
            unfold balanceOfAc.
            rewrite Horig_eq0.
            simpl.
            first [rewrite Hbal_eq0 | rewrite <- Hbal_eq0].
            apply N.le_min_r.
          }
        }
        rewrite HmaxTxFee_eq.
        unfold configuredReserveBalOfAddr.
        apply N.le_trans with (m := DefReserve `min` orig).
        {
          apply N.nlt_ge.
          exact n.
        }
        {
          rewrite Hreserve_hist.
          apply N.min_glb.
          {
            apply N.le_min_l.
          }
          {
            exact Hminorig_le_actual.
          }
        }
      }
      {
        apply bool_decide_eq_true_2.
        unfold configuredReserveBalOfAddr in *.
        assert (Hcur_debit :
            (debit <= cur)%N).
        {
          unfold debit, fee_mod, cur in *.
          exact Hdebit_le.
        }
      pose proof (mapModelLookup_update_assum_exactness_map_Some
                    (preTxAssumedState stm) _t_ (sender tx) x x0 Hlookup)
        as (aps0 & Horig_lookup & Hpre_lookup & Hstorage_lookup & _Hassum_lookup).
      set (aps_new := {| preTxState := exec_specs.preTxState x0;
                         preTxStorage := exec_specs.preTxStorage x0;
                         assumExactness := ex |}).
      assert (Hlookup_upd :
          mapModelLookup
            (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_))
            (sender tx) = Some (x, aps_new)).
      {
        rewrite mapModelLookup_update_assum_exactness_map.
        rewrite Horig_lookup. simpl.
        rewrite lookup_insert. simpl.
        rewrite decide_True.
        2: {
          reflexivity.
        }
        simpl.
        rewrite <- Hpre_lookup.
        rewrite <- Hstorage_lookup.
        reflexivity.
      }
      assert (Hlookup_new :
          mapModelLookup (newStates stm) (sender tx) =
          Some
            (nthElemPtr,
             (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
      {
        assert (Hnodup_new_keys : NoDup (map fst (newStates stm))).
        {
          eapply NoDup_map_fst_newStates_of_map.
          exact Hnodup_new_fst.
        }
        apply elem_of_list_to_map_1.
        {
          change (NoDup (map fst (newStates stm))).
          exact Hnodup_new_keys.
        }
        {
          apply list_elem_of_lookup_2 with (i := N.to_nat i).
          rewrite lookup_nth_error.
          exact Hnth.
        }
      }
      assert (Hau :
          assumptionAndUpdateOfAddr stf (sender tx) =
          Some
            {| preAssumption := aps_new;
               originalLoc := x;
               txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}).
      {
        unfold assumptionAndUpdateOfAddr, stf, update_assum_exactness_state; simpl.
        change
          ((update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex]> _t_)) !! sender tx)
          with
            (mapModelLookup
               (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex]> _t_))
               (sender tx)).
        change ((newStates stm) !! sender tx)
          with (mapModelLookup (newStates stm) (sender tx)).
        rewrite Hlookup_upd. simpl.
        rewrite Hlookup_new. simpl.
        reflexivity.
      }
      pose proof (Hsat0 (sender tx)) as Hsat_sender.
      unfold satisfiesAssumptions', satAccountAssumptions in Hsat_sender.
      unfold assumptionOfAddr in Hsat_sender.
      unfold stf, update_assum_exactness_state in Hsat_sender; simpl in Hsat_sender.
      change
        ((update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex]> _t_)) !! sender tx)
        with
          (mapModelLookup
             (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex]> _t_))
             (sender tx)) in Hsat_sender.
      rewrite Hlookup_upd in Hsat_sender.
      simpl in Hsat_sender.
      destruct Hsat_sender as [Hnon _Hstor].
      unfold satAccountNonStorageAssumptions in Hnon.
      simpl in Hnon.
      assert (Hpre_some : exists csAssumed, exec_specs.preTxState x0 = Some csAssumed).
      {
        destruct (exec_specs.preTxState x0) as [csAssumed|] eqn:Hprex0.
        {
          exists csAssumed.
          destruct Hprex0.
          reflexivity.
        }
        {
          exfalso.
          destruct Hnon.
        }
      }
      destruct Hpre_some as [csAssumed Hprex0].
      assert (Hpost_some : exists csUpdated, postTxState nthElemVstackTop = Some csUpdated).
      {
        destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost.
        {
          exists csUpdated.
          destruct Hpost.
          reflexivity.
        }
        {
          exfalso.
          assert (Hpre_none_x0 : exec_specs.preTxState x0 = None).
          {
            eapply (HvalidPost_update (sender tx) nthElemPtr
                      ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl) x x0);
              eauto.
          }
          rewrite Hprex0 in Hpre_none_x0.
          discriminate.
        }
      }
      destruct Hpost_some as [csUpdated Hpost].
      assert (Horig_eq :
          orig = csAssumed .^ _balance).
      {
        unfold orig, original_balance_pessimistic_model_map, preTxAccountOf_map.
        rewrite Hlookup.
        simpl.
        rewrite Hprex0.
        reflexivity.
      }
      assert (Hok : check_min_balance_ok cur debit = true).
      {
        unfold check_min_balance_ok.
        apply bool_decide_eq_true.
        exact Hcur_debit.
      }
      assert (Hpost_bal_formula :
          balanceOfAc (applyUpdates stf preTxState0) (sender tx) =
          match relaxedValidation stm with
          | false => cur
          | true =>
              if isNone (min_balance ex)
              then cur
              else
                Z.to_N
                  ((preTxState0 (sender tx)) .^ _balance +
                   (csUpdated .^ _balance - csAssumed .^ _balance))
          end).
      {
        unfold balanceOfAc, applyUpdates.
        rewrite Hau.
        simpl.
        rewrite Hpost.
        simpl.
        destruct (relaxedValidation stm) eqn:Hrel.
        {
          rewrite Hprex0.
          simpl.
          destruct (isNone (min_balance ex)) eqn:Hnone.
          {
            simpl.
            unfold cur, balanceOfAccount.
            rewrite Hpost.
            simpl.
            destruct csUpdated as [coreAcU incU relU balU]; simpl.
            repeat
              match goal with
              | |- context [balance ((_coreAc .@ _block_account_storage .= ?st) ?b)] =>
                  change (balance ((_coreAc .@ _block_account_storage .= st) b))
                    with (balance (b &: _coreAc .@ _block_account_storage .= st));
                  rewrite balance_update_storage
              end.
            destruct (nonce_exact ex); simpl;
              repeat
                match goal with
                | |- context [balance ((_nonce .= ?n) ?b)] =>
                    change (balance ((_nonce .= n) b)) with (balance (b &: _nonce .= n));
                    rewrite balance_update_nonce
                end;
              reflexivity.
          }
          {
            simpl.
            destruct csUpdated as [coreAcU incU relU balU]; simpl.
            destruct csAssumed as [coreAcA incA relA balA]; simpl.
            destruct (preTxState0 (sender tx)) as [coreAcP incP relP balP]; simpl.
            repeat
              match goal with
              | |- context [balance ((_balance .= ?n) ?b)] =>
                  change (balance ((_balance .= n) b)) with (balance (b &: _balance .= n));
                  rewrite balance_update_balance
              end.
            destruct (nonce_exact ex); simpl;
              repeat
                match goal with
                | |- context [balance ((_nonce .= ?n) ?b)] =>
                    change (balance ((_nonce .= n) b)) with (balance (b &: _nonce .= n));
                    rewrite balance_update_nonce
                end;
              repeat
                match goal with
                | |- context [balance ((_coreAc .@ _block_account_storage .= ?st) ?b)] =>
                    change (balance ((_coreAc .@ _block_account_storage .= st) b))
                      with (balance (b &: _coreAc .@ _block_account_storage .= st));
                    rewrite balance_update_storage
                end;
              reflexivity.
          }
        }
        {
          simpl.
          unfold cur, balanceOfAccount.
          rewrite Hpost.
          simpl.
          destruct csUpdated as [coreAcU incU relU balU]; simpl.
          repeat
            match goal with
            | |- context [balance ((_coreAc .@ _block_account_storage .= ?st) ?b)] =>
                change (balance ((_coreAc .@ _block_account_storage .= st) b))
                  with (balance (b &: _coreAc .@ _block_account_storage .= st));
                rewrite balance_update_storage
            end.
          reflexivity.
        }
      }
      destruct (relaxedValidation stm) eqn:Hrel.
      {
        destruct (isNone (min_balance ex)) eqn:Hnone.
        {
          rewrite Hpost_bal_formula.
          simpl.
          rewrite HmaxTxFee_eq.
          rewrite Hprex0 in Hnon.
          simpl in Hnon.
          destruct Hnon as [Hbal_eq _].
          assert (Hbal_eq' :
              (preTxState0 (sender tx)) .^ _balance = csAssumed .^ _balance).
          {
            first [exact Hbal_eq | symmetry; exact Hbal_eq].
          }
          assert (Hactual_eq' :
              balanceOfAc preTxState0 (sender tx) = (preTxState0 (sender tx)) .^ _balance).
          {
            unfold balanceOfAc.
            simpl.
            reflexivity.
          }
          assert (Hactual_eq :
              balanceOfAc preTxState0 (sender tx) = csAssumed .^ _balance).
          {
            exact (eq_trans Hactual_eq' Hbal_eq').
          }
          rewrite Hactual_eq.
          rewrite <- Horig_eq.
          rewrite Hreserve_hist.
          unfold debit in Hcur_debit.
          exact Hcur_debit.
        }
        {
          assert (Hex_some : exists m, min_balance ex = Some m).
          {
            destruct (min_balance ex) as [m|] eqn:Hmb.
            {
              exists m.
              reflexivity.
            }
            simpl in Hnone.
            discriminate.
          }
          destruct Hex_some as [m Hmb].
          rewrite Hpost_bal_formula.
          simpl.
          rewrite Hprex0 in Hnon.
          simpl in Hnon.
          assert (Hm_le_actual : (m <= (preTxState0 (sender tx)) .^ _balance)%N).
          {
            destruct Hnon as [Hmin_ok _].
            unfold min_balanceN in Hmin_ok.
            rewrite Hmb in Hmin_ok.
            simpl in Hmin_ok.
            change
              (match preTxState0 (sender tx) with
               | {| balance := balance |} => balance
               end)
              with ((preTxState0 (sender tx)) .^ _balance) in Hmin_ok.
            exact Hmin_ok.
          }
          assert (Hm_ge :
              (orig - (cur - debit) <= m)%N).
          {
            pose proof (min_balance_update_lower_bound ex0 orig cur debit Hok) as Hlb.
            change
              (match min_balance ex with
               | Some m0 => (orig - (cur - debit) <= m0)%N
               | None => True
               end) in Hlb.
            rewrite Hmb in Hlb.
            exact Hlb.
          }
          assert (Hdebit_le_postZ :
              (Z.of_N debit <=
               (preTxState0 (sender tx)) .^ _balance +
               (csUpdated .^ _balance - csAssumed .^ _balance))%Z).
          {
            apply N2Z.inj_le in Hm_ge.
            apply N2Z.inj_le in Hm_le_actual.
            rewrite Horig_eq in Hm_ge.
            unfold cur, balanceOfAccount in Hm_ge.
            rewrite Hpost in Hm_ge.
            simpl in Hm_ge.
            set (preBal := (preTxState0 (sender tx)) .^ _balance).
            set (assumedBal := csAssumed .^ _balance).
            set (updatedBal := csUpdated .^ _balance).
            assert (Hdebit_le_updated : (debit <= updatedBal)%N).
            {
              unfold cur, balanceOfAccount in Hcur_debit.
              rewrite Hpost in Hcur_debit.
              simpl in Hcur_debit.
              exact Hcur_debit.
            }
            destruct (N.leb (updatedBal - debit) assumedBal) eqn:Hle.
            {
              apply N.leb_le in Hle.
              rewrite N2Z.inj_sub in Hm_ge.
              {
                rewrite N2Z.inj_sub in Hm_ge.
                {
                  subst preBal assumedBal updatedBal.
                  cbn in Hm_ge.
                  set (A := Z.of_N (csAssumed .^ _balance)).
                  set (B := Z.of_N (csUpdated .^ _balance)).
                  set (D := Z.of_N debit).
                  set (P := Z.of_N ((preTxState0 (sender tx)) .^ _balance)).
                  change (A - (B - D) <= Z.of_N m)%Z in Hm_ge.
                  change (Z.of_N m <= P)%Z in Hm_le_actual.
                  change (D <= P + (B - A))%Z.
                  lia.
                }
                {
                  exact Hdebit_le_updated.
                }
              }
              {
                exact Hle.
              }
            }
            {
              apply N.leb_gt in Hle.
              assert (Hdiff_pos :
                  (Z.of_N assumedBal < Z.of_N (updatedBal - debit))%Z).
              {
                now apply N2Z.inj_lt.
              }
              rewrite N2Z.inj_sub in Hdiff_pos.
              {
                pose proof (N2Z.is_nonneg preBal) as Hpre_nonneg.
                lia.
              }
              {
                exact Hdebit_le_updated.
              }
	            }
	          }
	          set (preBalN := (preTxState0 (sender tx)) .^ _balance).
	          set (updBalN := csUpdated .^ _balance).
	          set (assBalN := csAssumed .^ _balance).
	          assert (Hlhs_le :
	              (Z.of_N
	                 (DefReserve
	                  `min` preBalN -
	                  fee_mod)
	               <=
	               Z.of_N preBalN +
	               (Z.of_N updBalN - Z.of_N assBalN))%Z).
	          {
	            assert (Hdebit_le_postZ' :
	                (Z.of_N debit <=
	                 Z.of_N preBalN +
	                 (Z.of_N updBalN - Z.of_N assBalN))%Z).
	            {
	              subst preBalN updBalN assBalN.
	              exact Hdebit_le_postZ.
	            }
	            assert (Hdebit_le_updN : (debit <= updBalN)%N).
	            {
	              subst updBalN.
	              unfold cur, balanceOfAccount in Hcur_debit.
	              rewrite Hpost in Hcur_debit.
	              simpl in Hcur_debit.
	              exact Hcur_debit.
	            }
	            assert (Hdebit_as_ass :
	                debit = (DefReserve `min` assBalN - fee_mod)%N).
	            {
	              subst assBalN.
	              unfold debit.
	              rewrite Horig_eq.
	              reflexivity.
	            }
	            rewrite Hdebit_as_ass in Hdebit_le_postZ'.
	            rewrite Hdebit_as_ass in Hdebit_le_updN.
	            eapply (sender_suff_arith preBalN assBalN updBalN fee_mod DefReserve);
	              eauto.
	          }
	          rewrite HmaxTxFee_eq.
	          assert (Hbal_ac :
	              balanceOfAc preTxState0 (sender tx) = (preTxState0 (sender tx)) .^ _balance).
	          {
	            unfold balanceOfAc.
	            reflexivity.
	          }
	          rewrite Hbal_ac.
	          subst preBalN updBalN assBalN.
	          eapply N_le_ZtoN_of_Zle.
	          {
	            eapply Z.le_trans.
	            {
	              apply N2Z.is_nonneg.
	            }
	            {
	              exact Hlhs_le.
	            }
	          }
		          {
		            rewrite Hreserve_hist.
		            exact Hlhs_le.
		          }
	        }
	      }
      {
        rewrite Hpost_bal_formula.
        rewrite HmaxTxFee_eq.
        unfold debit in Hcur_debit.
        rewrite Hprex0 in Hnon.
        simpl in Hnon.
        destruct Hnon as [Hmain _].
        destruct Hmain as [Hbal_eq _].
        assert (Hbal_sender :
            (preTxState0 (sender tx)) .^ _balance = csAssumed .^ _balance).
        {
          first [exact Hbal_eq | symmetry; exact Hbal_eq].
        }
        assert (Hbal_ac :
            balanceOfAc preTxState0 (sender tx) = (preTxState0 (sender tx)) .^ _balance).
        {
          unfold balanceOfAc.
          reflexivity.
        }
        rewrite Hbal_ac.
        rewrite Hbal_sender.
        rewrite <- Horig_eq.
        rewrite Hreserve_hist.
        exact Hcur_debit.
      }
    }
  }
  }
Qed.
