Require Import skylabs.auto.cpp.proof.
Require Import stdpp.gmap.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_update_helpers.
Require Import monad.proofs.execproofs.reservebal.sender_rewrite_lemmas.
Import linearity.

Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".
#[local] Open Scope N_scope.

(* Direct contradiction: if fee is at most the modeled sender reserve floor,
   the strict-lt branch is impossible. *)
Lemma sender_fee_lt_false_from_fee_le_min
  (ctx : MonadChainContext)
  (stm : StateM)
  (tx : TxWithHdr) :
  let fee :=
    tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx) in
  let sender_min :=
    DefReserve
      `min`
    original_balance_pessimistic_model_map
      (preTxAssumedState stm)
      (sender tx) in
  (fee <= sender_min)%N ->
  (sender_min < fee)%N ->
  False.
Proof.
  intros fee sender_min Hle Hlt.
  lia.
Qed.

(* Variant that uses the validation-style lower bound on original balance,
   plus an explicit lower bound from the non-dipping side condition. *)
Lemma sender_fee_lt_false_from_validation_and_nondip
  (ctx : MonadChainContext)
  (stm : StateM)
  (tx : TxWithHdr) :
  let fee :=
    tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx) in
  let reserve := DefReserve in
  let orig :=
    original_balance_pessimistic_model_map
      (preTxAssumedState stm)
      (sender tx) in
  (fee <= orig)%N ->
  (fee <= reserve)%N ->
  (reserve `min` orig < fee)%N ->
  False.
Proof.
  intros fee reserve orig Hle_orig Hle_res Hlt.
  assert (Hle_min : (fee <= reserve `min` orig)%N) by lia.
  lia.
Qed.

(* Bridge: original balance pessimistic model is unchanged by exactness-map updates. *)
Lemma sender_orig_balance_updated_eq_pre
  (stm : StateM)
  (updates : _)
  (tx : TxWithHdr) :
  original_balance_pessimistic_model_map
    (update_assum_exactness_map (preTxAssumedState stm) updates)
    (sender tx) =
  original_balance_pessimistic_model_map
    (preTxAssumedState stm)
    (sender tx).
Proof.
  apply original_balance_pessimistic_model_map_update_assum_exactness_map.
Qed.

(* NOTE: intentionally omitted.
   The fee bridge between gas_price_model and maxTxFee was admitted and unused.
   Reintroduce only when a proof actually depends on it. *)

Lemma satisfiesAssumptions_to_true_relaxed
  (st : StateM)
  (preTxState : StateOfAccounts) :
  relaxedValidation st = true ->
  satisfiesAssumptions st preTxState ->
  satisfiesAssumptions' true (preTxAssumedState st) preTxState.
Proof.
  intros Hrel Hsat.
  unfold satisfiesAssumptions in Hsat.
  rewrite Hrel in Hsat.
    exact Hsat.
Qed.

Lemma satisfiesAssumptions'_false_to_true
  (a : MapModel evm.address AssumedPreTxAccountState)
  (preTxState : StateOfAccounts) :
  satisfiesAssumptions' false a preTxState ->
  satisfiesAssumptions' true a preTxState.
Proof.
  intros Hsat acAddr.
  specialize (Hsat acAddr).
  unfold satAccountAssumptions in Hsat |- *.
  destruct Hsat as [Hnon Hstor].
  split.
  {
    unfold satAccountNonStorageAssumptions in Hnon |- *.
    destruct (assumptionOfAddr a acAddr) as [assumed|] eqn:Ha.
    {
      destruct (exec_specs.preTxState assumed) as [cs|] eqn:Hpre.
      {
        simpl in Hnon |- *.
        destruct Hnon as [[Hbal_exact Hbal_min_ok] Hnonce_false].
        split.
        {
          destruct (isNone (min_balance (assumExactness assumed))) eqn:Hnone; simpl.
          {
            exact Hbal_exact.
          }
          {
            exact Hbal_min_ok.
          }
        }
        {
          destruct (nonce_exact (assumExactness assumed)); simpl.
          {
            exact Hnonce_false.
          }
          {
            exact I.
          }
        }
      }
      {
        simpl in Hnon.
        contradiction.
      }
    }
    {
      exact I.
    }
  }
  {
    exact Hstor.
  }
Qed.

Lemma satisfiesAssumptions_to_true
  (st : StateM)
  (preTxState : StateOfAccounts) :
  satisfiesAssumptions st preTxState ->
  satisfiesAssumptions' true (preTxAssumedState st) preTxState.
Proof.
  intros Hsat.
  unfold satisfiesAssumptions in Hsat.
  destruct (relaxedValidation st) eqn:Hrel; simpl in Hsat.
  {
    exact Hsat.
  }
  {
    eapply satisfiesAssumptions'_false_to_true.
    exact Hsat.
  }
Qed.

Lemma satisfiesAssumptions_to_true_relaxed_update_assum_exactness_state
  (stm : StateM)
  (updates : gmap evm.address AssumptionExactness)
  (preTxState : StateOfAccounts) :
  relaxedValidation stm = true ->
  satisfiesAssumptions (update_assum_exactness_state stm updates) preTxState ->
  satisfiesAssumptions' true
    (update_assum_exactness_map (preTxAssumedState stm) updates)
    preTxState.
Proof.
  intros Hrel Hsat.
  unfold satisfiesAssumptions in Hsat |- *.
  unfold update_assum_exactness_state in Hsat |- *.
  simpl in Hsat |- *.
  rewrite Hrel in Hsat.
  exact Hsat.
Qed.

Lemma option1_hyp_separate
  (stm : StateM)
  (updates : gmap evm.address AssumptionExactness)
  (preTxState : StateOfAccounts) :
  relaxedValidation stm = true ->
  satisfiesAssumptions
    {| relaxedValidation := relaxedValidation stm;
       preTxAssumedState := update_assum_exactness_map (preTxAssumedState stm) updates;
       newStates := newStates stm;
       blockStatePtr := blockStatePtr stm;
       indices := indices stm;
       blockStateGloc := blockStateGloc stm;
       dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
       codeMap := codeMap stm |}
    preTxState ->
  satisfiesAssumptions' true
    (update_assum_exactness_map (preTxAssumedState stm) updates)
    preTxState.
Proof.
  intros Hrel Hsat.
  unfold satisfiesAssumptions in Hsat.
  simpl in Hsat.
  rewrite Hrel in Hsat.
  exact Hsat.
Qed.


Unset SsrIdents.

Import evmmisc.
Locate EvmAddr.
Import exec_specs.

Lemma senderBalanceInsuff_aug :
  forall (ctx : MonadChainContext) (hist : ExtraAcStates) (stm : StateM)
         (nthElemPtr nthElemVstackTopPtr : ptr)
         (nthElemVstackTop : UpdatedAccountState)
         (nthElemVstackTl : list (ptr * UpdatedAccountState))
         (_t_ : gmap evm.address AssumptionExactness)
         (tx : TxWithHdr) (i : N) (x : ptr) (x0 : AssumedPreTxAccountState),
    let orig :=
      original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) in
    let fee_mod :=
      ((tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256)%N in
    let debit := (DefReserve `min` orig - fee_mod)%N in
    let cur := balanceOfAccount (postTxState nthElemVstackTop) in
    let ex0 := min_balance_update (assumExactness x0) orig orig DefReserve in
    let ex := min_balance_update ex0 orig cur debit in
    let stf := update_assum_exactness_state stm (<[sender tx := ex]> _t_) in
    NoDup
      (map
         (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
            (let '(a, (b, _)) := x in (a, b)).1)
         (newStates stm)) ->
    nth_error (newStates stm) (N.to_nat i) =
      Some (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
    validPostNone (update_assum_exactness_state stm _t_) ->
    isAcSC (postTxState nthElemVstackTop) = false ->
    (forall addr : EvmAddr, configuredReserveBal (hist addr) = DefReserve) ->
    mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) = Some (x, x0) ->
    ~(debit <= cur)%N ->
    (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)) < 2 ^ 256)%N ->
    maxTxFee tx = (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))%N ->
    (forall preTxState : StateOfAccounts,
        satisfiesAssumptions' true
          (update_assum_exactness_map (preTxAssumedState stm)
             (<[sender tx:=min_balance_update
                             (min_balance_update (assumExactness x0)
                                (original_balance_pessimistic_model_map
                                   (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                                (original_balance_pessimistic_model_map
                                   (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                                DefReserve)
                             (original_balance_pessimistic_model_map
                                (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                             (balanceOfAccount (postTxState nthElemVstackTop))
                             (DefReserve `min`
                                original_balance_pessimistic_model_map
                                  (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) - fee_mod)]>
                _t_))
          preTxState ->
        false = isAllowedToEmpty 3 (preTxState, hist) [] tx) ->
    forall preTxState : StateOfAccounts,
      satisfiesAssumptions stf preTxState ->
      true =
        ~~ allFinalBalSufficient 3 (preTxState, hist)
             (applyUpdates stf preTxState)
             (map fst (newStates stm)) tx.
Proof.
  intros ctx hist stm nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl _t_ tx i x x0.
  intros orig fee_mod debit cur ex0 ex stf.
  intros HnodupNew Hnth HvalidPostStf Hsc Hreserve_hist Hlookup Hnotle Hfee_lt Hfee_raw Hallow.
  intros preState Hsat.
  assert (Hsat_true_pre :
      satisfiesAssumptions' true
        (update_assum_exactness_map (preTxAssumedState stm)
           (<[sender tx:=min_balance_update
                           (min_balance_update (assumExactness x0)
                              (original_balance_pessimistic_model_map
                                 (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                              (original_balance_pessimistic_model_map
                                 (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                              DefReserve)
                           (original_balance_pessimistic_model_map
                              (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
                           (balanceOfAccount (postTxState nthElemVstackTop))
                           (DefReserve `min`
                              original_balance_pessimistic_model_map
                                (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) - fee_mod)]>
              _t_))
        preState).
  {
    pose proof
      (satisfiesAssumptions_to_true stf preState Hsat) as Hsat_true.
    unfold stf, update_assum_exactness_state in Hsat_true.
    simpl in Hsat_true.
    exact Hsat_true.
  }
  assert (Hmem :
      (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl))
        ∈ newStates stm).
  {
    apply list_elem_of_lookup_2 with (i := N.to_nat i).
    rewrite lookup_nth_error. exact Hnth.
  }
  assert (Hin :
      sender tx ∈ map fst (newStates stm)).
  {
    apply (proj2 (list_elem_of_fmap _ _ _)).
    exists (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
    split; [reflexivity|exact Hmem].
  }
  apply eq_sym.
  apply negb_true_iff.
  apply Bool.not_true_is_false.
  intro Hall.
  unfold allFinalBalSufficient in Hall.
  assert (Hall' :
      forall a,
        In a (map fst (newStates stm)) ->
        finalBalSufficient 3 (preState, hist)
          (applyUpdates stf preState) tx a = true).
  {
    apply forallb_forall.
    exact Hall.
  }
  apply list_elem_of_In in Hin.
  specialize (Hall' (sender tx) Hin).
  unfold finalBalSufficient in Hall'.
  set (post := applyUpdates stf preState) in *.
  assert (Hlookup_new :
      mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) =
        Some (x, x0)) by exact Hlookup.
  pose proof (mapModelLookup_update_assum_exactness_map_Some
                (preTxAssumedState stm) _t_ (sender tx) x x0 Hlookup_new)
    as (aps0 & Horig & Hpre & Hstorage & _Hassum).
  set (aps_new := {| preTxState := exec_specs.preTxState x0;
                     preTxStorage := exec_specs.preTxStorage x0;
                     assumExactness := ex |}).
  assert (Hlookup_upd :
      mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_))
        (sender tx) = Some (x, aps_new)).
  {
    rewrite mapModelLookup_update_assum_exactness_map.
    assert (Hupd_lookup : (<[sender tx := ex]> _t_) !! sender tx = Some ex).
    {
      rewrite lookup_insert.
      destruct (decide (sender tx = sender tx)) as [_|Hneq].
      - reflexivity.
      - exfalso. apply Hneq. reflexivity.
    }
    rewrite Hupd_lookup.
    rewrite Horig.
    simpl.
    rewrite <- Hpre.
    rewrite <- Hstorage.
    reflexivity.
  }
  assert (HnodupNew' : NoDup (map fst (newStates stm))).
  {
    replace (map fst (newStates stm)) with
      (map (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
              (let '(a, (b, _)) := x in (a, b)).1) (newStates stm)).
    {
      exact HnodupNew.
    }
    {
      apply map_ext. intros [a [b tl]]. simpl. reflexivity.
    }
  }
  assert (Hlookup_newStates :
      newStates stm !! (sender tx) =
        Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
  {
    apply elem_of_list_to_map_1; [exact HnodupNew'|exact Hmem].
  }
  assert (Hau :
      assumptionAndUpdateOfAddr stf (sender tx) =
        Some {| preAssumption := aps_new;
                originalLoc := x;
                txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}).
  {
    unfold assumptionAndUpdateOfAddr, stf; simpl.
    change ((update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_)) !! (sender tx))
      with (mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_)) (sender tx)).
    rewrite Hlookup_upd. simpl.
    rewrite Hlookup_newStates. simpl.
    reflexivity.
  }
  assert (Hmb_none : min_balance (assumExactness aps_new) = None).
  {
    unfold aps_new, ex, min_balance_update.
    unfold check_min_balance_ok.
    rewrite bool_decide_false; [reflexivity|].
    intro Hle0. apply Hnotle. exact Hle0.
  }
  assert (Hsat_sender_true :
      satAccountAssumptions true
        (assumptionOfAddr
           (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_))
           (sender tx))
        (Some (preState (sender tx)))).
  {
    unfold satisfiesAssumptions' in Hsat_true_pre.
    specialize (Hsat_true_pre (sender tx)).
    exact Hsat_true_pre.
  }
  unfold assumptionOfAddr in Hsat_sender_true.
  unfold stf, update_assum_exactness_state in Hsat_sender_true; simpl in Hsat_sender_true.
  change
    ((update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_)) !! (sender tx))
    with
      (mapModelLookup
         (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_))
         (sender tx)) in Hsat_sender_true.
  rewrite Hlookup_upd in Hsat_sender_true. simpl in Hsat_sender_true.
  unfold satAccountAssumptions in Hsat_sender_true.
  destruct Hsat_sender_true as [Hnon _Hstor].
  unfold satAccountNonStorageAssumptions in Hnon.
  simpl in Hnon.
  destruct (preTxState aps_new) as [csAssumed|] eqn:Hpre'.
		  {
		    rewrite Hpre' in Hnon; simpl in Hnon.
		    rewrite Hmb_none in Hnon; simpl in Hnon.
	    assert (Hbal_assum' :
	        csAssumed .^ _balance = (preState (sender tx)) .^ _balance).
	    {
	      destruct Hnon as [Hbal_assum _Hnonce].
	      exact Hbal_assum.
	    }
	    assert (Horig_eq :
	        orig = csAssumed .^ _balance).
    {
      unfold orig, original_balance_pessimistic_model_map, preTxAccountOf_map.
      rewrite Hlookup_new. simpl. rewrite Hpre'. reflexivity.
    }
    assert (Hactual_eq' :
        balanceOfAc preState (sender tx) =
          (preState (sender tx)) .^ _balance).
    {
      unfold balanceOfAc. simpl. reflexivity.
    }
    assert (Hactual_eq :
        balanceOfAc preState (sender tx) = csAssumed .^ _balance).
    {
      exact (eq_trans Hactual_eq' (eq_sym Hbal_assum')).
    }
    assert (Hpre_orig :
        balanceOfAc preState (sender tx) = orig).
    {
      rewrite Hactual_eq.
      symmetry.
      exact Horig_eq.
    }
    assert (Hpostbal :
        balanceOfAc post (sender tx) = cur).
    {
      unfold post, applyUpdates, balanceOfAc.
      rewrite Hau. simpl.
      unfold accountFinalVal.
      simpl.
      destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost; simpl.
      {
        destruct (relaxedValidation stm) eqn:Hrel0; simpl.
        {
          rewrite Hpre'. simpl.
          rewrite Hmb_none. simpl.
          destruct (nonce_exact ex) eqn:Hnonce; simpl;
            unfold balanceOfAccount, cur; simpl;
            destruct csUpdated; simpl; reflexivity.
        }
        {
          unfold balanceOfAccount, cur.
          simpl.
          destruct csUpdated; simpl.
          reflexivity.
        }
      }
      {
        exfalso.
        assert (Hpre_none_x0 : preTxState x0 = None).
        {
          apply (HvalidPostStf (sender tx) nthElemPtr
                   ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl) x x0).
          { exact Hlookup_newStates. }
          { exact Hlookup_new. }
          { exact Hpost. }
        }
        assert (Hpre_none : preTxState aps_new = None).
        {
          unfold aps_new. simpl. exact Hpre_none_x0.
        }
        rewrite Hpre' in Hpre_none. discriminate.
      }
    }
    pose proof (Hallow preState Hsat_true_pre) as Hallow_false.
    assert (Hscpost : isSC post (sender tx) = false).
    {
      unfold isSC, post, applyUpdates.
      rewrite Hau. simpl.
      set (fv :=
             accountFinalVal (relaxedValidation stf)
               {| preAssumption := aps_new;
                  originalLoc := x;
                  txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}
               (Some (preState (sender tx)))).
      change (isAcSC (Some (match fv with | None => dummyAc | Some fv' => fv' end)) = false).
      destruct fv as [fv'|] eqn:Hfv; simpl.
      {
        unfold fv in Hfv.
        unfold accountFinalVal in Hfv.
        simpl in Hfv.
        destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost; simpl in Hfv.
        {
          destruct (relaxedValidation stm) eqn:Hrel0; simpl in Hfv.
          {
            rewrite Hpre' in Hfv. simpl in Hfv.
            rewrite Hmb_none in Hfv. simpl in Hfv.
            destruct (nonce_exact ex) eqn:Hnonce; simpl in Hfv.
            {
              change (isAcSC (Some fv') = false).
              inversion Hfv; subst.
              assert (Hsc' : isAcSC (Some csUpdated) = false).
              { exact Hsc. }
              set (st :=
                     updateStorage
                       (Some (block.block_account_storage
                                (coreAc (preState (sender tx)))))
                       (Some csUpdated)) in *.
              change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
              repeat rewrite isAcSC_update_storage.
              exact Hsc'.
            }
            {
              change (isAcSC (Some fv') = false).
              inversion Hfv; subst.
              assert (Hsc' : isAcSC (Some csUpdated) = false).
              { exact Hsc. }
              set (st :=
                     updateStorage
                       (Some (block.block_account_storage
                                (coreAc (preState (sender tx)))))
                       (Some csUpdated)) in *.
              change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
              repeat rewrite isAcSC_update_nonce.
              repeat rewrite isAcSC_update_storage.
              exact Hsc'.
            }
          }
          {
            change (isAcSC (Some fv') = false).
            inversion Hfv; subst.
            assert (Hsc' : isAcSC (Some csUpdated) = false).
            { exact Hsc. }
            set (st :=
                   updateStorage
                     (Some (block.block_account_storage
                              (coreAc (preState (sender tx)))))
                     (Some csUpdated)) in *.
            change ((_coreAc .@ _block_account_storage .= st) csUpdated)
              with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
            repeat rewrite isAcSC_update_storage.
            exact Hsc'.
          }
        }
        {
          exfalso.
          assert (Hpre_none_x0 : preTxState x0 = None).
          {
            apply (HvalidPostStf (sender tx) nthElemPtr
                     ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl) x x0).
            { exact Hlookup_newStates. }
            { exact Hlookup_new. }
            { exact Hpost. }
          }
          assert (Hpre_none : preTxState aps_new = None).
          {
            unfold aps_new. simpl. exact Hpre_none_x0.
          }
          rewrite Hpre' in Hpre_none. discriminate.
        }
      }
	      {
	        unfold fv in Hfv.
	        unfold accountFinalVal in Hfv.
	        simpl in Hfv.
	        destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost; simpl in Hfv.
	        {
	          destruct (relaxedValidation stf) eqn:Hrel'; rewrite Hrel' in Hfv; simpl in Hfv.
	          {
	            destruct (preTxState (preAssumption {| preAssumption := aps_new;
	                                                   originalLoc := x;
	                                                   txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}))
	                as [csAssumed'|] eqn:Hpre''; rewrite Hpre'' in Hfv; simpl in Hfv.
	            {
	              try rewrite Hmb_none in Hfv; simpl in Hfv.
	              exfalso; now inversion Hfv.
	            }
	            {
	              try rewrite Hmb_none in Hfv; simpl in Hfv.
	              exfalso; now inversion Hfv.
	            }
	          }
	          {
	            exfalso; now inversion Hfv.
	          }
	        }
	        {
	          assert (Hpre_none_x0 : preTxState x0 = None).
	          {
	            apply (HvalidPostStf (sender tx) nthElemPtr
	                     ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl) x x0).
	            { exact Hlookup_newStates. }
	            { exact Hlookup_new. }
	            { exact Hpost. }
	          }
	          assert (Hpre_none : preTxState aps_new = None).
	          {
	            unfold aps_new. simpl. exact Hpre_none_x0.
	          }
	          rewrite Hpre' in Hpre_none. discriminate.
	        }
	      }
    }
    rewrite Hscpost in Hall'.
    simpl in Hall'.
    rewrite bool_decide_true in Hall'; [|reflexivity].
    change (isAllowedToEmptyExec 3 (preState, hist) tx)
      with (isAllowedToEmpty 3 (preState, hist) [] tx) in Hall'.
    rewrite <- Hallow_false in Hall'.
    simpl in Hall'.
    apply andb_prop in Hall' as [_ Hall'].
    apply bool_decide_eq_true_1 in Hall'.
    unfold configuredReserveBalOfAddr in Hall'.
    rewrite Hreserve_hist in Hall'.
    rewrite Hpre_orig in Hall'.
    rewrite Hpostbal in Hall'.
    assert (Hfee_eq : maxTxFee tx = fee_mod).
    {
      change
        (maxTxFee tx =
           ((tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256)%N).
      rewrite Hfee_raw.
      rewrite N.mod_small; [reflexivity|exact Hfee_lt].
    }
    rewrite Hfee_eq in Hall'.
    apply Hnotle.
    exact Hall'.
  }
  {
    rewrite Hpre' in Hnon. simpl in Hnon. contradiction.
  }
Qed.

Lemma senderLowBalAndCannotDipIntoReseve :
  forall (ctx : MonadChainContext) (hist : ExtraAcStates) (stm : StateM)
         (nthElemPtr nthElemVstackTopPtr : ptr)
         (nthElemVstackTop : UpdatedAccountState)
         (nthElemVstackTl : list (ptr * UpdatedAccountState))
         (_t_ : gmap evm.address AssumptionExactness)
         (tx : TxWithHdr) (_i_ : nat) (i : N) (x : ptr) (x0 : AssumedPreTxAccountState),
    let orig :=
      original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) _t_)
        (sender tx) in
    let fee_mod :=
      ((tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))
        `mod` 2 ^ 256)%N in
    let debit := (DefReserve `min` orig - fee_mod)%N in
    let cur := balanceOfAccount (postTxState nthElemVstackTop) in
    let ex0 := min_balance_update (assumExactness x0) orig orig DefReserve in
    let ex := min_balance_update ex0 orig cur debit in
    let stf := update_assum_exactness_state stm (<[sender tx := ex]> _t_) in
    map fst (newStates stm) ⊆ map fst (preTxAssumedState stm) ->
    validStateM (update_assum_exactness_state stm _t_) ->
    validPostNone (update_assum_exactness_state stm _t_) ->
    validSliceInvariants (update_assum_exactness_state stm _t_) ->
    NoDup
      (map
         (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
            (let '(a, (b, _)) := x in (a, b)).1)
         (newStates stm)) ->
    nth_error (newStates stm) (N.to_nat i) =
      Some (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
    isAcSC (postTxState nthElemVstackTop) = false ->
    (forall addr : EvmAddr, configuredReserveBal (hist addr) = DefReserve) ->
    mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) = Some (x, x0) ->
    ~(debit <= cur)%N ->
    validTx tx ->
    option_map (fun t0 => (t0, header (currentBlock (blocks ctx))))
      (nth_error (transactions (currentBlock (blocks ctx))) _i_) = Some tx ->
    (forall preTxState : StateOfAccounts,
        satisfiesAssumptions' true
          (update_assum_exactness_map (preTxAssumedState stm)
             (<[sender tx := ex]> _t_))
          preTxState ->
        false = isAllowedToEmpty 3 (preTxState, hist) [] tx) ->
    validModel stf /\
    forall preTxState : StateOfAccounts,
      satisfiesAssumptions stf preTxState ->
      true =
        ~~ allFinalBalSufficient 3 (preTxState, hist)
             (applyUpdates stf preTxState)
             (map fst (newStates stm)) tx.
Proof.
  intros ctx hist stm nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl _t_ tx _i_ i x x0.
  intros orig fee_mod debit cur ex0 ex stf.
  intros Hmapfst HvalidState HvalidPost HvalidSlice Hnodup Hnth Hsc Hreserve_hist Hlookup Hnotle HvalidTx Htxidx Hallow.
  split.
  {
    assert (Hvalid_update : validModel (update_assum_exactness_state stm _t_)).
    {
      apply (validModel_of_components_update_assum_exactness_state stm _t_); eauto.
    }
    unfold stf, ex, ex0, orig.
    exact (sender_insert_validModel_twice stm _t_ tx x x0 cur debit Hvalid_update Hlookup).
  }
  {
    intros preTxState Hsat.
    unfold ex, ex0, debit, fee_mod, orig, cur in *.
    pose proof (tx_base_fee_per_gas_eq_of_txidx ctx _i_ tx Htxidx) as Hfee_base.
    assert (Hfee_lt :
      (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)) < 2 ^ 256)%N).
    {
      exact (gas_fee_model_lt_2_256_of_validTx_ctx ctx tx HvalidTx Hfee_base).
    }
    assert (Hfee_raw :
      maxTxFee tx = (tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))%N).
    {
      exact (maxTxFee_eq_fee_raw_of_validTx_ctx ctx tx HvalidTx Hfee_base).
    }
    eapply (senderBalanceInsuff_aug
              ctx hist stm nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl
              _t_ tx i x x0).
    { exact Hnodup. }                        (* HnodupNew *)
    { exact Hnth. }                          (* Hnth *)
    { exact HvalidPost. }                    (* HvalidPostStf *)
    { exact Hsc. }                           (* Hsc *)
    { eassumption. }                         (* Hreserve_hist *)
    { exact Hlookup. }                       (* Hlookup *)
    { exact Hnotle. }                        (* Hnotle *)
    { exact Hfee_lt. }                       (* Hfee_lt *)
    { exact Hfee_raw. }                      (* Hfee_raw *)
    { exact Hallow. }                        (* Hallow *)
    exact Hsat.
  }
Qed.




Lemma senderLowBalAndCanDipIntoReseve :
  forall (ctx : MonadChainContext) (hist : ExtraAcStates) (stm : StateM)
    (nthElemPtr nthElemVstackTopPtr : ptr)
    (nthElemVstackTop : UpdatedAccountState)
    (nthElemVstackTl : list (ptr * UpdatedAccountState))
    (_t_ : gmap evm.address AssumptionExactness)
    (tx : TxWithHdr) (x : ptr) (x0 : AssumedPreTxAccountState) (i : N),
    NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) (newStates stm))) ->
    nth_error (newStates stm) (N.to_nat i) =
      Some (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
    (forall preTxState : StateOfAccounts,
        satisfiesAssumptions (update_assum_exactness_state stm _t_) preTxState ->
        historyConsistent ctx hist ->
        true =
          allFinalBalSufficient 3 (preTxState, hist)
            (applyUpdates (update_assum_exactness_state stm _t_) preTxState)
            (map fst (takeN i (newStates stm))) tx) ->
    validModel (update_assum_exactness_state stm _t_) ->
    mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) =
      Some (x, x0) ->
    let orig :=
      original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) in
    let fee_mod :=
      ((tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))
       `mod` 2 ^ 256)%N in
    let debit := (DefReserve `min` orig - fee_mod)%N in
    let cur := balanceOfAccount (postTxState nthElemVstackTop) in
    let ex0 := min_balance_update (assumExactness x0) orig orig DefReserve in
    let ex := min_balance_update ex0 orig cur debit in
    (forall preTxState : StateOfAccounts,
        satisfiesAssumptions' true
          (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex]> _t_))
          preTxState ->
        true = isAllowedToEmpty 3 (preTxState, hist) [] tx) ->
    validModel (update_assum_exactness_state stm (<[sender tx := ex]> _t_))
    /\
    forall preTxState : StateOfAccounts,
      satisfiesAssumptions
        (update_assum_exactness_state stm (<[sender tx := ex]> _t_))
        preTxState ->
      historyConsistent ctx hist ->
      true =
        allFinalBalSufficient 3 (preTxState, hist)
          (applyUpdates
             (update_assum_exactness_state stm (<[sender tx := ex]> _t_))
             preTxState)
          (map fst (takeN (1 + i) (newStates stm))) tx.
Proof.
  intros ctx hist stm nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl _t_ tx x x0 i.
  intros Hnodup Hnth Hall_i Hvalid_update Hlookup.
  cbn.
  intros Hallow.
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
    intros preTxState Hsat Hhist.
    eapply (allFinalBalSufficient_takeN_succ
              stf ctx hist tx i (sender tx) nthElemPtr
              ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
    {
      intros preTxState0 Hsat0.
      eapply (allFinalBalSufficient_takeN_i_update_assum_exactness_state_insert
                stm ctx hist tx i (sender tx) nthElemPtr
                ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)
                _t_ ex preTxState0 x x0).
      { exact Hnodup. }
      { exact Hnth. }
      {
        intros preTxState1 Hsat1.
        eapply Hall_i; eauto.
      }
      { exact Hvalid_update. }
      { exact Hlookup. }
      { exact Hstr_ex. }
      { exact Hsat0. }
    }
    { exact Hnth_stf. }
    {
      intros preTxState0 Hsat0.
      unfold finalBalSufficient.
      destruct (isSC (applyUpdates stf preTxState0) (sender tx)); [reflexivity|].
      rewrite bool_decide_true; [|reflexivity].
      change (isAllowedToEmptyExec 3 (preTxState0, hist) tx)
        with (isAllowedToEmpty 3 (preTxState0, hist) [] tx).
      pose proof
        (satisfiesAssumptions_to_true stf preTxState0 Hsat0) as Hsat_true.
      unfold stf, update_assum_exactness_state in Hsat_true.
      simpl in Hsat_true.
      pose proof (Hallow preTxState0 Hsat_true) as Hallow_true.
      rewrite <- Hallow_true.
      reflexivity.
    }
    { exact Hsat. }
  }
Qed.


(* similar to senderLowBalAndCannotDipIntoReseve, but in this case, sender's balance is even lower than the reserve so in the code below
from reserve_balance.cpp, violation_threshold.has_value() is false, so 
state.check_min_balance(addr, violation_threshold.value()) is skipped so it does not modify the State::origina_ further with modified balance constraits due to the reads of balance 

        if (!violation_threshold.has_value() ||
            !state.check_min_balance(addr, violation_threshold.value())) {

 *)

Lemma senderReallyLowBalAndCannotDipIntoReseve:
  ∀ (ctx : MonadChainContext) (i : nat) (hist : ExtraAcStates) (stm : StateM)
    (nthElemPtr nthElemVstackTopPtr : ptr) (nthElemVstackTop : UpdatedAccountState)
    (nthElemVstackTl : list (ptr * UpdatedAccountState))
    (_t_ : gmap evm.address AssumptionExactness)
    (tx := nth i (map (λ t : Transaction, (t, header (cblock ctx))) (transactions (cblock ctx))) dummyTx)
    (aps : AssumedPreTxAccountState) (t : N) (loc : ptr),
    validTx tx
    → (∀ addr : EvmAddr, configuredReserveBal (hist addr) = DefReserve)
      → updates_stricter stm _t_
        → nth_error (newStates stm) (N.to_nat t) =
          Some (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl))
          → NoDup
              (map (λ x : evm.address * (ptr * list (ptr * UpdatedAccountState)), (let '(a, (b, _)) := x in (a, b)).1)
                 (newStates stm))
            → NoDup
                (map (λ x : evm.address * (ptr * AssumedPreTxAccountState), (let '(a, (b, _)) := x in (a, b)).1)
                   (update_assum_exactness_map (preTxAssumedState stm) _t_))
              → validModel (update_assum_exactness_state stm _t_)
                → false = isAcSC (postTxState nthElemVstackTop)
                  → option_map (λ t0 : Transaction, (t0, header (currentBlock (blocks ctx))))
                          (nth_error (transactions (currentBlock (blocks ctx))) i) =
                        Some
                          (nth i
                             (map (λ t0 : Transaction, (t0, header (currentBlock (blocks ctx))))
                                (transactions (currentBlock (blocks ctx))))
                             dummyTx)
                        → (DefReserve
                           `min` original_balance_pessimistic_model_map
                                   (update_assum_exactness_map (preTxAssumedState stm) _t_)
                                   (sender tx) <
                           (tx_gas_limit tx.1.1 *
                            gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))
                           `mod` 2 ^ 256)%N
                          → (∀ preTxState : StateOfAccounts,
                               satisfiesAssumptions' true
                                 (check_min_original_balance_update
                                    (update_assum_exactness_map (preTxAssumedState stm) _t_)
                                    (sender tx) DefReserve)
                                 preTxState
                               → false = isAllowedToEmpty 3 (preTxState, hist) [] tx)
                            → mapModelLookup
                                (update_assum_exactness_map (preTxAssumedState stm) _t_)
                                (sender tx) =
                              Some (loc, aps)
                              → validModel
                                  {|
                                    relaxedValidation := relaxedValidation stm;
                                    preTxAssumedState :=
                                      update_assum_exactness_map
                                        (preTxAssumedState stm)
                                        (<[sender tx:=min_balance_update
                                                       (assumExactness aps)
                                                       (original_balance_pessimistic_model_map
                                                          (update_assum_exactness_map
                                                             (preTxAssumedState stm) _t_)
                                                          (sender tx))
                                                       (original_balance_pessimistic_model_map
                                                          (update_assum_exactness_map
                                                             (preTxAssumedState stm) _t_)
                                                          (sender tx))
                                                       DefReserve]>
                                           _t_);
                                    newStates := newStates stm;
                                    blockStatePtr := blockStatePtr stm;
                                    indices := indices stm;
                                    blockStateGloc := blockStateGloc stm;
                                    dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                    codeMap := codeMap stm
                                  |}
                                ∧ updates_stricter stm
                                    (<[sender tx:=min_balance_update
                                                    (assumExactness aps)
                                                    (original_balance_pessimistic_model_map
                                                       (update_assum_exactness_map
                                                          (preTxAssumedState stm) _t_)
                                                       (sender tx))
                                                    (original_balance_pessimistic_model_map
                                                       (update_assum_exactness_map
                                                          (preTxAssumedState stm) _t_)
                                                       (sender tx))
                                                    DefReserve]>
                                       _t_)
                                  ∧ ∀ preTxState : StateOfAccounts,
                                      satisfiesAssumptions
                                        {|
                                          relaxedValidation := relaxedValidation stm;
                                          preTxAssumedState :=
                                            update_assum_exactness_map
                                              (preTxAssumedState stm)
                                              (<[sender tx:=min_balance_update
                                                             (assumExactness aps)
                                                             (original_balance_pessimistic_model_map
                                                                (update_assum_exactness_map
                                                                   (preTxAssumedState stm) _t_)
                                                                (sender tx))
                                                             (original_balance_pessimistic_model_map
                                                                (update_assum_exactness_map
                                                                   (preTxAssumedState stm) _t_)
                                                                (sender tx))
                                                             DefReserve]>
                                                 _t_);
                                          newStates := newStates stm;
                                          blockStatePtr := blockStatePtr stm;
                                          indices := indices stm;
                                          blockStateGloc := blockStateGloc stm;
                                          dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                          codeMap := codeMap stm
                                        |} preTxState
                                      → true =
                                        ~~
                                        allFinalBalSufficient 3 (preTxState, hist)
                                          (applyUpdates
                                             {|
                                               relaxedValidation := relaxedValidation stm;
                                               preTxAssumedState :=
                                                 update_assum_exactness_map
                                                   (preTxAssumedState stm)
                                                   (<[sender tx:=min_balance_update
                                                                  (assumExactness aps)
                                                                  (original_balance_pessimistic_model_map
                                                                    (update_assum_exactness_map
                                                                    (preTxAssumedState stm) _t_)
                                                                    (sender tx))
                                                                  (original_balance_pessimistic_model_map
                                                                    (update_assum_exactness_map
                                                                    (preTxAssumedState stm) _t_)
                                                                    (sender tx))
                                                                  DefReserve]>
                                                      _t_);
                                               newStates := newStates stm;
                                               blockStatePtr := blockStatePtr stm;
                                               indices := indices stm;
                                               blockStateGloc := blockStateGloc stm;
                                               dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                               codeMap := codeMap stm
                                             |} preTxState)
                                          (map fst (newStates stm)) tx.
Proof.
  intros ctx i hist stm.
  intros nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl _t_ tx aps t loc.
  intros HvalidTx Hreserve_hist Hstr_updates Hnth Hnodup_new Hnodup_update.
  intros Hvalid_update Hsc_false Htxidx Hlow.
  intros Hcannot_empty Hlookup.
  set (orig :=
         original_balance_pessimistic_model_map
           (update_assum_exactness_map (preTxAssumedState stm) _t_)
           (sender tx)).
  set (ex0 := min_balance_update (assumExactness aps) orig orig DefReserve).
  set (stf := update_assum_exactness_state stm (<[sender tx := ex0]> _t_)).
  assert (Hvalid_stf : validModel stf).
  {
    unfold stf, ex0, orig.
    exact (sender_insert_validModel_once stm _t_ tx loc aps Hvalid_update Hlookup).
  }
  split.
  {
    exact Hvalid_stf.
  }
  assert (Hstr_insert : updates_stricter stm (<[sender tx := ex0]> _t_)).
  {
    unfold ex0, orig.
    exact (sender_insert_updates_stricter_once stm _t_ tx loc aps Hstr_updates Hlookup).
  }
  split.
  {
    exact Hstr_insert.
  }
  intros preState Hsat.
  pose proof (satisfiesAssumptions_to_true stf preState Hsat) as Hsat_true.
  pose proof
    (nodup_map_fst_update_assum_exactness_map
       (preTxAssumedState stm) _t_ Hnodup_update) as Hnodup_update_fst.
  pose proof
    (sender_check_min_eq_of_lookup
       stm _t_ tx loc aps ex0 Hnodup_update_fst Hlookup eq_refl) as Hcheck_eq.
  unfold stf, update_assum_exactness_state in Hsat_true.
  simpl in Hsat_true.
  rewrite <- Hcheck_eq in Hsat_true.
  pose proof (Hcannot_empty preState Hsat_true) as Hallow_false.
  apply eq_sym.
  apply negb_true_iff.
  apply Bool.not_true_is_false.
  intro Hall_all.
  unfold allFinalBalSufficient in Hall_all.
  assert (Hmem_sender :
    (sender tx,
     (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl))
      ∈ newStates stm).
  {
    apply list_elem_of_lookup_2 with (i := N.to_nat t).
    rewrite lookup_nth_error.
    exact Hnth.
  }
  assert (Hin_sender :
    sender tx ∈ map fst (newStates stm)).
  {
    apply (proj2 (list_elem_of_fmap _ _ _)).
    exists
      (sender tx,
       (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
    split; [reflexivity|exact Hmem_sender].
  }
  apply list_elem_of_In in Hin_sender.
  apply forallb_forall with (x := sender tx) in Hall_all; [|exact Hin_sender].
  unfold finalBalSufficient in Hall_all.
  set (post := applyUpdates stf preState) in *.
  assert (Hlookup_new :
    mapModelLookup (newStates stm) (sender tx) =
    Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
  {
    pose proof (NoDup_map_fst_newStates_of_map_key_ptr stm Hnodup_new) as Hnodup_new_plain.
    apply elem_of_list_to_map_1; [exact Hnodup_new_plain|exact Hmem_sender].
  }
  assert (Hlookup_upd :
    mapModelLookup
      (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx := ex0]> _t_))
      (sender tx) =
    Some (loc, {| preTxState := exec_specs.preTxState aps;
                  preTxStorage := exec_specs.preTxStorage aps;
                  assumExactness := ex0 |})).
  {
    pose proof
      (mapModelLookup_update_assum_exactness_map_Some
         (preTxAssumedState stm) _t_ (sender tx) loc aps Hlookup)
      as (aps0 & Horig_lookup & Hpre_lookup & Hstorage_lookup & _Hassum_lookup).
    rewrite mapModelLookup_update_assum_exactness_map.
    assert (Hupd_lookup : (<[sender tx := ex0]> _t_) !! sender tx = Some ex0).
    {
      rewrite lookup_insert.
      destruct (decide (sender tx = sender tx)) as [_|Hneq].
      - reflexivity.
      - exfalso. apply Hneq. reflexivity.
    }
    rewrite Hupd_lookup.
    rewrite Horig_lookup.
    simpl.
    rewrite <- Hpre_lookup.
    rewrite <- Hstorage_lookup.
    reflexivity.
  }
  assert (Hau :
    assumptionAndUpdateOfAddr stf (sender tx) =
      Some
        {| preAssumption := {| preTxState := exec_specs.preTxState aps;
                               preTxStorage := exec_specs.preTxStorage aps;
                               assumExactness := ex0 |};
           originalLoc := loc;
           txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}).
  {
    unfold assumptionAndUpdateOfAddr, stf, update_assum_exactness_state.
    simpl.
    change
      ((update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex0]> _t_)) !! sender tx)
      with
        (mapModelLookup
           (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex0]> _t_))
           (sender tx)).
    rewrite Hlookup_upd. simpl.
    change ((newStates stm) !! sender tx)
      with (mapModelLookup (newStates stm) (sender tx)).
    rewrite Hlookup_new. simpl.
    reflexivity.
  }
  pose proof (Hsat_true (sender tx)) as Hsat_sender.
  rewrite Hcheck_eq in Hsat_sender.
  unfold satAccountAssumptions in Hsat_sender.
  destruct Hsat_sender as [Hnon_sender _Hstor_sender].
  unfold satAccountNonStorageAssumptions in Hnon_sender.
  unfold assumptionOfAddr in Hnon_sender.
  change
    ((update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex0]> _t_)) !! sender tx)
    with
      (mapModelLookup
         (update_assum_exactness_map (preTxAssumedState stm) (<[sender tx:=ex0]> _t_))
         (sender tx))
    in Hnon_sender.
  rewrite Hlookup_upd in Hnon_sender.
  simpl in Hnon_sender.
  destruct (exec_specs.preTxState aps) as [csAssumed|] eqn:Hpre_aps.
  {
    assert (Horig_cs : orig = csAssumed .^ _balance).
    {
      unfold orig, original_balance_pessimistic_model_map, preTxAccountOf_map.
      rewrite Hlookup. simpl. rewrite Hpre_aps. reflexivity.
    }
    assert (Hsc_post : isSC post (sender tx) = false).
    {
      unfold post, isSC, applyUpdates.
      rewrite Hau. simpl.
      set (fv :=
             accountFinalVal (relaxedValidation stf)
               {| preAssumption := {| preTxState := exec_specs.preTxState aps;
                                      preTxStorage := exec_specs.preTxStorage aps;
                                      assumExactness := ex0 |};
                  originalLoc := loc;
                  txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}
               (Some (preState (sender tx)))).
      destruct fv as [fv'|] eqn:Hfv; simpl.
      {
        unfold fv in Hfv.
        unfold accountFinalVal in Hfv.
        simpl in Hfv.
        destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost; simpl in Hfv.
        {
          assert (Hsc_upd : isAcSC (Some csUpdated) = false).
          {
            symmetry.
            exact Hsc_false.
          }
          destruct (relaxedValidation stf) eqn:Hrel; simpl in Hfv.
          {
            rewrite Hpre_aps in Hfv. simpl in Hfv.
            destruct (isNone (min_balance ex0)) eqn:Hnone; simpl in Hfv.
            {
              destruct (nonce_exact ex0) eqn:Hnonce; simpl in Hfv.
              {
                inversion Hfv; subst.
                set (st :=
                       updateStorage
                         (Some (block.block_account_storage
                                  (coreAc (preState (sender tx)))))
                         (Some csUpdated)) in *.
                change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                  with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                repeat rewrite isAcSC_update_storage.
                unfold stf, update_assum_exactness_state in Hrel; simpl in Hrel.
                rewrite Hrel in H0; simpl in H0.
                inversion H0; subst; clear H0.
                unfold isAcSC in Hsc_upd |- *; simpl in *.
                try rewrite Hfv; simpl.
                destruct csUpdated; simpl in *.
                destruct coreAc; simpl in *.
                exact Hsc_upd.
              }
              {
                inversion Hfv; subst.
                set (st :=
                       updateStorage
                         (Some (block.block_account_storage
                                  (coreAc (preState (sender tx)))))
                         (Some csUpdated)) in *.
                change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                  with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                repeat rewrite isAcSC_update_nonce.
                repeat rewrite isAcSC_update_storage.
                unfold stf, update_assum_exactness_state in Hrel; simpl in Hrel.
                rewrite Hrel in H0; simpl in H0.
                inversion H0; subst; clear H0.
                unfold isAcSC in Hsc_upd |- *; simpl in *.
                try rewrite Hfv; simpl.
                destruct csUpdated; simpl in *.
                destruct coreAc; simpl in *.
                exact Hsc_upd.
              }
            }
            {
              destruct (nonce_exact ex0) eqn:Hnonce; simpl in Hfv.
              {
                inversion Hfv; subst.
                set (st :=
                       updateStorage
                         (Some (block.block_account_storage
                                  (coreAc (preState (sender tx)))))
                         (Some csUpdated)) in *.
                change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                  with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                repeat rewrite isAcSC_update_storage.
                unfold stf, update_assum_exactness_state in Hrel; simpl in Hrel.
                rewrite Hrel in H0; simpl in H0.
                inversion H0; subst; clear H0.
                unfold isAcSC in Hsc_upd |- *; simpl in *.
                try rewrite Hfv; simpl.
                destruct csUpdated; simpl in *.
                destruct coreAc; simpl in *.
                exact Hsc_upd.
              }
              {
                inversion Hfv; subst.
                set (st :=
                       updateStorage
                         (Some (block.block_account_storage
                                  (coreAc (preState (sender tx)))))
                         (Some csUpdated)) in *.
                change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                  with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                repeat rewrite isAcSC_update_nonce.
                repeat rewrite isAcSC_update_storage.
                unfold stf, update_assum_exactness_state in Hrel; simpl in Hrel.
                rewrite Hrel in H0; simpl in H0.
                inversion H0; subst; clear H0.
                unfold isAcSC in Hsc_upd |- *; simpl in *.
                try rewrite Hfv; simpl.
                destruct csUpdated; simpl in *.
                destruct coreAc; simpl in *.
                exact Hsc_upd.
              }
            }
          }
          {
            inversion Hfv; subst.
            set (st :=
                   updateStorage
                     (Some (block.block_account_storage
                              (coreAc (preState (sender tx)))))
                     (Some csUpdated)) in *.
            change ((_coreAc .@ _block_account_storage .= st) csUpdated)
              with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
            repeat rewrite isAcSC_update_storage.
            unfold stf, update_assum_exactness_state in Hrel; simpl in Hrel.
            rewrite Hrel in H0; simpl in H0.
            inversion H0; subst; clear H0.
            rewrite Hrel in Hfv.
            rewrite Hrel.
            simpl in *.
            unfold isAcSC in Hsc_upd |- *; simpl in *.
            try rewrite Hfv; simpl.
            destruct csUpdated; simpl in *.
            destruct coreAc; simpl in *.
            exact Hsc_upd.
          }
        }
        {
          simpl in Hfv.
          discriminate.
        }
      }
      {
        pose proof (validModel_validPostNone stf Hvalid_stf) as HvalidPost_stf.
        assert (Hlookup_new_stf :
          mapModelLookup (newStates stf) (sender tx) =
          Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
        {
          unfold stf, update_assum_exactness_state.
          simpl.
          exact Hlookup_new.
        }
        assert (Hlookup_pre_stf :
          mapModelLookup (preTxAssumedState stf) (sender tx) =
          Some (loc, {| preTxState := exec_specs.preTxState aps;
                        preTxStorage := exec_specs.preTxStorage aps;
                        assumExactness := ex0 |})).
        {
          unfold stf, update_assum_exactness_state.
          simpl.
          rewrite Hpre_aps.
          exact Hlookup_upd.
        }
        specialize
          (HvalidPost_stf (sender tx) nthElemPtr
             ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)
             loc {| preTxState := exec_specs.preTxState aps;
                    preTxStorage := exec_specs.preTxStorage aps;
                    assumExactness := ex0 |}
             Hlookup_new_stf Hlookup_pre_stf).
        simpl in HvalidPost_stf.
        destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost.
        {
          exfalso.
          unfold fv in Hfv.
          unfold accountFinalVal in Hfv.
          simpl in Hfv.
          rewrite Hpre_aps in Hfv.
          rewrite Hpost in Hfv.
          destruct (relaxedValidation stm); simpl in Hfv; discriminate.
        }
        {
          exfalso.
          specialize (HvalidPost_stf eq_refl).
          rewrite Hpre_aps in HvalidPost_stf.
          congruence.
        }
      }
    }
    rewrite Hsc_post in Hall_all.
    simpl in Hall_all.
    rewrite bool_decide_true in Hall_all; [|reflexivity].
    change (isAllowedToEmptyExec 3 (preState, hist) tx)
      with (isAllowedToEmpty 3 (preState, hist) [] tx) in Hall_all.
    rewrite <- Hallow_false in Hall_all.
    simpl in Hall_all.
    apply andb_prop in Hall_all as [Hfee_le_actual _].
    apply bool_decide_eq_true_1 in Hfee_le_actual.
    unfold configuredReserveBalOfAddr in Hfee_le_actual.
    rewrite Hreserve_hist in Hfee_le_actual.
    unfold balanceOfAc in Hfee_le_actual.
    simpl in Hfee_le_actual.
    assert (Herb_le :
      (DefReserve `min` balanceOfAc preState (sender tx)
       <= DefReserve `min` orig)%N).
    {
      unfold balanceOfAc.
      destruct Hnon_sender as [Hbal_part _Hnonce_part].
      destruct (isNone (min_balance ex0)) eqn:Hnone.
      {
        simpl in Hbal_part.
        assert (Hpre_bal_eq : (balanceOfAc preState (sender tx) = orig)%N).
        {
          unfold balanceOfAc.
          rewrite Horig_cs.
          symmetry.
          exact Hbal_part.
        }
        unfold balanceOfAc in Hpre_bal_eq.
        simpl in Hpre_bal_eq.
        rewrite Hpre_bal_eq.
        reflexivity.
      }
      {
        simpl in Hbal_part.
        assert (Horig_ge_def : (DefReserve <= orig)%N).
        {
          destruct (decide (DefReserve <= orig)%N) as [Hok|Hok].
          {
            exact Hok.
          }
          {
            exfalso.
            unfold ex0 in Hnone.
            unfold min_balance_update, check_min_balance_ok in Hnone.
            rewrite bool_decide_false in Hnone; [|exact Hok].
            simpl in Hnone.
            discriminate.
          }
        }
        assert (Hmb_le_pre :
          (min_balanceN ex0 <= balance (preState (sender tx)))%N).
        {
          destruct (isSome (min_balance ex0)) eqn:Hsome.
          {
            simpl in Hbal_part.
            exact Hbal_part.
          }
          {
            exfalso.
            assert (HisNone_true : isNone (min_balance ex0) = true).
            {
              destruct (min_balance ex0) as [m|] eqn:Hmb; simpl in Hsome.
              {
                discriminate.
              }
              {
                reflexivity.
              }
            }
            rewrite Hnone in HisNone_true.
            discriminate.
          }
        }
        assert (Hdef_le_mb : (DefReserve <= min_balanceN ex0)%N).
        {
          assert (Hok1 : check_min_balance_ok orig DefReserve = true).
          {
            unfold check_min_balance_ok.
            destruct (bool_decide (DefReserve <= orig)%N) eqn:Hok.
            {
              reflexivity.
            }
            {
              apply bool_decide_eq_false_1 in Hok.
              exfalso.
              nia.
            }
          }
          pose proof (min_balance_update_lower_bound (assumExactness aps) orig orig DefReserve Hok1) as Hlb.
          unfold ex0 in Hlb.
          destruct (min_balance (min_balance_update (assumExactness aps) orig orig DefReserve)) as [m|] eqn:Hm.
          {
            simpl in Hlb.
            unfold min_balanceN.
            rewrite Hm.
            simpl.
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
                  exact Horig_ge_def.
                }
              }
              {
                nia.
              }
            }
            rewrite <- Hsub.
            exact Hlb.
          }
          {
            unfold ex0 in Hnone.
            rewrite Hm in Hnone.
            simpl in Hnone.
            discriminate.
          }
        }
        assert (Hdef_le_pre : (DefReserve <= balance (preState (sender tx)))%N).
        {
          eapply N.le_trans; [exact Hdef_le_mb|exact Hmb_le_pre].
        }
        rewrite N.min_l; [|exact Hdef_le_pre].
        rewrite N.min_l; [|exact Horig_ge_def].
        apply N.le_refl.
      }
    }
    pose proof (tx_base_fee_per_gas_eq_of_txidx ctx i tx Htxidx) as Hfee_base.
    assert (Hfee_eq :
      maxTxFee tx =
      ((tx_gas_limit tx.1.1 * gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx)))
       `mod` 2 ^ 256)%N).
    {
      exact (maxTxFee_eq_fee_mod_of_validTx_ctx ctx tx HvalidTx Hfee_base).
    }
    assert (Hfee_le_orig : (maxTxFee tx <= DefReserve `min` orig)%N).
    {
      eapply N.le_trans.
      { exact Hfee_le_actual. }
      { exact Herb_le. }
    }
    rewrite Hfee_eq in Hfee_le_orig.
    unfold orig in Hfee_le_orig.
    apply N.nlt_ge in Hfee_le_orig.
    apply Hfee_le_orig.
    apply N2Z.inj_lt.
    zify.
    assert
      ((tx_gas_limit tx.1.1 *
        gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `rem` 2 ^ 256 =
       (tx_gas_limit tx.1.1 *
        gas_price_model 9 tx.1 (base_fee_per_gas (cblock ctx))) `mod` 2 ^ 256) as Hrem_mod.
    {
      apply Z.rem_mod_nonneg; nia.
    }
    exact Hlow.
  }
  {
    contradiction.
  }
Qed.


(* similar to senderLowBalAndCanDipIntoReseve, but in this case, sender's balance is even lower than the reserve so in the code below
from reserve_balance.cpp, violation_threshold.has_value() is false, so 
state.check_min_balance(addr, violation_threshold.value()) is skipped so it does not modify the State::origina_ further with modified balance constraits due to the reads of balance 

        if (!violation_threshold.has_value() ||
            !state.check_min_balance(addr, violation_threshold.value())) {

also similar to senderReallyLowBalAndCannotDipIntoReseve in the sense that even there, the sender's ballence was really low: lower than the reserve so the same short circuiting happened.

 *)

Lemma senderReallyLowBalAndCanDipIntoReseve:
  forall (ctx : MonadChainContext) (hist : ExtraAcStates) (stm : StateM)
    (nthElemPtr nthElemVstackTopPtr : ptr)
    (nthElemVstackTop : UpdatedAccountState)
    (nthElemVstackTl : list (ptr * UpdatedAccountState))
    (_t_ : gmap evm.address AssumptionExactness)
    (tx : TxWithHdr) (aps : AssumedPreTxAccountState) (t : N) (loc : ptr),
    updates_stricter stm _t_ ->
    nth_error (newStates stm) (N.to_nat t) =
      Some (sender tx, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
    (forall preTxState : StateOfAccounts,
        satisfiesAssumptions (update_assum_exactness_state stm _t_) preTxState ->
        historyConsistent ctx hist ->
        true =
          allFinalBalSufficient 3 (preTxState, hist)
            (applyUpdates (update_assum_exactness_state stm _t_) preTxState)
            (map fst (takeN t (newStates stm))) tx) ->
    validModel (update_assum_exactness_state stm _t_) ->
    NoDup
      (map
         (λ x : evm.address * (ptr * AssumedPreTxAccountState),
            (let '(a, (b, _)) := x in (a, b)).1)
         (update_assum_exactness_map (preTxAssumedState stm) _t_)) ->
    mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) = Some (loc, aps) ->
    NoDup (map fst (map (λ '(a, (b, _)), (a, b)) (newStates stm))) ->
    (forall preTxState : StateOfAccounts,
        satisfiesAssumptions' true
          (check_min_original_balance_update
             (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) DefReserve)
          preTxState ->
        true = isAllowedToEmpty 3 (preTxState, hist) [] tx) ->
    let ex0 :=
      min_balance_update
        (assumExactness aps)
        (original_balance_pessimistic_model_map
           (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
        (original_balance_pessimistic_model_map
           (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx))
        DefReserve in
    validModel (update_assum_exactness_state stm (<[sender tx := ex0]> _t_))
    /\ (forall preTxState : StateOfAccounts,
          satisfiesAssumptions
            (update_assum_exactness_state stm (<[sender tx := ex0]> _t_))
            preTxState ->
          historyConsistent ctx hist ->
          true =
            allFinalBalSufficient 3 (preTxState, hist)
              (applyUpdates (update_assum_exactness_state stm (<[sender tx := ex0]> _t_)) preTxState)
              (map fst (takeN (1 + t) (newStates stm))) tx)
    /\ updates_stricter stm (<[sender tx := ex0]> _t_).
Proof.
  intros ctx hist stm.
  intros nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl _t_ tx aps t loc.
  intros Hstr_updates Hnth Hall_takeN Hvalid_update.
  intros Hnodup_update Hlookup Hnodup_new_fst Hcan_empty.
  set (orig :=
         original_balance_pessimistic_model_map
           (update_assum_exactness_map (preTxAssumedState stm) _t_)
           (sender tx)).
  set (ex0 := min_balance_update (assumExactness aps) orig orig DefReserve).
  set (stf := update_assum_exactness_state stm (<[sender tx := ex0]> _t_)).
  assert (Hvalid_stf : validModel stf).
  {
    unfold stf, ex0, orig.
    exact (sender_insert_validModel_once stm _t_ tx loc aps Hvalid_update Hlookup).
  }
  assert (Hstr_insert : updates_stricter stm (<[sender tx := ex0]> _t_)).
  {
    unfold ex0, orig.
    exact (sender_insert_updates_stricter_once stm _t_ tx loc aps Hstr_updates Hlookup).
  }
  pose proof
    (nodup_map_fst_update_assum_exactness_map
       (preTxAssumedState stm) _t_ Hnodup_update) as Hnodup_update_fst.
  pose proof
    (sender_check_min_eq_of_lookup
      stm _t_ tx loc aps ex0 Hnodup_update_fst Hlookup eq_refl) as Hcheck_eq.
  split.
  {
    exact Hvalid_stf.
  }
  split.
  {
    intros preState Hsat Hhist0.
    eapply (allFinalBalSufficient_takeN_succ
              stf ctx hist tx t (sender tx) nthElemPtr
              ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
    {
      intros preState0 Hsat0.
      eapply (allFinalBalSufficient_takeN_i_update_assum_exactness_state_insert
                stm ctx hist tx t (sender tx) nthElemPtr
                ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)
                _t_ ex0 preState0 loc aps).
      {
        exact Hnodup_new_fst.
      }
      {
        exact Hnth.
      }
      {
        intros preTxState0 Hsat_old.
        eapply Hall_takeN; eauto.
      }
      {
        exact Hvalid_update.
      }
      {
        exact Hlookup.
      }
	      {
	        unfold ex0.
	        apply assumption_exactness_stricter_min_balance_update.
	      }
      {
        exact Hsat0.
      }
    }
    {
      unfold stf, update_assum_exactness_state.
      simpl.
      exact Hnth.
    }
    {
      intros preState0 Hsat0.
      unfold finalBalSufficient.
      destruct (isSC (applyUpdates stf preState0) (sender tx)) eqn:Hsc_sender.
      {
        reflexivity.
      }
      {
        rewrite bool_decide_true; [|reflexivity].
        change (isAllowedToEmptyExec 3 (preState0, hist) tx)
          with (isAllowedToEmpty 3 (preState0, hist) [] tx).
        pose proof (satisfiesAssumptions_to_true stf preState0 Hsat0) as Hsat_true.
        unfold stf, update_assum_exactness_state in Hsat_true.
        simpl in Hsat_true.
        rewrite <- Hcheck_eq in Hsat_true.
        pose proof (Hcan_empty preState0 Hsat_true) as Hallow_true.
        rewrite <- Hallow_true.
        reflexivity.
      }
    }
    {
      exact Hsat.
    }
  }
  {
    exact Hstr_insert.
  }
Qed.
