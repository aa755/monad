Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import skylabs.brick.libstdcpp.algorithms.spec.
Require Import skylabs.brick.libstdcpp.new.spec_exc.

Require Import skylabs.auto.cpp.prelude.test.

Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import skylabs.lang.cpp.cpp.
Require Import stdpp.gmap.
Require Import stdpp.fin_map_dom.
Require Import monad.proofs.misc.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.cpp.spec.
From AAC_tactics Require Import AAC.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.

Set Default Goal Selector "!".
Import cQp_compat.
Set Warnings "+sl-impossible-patterns".
#[local] Open Scope lens_scope.

Local Transparent isSC isAcSC.
#[local] Arguments Lens.set : simpl never.
#[local] Arguments Lens.over : simpl never.
#[local] Arguments lens_compose : simpl never.


Lemma lastgoal:
  ∀ (ctx : MonadChainContext) (i_ : nat) (stm : StateM) (pbs : AugmentedState),
    (Z.of_nat i_ < lengthZ (transactions (currentBlock (blocks ctx))))%Z
    → ∀ (nthelemAddr : evm.address) (nthElemPtr nthElemVstackTopPtr : ptr) (nthElemVstackTop : UpdatedAccountState) 
        (nthElemVstackTl : list (ptr * UpdatedAccountState)) (t_ : gmap evm.address AssumptionExactness),
        (0 ≤ lengthZ (transactions (currentBlock (blocks ctx))))%Z
        → bitsize.bound bitsize.W64 Unsigned (lengthZ (transactions (currentBlock (blocks ctx))))
          → let tx := nth i_ (txsWithHdr (cblock ctx)) dummyTx in
            InstantiationOfType Transaction tx.1
            → lengthN (transactions (currentBlock (blocks ctx))) = Z.to_N (lengthZ (transactions (currentBlock (blocks ctx))) - 0)
              → map fst (newStates stm) ⊆ map fst (preTxAssumedState stm)
                → stateCodeMapInvariants stm
                  → NoDup
                      (map (λ x : evm.address * (ptr * list (ptr * UpdatedAccountState)), (let '(a, (b, _)) := x in (a, b)).1)
                         (newStates stm))
                    → NoDup
                        (map (λ x : evm.address * (ptr * AssumedPreTxAccountState), (let '(a, (b, _)) := x in (a, b)).1)
                           (preTxAssumedState stm))
                      → ∀ i : N,
                          (i ≤ lengthN (newStates stm))%N
                          → updates_stricter stm t_
                            → nth_error (newStates stm) (N.to_nat i) =
                              Some (nthelemAddr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl))
                              → i ≠ lengthN (newStates stm)
                                → (∀ preTxState : AugmentedState,
                                     satisfiesAssumptions
                                       {|
                                         relaxedValidation := relaxedValidation stm;
                                         preTxAssumedState := update_assum_exactness_map (preTxAssumedState stm) t_;
                                         newStates := newStates stm;
                                         blockStatePtr := blockStatePtr stm;
                                         indices := indices stm;
                                         blockStateGloc := blockStateGloc stm;
                                         dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                         codeMap := codeMap stm
                                       |} preTxState.1
                                     → historyConsistent ctx preTxState.2
                                       → true =
                                         allFinalBalSufficient 3 preTxState
                                           (applyUpdates
                                              {|
                                                relaxedValidation := relaxedValidation stm;
                                                preTxAssumedState := update_assum_exactness_map (preTxAssumedState stm) t_;
                                                newStates := newStates stm;
                                                blockStatePtr := blockStatePtr stm;
                                                indices := indices stm;
                                                blockStateGloc := blockStateGloc stm;
                                                dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                                codeMap := codeMap stm
                                              |} preTxState.1)
                                           (map fst (takeN i (newStates stm))) tx)
                                  → gdom t_ ⊆ map fst (takeN i (newStates stm))
                                    → stateCodeMapInvariants
                                        {|
                                          relaxedValidation := relaxedValidation stm;
                                          preTxAssumedState := update_assum_exactness_map (preTxAssumedState stm) t_;
                                          newStates := newStates stm;
                                          blockStatePtr := blockStatePtr stm;
                                          indices := indices stm;
                                          blockStateGloc := blockStateGloc stm;
                                          dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                          codeMap := codeMap stm
                                        |}
                                      → validModel
                                          {|
                                            relaxedValidation := relaxedValidation stm;
                                            preTxAssumedState := update_assum_exactness_map (preTxAssumedState stm) t_;
                                            newStates := newStates stm;
                                            blockStatePtr := blockStatePtr stm;
                                            indices := indices stm;
                                            blockStateGloc := blockStateGloc stm;
                                            dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                            codeMap := codeMap stm
                                          |}
                                      → NoDup
                                          (map (λ x : evm.address * (ptr * AssumedPreTxAccountState), (let '(a, (b, _)) := x in (a, b)).1)
                                             (update_assum_exactness_map (preTxAssumedState stm) t_))
                                        → (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl ≠ []
                                          → isAcSC (postTxState nthElemVstackTop) = false
                                            → is_Some (mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) t_) nthelemAddr)
                                              → nthelemAddr ≠ sender tx
                                                → NoDup
                                                    (map
                                                       (λ x : evm.address * (ptr * AssumedPreTxAccountState),
                                                          (let '(a, (b, _)) := x in (a, b)).1)
                                                       (check_min_original_balance_update
                                                          (update_assum_exactness_map (preTxAssumedState stm) t_) nthelemAddr
                                                          (DefReserve)))
                                                  → is_Some
                                                      (mapModelLookup
                                                         (check_min_original_balance_update
                                                            (update_assum_exactness_map (preTxAssumedState stm) t_) nthelemAddr
                                                            (DefReserve))
                                                         nthelemAddr)
                                                    → (DefReserve
                                                       `min` original_balance_pessimistic_model_map
                                                               (update_assum_exactness_map (preTxAssumedState stm) t_) nthelemAddr
                                                       ≤ balanceOfAccount (postTxState nthElemVstackTop))%N
                                                    → (∀ preTxState : AugmentedState,
                                                         historyConsistent ctx preTxState.2 →
                                                           configuredReserveBalOfAddr preTxState.2 nthelemAddr =
                                                             DefReserve)
                                                    → ∀ (x : ptr) (x0 : AssumedPreTxAccountState),
                                                        
                                                          mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) t_) nthelemAddr =
                                                            Some (x, x0)
                                                          → (match preTxState x0 with
                                                             | Some cs =>
                                                                 if isSome (min_balance (assumExactness x0))
                                                                 then (min_balanceN (assumExactness x0) <= cs .^ _balance)%N
                                                                 else True
                                                             | None => True
                                                             end)
                                                          → (postTxState nthElemVstackTop = None → exec_specs.preTxState x0 = None)
                                                                 
                                                          → update_assum_exactness_at nthelemAddr
                                                              (λ ex : AssumptionExactness,
                                                                 min_balance_update ex
                                                                   (original_balance_pessimistic_model_map
                                                                      (update_assum_exactness_map (preTxAssumedState stm) t_) nthelemAddr)
                                                                   (balanceOfAccount (postTxState nthElemVstackTop))
                                                                   (DefReserve
                                                                    `min` original_balance_pessimistic_model_map
                                                                            (update_assum_exactness_map (preTxAssumedState stm) t_)
                                                                            nthelemAddr))
                                                              (check_min_original_balance_update
                                                                 (update_assum_exactness_map (preTxAssumedState stm) t_) nthelemAddr
                                                                 (DefReserve)) =
                                                            update_assum_exactness_map (preTxAssumedState stm)
                                                              (<[nthelemAddr:=(λ ex : AssumptionExactness,
                                                                                 min_balance_update ex
                                                                                   (original_balance_pessimistic_model_map
                                                                                      (update_assum_exactness_map (preTxAssumedState stm) t_)
                                                                                      nthelemAddr)
                                                                                   (balanceOfAccount (postTxState nthElemVstackTop))
                                                                                   (DefReserve
                                                                                    `min` original_balance_pessimistic_model_map
                                                                                            (update_assum_exactness_map
                                                                                               (preTxAssumedState stm) t_)
                                                                                            nthelemAddr))
                                                                                (min_balance_update (assumExactness x0)
                                                                                   (original_balance_pessimistic_model_map
                                                                                      (update_assum_exactness_map (preTxAssumedState stm) t_)
                                                                                      nthelemAddr)
                                                                                   (original_balance_pessimistic_model_map
                                                                                      (update_assum_exactness_map (preTxAssumedState stm) t_)
                                                                                      nthelemAddr)
                                                                                   (DefReserve))]>
                                                                 t_)
                                                            → NoDup
                                                                (map fst
                                                                   (map
                                                                      (λ pat : evm.address * (ptr * AssumedPreTxAccountState),
                                                                         let (a1, y) := pat in let (b0, _) := y in (a1, b0))
                                                                      (check_min_original_balance_update
                                                                         (update_assum_exactness_map (preTxAssumedState stm) t_) nthelemAddr
                                                                         (DefReserve))))
                                                              → ∀ (xxx := i_) (preTxState : AugmentedState),
                                                                  satisfiesAssumptions
                                                                    {|
                                                                      relaxedValidation := relaxedValidation stm;
                                                                      preTxAssumedState :=
                                                                        update_assum_exactness_map (preTxAssumedState stm)
                                                                          (<[nthelemAddr:=min_balance_update
                                                                                            (min_balance_update 
                                                                                               (assumExactness x0)
                                                                                               (original_balance_pessimistic_model_map
                                                                                                  (update_assum_exactness_map
                                                                                                     (preTxAssumedState stm) t_)
                                                                                                  nthelemAddr)
                                                                                               (original_balance_pessimistic_model_map
                                                                                                  (update_assum_exactness_map
                                                                                                     (preTxAssumedState stm) t_)
                                                                                                  nthelemAddr)
                                                                                               (DefReserve))
                                                                                            (original_balance_pessimistic_model_map
                                                                                               (update_assum_exactness_map
                                                                                                  (preTxAssumedState stm) t_)
                                                                                               nthelemAddr)
                                                                                            (balanceOfAccount (postTxState nthElemVstackTop))
                                                                                            (DefReserve
                                                                                             `min` original_balance_pessimistic_model_map
                                                                                                     (update_assum_exactness_map
                                                                                                        (preTxAssumedState stm) t_)
                                                                                                     nthelemAddr)]>
                                                                             t_);
                                                                      newStates := newStates stm;
                                                                      blockStatePtr := blockStatePtr stm;
                                                                      indices := indices stm;
                                                                      blockStateGloc := blockStateGloc stm;
                                                                      dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                                                      codeMap := codeMap stm
                                                                    |} preTxState.1
                                                                  → historyConsistent ctx preTxState.2
                                                                    → true =
                                                                      allFinalBalSufficient 3 preTxState
                                                                        (applyUpdates
                                                                           {|
                                                                             relaxedValidation := relaxedValidation stm;
                                                                             preTxAssumedState :=
                                                                               update_assum_exactness_map (preTxAssumedState stm)
                                                                                 (<[nthelemAddr:=min_balance_update
                                                                                                   (min_balance_update 
                                                                                                      (assumExactness x0)
                                                                                                      (original_balance_pessimistic_model_map
                                                                                                         (update_assum_exactness_map
                                                                                                            (preTxAssumedState stm) t_)
                                                                                                         nthelemAddr)
                                                                                                      (original_balance_pessimistic_model_map
                                                                                                         (update_assum_exactness_map
                                                                                                            (preTxAssumedState stm) t_)
                                                                                                         nthelemAddr)
                                                                                                      (DefReserve))
                                                                                                   (original_balance_pessimistic_model_map
                                                                                                      (update_assum_exactness_map
                                                                                                         (preTxAssumedState stm) t_)
                                                                                                      nthelemAddr)
                                                                                                   (balanceOfAccount
                                                                                                      (postTxState nthElemVstackTop))
                                                                                                   (DefReserve
                                                                                                    `min` original_balance_pessimistic_model_map
                                                                                                            (update_assum_exactness_map
                                                                                                               (preTxAssumedState stm) t_)
                                                                                                            nthelemAddr)]>
                                                                                    t_);
                                                                             newStates := newStates stm;
                                                                             blockStatePtr := blockStatePtr stm;
                                                                             indices := indices stm;
                                                                             blockStateGloc := blockStateGloc stm;
                                                                             dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
                                                                             codeMap := codeMap stm
                                                                           |} preTxState.1)
                                                                        (map fst (takeN (1 + i) (newStates stm))) tx.
Proof.
  intros.
  repeat match goal with
  | H : (0 ≤ lengthZ (transactions (currentBlock (blocks _))))%Z |- _ => clear H
  | H : lengthN (transactions (currentBlock (blocks _))) = _ |- _ => clear H
  end.
  eapply (allFinalBalSufficient_takeN_succ_update_assum_exactness_state_insert
            stm ctx preTxState.2 tx i nthelemAddr t_
            nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl x x0).
  { exact H6. }
  { exact H10. }
  { intros preTxState0 Hsat0 Hhist0.
    exact (H12 (preTxState0, preTxState.2) Hsat0 Hhist0). }
  { exact H25. }
  { exact H15. }
  { exact H18. }
  { exact H20. }
  { exact H23. }
  { exact (H24 preTxState H31). }
  { exact H30. }
  { exact H31. }
Qed.

Unset SsrIdents.

Lemma validPres:
  ∀ (stm : StateM) (pbs : AugmentedState)
    (nthelemAddr : evm.address) (nthElemVstackTop : UpdatedAccountState)
    (_t_ : gmap evm.address AssumptionExactness),
    map fst (newStates stm) ⊆ map fst (preTxAssumedState stm)
    → validStateM (update_assum_exactness_state stm _t_)
    → validPostNone (update_assum_exactness_state stm _t_)
    → validSliceInvariants (update_assum_exactness_state stm _t_)
    → ∀ (x : ptr) (x0 : AssumedPreTxAccountState),
        mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_)
          nthelemAddr = Some (x, x0)
        → validModel
            {|
              relaxedValidation := relaxedValidation stm;
              preTxAssumedState :=
                update_assum_exactness_map (preTxAssumedState stm)
                  (<[nthelemAddr:=min_balance_update
                                    (min_balance_update (assumExactness x0)
                                       (original_balance_pessimistic_model_map
                                          (update_assum_exactness_map
                                             (preTxAssumedState stm) _t_) nthelemAddr)
                                       (original_balance_pessimistic_model_map
                                          (update_assum_exactness_map
                                             (preTxAssumedState stm) _t_) nthelemAddr)
                                       (DefReserve))
                                    (original_balance_pessimistic_model_map
                                       (update_assum_exactness_map
                                          (preTxAssumedState stm) _t_) nthelemAddr)
                                    (balanceOfAccount (postTxState nthElemVstackTop))
                                    (DefReserve
                                     `min`
                                     original_balance_pessimistic_model_map
                                       (update_assum_exactness_map
                                          (preTxAssumedState stm) _t_) nthelemAddr)]>
                   _t_);
              newStates := newStates stm;
              blockStatePtr := blockStatePtr stm;
              indices := indices stm;
              blockStateGloc := blockStateGloc stm;
              dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
              codeMap := codeMap stm
            |}.
Proof.
  intros.
  set (orig :=
        original_balance_pessimistic_model_map
          (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr).
  set (max_reserve := DefReserve).
  set (reserve := N.min max_reserve orig).
  set (cur := balanceOfAccount (postTxState nthElemVstackTop)).
  set (ex0 := min_balance_update (assumExactness x0) orig orig max_reserve).
  set (ex := min_balance_update ex0 orig cur reserve).
  assert (Hvalid_update :
      validModel (update_assum_exactness_state stm _t_)).
  { apply (validModel_of_components_update_assum_exactness_state stm _t_); eauto. }
  assert (Hbound :
      match preTxState x0 with
      | Some cs =>
          if isSome (min_balance ex)
          then (min_balanceN ex <= cs .^ _balance)%N
          else True
      | None => True
      end).
  { apply (min_balance_update_twice_bound_of_validStateM
             stm _t_ nthelemAddr x x0 cur reserve max_reserve); eauto. }
  assert (Hstr : assumption_exactness_stricter (assumExactness x0) ex).
  { unfold ex, ex0.
    apply assumption_exactness_stricter_min_balance_update_twice. }
  eapply (validModel_update_assum_exactness_state_insert
            stm _t_ nthelemAddr ex x x0); eauto.
Qed.

Lemma NoDup_map_fst_newStates_of_map (stm: StateM) :
  NoDup (map fst (map (λ '(a, (b, _)), (a, b)) (newStates stm))) ->
  NoDup (map fst (newStates stm)).
Proof.
  intro H.
  replace (map fst (newStates stm)) with
    (map fst (map (λ '(a, (b, _)), (a, b)) (newStates stm))).
  { exact H. }
  rewrite map_map. apply map_ext. intros [a [b tl]]. simpl. reflexivity.
Qed.

Lemma nth_error_newStates_nonempty_of_validPostNone_update_assum_exactness_state
    (stm0 : StateM)
    (updates0 : gmap evm.address AssumptionExactness)
    (i0 : N)
    (addr0 : evm.address)
    (loc0 : ptr)
    (tl0 : list (ptr * UpdatedAccountState)) :
  NoDup (map fst (map (λ '(a, (b, _)), (a, b)) (newStates stm0))) ->
  nth_error (newStates stm0) (N.to_nat i0) = Some (addr0, (loc0, tl0)) ->
  map fst (newStates stm0) ⊆
    map fst (update_assum_exactness_map (preTxAssumedState stm0) updates0) ->
  validPostNone (update_assum_exactness_state stm0 updates0) ->
  tl0 <> [].
Proof.
  intros Hnodup0 Hnth0 Hsubset0 Hpost0 Hnil0.
  assert (Hmem0 :
    (addr0, (loc0, tl0)) ∈ newStates stm0).
  {
    apply list_elem_of_lookup_2 with (i := N.to_nat i0).
    rewrite lookup_nth_error.
    exact Hnth0.
  }
  assert (Hnodup0_plain : NoDup (map fst (newStates stm0))).
  {
    eapply NoDup_map_fst_newStates_of_map.
    exact Hnodup0.
  }
  assert (Hlookup_new0 :
    mapModelLookup (newStates stm0) addr0 = Some (loc0, tl0)).
  {
    apply elem_of_list_to_map_1; [exact Hnodup0_plain|exact Hmem0].
  }
  assert (Hpre_some0 :
    is_Some
      (mapModelLookup
         (update_assum_exactness_map (preTxAssumedState stm0) updates0)
         addr0)).
  {
    eapply mapModelLookup_is_Some_of_subset_nth.
    { exact Hsubset0. }
    { exact Hnth0. }
  }
  destruct (mapModelLookup_exists_of_is_Some
              (update_assum_exactness_map (preTxAssumedState stm0) updates0)
              addr0 Hpre_some0) as [locp [apsp Hlookup_pre0]].
  pose proof (Hpost0 addr0 loc0 tl0 locp apsp Hlookup_new0 Hlookup_pre0) as Hmust.
  rewrite Hnil0 in Hmust.
  exact Hmust.
Qed.
(*
the goal below is to establish the postcondition of [dipped_into_reserve_spec] (defined in reservebal/reserve_balance.v), which is the spec of the following function from
reserve_balance.cpp. This goal comes from the proof of the return true in the else branch 

        if (!violation_threshold.has_value() ||
            !state.check_min_balance(addr, violation_threshold.value())) {
            if (addr == sender) {
                if (!can_sender_dip_into_reserve(
                        sender, i, effective_is_delegated, ctx)) {
                    // Safety: this assertion is recoverable because it can be
                    // triggered via RPC parameter setting.
                    MONAD_ASSERT_THROW(
                        violation_threshold.has_value(),
                        "gas fee greater than reserve for non-dipping "
                        "transaction");
                    return true;
                }
                // Skip if allowed to dip into reserve
            }
            else {
                // Safety: this assertion should not be a recoverable one, as it
                // indicates a logic error in the surrounding code: the
                // violation threshold can only be nullopt when addr == sender,
                // which is not the case in this branch.
                MONAD_ASSERT(violation_threshold.has_value());
                return true; // goal below is for this branch
            }

*)

Lemma nonSenderBalanceInsuff_aug :
  forall (ctx : MonadChainContext) (stm : StateM)
         (nthelemAddr : evm.address)
         (nthElemPtr nthElemVstackTopPtr : ptr)
         (nthElemVstackTop : UpdatedAccountState)
         (nthElemVstackTl : list (ptr * UpdatedAccountState))
         (_t_ : gmap evm.address AssumptionExactness)
         (tx : TxWithHdr) (i : N) (x : ptr) (x0 : AssumedPreTxAccountState),
    let orig :=
      original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr in
    let reserve := DefReserve in
    let debit := (N.min reserve orig : N) in
    let cur := balanceOfAccount (postTxState nthElemVstackTop) in
    let ex0 := min_balance_update (assumExactness x0) orig orig reserve in
    let ex := min_balance_update ex0 orig cur debit in
    let stf := update_assum_exactness_state stm (<[nthelemAddr := ex]> _t_) in
    NoDup
      (map
         (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
            (let '(a, (b, _)) := x in (a, b)).1)
         (newStates stm)) ->
    nth_error (newStates stm) (N.to_nat i) =
      Some (nthelemAddr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
    validPostNone (update_assum_exactness_state stm _t_) ->
    isAcSC (postTxState nthElemVstackTop) = false ->
    nthelemAddr <> sender tx ->
    mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr = Some (x, x0) ->
    ~(debit <= cur)%N ->
    forall preTxState : AugmentedState,
      satisfiesAssumptions stf preTxState.1 ->
      historyConsistent ctx preTxState.2 ->
      configuredReserveBalOfAddr preTxState.2 nthelemAddr = reserve ->
      true =
      ~~ allFinalBalSufficient 3 preTxState
           (applyUpdates stf preTxState.1)
           (map fst (newStates stm)) tx.
Proof.
  intros ctx stm nthelemAddr nthElemPtr nthElemVstackTopPtr
         nthElemVstackTop nthElemVstackTl _t_ tx i x x0.
  intros orig reserve debit cur ex0 ex stf.
  intros HnodupNew Hnth HvalidPostStf Hsc Hneqsender Hlookup Hnotle
         preTxStateA Hsat Hhist Hreserve_eq.
  (* membership in newStates *)
  assert (Hmem :
      (nthelemAddr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl))
        ∈ newStates stm).
  { apply list_elem_of_lookup_2 with (i := N.to_nat i).
    rewrite lookup_nth_error. exact Hnth. }
  assert (Hin :
      nthelemAddr ∈ map fst (newStates stm)).
  { apply (proj2 (list_elem_of_fmap _ _ _)).
    exists (nthelemAddr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
    split; [reflexivity|exact Hmem]. }
  (* goal: negation of allFinalBalSufficient *)
  apply eq_sym.
  apply negb_true_iff.
  apply Bool.not_true_is_false.
  intro Hall.
  unfold allFinalBalSufficient in Hall.
  assert (Hall' :
      forall a,
        In a (map fst (newStates stm)) ->
        finalBalSufficient 3 preTxStateA (applyUpdates stf preTxStateA.1) tx a = true).
  { apply forallb_forall.
    unfold stf, update_assum_exactness_state.
    exact Hall. }
  apply list_elem_of_In in Hin.
  specialize (Hall' nthelemAddr Hin).
  (* show finalBalSufficient is false *)
  unfold finalBalSufficient in Hall'.
  set (post := applyUpdates stf preTxStateA.1) in *.
  (* show isSC post nthelemAddr = false *)
  assert (Hlookup_new :
      mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr =
        Some (x, x0)) by exact Hlookup.
  pose proof (mapModelLookup_update_assum_exactness_map_Some
                (preTxAssumedState stm) _t_ nthelemAddr x x0 Hlookup_new)
    as (aps0 & Horig & Hpre & Hstorage & _Hassum).
  set (aps_new :=
         {| preTxState := preTxState x0;
            preTxStorage := preTxStorage x0;
            assumExactness := ex |}).
  assert (Hlookup_upd :
      mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) (<[nthelemAddr := ex]> _t_))
        nthelemAddr = Some (x, aps_new)).
  { rewrite mapModelLookup_update_assum_exactness_map.
    assert (Hupd_lookup : (<[nthelemAddr := ex]> _t_) !! nthelemAddr = Some ex).
    {
      rewrite lookup_insert.
      destruct (decide (nthelemAddr = nthelemAddr)) as [_|Hneq].
      - reflexivity.
      - exfalso. apply Hneq. reflexivity.
    }
    rewrite Hupd_lookup.
    rewrite Horig. simpl.
    rewrite <- Hpre.
    rewrite <- Hstorage.
    reflexivity. }
  assert (HnodupNew' : NoDup (map fst (newStates stm))).
  { replace (map fst (newStates stm)) with
      (map (λ x : evm.address * (ptr * list (ptr * UpdatedAccountState)),
              (let '(a, (b, _)) := x in (a, b)).1) (newStates stm)).
    - exact HnodupNew.
    - apply map_ext. intros [a [b tl]]. simpl. reflexivity. }
  assert (Hlookup_newStates :
      newStates stm !! nthelemAddr =
        Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
  { apply elem_of_list_to_map_1; [exact HnodupNew'|exact Hmem]. }
  assert (Hau :
      assumptionAndUpdateOfAddr stf nthelemAddr =
        Some {| preAssumption := aps_new;
                originalLoc := x;
                txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}).
  { unfold assumptionAndUpdateOfAddr, stf; simpl.
    change ((update_assum_exactness_map (preTxAssumedState stm) (<[nthelemAddr := ex]> _t_)) !! nthelemAddr)
      with (mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) (<[nthelemAddr := ex]> _t_)) nthelemAddr).
    rewrite Hlookup_upd. simpl.
    rewrite Hlookup_newStates. simpl.
    reflexivity. }
  (* use satisfiesAssumptions to relate actual pre balance to assumed *)
  specialize (Hsat nthelemAddr).
  unfold assumptionOfAddr in Hsat.
  unfold stf, update_assum_exactness_state in Hsat; simpl in Hsat.
  change
    ((update_assum_exactness_map (preTxAssumedState stm) (<[nthelemAddr := ex]> _t_)) !! nthelemAddr)
    with
      (mapModelLookup
         (update_assum_exactness_map (preTxAssumedState stm) (<[nthelemAddr := ex]> _t_))
         nthelemAddr) in Hsat.
  rewrite Hlookup_upd in Hsat. simpl in Hsat.
  unfold satAccountAssumptions in Hsat.
  destruct Hsat as [Hnon _Hstor].
  unfold satAccountNonStorageAssumptions in Hnon.
  simpl in Hnon.
  assert (Hmb_none : min_balance (assumExactness aps_new) = None).
  { unfold aps_new, ex, min_balance_update.
    unfold check_min_balance_ok.
    rewrite bool_decide_false; [reflexivity|].
    intro Hle0.
    apply Hnotle.
    unfold debit, reserve, orig, cur in Hle0.
    exact Hle0. }
	  destruct (preTxState aps_new) as [csAssumed|] eqn:Hpre'.
	  - rewrite Hpre' in Hnon; simpl in Hnon.
	    rewrite Hmb_none in Hnon; simpl in Hnon.
	    assert (Hbal_assum' : csAssumed .^ _balance = (preTxStateA.1 nthelemAddr) .^ _balance).
	    {
	      destruct (relaxedValidation stm) eqn:Hrel; simpl in Hnon.
	      {
	        destruct Hnon as [Hbal_assum _Hnonce].
	        exact Hbal_assum.
	      }
	      {
	        destruct Hnon as [[Hbal_assum _Hmin_ok] _Hnonce].
	        exact Hbal_assum.
	      }
	    }
	    (* relate orig and actual pre balance *)
	    assert (Horig_eq :
	        orig = csAssumed .^ _balance).
    { unfold orig, original_balance_pessimistic_model_map, preTxAccountOf_map.
      rewrite Hlookup_new. simpl. rewrite Hpre'. reflexivity. }
    assert (Hactual_eq' :
        balanceOfAc preTxStateA.1 nthelemAddr =
          (preTxStateA.1 nthelemAddr) .^ _balance).
    { unfold balanceOfAc. simpl. reflexivity. }
    assert (Hactual_eq :
        balanceOfAc preTxStateA.1 nthelemAddr = csAssumed .^ _balance).
    { exact (eq_trans Hactual_eq' (eq_sym Hbal_assum')). }
    assert (Hpre_orig :
        balanceOfAc preTxStateA.1 nthelemAddr = orig).
    { rewrite Hactual_eq.
      symmetry.
      exact Horig_eq. }
    (* compute isSC post *)
    assert (Hscpost : isSC post nthelemAddr = false).
    { (* reuse isSC_applyUpdates_false_nth by reasoning as in isSC_applyUpdates_true_nth *)
      unfold isSC, post, applyUpdates.
      rewrite Hau. simpl.
      set (fv :=
             accountFinalVal (relaxedValidation stf)
               {| preAssumption := aps_new;
                  originalLoc := x;
                  txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}
               (Some (preTxStateA.1 nthelemAddr))).
      change (isAcSC (Some (match fv with | None => dummyAc | Some fv' => fv' end)) = false).
      destruct fv as [fv'|] eqn:Hfv; simpl.
      - unfold fv in Hfv.
        unfold accountFinalVal in Hfv.
        simpl in Hfv.
        destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost; simpl in Hfv.
        + destruct (relaxedValidation stf) eqn:Hrel; simpl in Hfv.
          * have Hrelstm : relaxedValidation stm = relaxedValidation stf.
            { unfold stf, update_assum_exactness_state; simpl; reflexivity. }
            rewrite Hrelstm in Hfv. rewrite Hrel in Hfv.
            destruct (preTxState x0) eqn:Hprex; simpl in Hfv.
            -- clear Hprex.
              destruct (preTxState (preAssumption {| preAssumption := aps_new;
                                                     originalLoc := x;
                                                     txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}))
                as [csAssumed'|] eqn:Hpre''; simpl in Hfv.
              { try rewrite Hmb_none in Hfv; simpl in Hfv.
                destruct (nonce_exact ex) eqn:Hnonce; simpl in Hfv.
                - change (isAcSC (Some fv') = false).
                  inversion Hfv; subst.
                  set (st :=
                         updateStorage
                           (Some (block.block_account_storage
                                    (coreAc (preTxStateA.1 nthelemAddr))))
                           (Some csUpdated)) in *.
                  change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                    with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                  have Hsc' : isAcSC (Some csUpdated) = false.
                  { move: Hsc; by rewrite ?Hpost. }
                  rewrite (isAcSC_update_storage csUpdated st).
                  exact Hsc'.
                - change (isAcSC (Some fv') = false).
                  inversion Hfv; subst.
                  set (st :=
                         updateStorage
                           (Some (block.block_account_storage
                                    (coreAc (preTxStateA.1 nthelemAddr))))
                           (Some csUpdated)) in *.
                  change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                    with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                  have Hsc' : isAcSC (Some csUpdated) = false.
                  { move: Hsc; by rewrite ?Hpost. }
                  repeat rewrite isAcSC_update_nonce.
                  rewrite (isAcSC_update_storage csUpdated st).
                  exact Hsc'. }
              { try rewrite Hmb_none in Hfv; simpl in Hfv.
                destruct (nonce_exact ex) eqn:Hnonce; simpl in Hfv.
                - change (isAcSC (Some fv') = false).
                  inversion Hfv; subst.
                  set (st :=
                         updateStorage
                           (Some (block.block_account_storage
                                    (coreAc (preTxStateA.1 nthelemAddr))))
                           (Some csUpdated)) in *.
                  change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                    with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                  have Hsc' : isAcSC (Some csUpdated) = false.
                  { move: Hsc; by rewrite ?Hpost. }
                  rewrite (isAcSC_update_storage csUpdated st).
                  exact Hsc'.
                - change (isAcSC (Some fv') = false).
                  inversion Hfv; subst.
                  set (st :=
                         updateStorage
                           (Some (block.block_account_storage
                                    (coreAc (preTxStateA.1 nthelemAddr))))
                           (Some csUpdated)) in *.
                  change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                    with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                  have Hsc' : isAcSC (Some csUpdated) = false.
                  { move: Hsc; by rewrite ?Hpost. }
                  repeat rewrite isAcSC_update_nonce.
                  rewrite (isAcSC_update_storage csUpdated st).
                  exact Hsc'. }
            -- clear Hprex.
              destruct (preTxState (preAssumption {| preAssumption := aps_new;
                                                     originalLoc := x;
                                                     txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}))
                as [csAssumed'|] eqn:Hpre''; simpl in Hfv.
              { try rewrite Hmb_none in Hfv; simpl in Hfv.
                destruct (nonce_exact ex) eqn:Hnonce; simpl in Hfv.
                - change (isAcSC (Some fv') = false).
                  inversion Hfv; subst.
                  set (st :=
                         updateStorage
                           (Some (block.block_account_storage
                                    (coreAc (preTxStateA.1 nthelemAddr))))
                           (Some csUpdated)) in *.
                  change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                    with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                  have Hsc' : isAcSC (Some csUpdated) = false.
                  { move: Hsc; by rewrite ?Hpost. }
                  rewrite (isAcSC_update_storage csUpdated st).
                  exact Hsc'.
                - change (isAcSC (Some fv') = false).
                  inversion Hfv; subst.
                  set (st :=
                         updateStorage
                           (Some (block.block_account_storage
                                    (coreAc (preTxStateA.1 nthelemAddr))))
                           (Some csUpdated)) in *.
                  change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                    with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                  have Hsc' : isAcSC (Some csUpdated) = false.
                  { move: Hsc; by rewrite ?Hpost. }
                  repeat rewrite isAcSC_update_nonce.
                  rewrite (isAcSC_update_storage csUpdated st).
                  exact Hsc'. }
              { try rewrite Hmb_none in Hfv; simpl in Hfv.
                destruct (nonce_exact ex) eqn:Hnonce; simpl in Hfv.
                - change (isAcSC (Some fv') = false).
                  inversion Hfv; subst.
                  set (st :=
                         updateStorage
                           (Some (block.block_account_storage
                                    (coreAc (preTxStateA.1 nthelemAddr))))
                           (Some csUpdated)) in *.
                  change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                    with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                  have Hsc' : isAcSC (Some csUpdated) = false.
                  { move: Hsc; by rewrite ?Hpost. }
                  rewrite (isAcSC_update_storage csUpdated st).
                  exact Hsc'.
                - change (isAcSC (Some fv') = false).
                  inversion Hfv; subst.
                  set (st :=
                         updateStorage
                           (Some (block.block_account_storage
                                    (coreAc (preTxStateA.1 nthelemAddr))))
                           (Some csUpdated)) in *.
                  change ((_coreAc .@ _block_account_storage .= st) csUpdated)
                    with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
                  have Hsc' : isAcSC (Some csUpdated) = false.
                  { move: Hsc; by rewrite ?Hpost. }
                  repeat rewrite isAcSC_update_nonce.
                  rewrite (isAcSC_update_storage csUpdated st).
                  exact Hsc'. }
          * have Hrelstm : relaxedValidation stm = relaxedValidation stf.
            { unfold stf, update_assum_exactness_state; simpl; reflexivity. }
            rewrite Hrelstm in Hfv. rewrite Hrel in Hfv.
            change (isAcSC (Some fv') = false).
            inversion Hfv; subst.
            set (st :=
                   updateStorage
                     (Some (block.block_account_storage
                              (coreAc (preTxStateA.1 nthelemAddr))))
                     (Some csUpdated)) in *.
            change ((_coreAc .@ _block_account_storage .= st) csUpdated)
              with (csUpdated &: _coreAc .@ _block_account_storage .= st) in *.
            have Hsc' : isAcSC (Some csUpdated) = false.
            { move: Hsc; by rewrite ?Hpost. }
            rewrite (isAcSC_update_storage csUpdated st).
            exact Hsc'.
        + inversion Hfv; subst; try exact Hsc.
      - (* fv = None -> contradiction via validPostNone *)
        unfold fv in Hfv.
        unfold accountFinalVal in Hfv.
        simpl in Hfv.
        destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost; simpl in Hfv.
        + destruct (relaxedValidation stf) eqn:Hrel; rewrite Hrel in Hfv; simpl in Hfv.
          * destruct (preTxState (preAssumption {| preAssumption := aps_new;
                                                   originalLoc := x;
                                                   txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}))
              as [csAssumed'|] eqn:Hpre''; rewrite Hpre'' in Hfv; simpl in Hfv.
            { try rewrite Hmb_none in Hfv; simpl in Hfv.
              exfalso; now inversion Hfv. }
            { try rewrite Hmb_none in Hfv; simpl in Hfv.
              exfalso; now inversion Hfv. }
          * exfalso; now inversion Hfv.
        + (* use validPostNone (for _t_) to show preTxState x0 = None, contradict Hpre' *)
          have Hpre_none_x0 : preTxState x0 = None.
          { apply (HvalidPostStf nthelemAddr nthElemPtr
                     ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl) x x0).
            - exact Hlookup_newStates.
            - exact Hlookup_new.
            - exact Hpost. }
          have Hpre_none : preTxState aps_new = None.
          { unfold aps_new; simpl. exact Hpre_none_x0. }
          rewrite Hpre' in Hpre_none. discriminate.
    }
    (* finalize finalBalSufficient false *)
    rewrite Hscpost in Hall'.
    simpl in Hall'.
    rewrite bool_decide_false in Hall'; [|intro Heq; apply Hneqsender; symmetry; exact Heq].
    unfold asbool in Hall'.
    unfold bool_decide in Hall'.
    assert (Hpostbal :
        balanceOfAc post nthelemAddr = cur).
    { unfold post, applyUpdates, balanceOfAc.
      rewrite Hau. simpl.
      unfold accountFinalVal. simpl.
      destruct (postTxState nthElemVstackTop) as [csUpdated|] eqn:Hpost; simpl.
      { have Hrelstm : relaxedValidation stm = relaxedValidation stf.
        { unfold stf, update_assum_exactness_state; simpl; reflexivity. }
        rewrite Hrelstm.
        destruct (relaxedValidation stf) eqn:Hrel; simpl.
        { (* relaxedValidation = true *)
          (* preAssumption is aps_new, so rewrite preTxState aps_new *)
          rewrite Hpre'. simpl.
          rewrite Hmb_none. simpl.
          destruct (nonce_exact ex) eqn:Hnonce; simpl;
            repeat
              match goal with
              | |- context[balance ((_nonce .= ?n) ?b)] =>
                  change (balance ((_nonce .= n) b)) with (balance (b &: _nonce .= n));
                  rewrite balance_update_nonce
              end;
            repeat
              match goal with
              | |- context[balance ((_coreAc .@ _block_account_storage .= ?st) ?b)] =>
                  change (balance ((_coreAc .@ _block_account_storage .= st) b)) with
                    (balance (b &: _coreAc .@ _block_account_storage .= st));
                  rewrite balance_update_storage
              end;
            unfold balanceOfAccount, cur; reflexivity. }
        { (* relaxedValidation = false: base used *)
          unfold balanceOfAccount, cur.
          repeat
            match goal with
            | |- context[balance ((_coreAc .@ _block_account_storage .= ?st) ?b)] =>
                change (balance ((_coreAc .@ _block_account_storage .= st) b)) with
                  (balance (b &: _coreAc .@ _block_account_storage .= st));
                rewrite balance_update_storage
            end.
          reflexivity. } }
      { unfold balanceOfAccount, cur. reflexivity. } }
    unfold reserve in Hall'.
    rewrite Hreserve_eq in Hall'.
    destruct (N.le_dec (N.min reserve (balanceOfAc preTxStateA.1 nthelemAddr))
                       (balanceOfAc post nthelemAddr)) as [Hle'|Hnle].
    { (* show the inequality is false *)
      have Hnotle_mapped :
        ¬ (N.min reserve (balanceOfAc preTxStateA.1 nthelemAddr) ≤
           balanceOfAc post nthelemAddr)%N.
      { intro Hle0.
        apply Hnotle.
        unfold debit.
        rewrite <- Hpostbal.
        rewrite <- Hpre_orig.
        exact Hle0. }
      exact (Hnotle_mapped Hle'). }
    {
      simpl in Hall'.
      unfold decide_rel in Hall'.
      apply bool_decide_eq_true_1 in Hall'.
      exfalso. apply Hnle. exact Hall'. }
  - (* None case contradicts Hnon *)
    rewrite Hpre' in Hnon; simpl in Hnon. contradiction.
Qed.

(* Thin compatibility wrapper over [nonSenderBalanceInsuff_aug].
   Candidate to inline at call sites later. *)
Lemma nonSenderBalanceInsuff :
  forall (ctx : MonadChainContext) (stm : StateM)
         (nthelemAddr : evm.address)
         (nthElemPtr nthElemVstackTopPtr : ptr)
         (nthElemVstackTop : UpdatedAccountState)
         (nthElemVstackTl : list (ptr * UpdatedAccountState))
         (_t_ : gmap evm.address AssumptionExactness)
         (tx : TxWithHdr) (i : N) (x : ptr) (x0 : AssumedPreTxAccountState)
         (hist : ExtraAcStates),
    let orig :=
      original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr in
    let reserve := DefReserve in
    let debit := (N.min reserve orig : N) in
    let cur := balanceOfAccount (postTxState nthElemVstackTop) in
    let ex0 := min_balance_update (assumExactness x0) orig orig reserve in
    let ex := min_balance_update ex0 orig cur debit in
    let stf := update_assum_exactness_state stm (<[nthelemAddr := ex]> _t_) in
    NoDup
      (map
         (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
            (let '(a, (b, _)) := x in (a, b)).1)
         (newStates stm)) ->
    nth_error (newStates stm) (N.to_nat i) =
      Some (nthelemAddr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
    validPostNone (update_assum_exactness_state stm _t_) ->
    isAcSC (postTxState nthElemVstackTop) = false ->
    nthelemAddr <> sender tx ->
    mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr = Some (x, x0) ->
    ~(debit <= cur)%N ->
    forall preTxState : StateOfAccounts,
      satisfiesAssumptions stf preTxState ->
      historyConsistent ctx hist ->
      configuredReserveBalOfAddr hist nthelemAddr = DefReserve ->
      true =
      ~~ allFinalBalSufficient 3 (preTxState, hist)
           (applyUpdates stf preTxState)
           (map fst (newStates stm)) tx.
Proof.
  intros ctx stm nthelemAddr nthElemPtr nthElemVstackTopPtr
         nthElemVstackTop nthElemVstackTl _t_ tx i x x0 hist.
  intros orig reserve debit cur ex0 ex stf.
  intros HnodupNew Hnth HvalidPostStf Hsc Hneqsender Hlookup Hnotle
         preTxState Hsat Hhist Hreserve_hist.
  eapply (nonSenderBalanceInsuff_aug
            ctx stm nthelemAddr nthElemPtr nthElemVstackTopPtr
            nthElemVstackTop nthElemVstackTl _t_ tx i x x0); simpl; eauto.
Qed.
