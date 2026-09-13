Require Import monad.proofs.misc.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.reservebal_specs.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import monad.proofs.execproofs.reservebal.check_min_original_balance_proof.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import stdpp.gmap.

Import exec_specs.
Import linearity.

Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".
Open Scope N_scope.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Opaque Zdigits.binary_value Zdigits.Z_to_binary.
Opaque w256_to_Z.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  #[local] Instance learn_block_state_rfrag :
    AtLearnEq3 BlockState.Rfrag :=
    ltac:(solve_learnable).

  #[local] Hint Opaque
    state_recent_account_state_spec
    state_original_account_state_spec
    StateCurrentLookupR
    UpdatedAccountStateR
    u256R
    optional_specs.optionR : sl_opacity.

  Lemma map_fst_current_spine
      (m : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    map fst (map (fun '(a, (b, _)) => (a, b)) m) = map fst m.
  Proof using.
    induction m as [| [addr [loc updates]] tl IH]; simpl; [reflexivity |].
    now f_equal.
  Qed.

  Lemma mapModelLookup_none_of_not_in_current_spine
      (m : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address) :
    addr ∉ map fst (map (fun '(a, (b, _)) => (a, b)) m) ->
    mapModelLookup m addr = None.
  Proof using.
    rewrite map_fst_current_spine.
    intro Hnot.
    destruct (mapModelLookup m addr) eqn:Hlookup; [| reflexivity].
    exfalso.
    apply Hnot.
    apply mapModelLookup_is_Some_implies_mem.
    eauto.
  Qed.

  Lemma state_original_account_state_block_stateR_of_is_Some
      (this : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) :
    is_Some (mapModelLookup orig addr) ->
    emp |-- state_original_account_state_block_stateR this orig addr.
  Proof using.
    intros [orig_state Horig].
    unfold state_original_account_state_block_stateR.
    rewrite Horig.
    go.
  Qed.

  Definition state_original_account_state_block_stateR_of_is_Some_B
      this orig addr Horig :=
    [BWD] (state_original_account_state_block_stateR_of_is_Some
             this orig addr Horig).

  Lemma state_original_account_state_block_stateR_drop_of_is_Some
      (this : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) :
    is_Some (mapModelLookup orig addr) ->
    state_original_account_state_block_stateR this orig addr |-- emp.
  Proof using.
    intros [orig_state Horig].
    unfold state_original_account_state_block_stateR.
    rewrite Horig.
    go.
  Qed.

  Definition state_original_account_state_block_stateR_drop_of_is_Some_F
      this orig addr Horig :=
    [FWD] (state_original_account_state_block_stateR_drop_of_is_Some
             this orig addr Horig).

  Lemma state_recent_account_state_post_original_lookup_is_Some
      (st st_final : StateM) (addr : evmopsem.evm.address)
      (retp : ptr) (acct : option AccountM) :
    is_Some (mapModelLookup (preTxAssumedState st) addr) ->
    state_recent_account_state_post st addr st_final retp acct ->
    is_Some (mapModelLookup (preTxAssumedState st_final) addr).
  Proof using.
    intros Horig Hpost.
    unfold state_recent_account_state_post in Hpost.
    destruct (mapModelLookup (newStates st) addr) as [[curp updates] |].
    {
      destruct Hpost as [? [? [? [? [Hst_final ?]]]]].
      subst st_final.
      exact Horig.
    }
    destruct Hpost as [loc [orig_final [orig_state [Hpost [Hst_final ?]]]]].
    subst st_final.
    unfold state_original_account_state_post in Hpost.
    destruct Horig as [[old_loc old_state] Hlookup].
    rewrite Hlookup in Hpost.
    destruct Hpost as [Horig_final _].
    subst orig_final.
    eexists.
    exact Hlookup.
  Qed.

  Lemma state_recent_account_state_post_blockStatePtr
      (st st_final : StateM) (addr : evmopsem.evm.address)
      (retp : ptr) (acct : option AccountM) :
    state_recent_account_state_post st addr st_final retp acct ->
    blockStatePtr st_final = blockStatePtr st.
  Proof using.
    intro Hpost.
    unfold state_recent_account_state_post in Hpost.
    destruct (mapModelLookup (newStates st) addr) as [[curp updates] |].
    {
      destruct Hpost as [? [? [? [? [Hst_final ?]]]]].
      subst st_final.
      reflexivity.
    }
    destruct Hpost as [? [? [? [? [Hst_final ?]]]]].
    subst st_final.
    reflexivity.
  Qed.

  Lemma state_original_account_state_post_lookup
      (orig orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr) (orig_state : AssumedPreTxAccountState) :
    state_original_account_state_post orig addr orig_final loc orig_state ->
    mapModelLookup orig_final addr = Some (loc, orig_state).
  Proof using.
    intro Hpost.
    unfold state_original_account_state_post in Hpost.
    destruct (mapModelLookup orig addr) as [[old_loc old_state] |] eqn:Hlookup.
    {
      destruct Hpost as [-> [-> ->]].
      exact Hlookup.
    }
    destruct Hpost as [acct [-> ->]].
    unfold mapModelLookup.
    rewrite lookup_insert.
    cbn.
    destruct (decide (addr = addr)) as [_ | Hcontra].
    2:{ contradiction Hcontra; reflexivity. }
    reflexivity.
  Qed.

  Lemma state_original_account_state_post_existing
      (orig orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc old_loc : ptr)
      (orig_state old_state : AssumedPreTxAccountState) :
    mapModelLookup orig addr = Some (old_loc, old_state) ->
    state_original_account_state_post orig addr orig_final loc orig_state ->
    orig_final = orig /\ loc = old_loc /\ orig_state = old_state.
  Proof using.
    intros Hlookup Hpost.
    unfold state_original_account_state_post in Hpost.
    rewrite Hlookup in Hpost.
    exact Hpost.
  Qed.

  Local Transparent AccountStateRcore.

  Lemma AccountStateRcore_keep_optional_account_ref (p : ptr) q acct :
    p |-> AccountStateRcore q acct
    |--
    p |-> AccountStateRcore q acct
    ** reference_to "std::optional<monad::Account>"
      (p ,, o_field CU "monad::AccountState::account_").
  Proof using CU MODd Sigma.
    unfold AccountStateRcore.
    go.
    iExists transient_map.
    go.
  Qed.

  Lemma observeAccountStateOptionalAccountRef (p : ptr) q acct :
    Observe
      (reference_to "std::optional<monad::Account>"
        (p ,, o_field CU "monad::AccountState::account_"))
      (p |-> AccountStateRcore q acct).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _ |].
    exact (AccountStateRcore_keep_optional_account_ref p q acct).
  Qed.

  Definition observeAccountStateOptionalAccountRef_F p q acct :=
    @observe_fwd _ _ _ (observeAccountStateOptionalAccountRef p q acct).

  #[local] Hint Resolve
    observeAccountStateOptionalAccountRef_F : sl_opacity.

  Lemma recent_account_state_return_to_state_and_account_ref
      (this retp : ptr) (st_final : StateM) (acct : option AccountM) :
    retp |-> AccountStateRcore 1 acct
    ** (retp |-> AccountStateRcore 1 acct -* this |-> StateR st_final)
    |--
    reference_to "std::optional<monad::Account>"
      (retp ,, o_field CU "monad::AccountState::account_")
    ** this |-> StateR st_final.
  Proof using CU MODd Sigma.
    set (P := retp |-> AccountStateRcore 1 acct).
    set (R :=
      reference_to "std::optional<monad::Account>"
        (retp ,, o_field CU "monad::AccountState::account_")).
    set (Q := this |-> StateR st_final).
    change (P ** (P -* Q) |-- R ** Q).
    etransitivity.
    {
      apply bi.sep_mono_l.
      unfold P, R.
      exact (AccountStateRcore_keep_optional_account_ref retp 1 acct).
    }
    change ((P ** R) ** (P -* Q) |-- R ** Q).
    go.
  Qed.

  Definition recent_account_state_return_to_state_and_account_ref_F
      this retp st_final acct :=
    [FWD] (recent_account_state_return_to_state_and_account_ref
             this retp st_final acct).

  Lemma borrow_original_account_payload
      (map_ptr : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 orig
    |--
    loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState"
         |-> OriginalAccountStateR 1 orig_state
    ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, orig_state)) ∈ orig).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_N :
      nth_error orig (N.to_nat (N.of_nat i)) = Some (addr, (loc, orig_state))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    rewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address AssumedPreTxAccountState _
      "monad::Address" "monad::OriginalAccountState"
      addressR OriginalAccountStateR
      orig (N.of_nat i) (addr, (loc, orig_state)) addr map_ptr
      Hnth_N eq_refl).
    unfold pairR.
    go.
  Qed.

  Definition borrow_original_account_payload_F
      map_ptr orig addr loc orig_state Hlookup :=
    [FWD] (borrow_original_account_payload
             map_ptr orig addr loc orig_state Hlookup).

  Lemma borrow_current_head_payload
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 cur
    |--
    (loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr)
    ** (loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl))
    ** (upd_loc |-> UpdatedAccountStateR 1 upd)
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** (map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (removeKey cur addr)).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, (upd_loc, upd) :: tl)) ∈ cur).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_N :
      nth_error cur (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, (upd_loc, upd) :: tl))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    rewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      cur (N.of_nat i) (addr, (loc, (upd_loc, upd) :: tl)) addr map_ptr
      Hnth_N eq_refl).
    unfold pairR, VersionStackR.
    simpl.
    go.
  Qed.

  Definition borrow_current_head_payload_F
      map_ptr cur addr loc upd_loc upd tl Hlookup :=
    [FWD] (borrow_current_head_payload
             map_ptr cur addr loc upd_loc upd tl Hlookup).

  Lemma reinsert_current_head_payload
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    (loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr)
    ** (loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl))
    ** (upd_loc |-> UpdatedAccountStateR 1 upd)
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** (map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (removeKey cur addr))
    |--
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 cur.
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, (upd_loc, upd) :: tl)) ∈ cur).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_N :
      nth_error cur (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, (upd_loc, upd) :: tl))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      cur (N.of_nat i) (addr, (loc, (upd_loc, upd) :: tl)) addr map_ptr
      Hnth_N eq_refl).
    unfold pairR, VersionStackR.
    simpl.
    go.
  Qed.

  Definition reinsert_current_head_payload_B
      map_ptr cur addr loc upd_loc upd tl Hlookup :=
    [BWD] (reinsert_current_head_payload
             map_ptr cur addr loc upd_loc upd tl Hlookup).

  Lemma UpdatedAccountStateR_separated_fold
      (p : ptr) q upd :
    p |-> AccountStateRcore q (postTxState upd)
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR q (substateModel upd)
    |-- p |-> UpdatedAccountStateR q upd.
  Proof using CU MODd Sigma.
    unfold UpdatedAccountStateR.
    go.
  Qed.

  Definition UpdatedAccountStateR_separated_fold_B p q upd :=
    [BWD] (UpdatedAccountStateR_separated_fold p q upd).

  Lemma borrow_current_head_slice
      (map_ptr : ptr)
      (qcur : Qp)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    map_ptr |-> AnkerMapSliceR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR
          (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          qcur addr ((upd_loc, upd) :: tl)
          (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
    |--
    upd_loc |-> UpdatedAccountStateR 1 upd
    ** (upd_loc |-> UpdatedAccountStateR 1 upd -*
        map_ptr |-> AnkerMapSliceR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR
          (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          qcur addr ((upd_loc, upd) :: tl)
          (map (fun '(a1, (b0, _)) => (a1, b0)) cur)).
  Proof using CU MODd Sigma.
    unfold AnkerMapSliceR, VersionStackR.
    go.
    match goal with
    | |- context [nth_error ?xs (N.to_nat ?i)] =>
        destruct (nth_error xs (N.to_nat i)) as [[slice_addr slice_loc] |]
          eqn:Hslice
    end.
    {
      go using UpdatedAccountStateR_separated_fold_B.
      iExists i.
      rewrite Hslice.
      go using UpdatedAccountStateR_separated_fold_B.
    }
    {
      go.
    }
  Qed.

  Definition borrow_current_head_slice_F
      map_ptr qcur cur addr upd_loc upd tl :=
    [FWD] (borrow_current_head_slice
             map_ptr qcur cur addr upd_loc upd tl).

  Lemma borrow_current_lookup_head
      (map_ptr : ptr)
      (qcur : Qp)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (cur_loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (cur_loc, (upd_loc, upd) :: tl) ->
    StateCurrentLookupR map_ptr qcur addr cur
    |--
    upd_loc |-> UpdatedAccountStateR 1 upd
    ** (upd_loc |-> UpdatedAccountStateR 1 upd -*
        StateCurrentLookupR map_ptr qcur addr cur).
  Proof using CU MODd Sigma.
    intro Hlookup.
    unfold StateCurrentLookupR.
    rewrite Hlookup.
    exact (borrow_current_head_slice
             (map_ptr ,, o_field CU "monad::State::current_")
             qcur cur addr upd_loc upd tl).
  Qed.

  Definition borrow_current_lookup_head_F
      map_ptr qcur cur addr cur_loc upd_loc upd tl Hlookup :=
    [FWD] (borrow_current_lookup_head
             map_ptr qcur cur addr cur_loc upd_loc upd tl Hlookup).

  Lemma use_wand_local_r (P Q : mpred) : P ** (P -* Q) |-- Q.
  Proof using.
    exact (bi.wand_elim_r P Q).
  Qed.

  Definition use_wand_local_r_F P Q :=
    [FWD] (use_wand_local_r P Q).

  Lemma state_with_preTxAssumedState_same (st : StateM) :
    state_with_preTxAssumedState st (preTxAssumedState st) = st.
  Proof using.
    destruct st.
    reflexivity.
  Qed.

  Lemma original_balance_pessimistic_model_eq_map
      (st : StateM) (addr : evmopsem.evm.address) :
    original_balance_pessimistic_model st addr =
    original_balance_pessimistic_model_map (preTxAssumedState st) addr.
  Proof using.
    reflexivity.
  Qed.

  Lemma current_balance_pessimistic_model_current_lookup
      (st : StateM) (addr : evmopsem.evm.address)
      (loc upd_loc : ptr) (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup (newStates st) addr = Some (loc, (upd_loc, upd) :: tl) ->
    current_balance_pessimistic_model st addr =
    balanceOfAccount (postTxState upd).
  Proof using.
    intro Hlookup.
    unfold current_balance_pessimistic_model, recentAccountOf.
    rewrite Hlookup.
    reflexivity.
  Qed.

  Lemma current_balance_pessimistic_model_original_lookup
      (st : StateM) (addr : evmopsem.evm.address) :
    mapModelLookup (newStates st) addr = None ->
    current_balance_pessimistic_model st addr =
    original_balance_pessimistic_model st addr.
  Proof using.
    intro Hlookup.
    unfold current_balance_pessimistic_model,
      original_balance_pessimistic_model, recentAccountOf.
    rewrite Hlookup.
    reflexivity.
  Qed.

  Lemma code_entries_of_preTxAssumed_update_assum_exactness_at
      (m : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (f : AssumptionExactness -> AssumptionExactness) :
    code_entries_of_preTxAssumed (update_assum_exactness_at addr f m) =
    code_entries_of_preTxAssumed m.
  Proof using.
    induction m as [| [addr' [loc aps]] tl IH]; simpl.
    {
      reflexivity.
    }
    unfold update_assum_exactness_at in *; simpl in *.
    destruct (bool_decide (addr' = addr)); simpl;
      rewrite IH; reflexivity.
  Qed.

  Lemma stateCodeMapInvariants_update_assum_exactness_state_at
      (st : StateM) (addr : evmopsem.evm.address)
      (f : AssumptionExactness -> AssumptionExactness) :
    stateCodeMapInvariants st ->
    stateCodeMapInvariants (update_assum_exactness_state_at st addr f).
  Proof using.
    cbv delta [stateCodeMapInvariants update_assum_exactness_state_at
      codeMapOfNewStates codeMapOfPreTxAssumedAccounts all_code_entries].
    simpl.
    repeat rewrite code_entries_of_preTxAssumed_update_assum_exactness_at.
    auto.
  Qed.

  #[local] Hint Resolve
    stateCodeMapInvariants_update_assum_exactness_state_at : pure.

  Lemma StateCodeMapR_update_assum_exactness_state_at
      (p : ptr) (st : StateM) (addr : evmopsem.evm.address)
      (f : AssumptionExactness -> AssumptionExactness) :
    p |-> StateCodeMapR st
    |-- p |-> StateCodeMapR (update_assum_exactness_state_at st addr f).
  Proof using CU MODd Sigma.
    unfold StateCodeMapR.
    go.
  Qed.

  Definition StateCodeMapR_update_assum_exactness_state_at_F
      p st addr f :=
    [FWD] (StateCodeMapR_update_assum_exactness_state_at p st addr f).

  Lemma check_min_balance_current_reassemble
      (this p : ptr) (st : StateM) (addr : evmopsem.evm.address)
      (cur_loc upd_loc : ptr) (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) (value : N) :
    mapModelLookup (newStates st) addr = Some (cur_loc, (upd_loc, upd) :: tl) ->
    this |-> StateCodeMapR st
    ** this ,, o_field CU "monad::State::current_"
        |-> AnkerMapPayloadsR
              "monad::Address" "monad::VersionStack<monad::AccountState>"
              addressR
              (VersionStackR "monad::AccountState" UpdatedAccountStateR)
              1 (removeKey (newStates st) addr)
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** cur_loc ,, pairSndOffset
                    "monad::Address" "monad::VersionStack<monad::AccountState>"
        |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** cur_loc ,, pairFstOffset
                    "monad::Address" "monad::VersionStack<monad::AccountState>"
        |-> addressR (1 / 2) addr
    ** this ,, o_field CU "monad::State::original_"
        |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
              addressToN addressR 1
              (map (fun '(a1, (b0, _)) => (a1, b0))
                 (preTxAssumedState st))
    ** this ,, o_field CU "monad::State::original_"
        |-> AnkerMapPayloadsR
              "monad::Address" "monad::OriginalAccountState"
              addressR OriginalAccountStateR 1
              (check_min_balance_update_with_account
                 (preTxAssumedState st) addr (postTxState upd) value)
    ** upd_loc |-> AccountStateRcore 1 (postTxState upd)
    ** upd_loc ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 (substateModel upd)
    ** p |-> boolR 1$m
          (check_min_balance_ok (balanceOfAccount (postTxState upd)) value)
    |--
    this ,, o_field CU "monad::State::current_"
      |-> AnkerMapPayloadsR
            "monad::Address" "monad::VersionStack<monad::AccountState>"
            addressR
            (VersionStackR "monad::AccountState" UpdatedAccountStateR)
            1 (newStates st)
    ** (this ,, o_field CU "monad::State::original_"
          |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                addressToN addressR 1
                (map (fun '(a1, (b0, _)) => (a1, b0))
                   (update_assum_exactness_at addr
                      (fun ex =>
                         min_balance_update ex
                           (original_balance_pessimistic_model st addr)
                           (current_balance_pessimistic_model st addr)
                           value)
                      (preTxAssumedState st)))
       ** this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR
                "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1
                (update_assum_exactness_at addr
                   (fun ex =>
                      min_balance_update ex
                        (original_balance_pessimistic_model st addr)
                        (current_balance_pessimistic_model st addr)
                        value)
                   (preTxAssumedState st))
       ** this |-> StateCodeMapR
            (update_assum_exactness_state_at st addr
               (fun ex =>
                  min_balance_update ex
                    (original_balance_pessimistic_model st addr)
                    (current_balance_pessimistic_model st addr)
                    value))
       ** p |-> boolR 1$m
            (check_min_balance_ok (current_balance_pessimistic_model st addr)
               value)).
  Proof using CU MODd Sigma.
    intro Hcur.
    rewrite original_balance_pessimistic_model_eq_map.
    rewrite (current_balance_pessimistic_model_current_lookup
               st addr cur_loc upd_loc upd tl Hcur).
    set (f := fun ex =>
      min_balance_update ex
        (original_balance_pessimistic_model_map (preTxAssumedState st) addr)
        (balanceOfAccount (postTxState upd))
        value).
    change (check_min_balance_update_with_account
              (preTxAssumedState st) addr (postTxState upd) value)
      with (update_assum_exactness_at addr f (preTxAssumedState st)).
    rewrite map_key_ptr_update_assum_exactness_at.
    pose proof
      (reinsert_current_head_payload
         (this ,, o_field CU "monad::State::current_")
         (newStates st) addr cur_loc upd_loc upd tl Hcur) as Hreinsert.
    pose proof
      (UpdatedAccountStateR_separated_fold upd_loc 1 upd) as Hfold_upd.
    pose proof
      (StateCodeMapR_update_assum_exactness_state_at this st addr f) as Hcode.
    wapply Hcode.
    wapply Hreinsert.
    wapply Hfold_upd.
    go using use_wand_local_r_F.
  Qed.

  Definition check_min_balance_current_reassemble_F
      this p st addr cur_loc upd_loc upd tl value Hcur :=
    [FWD] (check_min_balance_current_reassemble
             this p st addr cur_loc upd_loc upd tl value Hcur).

  Lemma original_balance_pessimistic_model_map_lookup
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr) (orig_state : AssumedPreTxAccountState) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    original_balance_pessimistic_model_map orig addr =
    balanceOfAccount (preTxState orig_state).
  Proof using.
    intro Hlookup.
    unfold original_balance_pessimistic_model_map, preTxAccountOf_map.
    rewrite Hlookup.
    reflexivity.
  Qed.

  Lemma check_min_balance_original_reassemble
      (this p : ptr) (st : StateM) (addr : evmopsem.evm.address)
      (loc : ptr) (orig_state : AssumedPreTxAccountState) (value : N) :
    mapModelLookup (newStates st) addr = None ->
    mapModelLookup (preTxAssumedState st) addr = Some (loc, orig_state) ->
    this |-> StateCodeMapR st
    ** this ,, o_field CU "monad::State::original_"
        |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
              addressToN addressR 1
              (map (fun '(a1, (b0, _)) => (a1, b0))
                 (preTxAssumedState st))
    ** this ,, o_field CU "monad::State::original_"
        |-> AnkerMapPayloadsR
              "monad::Address" "monad::OriginalAccountState"
              addressR OriginalAccountStateR 1
              (check_min_balance_update_with_account
                 (preTxAssumedState st) addr (preTxState orig_state) value)
    ** p |-> boolR 1$m
          (check_min_balance_ok (balanceOfAccount (preTxState orig_state))
             value)
    |--
    this ,, o_field CU "monad::State::original_"
      |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
            addressToN addressR 1
            (map (fun '(a1, (b0, _)) => (a1, b0))
               (update_assum_exactness_at addr
                  (fun ex =>
                     min_balance_update ex
                       (original_balance_pessimistic_model st addr)
                       (current_balance_pessimistic_model st addr)
                       value)
                  (preTxAssumedState st)))
    ** this ,, o_field CU "monad::State::original_"
      |-> AnkerMapPayloadsR
            "monad::Address" "monad::OriginalAccountState"
            addressR OriginalAccountStateR 1
            (update_assum_exactness_at addr
               (fun ex =>
                  min_balance_update ex
                    (original_balance_pessimistic_model st addr)
                    (current_balance_pessimistic_model st addr)
                    value)
               (preTxAssumedState st))
    ** this |-> StateCodeMapR
          (update_assum_exactness_state_at st addr
             (fun ex =>
                min_balance_update ex
                  (original_balance_pessimistic_model st addr)
                  (current_balance_pessimistic_model st addr)
                  value))
    ** p |-> boolR 1$m
          (check_min_balance_ok (current_balance_pessimistic_model st addr)
             value).
  Proof using CU MODd Sigma.
    intros Hcur Hlookup.
    rewrite (current_balance_pessimistic_model_original_lookup st addr Hcur).
    rewrite original_balance_pessimistic_model_eq_map.
    rewrite (original_balance_pessimistic_model_map_lookup
               (preTxAssumedState st) addr loc orig_state Hlookup).
    set (bal := balanceOfAccount (preTxState orig_state)).
    set (f := fun ex => min_balance_update ex bal bal value).
    unfold check_min_balance_update_with_account.
    rewrite (original_balance_pessimistic_model_map_lookup
               (preTxAssumedState st) addr loc orig_state Hlookup).
    change (update_assum_exactness_at addr
              (fun ex => min_balance_update ex bal bal value)
              (preTxAssumedState st))
      with (update_assum_exactness_at addr f (preTxAssumedState st)).
    rewrite map_key_ptr_update_assum_exactness_at.
    pose proof
      (StateCodeMapR_update_assum_exactness_state_at this st addr f) as Hcode.
    wapply Hcode.
    go using use_wand_local_r_F.
  Qed.

  Definition check_min_balance_original_reassemble_F
      this p st addr loc orig_state value Hcur Hlookup :=
    [FWD] (check_min_balance_original_reassemble
             this p st addr loc orig_state value Hcur Hlookup).

  Lemma mapModelLookup_update_assum_exactness_at_eq_local
      (m : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (f : AssumptionExactness -> AssumptionExactness) :
    mapModelLookup (update_assum_exactness_at addr f m) addr =
    match mapModelLookup m addr with
    | Some (loc, aps) =>
        Some (loc, update_assum_exactness_assumed f aps)
    | None => None
    end.
  Proof using.
    induction m as [| [addr' [loc aps]] tl IH]; simpl.
    {
      reflexivity.
    }
    destruct (decide (addr' = addr)) as [Heq | Hneq].
    {
      subst addr'.
      unfold mapModelLookup; simpl.
      rewrite lookup_insert.
      unfold update_assum_exactness_at; simpl.
      rewrite (bool_decide_eq_true_2 (addr = addr)); [| reflexivity].
      simpl.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_ | Hcontra].
      2:{ contradiction Hcontra; reflexivity. }
      reflexivity.
    }
    unfold mapModelLookup; simpl.
    unfold update_assum_exactness_at; simpl.
    rewrite (bool_decide_eq_false_2 (addr' = addr)); [| exact Hneq].
    simpl.
    rewrite lookup_insert_ne.
    2:{ intro Heq. apply Hneq. exact Heq. }
    rewrite lookup_insert_ne.
    2:{ intro Heq. apply Hneq. exact Heq. }
    exact IH.
  Qed.

  Lemma mapModelLookup_update_assum_exactness_at_ne
      (m : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr a : evmopsem.evm.address)
      (f : AssumptionExactness -> AssumptionExactness) :
    a <> addr ->
    mapModelLookup (update_assum_exactness_at addr f m) a =
    mapModelLookup m a.
  Proof using.
    intro Hneq.
    induction m as [| [addr' [loc aps]] tl IH]; simpl.
    {
      reflexivity.
    }
    unfold mapModelLookup in *; simpl in *.
    unfold update_assum_exactness_at in *; simpl in *.
    destruct (bool_decide (addr' = addr)) eqn:Heq_addr; simpl.
    {
      rewrite bool_decide_eq_true in Heq_addr.
      subst addr'.
      rewrite !lookup_insert_ne.
      { exact IH. }
      { intro Heq. apply Hneq. symmetry. exact Heq. }
      { intro Heq. apply Hneq. symmetry. exact Heq. }
    }
    destruct (decide (a = addr')) as [-> | Ha_ne].
    {
      rewrite !lookup_insert.
      cbn.
      destruct (decide (addr' = addr')) as [_ | Hcontra].
      2:{ contradiction Hcontra; reflexivity. }
      reflexivity.
    }
    rewrite !lookup_insert_ne.
    { exact IH. }
    { intro Heq. apply Ha_ne. symmetry. exact Heq. }
    { intro Heq. apply Ha_ne. symmetry. exact Heq. }
  Qed.

  Lemma assumptionAndUpdateOfAddr_update_assum_exactness_state_at_ne
      (st : StateM) (addr a : evmopsem.evm.address)
      (f : AssumptionExactness -> AssumptionExactness) :
    a <> addr ->
    assumptionAndUpdateOfAddr (update_assum_exactness_state_at st addr f) a =
    assumptionAndUpdateOfAddr st a.
  Proof using.
    intro Hneq.
    unfold assumptionAndUpdateOfAddr, update_assum_exactness_state_at; simpl.
    change ((update_assum_exactness_at addr f (preTxAssumedState st)) !! a)
      with (mapModelLookup (update_assum_exactness_at addr f (preTxAssumedState st)) a).
    change (preTxAssumedState st !! a)
      with (mapModelLookup (preTxAssumedState st) a).
    rewrite mapModelLookup_update_assum_exactness_at_ne; [reflexivity | exact Hneq].
  Qed.

  Lemma validSliceInvariants_update_assum_exactness_state_at_min_balance
      (st : StateM) (addr : evmopsem.evm.address)
      (loc : ptr) (aps : AssumedPreTxAccountState)
      (cur value : N) :
    validSliceInvariants st ->
    mapModelLookup (preTxAssumedState st) addr = Some (loc, aps) ->
    validSliceInvariants
      (update_assum_exactness_state_at st addr
         (fun ex =>
            min_balance_update ex
              (original_balance_pessimistic_model st addr) cur value)).
  Proof using.
    intros Hslice Hlookup a au Hau.
    destruct (decide (a = addr)) as [Heq | Hneq].
    {
      subst a.
      unfold assumptionAndUpdateOfAddr, update_assum_exactness_state_at in Hau.
      simpl in Hau.
      change ((update_assum_exactness_at addr
                 (λ ex : AssumptionExactness,
                    min_balance_update ex (original_balance_pessimistic_model st addr)
                      cur value) (preTxAssumedState st)) !! addr)
        with (mapModelLookup
                (update_assum_exactness_at addr
                   (λ ex : AssumptionExactness,
                      min_balance_update ex (original_balance_pessimistic_model st addr)
                        cur value) (preTxAssumedState st)) addr) in Hau.
      rewrite mapModelLookup_update_assum_exactness_at_eq_local in Hau.
      rewrite Hlookup in Hau.
      simpl in Hau.
      inversion Hau; subst au; clear Hau.
      unfold update_assum_exactness_assumed.
      set (txs :=
        (newStates st !! addr) ≫=
          (fun a : ptr * list (ptr * UpdatedAccountState) =>
             match head a.2 with
             | Some (loc0, upd) => Some (a.1, (loc0, upd))
             | None => None
             end)) in *.
      assert (Hold_slice :
        sliceInvariants
          {| preAssumption := aps;
             originalLoc := loc;
             txUpdates := txs |}).
      {
        apply Hslice with (addr := addr).
        unfold assumptionAndUpdateOfAddr.
        change (preTxAssumedState st !! addr)
          with (mapModelLookup (preTxAssumedState st) addr).
        rewrite Hlookup.
        subst txs.
        reflexivity.
      }
      pose proof
        (assumption_exactness_stricter_min_balance_update
           (assumExactness aps)
           (original_balance_pessimistic_model st addr) cur value)
        as [Hmin _].
      unfold min_balance_stricter in Hmin.
      unfold sliceInvariants in Hold_slice |- *.
      destruct (min_balance (assumExactness aps)) as [old_min |] eqn:Hold_min.
      {
        destruct (min_balance
          (min_balance_update (assumExactness aps)
             (original_balance_pessimistic_model st addr) cur value))
          as [new_min |] eqn:Hnew_min.
        {
          rewrite Hold_min in Hold_slice.
          rewrite Hnew_min.
          simpl in Hmin.
          destruct txs as [[cur_loc [upd_loc upd]] |]; simpl in *; [| exact I].
          destruct (postTxState upd) as [updated |]; simpl in *; [| exact I].
          destruct (preTxState aps) as [assumed |]; simpl in *; [| exact I].
          eapply N.le_trans; [exact Hold_slice | exact Hmin].
        }
        rewrite Hnew_min.
        destruct txs; exact I.
      }
      destruct (min_balance
        (min_balance_update (assumExactness aps)
           (original_balance_pessimistic_model st addr) cur value))
        as [new_min |] eqn:Hnew_min.
      {
        contradiction.
      }
      rewrite Hnew_min.
      destruct txs; exact I.
    }
    apply Hslice with (addr := a).
    rewrite <-
      (assumptionAndUpdateOfAddr_update_assum_exactness_state_at_ne
         st addr a
         (fun ex =>
            min_balance_update ex
              (original_balance_pessimistic_model st addr) cur value)
         Hneq).
    exact Hau.
  Qed.

  Lemma validModel_update_assum_exactness_state_at_min_balance
      (st : StateM) (addr : evmopsem.evm.address)
      (loc : ptr) (aps : AssumedPreTxAccountState)
      (cur value : N) :
    validModel st ->
    mapModelLookup (preTxAssumedState st) addr = Some (loc, aps) ->
    validModel
      (update_assum_exactness_state_at st addr
         (fun ex =>
            min_balance_update ex
              (original_balance_pessimistic_model st addr) cur value)).
  Proof using.
    intros Hvalid Hlookup.
    unfold validModel in *.
    destruct Hvalid as [Hsub [Hstate [Hpost Hslice]]].
    split.
    {
      unfold update_assum_exactness_state_at; simpl.
      rewrite map_fst_update_assum_exactness_at.
      exact Hsub.
    }
    split.
    {
      intro a.
      destruct (decide (a = addr)) as [-> | Hneq].
      {
        unfold assumptionAndUpdateOfAddr, update_assum_exactness_state_at; simpl.
        change ((update_assum_exactness_at addr
                   (λ ex : AssumptionExactness,
                      min_balance_update ex (original_balance_pessimistic_model st addr)
                        cur value) (preTxAssumedState st)) !! addr)
          with (mapModelLookup
                  (update_assum_exactness_at addr
                     (λ ex : AssumptionExactness,
                        min_balance_update ex (original_balance_pessimistic_model st addr)
                          cur value) (preTxAssumedState st)) addr).
        rewrite mapModelLookup_update_assum_exactness_at_eq_local.
        rewrite Hlookup.
        simpl.
        unfold validAU; simpl.
        destruct (preTxState aps) as [cs |] eqn:Hpre; [| exact I].
        destruct
          (isSome
             (min_balance
                (min_balance_update (assumExactness aps)
                   (original_balance_pessimistic_model st addr) cur value)))
          eqn:Hsome; [| exact I].
        destruct
          (min_balance
             (min_balance_update (assumExactness aps)
                (original_balance_pessimistic_model st addr) cur value))
          as [new_min |] eqn:Hnew_min; [| discriminate].
        unfold min_balanceN.
        rewrite Hnew_min.
        simpl.
        pose proof (validModel_bound_of_lookup st addr loc aps) as Hbound.
        specialize (Hbound (conj Hsub (conj Hstate (conj Hpost Hslice))) Hlookup).
        rewrite Hpre in Hbound.
        simpl in Hbound.
        assert (Hold_bound :
          match min_balance (assumExactness aps) with
          | Some old_min => (old_min <= cs .^ _balance)%N
          | None => True
          end).
        {
          destruct (min_balance (assumExactness aps)) as [old_min |] eqn:Hold_min;
            [| exact I].
          unfold min_balanceN in Hbound.
          rewrite Hold_min in Hbound.
          simpl in Hbound.
          exact Hbound.
        }
        assert (Horig_eq :
          original_balance_pessimistic_model st addr = cs .^ _balance).
        {
          unfold original_balance_pessimistic_model, preTxAccountOf.
          rewrite Hlookup.
          simpl.
          rewrite Hpre.
          reflexivity.
        }
        pose proof
          (min_balance_update_upper_bound
             (assumExactness aps)
             (original_balance_pessimistic_model st addr) cur value)
          as Hupper.
        rewrite Horig_eq in Hnew_min.
        rewrite Horig_eq in Hupper.
        specialize (Hupper Hold_bound).
        rewrite Hnew_min in Hupper.
        exact Hupper.
      }
      rewrite assumptionAndUpdateOfAddr_update_assum_exactness_state_at_ne;
        [exact (Hstate a) | exact Hneq].
    }
    split.
    {
      intros a loc1 tl loc0 aps1 Hnew Hpre.
      destruct (decide (a = addr)) as [-> | Hneq].
      {
        unfold update_assum_exactness_state_at in Hpre; simpl in Hpre.
        change ((update_assum_exactness_at addr
                   (λ ex : AssumptionExactness,
                      min_balance_update ex (original_balance_pessimistic_model st addr)
                        cur value) (preTxAssumedState st)) !! addr)
          with (mapModelLookup
                  (update_assum_exactness_at addr
                     (λ ex : AssumptionExactness,
                        min_balance_update ex (original_balance_pessimistic_model st addr)
                          cur value) (preTxAssumedState st)) addr) in Hpre.
        rewrite mapModelLookup_update_assum_exactness_at_eq_local in Hpre.
        rewrite Hlookup in Hpre.
        inversion Hpre; subst loc0 aps1; clear Hpre.
        simpl.
        eapply Hpost; eauto.
      }
      unfold update_assum_exactness_state_at in Hpre; simpl in Hpre.
      change ((update_assum_exactness_at addr
                 (λ ex : AssumptionExactness,
                    min_balance_update ex (original_balance_pessimistic_model st addr)
                      cur value) (preTxAssumedState st)) !! a)
        with (mapModelLookup
                (update_assum_exactness_at addr
                   (λ ex : AssumptionExactness,
                      min_balance_update ex (original_balance_pessimistic_model st addr)
                        cur value) (preTxAssumedState st)) a) in Hpre.
      rewrite mapModelLookup_update_assum_exactness_at_ne in Hpre;
        [| exact Hneq].
      eapply Hpost; eauto.
    }
    {
      eapply validSliceInvariants_update_assum_exactness_state_at_min_balance; eauto.
    }
  Qed.

  #[local] Hint Resolve
    validModel_update_assum_exactness_state_at_min_balance : pure.

  Lemma prf_state_record_balance_constraint_for_debit :
    verify[state_cpp.source] state_record_balance_constraint_for_debit_spec.
  Proof using MODd.
    verify_spec.
    go.
    iExists orig.
    iExists qcur.
    iExists cur.
    go.
    match goal with
    | Hrecent : state_recent_account_slice_post orig cur addr
        ?orig_after ?recent_loc ?accountp ?recent_orig_state ?acct |- _ =>
        rename Hrecent into Hrecent_post;
        unfold state_recent_account_slice_post in Hrecent_post;
        destruct (mapModelLookup cur addr) as [[cur_loc updates] |] eqn:Hcur
    end.
    {
      destruct Hrecent_post
        as [upd_loc [upd [tl [Hupdates [Horig_after [Haccountp Hacct]]]]]].
      subst.
      go using borrow_current_lookup_head_F.
      iExists (postTxState upd).
      unfold UpdatedAccountStateR, AccountStateRcore.
      go.
      destruct (postTxState upd) as [acct|] eqn:Hacct.
      {
        go.
        go using optional_specs.trivial_optional_some_split_F.
        unfold AccountR.
        go.
        fold AccountR.
        iExists orig.
        go.
        match goal with
        | Hsome : is_Some (mapModelLookup orig addr) |- _ =>
            destruct Hsome as [[old_loc old_state] Horig_old]
        end.
        match goal with
        | Hpost : state_original_account_state_post orig addr
            ?orig_final ?loc ?orig_state |- _ =>
            destruct (state_original_account_state_post_existing
              orig orig_final addr loc old_loc orig_state old_state
              Horig_old Hpost) as [Hmap [Hloc Hstate]];
            subst
        end.
        go using borrow_original_account_payload_F.
        wp_if.
        {
          intros Hge.
          go.
          iExists (preTxState old_state).
          unfold OriginalAccountStateR.
          go.
          destruct (preTxState old_state) as [original|] eqn:Horiginal.
          {
            go using optional_specs.trivial_optional_some_split_F.
            unfold AccountR.
            go.
            fold AccountR.
            iExists original.
            go using optional_specs.trivial_optional_some_split_F.
            unfold AccountR.
            go.
            fold AccountR.
            wp_if.
            {
              intros Hgt.
              rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ Hge ltac:(assumption)) in Hgt |- *.
              go.
              rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ (N.lt_le_incl _ _ Hgt)
                ltac:(assumption)).
              iExists old_state.
              wapply (OriginalAccountStateR_separated_fold
                (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
                1 old_state).
              rewrite Horiginal.
              go using optionR_account_some_separated_fold_B.
              unfold account_option_layout.
              go using AccountR_separated_fold_B.
              unfold original_balance_pessimistic_model_assumed.
              rewrite Horiginal.
              cbn [balanceOfAccount].
              change (original .^ _balance) with (balance original).
              match goal with
              | Hbal : balance original = _ |- _ => rewrite Hbal
              end.
              go.
              iExists orig, old_loc, old_state.
              unfold check_min_balance_recent_account_model.
              rewrite Hcur.
              cbn [current_balance_pessimistic_model_stack recentAccountOf_stack].
              rewrite Hacct.
              unfold check_min_balance_update_model.
              rewrite (original_balance_pessimistic_model_map_lookup
                orig addr old_loc old_state Horig_old) Horiginal.
              change (balanceOfAccount (Some acct)) with (balance acct).
              change (balanceOfAccount (Some original)) with (balance original).
              match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
              match goal with Hbal : balance original = _ |- _ => rewrite Hbal end.
              assert (Hok : check_min_balance_ok
                (w256_to_N (block.block_account_balance (coreAc acct))) value = true).
              { apply bool_decide_true. exact Hge. }
              unfold min_balance_update.
              rewrite Hok.
              rewrite (proj2 (N.ltb_lt _ _) Hgt).
              rewrite map_key_ptr_update_assum_exactness_at.
              go.
              iExists _.
              eagerUnifyC.
              unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
              rewrite Hacct.
              change (balanceOfAccount (Some acct)) with (balance acct).
              match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
              rewrite Hok.
              fold OriginalAccountStateR.
              match goal with
              | |- context [update_assum_exactness_at addr ?f orig] =>
                  wapply (reinsert_updated_original_account_payload_only
                    (this ,, o_field CU "monad::State::original_")
                    _ orig addr old_loc old_state f Horig_old eq_refl)
              end.
              go.
            }
            {
              intros Hnlt.
              rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ Hge ltac:(assumption)) in Hnlt.
              wapply (OriginalAccountStateR_separated_fold
                (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
                1 old_state).
              rewrite Horiginal.
              go using optionR_account_some_separated_fold_B.
              unfold account_option_layout.
              go using AccountR_separated_fold_B.
              iExists orig, old_loc, old_state.
              unfold check_min_balance_recent_account_model.
              rewrite Hcur.
              cbn [recentAccountOf_stack].
              rewrite Hacct.
              unfold check_min_balance_update_model.
              rewrite (original_balance_pessimistic_model_map_lookup
                orig addr old_loc old_state Horig_old) Horiginal.
              change (balanceOfAccount (Some acct)) with (balance acct).
              change (balanceOfAccount (Some original)) with (balance original).
              match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
              match goal with Hbal : balance original = _ |- _ => rewrite Hbal end.
              assert (Hok : check_min_balance_ok
                (w256_to_N (block.block_account_balance (coreAc acct))) value = true).
              { apply bool_decide_true. exact Hge. }
              unfold min_balance_update.
              rewrite Hok (proj2 (N.ltb_ge _ _) Hnlt).
              rewrite map_key_ptr_update_assum_exactness_at.
              go.
              iExists _.
              eagerUnifyC.
              unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
              rewrite Hacct.
              change (balanceOfAccount (Some acct)) with (balance acct).
              match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
              rewrite Hok.
              fold OriginalAccountStateR.
              match goal with
              | |- context [update_assum_exactness_at addr ?f orig] =>
                  assert (Hsame : update_assum_exactness_assumed f old_state = old_state);
                  [ destruct old_state as [ac storage [bound nonce]];
                    destruct bound; reflexivity
                  | wapply (reinsert_updated_original_account_payload_only
                      (this ,, o_field CU "monad::State::original_")
                      _ orig addr old_loc old_state f Horig_old eq_refl) ]
              end.
              rewrite Hsame.
              go.
            }
          }
          {
            go.
            wapply (OriginalAccountStateR_separated_fold
              (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
              1 old_state).
            rewrite Horiginal.
            go.
            iExists orig, old_loc, old_state.
            unfold check_min_balance_recent_account_model.
            rewrite Hcur.
            cbn [recentAccountOf_stack].
            rewrite Hacct.
            unfold check_min_balance_update_model.
            rewrite (original_balance_pessimistic_model_map_lookup
              orig addr old_loc old_state Horig_old) Horiginal.
            change (balanceOfAccount (Some acct)) with (balance acct).
            match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
            assert (Hok : check_min_balance_ok
              (w256_to_N (block.block_account_balance (coreAc acct))) value = true).
            { apply bool_decide_true. exact Hge. }
            unfold min_balance_update.
            rewrite Hok.
            cbn [balanceOfAccount N.ltb].
            rewrite (proj2 (N.ltb_ge _ 0) (N.le_0_l _)).
            rewrite map_key_ptr_update_assum_exactness_at.
            go.
            iExists _.
            eagerUnifyC.
            unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
            rewrite Hacct.
            change (balanceOfAccount (Some acct)) with (balance acct).
            match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
            rewrite Hok.
            fold OriginalAccountStateR.
            match goal with
            | |- context [update_assum_exactness_at addr ?f orig] =>
                assert (Hsame : update_assum_exactness_assumed f old_state = old_state);
                [ destruct old_state as [ac storage [bound nonce]];
                  destruct bound; reflexivity
                | wapply (reinsert_updated_original_account_payload_only
                    (this ,, o_field CU "monad::State::original_")
                    _ orig addr old_loc old_state f Horig_old eq_refl) ]
            end.
            rewrite Hsame.
            go.
          }
        }
        {
          intros Hlt.
          go.
          iExists old_state.
          go.
          iExists orig, old_loc, old_state.
          unfold check_min_balance_recent_account_model.
          rewrite Hcur.
          cbn [recentAccountOf_stack].
          rewrite Hacct.
          unfold check_min_balance_update_model.
          change (balanceOfAccount (Some acct)) with (balance acct).
          match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
          assert (Hok : check_min_balance_ok
            (w256_to_N (block.block_account_balance (coreAc acct))) value = false).
          { apply bool_decide_false. lia. }
          unfold min_balance_update.
          rewrite Hok map_key_ptr_update_assum_exactness_at.
          go.
          iExists _.
          eagerUnifyC.
          unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
          rewrite Hacct.
          change (balanceOfAccount (Some acct)) with (balance acct).
          match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
          rewrite Hok.
          wapply (reinsert_updated_original_account_payload_only
            (this ,, o_field CU "monad::State::original_")
            _ orig addr old_loc old_state exact_balance_update Horig_old eq_refl).
          go.
        }
      }
      {
        go.
        rewrite Z.mod_0_l; [| unfold uint64_word_modulus; lia].
        cbn [Z.to_N].
        iExists orig.
        go.
        match goal with
        | Hsome : is_Some (mapModelLookup orig addr) |- _ =>
            destruct Hsome as [[old_loc old_state] Horig_old]
        end.
        match goal with
        | Hpost : state_original_account_state_post orig addr
            ?orig_final ?loc ?orig_state |- _ =>
            destruct (state_original_account_state_post_existing
              orig orig_final addr loc old_loc orig_state old_state
              Horig_old Hpost) as [Hmap [Hloc Hstate]];
            subst
        end.
        go using borrow_original_account_payload_F.
        wp_if.
        {
          intros Hge.
          go.
          iExists (preTxState old_state).
          unfold OriginalAccountStateR.
          go.
          destruct (preTxState old_state) as [original|] eqn:Horiginal.
          {
            go using optional_specs.trivial_optional_some_split_F.
            unfold AccountR.
            go.
            fold AccountR.
            iExists original.
            go using optional_specs.trivial_optional_some_split_F.
            unfold AccountR.
            go.
            fold AccountR.
            wp_if.
            {
              intros Hgt.
              rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ (N.le_refl 0) ltac:(assumption)) in Hgt |- *.
              go.
              rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ (N.lt_le_incl _ _ Hgt)
                ltac:(assumption)).
              iExists old_state.
              wapply (OriginalAccountStateR_separated_fold
                (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
                1 old_state).
              rewrite Horiginal.
              go using optionR_account_some_separated_fold_B.
              unfold account_option_layout.
              go using AccountR_separated_fold_B.
              unfold original_balance_pessimistic_model_assumed.
              rewrite Horiginal.
              cbn [balanceOfAccount].
              change (original .^ _balance) with (balance original).
              match goal with
              | Hbal : balance original = _ |- _ => rewrite Hbal
              end.
              go.
              iExists orig, old_loc, old_state.
              unfold check_min_balance_recent_account_model.
              rewrite Hcur.
              cbn [current_balance_pessimistic_model_stack recentAccountOf_stack].
              rewrite Hacct.
              unfold check_min_balance_update_model.
              rewrite (original_balance_pessimistic_model_map_lookup
                orig addr old_loc old_state Horig_old) Horiginal.
              change (balanceOfAccount None) with 0%N.
              change (balanceOfAccount (Some original)) with (balance original).
              match goal with Hbal : balance original = _ |- _ => rewrite Hbal end.
              assert (Hok : check_min_balance_ok
                0%N 0%N = true).
              { reflexivity. }
              unfold min_balance_update.
              rewrite Hok.
              rewrite (proj2 (N.ltb_lt _ _) Hgt).
              rewrite map_key_ptr_update_assum_exactness_at.
              go.
              iExists _.
              eagerUnifyC.
              unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
              rewrite Hacct.
              change (balanceOfAccount None) with 0%N.
              rewrite Hok.
              fold OriginalAccountStateR.
              match goal with
              | |- context [update_assum_exactness_at addr ?f orig] =>
                  wapply (reinsert_updated_original_account_payload_only
                    (this ,, o_field CU "monad::State::original_")
                    _ orig addr old_loc old_state f Horig_old eq_refl)
              end.
              go.
            }
            {
              intros Hnlt.
              rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ (N.le_refl 0) ltac:(assumption)) in Hnlt.
              wapply (OriginalAccountStateR_separated_fold
                (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
                1 old_state).
              rewrite Horiginal.
              go using optionR_account_some_separated_fold_B.
              unfold account_option_layout.
              go using AccountR_separated_fold_B.
              iExists orig, old_loc, old_state.
              unfold check_min_balance_recent_account_model.
              rewrite Hcur.
              cbn [recentAccountOf_stack].
              rewrite Hacct.
              unfold check_min_balance_update_model.
              rewrite (original_balance_pessimistic_model_map_lookup
                orig addr old_loc old_state Horig_old) Horiginal.
              change (balanceOfAccount None) with 0%N.
              change (balanceOfAccount (Some original)) with (balance original).
              match goal with Hbal : balance original = _ |- _ => rewrite Hbal end.
              assert (Hok : check_min_balance_ok
                0%N 0%N = true).
              { reflexivity. }
              unfold min_balance_update.
              rewrite Hok (proj2 (N.ltb_ge 0
                (w256_to_N (block.block_account_balance (coreAc original)))) ltac:(lia)).
              rewrite map_key_ptr_update_assum_exactness_at.
              go.
              iExists _.
              eagerUnifyC.
              unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
              rewrite Hacct.
              change (balanceOfAccount None) with 0%N.
              rewrite Hok.
              fold OriginalAccountStateR.
              match goal with
              | |- context [update_assum_exactness_at addr ?f orig] =>
                  assert (Hsame : update_assum_exactness_assumed f old_state = old_state);
                  [ destruct old_state as [ac storage [bound nonce]];
                    destruct bound; reflexivity
                  | wapply (reinsert_updated_original_account_payload_only
                      (this ,, o_field CU "monad::State::original_")
                      _ orig addr old_loc old_state f Horig_old eq_refl) ]
              end.
              rewrite Hsame.
              go.
            }
          }
          {
            go.
            wapply (OriginalAccountStateR_separated_fold
              (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
              1 old_state).
            rewrite Horiginal.
            go.
            iExists orig, old_loc, old_state.
            unfold check_min_balance_recent_account_model.
            rewrite Hcur.
            cbn [recentAccountOf_stack].
            rewrite Hacct.
            unfold check_min_balance_update_model.
            rewrite (original_balance_pessimistic_model_map_lookup
              orig addr old_loc old_state Horig_old) Horiginal.
            change (balanceOfAccount None) with 0%N.
            assert (Hok : check_min_balance_ok
              0%N 0%N = true).
            { reflexivity. }
            unfold min_balance_update.
            rewrite Hok.
            cbn [balanceOfAccount N.ltb].
            rewrite (proj2 (N.ltb_ge _ 0) (N.le_0_l _)).
            rewrite map_key_ptr_update_assum_exactness_at.
            go.
            iExists _.
            eagerUnifyC.
            unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
            rewrite Hacct.
            change (balanceOfAccount None) with 0%N.
            rewrite Hok.
            fold OriginalAccountStateR.
            match goal with
            | |- context [update_assum_exactness_at addr ?f orig] =>
                assert (Hsame : update_assum_exactness_assumed f old_state = old_state);
                [ destruct old_state as [ac storage [bound nonce]];
                  destruct bound; reflexivity
                | wapply (reinsert_updated_original_account_payload_only
                    (this ,, o_field CU "monad::State::original_")
                    _ orig addr old_loc old_state f Horig_old eq_refl) ]
            end.
            rewrite Hsame.
            go.
          }
        }
        {
          intros Hlt.
          go.
          iExists old_state.
          go.
          iExists orig, old_loc, old_state.
          unfold check_min_balance_recent_account_model.
          rewrite Hcur.
          cbn [recentAccountOf_stack].
          rewrite Hacct.
          unfold check_min_balance_update_model.
          change (balanceOfAccount None) with 0%N.
          assert (Hok : check_min_balance_ok
            0%N value = false).
          { apply bool_decide_false. lia. }
          unfold min_balance_update.
          rewrite Hok map_key_ptr_update_assum_exactness_at.
          go.
          iExists _.
          eagerUnifyC.
          unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
          rewrite Hacct.
          change (balanceOfAccount None) with 0%N.
          rewrite Hok.
          wapply (reinsert_updated_original_account_payload_only
            (this ,, o_field CU "monad::State::original_")
            _ orig addr old_loc old_state exact_balance_update Horig_old eq_refl).
          go.
        }
      }
    }
    {
      destruct Hrecent_post as [Hrecent_post [Haccountp Hacct]].
      match goal with
      | Hpost : state_original_account_state_post orig addr
          ?after ?loc ?state |- _ =>
          rename after into orig_after;
          rename loc into old_loc;
          rename state into old_state;
          pose proof (state_original_account_state_post_lookup
            orig orig_after addr old_loc old_state Hpost) as Horig_old
      end.
      subst.
      go using borrow_original_account_payload_F.
      iExists (preTxState old_state).
      unfold OriginalAccountStateR.
      go.
      destruct (preTxState old_state) as [acct|] eqn:Hacct.
      {
        go using optional_specs.trivial_optional_some_split_F.
        unfold AccountR.
        go.
        fold AccountR.
        iExists acct.
        go using optional_specs.trivial_optional_some_split_F.
        unfold AccountR.
        go.
        fold AccountR.
        wapply (OriginalAccountStateR_separated_fold
          (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
          1 old_state).
        rewrite Hacct.
        go using optionR_account_some_separated_fold_B.
        unfold account_option_layout.
        go using AccountR_separated_fold_B.
        fold OriginalAccountStateR.
        wapply (reinsert_original_account_payload_only
          (this ,, o_field CU "monad::State::original_")
          _ orig_after addr old_loc old_state Horig_old eq_refl).
        go.
        iExists orig_after.
        go.
        match goal with
        | Hpost : state_original_account_state_post orig_after addr
            ?orig_final ?loc ?orig_state |- _ =>
            destruct (state_original_account_state_post_existing
              orig_after orig_final addr loc old_loc orig_state old_state
              Horig_old Hpost) as [Hmap [Hloc Hstate]];
            subst
        end.
        go using borrow_original_account_payload_F.
        wp_if.
        {
          intros Hge.
          go.
          iExists (preTxState old_state).
          unfold OriginalAccountStateR.
          go.
          rewrite Hacct.
          go using optional_specs.trivial_optional_some_split_F.
          unfold AccountR.
          go.
          fold AccountR.
          iExists acct.
          go using optional_specs.trivial_optional_some_split_F.
          unfold AccountR.
          go.
          fold AccountR.
          wp_if.
          {
            intros Hgt.
            rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ Hge ltac:(assumption)) in Hgt |- *.
            go.
            rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ (N.lt_le_incl _ _ Hgt)
              ltac:(assumption)).
            iExists old_state.
            wapply (OriginalAccountStateR_separated_fold
              (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
              1 old_state).
            rewrite Hacct.
            go using optionR_account_some_separated_fold_B.
            unfold account_option_layout.
            go using AccountR_separated_fold_B.
            unfold original_balance_pessimistic_model_assumed.
            rewrite Hacct.
            cbn [balanceOfAccount].
            change (acct .^ _balance) with (balance acct).
            match goal with
            | Hbal : balance acct = _ |- _ => rewrite Hbal
            end.
            go.
            iExists old_state, orig_after, old_loc.
            unfold check_min_balance_recent_account_model.
            rewrite Hcur.
            cbn [current_balance_pessimistic_model_stack recentAccountOf_stack].
            rewrite Hacct.
            unfold check_min_balance_update_model.
            rewrite (original_balance_pessimistic_model_map_lookup
              orig_after addr old_loc old_state Horig_old) Hacct.
            change (balanceOfAccount (Some acct)) with (balance acct).
            match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
            assert (Hok : check_min_balance_ok
              (w256_to_N (block.block_account_balance (coreAc acct))) value = true).
            { apply bool_decide_true. exact Hge. }
            unfold min_balance_update.
            rewrite Hok.
            rewrite (proj2 (N.ltb_lt _ _) Hgt).
            rewrite map_key_ptr_update_assum_exactness_at.
            go.
            fold OriginalAccountStateR.
            match goal with
            | |- context [update_assum_exactness_at addr ?f orig_after] =>
                wapply (reinsert_updated_original_account_payload_only
                  (this ,, o_field CU "monad::State::original_")
                  _ orig_after addr old_loc old_state f Horig_old eq_refl)
            end.
            go.
          }
          {
            intros Hnlt.
            rewrite (dippedlam_lemmas.u256_sub_mod_small _ _ Hge ltac:(assumption)) in Hnlt.
            wapply (OriginalAccountStateR_separated_fold
              (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
              1 old_state).
            rewrite Hacct.
            go using optionR_account_some_separated_fold_B.
            unfold account_option_layout.
            go using AccountR_separated_fold_B.
            iExists old_state, orig_after, old_loc.
            unfold check_min_balance_recent_account_model.
            rewrite Hcur.
            cbn [recentAccountOf_stack].
            rewrite Hacct.
            unfold check_min_balance_update_model.
            rewrite (original_balance_pessimistic_model_map_lookup
              orig_after addr old_loc old_state Horig_old) Hacct.
            change (balanceOfAccount (Some acct)) with (balance acct).
            match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
            assert (Hok : check_min_balance_ok
              (w256_to_N (block.block_account_balance (coreAc acct))) value = true).
            { apply bool_decide_true. exact Hge. }
            unfold min_balance_update.
            rewrite Hok (proj2 (N.ltb_ge
              (w256_to_N (block.block_account_balance (coreAc acct)) - value)
              (w256_to_N (block.block_account_balance (coreAc acct)))) ltac:(lia)).
            rewrite map_key_ptr_update_assum_exactness_at.
            go.
            fold OriginalAccountStateR.
            match goal with
            | |- context [update_assum_exactness_at addr ?f orig_after] =>
                assert (Hsame : update_assum_exactness_assumed f old_state = old_state);
                [ destruct old_state as [ac storage [bound nonce]];
                  destruct bound; reflexivity
                | wapply (reinsert_updated_original_account_payload_only
                    (this ,, o_field CU "monad::State::original_")
                    _ orig_after addr old_loc old_state f Horig_old eq_refl) ]
            end.
            rewrite Hsame.
            go.
          }
        }
        {
          intros Hlt.
          go.
          iExists old_state.
          go.
          iExists old_state, orig_after, old_loc.
          unfold check_min_balance_recent_account_model.
          rewrite Hcur.
          cbn [recentAccountOf_stack].
          rewrite Hacct.
          unfold check_min_balance_update_model.
          change (balanceOfAccount (Some acct)) with (balance acct).
          match goal with Hbal : balance acct = _ |- _ => rewrite Hbal end.
          assert (Hok : check_min_balance_ok
            (w256_to_N (block.block_account_balance (coreAc acct))) value = false).
          { apply bool_decide_false. lia. }
          unfold min_balance_update.
          rewrite Hok map_key_ptr_update_assum_exactness_at.
          go.
          wapply (reinsert_updated_original_account_payload_only
            (this ,, o_field CU "monad::State::original_")
            _ orig_after addr old_loc old_state exact_balance_update Horig_old eq_refl).
          go.
        }
      }
      {
        go.
        rewrite Z.mod_0_l; [| unfold uint64_word_modulus; lia].
        cbn [Z.to_N].
        wapply (OriginalAccountStateR_separated_fold
          (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
          1 old_state).
        rewrite Hacct.
        go.
        fold OriginalAccountStateR.
        wapply (reinsert_original_account_payload_only
          (this ,, o_field CU "monad::State::original_")
          _ orig_after addr old_loc old_state Horig_old eq_refl).
        go.
        iExists orig_after.
        go.
        match goal with
        | Hpost : state_original_account_state_post orig_after addr ?orig_final ?loc ?orig_state |- _ =>
            destruct (state_original_account_state_post_existing
              orig_after orig_final addr loc old_loc orig_state old_state Horig_old Hpost)
              as [Hmap [Hloc Hstate]]; subst
        end.
        go using borrow_original_account_payload_F.
        wp_if.
        {
          intros Hge.
          go.
          iExists (preTxState old_state).
          unfold OriginalAccountStateR.
          go.
          rewrite Hacct.
          go.
          iExists old_state, orig_after, old_loc.
          unfold check_min_balance_recent_account_model.
          rewrite Hcur Hacct.
          unfold check_min_balance_update_model.
          rewrite (original_balance_pessimistic_model_map_lookup
            orig_after addr old_loc old_state Horig_old) Hacct.
          cbn [balanceOfAccount].
          unfold min_balance_update.
          change (check_min_balance_ok 0 0) with true.
          cbn [N.sub N.ltb].
          rewrite map_key_ptr_update_assum_exactness_at.
          go.
          fold OriginalAccountStateR.
          match goal with
          | |- context [update_assum_exactness_at addr ?f orig_after] =>
              assert (Hsame : update_assum_exactness_assumed f old_state = old_state);
              [ destruct old_state as [ac storage [bound nonce]];
                destruct bound; reflexivity
              | wapply (reinsert_updated_original_account_payload_only
                  (this ,, o_field CU "monad::State::original_")
                  _ orig_after addr old_loc old_state f Horig_old eq_refl) ]
          end.
          rewrite Hsame.
          wapply (OriginalAccountStateR_separated_fold
            (old_loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
            1 old_state).
          rewrite Hacct.
          go.
        }
        {
          intros Hlt.
          go.
          iExists old_state.
          go.
          iExists old_state, orig_after, old_loc.
          unfold check_min_balance_recent_account_model.
          rewrite Hcur Hacct.
          unfold check_min_balance_update_model.
          cbn [balanceOfAccount].
          assert (Hok : check_min_balance_ok 0 value = false).
          { apply bool_decide_false. lia. }
          unfold min_balance_update.
          rewrite Hok map_key_ptr_update_assum_exactness_at.
          go.
          wapply (reinsert_updated_original_account_payload_only
            (this ,, o_field CU "monad::State::original_")
            _ orig_after addr old_loc old_state exact_balance_update Horig_old eq_refl).
          go.
        }
      }
    }
  Qed.
End with_Sigma.
