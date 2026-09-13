Require Import monad.proofs.misc.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.reservebal_specs.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.initialize.
Require Import skylabs.auto.cpp.hints.inline_invoke.
Require Import skylabs.auto.cpp.hints.invoke.
Require Import skylabs.auto.cpp.hints.ptrs.valid.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import stdpp.gmap.

Import exec_specs.
Import linearity.

Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Opaque Zdigits.binary_value Zdigits.Z_to_binary.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  Arguments pair_name/.
  Arguments pair_ty/.
  Arguments pairFstOffset/.
  Arguments pairSndOffset/.
  Arguments pairOffsets/.
  Arguments anker_pair_name/.
  Arguments anker_pair_ty/.
  Arguments anker_allocator_name/.
  Arguments anker_hash_name/.
  Arguments anker_equal_to_name/.
  Arguments anker_table_name/.
  Arguments anker_segvec_name/.
  Arguments anker_iter_name/.
  Arguments anker_iter_ty/.
  Arguments address_set_table_ty/.
  Arguments address_set_table_allocator_ty/.

  #[local] Instance learn_block_state_rfrag :
    AtLearnEq3 BlockState.Rfrag :=
    ltac:(solve_learnable).
  #[local] Instance learn_anker_payloads {K V} :
    LearnEq6 (@AnkerMapPayloadsR _ _ Sigma K V) :=
    ltac:(solve_learnable).
  #[local] Instance learn_original_account_state :
    LearnEq2 OriginalAccountStateR :=
    ltac:(solve_learnable).

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).

  Lemma map_snd_nil_inv {A B : Type} (elts : list (A * B)) :
    map snd elts = [] ->
    elts = [].
  Proof using.
    destruct elts; simpl; congruence.
  Qed.

  #[local] Hint Resolve map_snd_nil_inv : pure.

  Transparent StateDirtyStackR.

  Lemma borrow_empty_dirty_stack (p : ptr) (q : Qp) :
    p |-> StateDirtyStackR q []
    |--
    p |-> deque_specs.DequeR
            address_set_table_ty address_set_table_allocator_ty
            SenderAuthoritiesSetR q []
    ** (p |-> deque_specs.DequeR
            address_set_table_ty address_set_table_allocator_ty
            SenderAuthoritiesSetR q [] -*
        p |-> StateDirtyStackR q []).
  Proof using.
    go.
    unfold StateDirtyStackR.
    go.
  Qed.

  Definition borrow_empty_dirty_stack_F p q :=
    [FWD] (borrow_empty_dirty_stack p q).

  Opaque StateDirtyStackR.

  Definition current_map_model
      (addr : evmopsem.evm.address) (loc update_loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :=
    (addr, (loc, [(update_loc, initial_updated_account_state orig_state)])) :: cur.

  Lemma borrow_inserted_current_payload
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc update_loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (current_map_model addr loc update_loc orig_state cur)
    |--
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackR "monad::AccountState" UpdatedAccountStateR
              1 [(update_loc, initial_updated_account_state orig_state)]
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (removeKey
               (current_map_model addr loc update_loc orig_state cur) addr).
  Proof using CU MODd Sigma.
    rewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      (current_map_model addr loc update_loc orig_state cur)
      0%N
      (addr, (loc, [(update_loc, initial_updated_account_state orig_state)]))
      addr map_ptr
      eq_refl eq_refl).
    unfold pairR.
    go.
  Qed.

  Definition borrow_inserted_current_payload_F
      map_ptr cur addr loc update_loc orig_state :=
    [FWD] (borrow_inserted_current_payload
             map_ptr cur addr loc update_loc orig_state).

  Lemma reinsert_inserted_current_payload
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc update_loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackR "monad::AccountState" UpdatedAccountStateR
              1 [(update_loc, initial_updated_account_state orig_state)]
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (removeKey
               (current_map_model addr loc update_loc orig_state cur) addr)
    |--
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (current_map_model addr loc update_loc orig_state cur).
  Proof using CU MODd Sigma.
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      (current_map_model addr loc update_loc orig_state cur)
      0%N
      (addr, (loc, [(update_loc, initial_updated_account_state orig_state)]))
      addr map_ptr
      eq_refl eq_refl).
    unfold pairR.
    go.
  Qed.

  Definition reinsert_inserted_current_payload_B
      map_ptr cur addr loc update_loc orig_state :=
    [BWD] (reinsert_inserted_current_payload
             map_ptr cur addr loc update_loc orig_state).

  Lemma UpdatedAccountStateR_separated_fold
      (p : ptr) q upd :
    p |-> AccountStateRcore q (postTxState upd)
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR q (substateModel upd)
    |-- p |-> UpdatedAccountStateR q upd.
  Proof using CU MODd Sigma.
    go.
  Qed.

  Definition UpdatedAccountStateR_separated_fold_B p q upd :=
    [BWD] (UpdatedAccountStateR_separated_fold p q upd).

  Lemma current_spine_snd_map
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    map snd (map (fun '(a1, (b0, _)) => (a1, b0)) cur) =
    map (fun x => x.2.1) cur.
  Proof using.
    induction cur as [| [a [b updates]] tl IH]; simpl; [reflexivity |].
    now f_equal.
  Qed.

  Lemma current_spine_fst_map
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    map fst (map (fun '(a1, (b0, _)) => (a1, b0)) cur) =
    map fst cur.
  Proof using.
    induction cur as [| [a [b updates]] tl IH]; simpl; [reflexivity |].
    now f_equal.
  Qed.

  Lemma current_spine_not_elem
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address) :
    addr ∉ map fst cur ->
    addr ∉ map fst (map (fun '(a1, (b0, _)) => (a1, b0)) cur).
  Proof using.
    rewrite current_spine_fst_map.
    auto.
  Qed.

  Lemma current_spine_lengthN
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    lengthN (map (fun '(a1, (b0, _)) => (a1, b0)) cur) =
    lengthN cur.
  Proof using.
    rewrite lengthN_map.
    reflexivity.
  Qed.

  Lemma current_spine_lengthN_sym
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    lengthN cur =
    lengthN (map (fun '(a1, (b0, _)) => (a1, b0)) cur).
  Proof using.
    symmetry.
    apply current_spine_lengthN.
  Qed.

  Lemma current_spine_iterR_snd_map_at
      (p : ptr) (i : N)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    p |-> AnkerMapIterR
        "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m i
        (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) cur))
    |--
    p |-> AnkerMapIterR
        "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m i
        (map (fun x => x.2.1) cur).
  Proof using.
    rewrite current_spine_snd_map.
    go.
  Qed.

  Lemma current_spine_iterR_snd_map_rev_at
      (p : ptr) (i : N)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    p |-> AnkerMapIterR
        "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m i
        (map (fun x => x.2.1) cur)
    |--
    p |-> AnkerMapIterR
        "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m i
        (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) cur)).
  Proof using.
    rewrite current_spine_snd_map.
    go.
  Qed.

  Lemma current_spine_iterR_end_map_rev_at
      (p : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    p |-> AnkerMapIterR
        "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m
        (lengthN cur)
        (map (fun x => x.2.1) cur)
    |--
    p |-> AnkerMapIterR
        "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m
        (lengthN (map (fun '(a1, (b0, _)) => (a1, b0)) cur))
        (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) cur)).
  Proof using.
    rewrite current_spine_snd_map.
    rewrite current_spine_lengthN.
    go.
  Qed.

  Lemma current_find_index_not_end
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address) (i : N) :
    option_map fst
      (nth_error (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
        (N.to_nat i)) = Some addr ->
    i <> lengthN (map (fun '(a1, (b0, _)) => (a1, b0)) cur).
  Proof using.
    intros Hnth Heq.
    destruct (nth_error
      (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
      (N.to_nat i)) as [[addr' loc]|] eqn:Hnth_lookup.
    2: discriminate.
    simpl in Hnth.
    subst i.
    unfold lengthN in Hnth_lookup.
    rewrite Nat2N.id in Hnth_lookup.
    pose proof
      (proj2
        (nth_error_None
          (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
          (length (map (fun '(a1, (b0, _)) => (a1, b0)) cur)))
        (Nat.le_refl _)) as Hnone.
    rewrite Hnone in Hnth_lookup.
    discriminate.
  Qed.

  Lemma current_spine_lookup_ploc_exists
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address) (i : N) :
    option_map fst
      (nth_error (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
        (N.to_nat i)) = Some addr ->
    exists ploc,
      nth_error (map (fun x => x.2.1) cur) (N.to_nat i) = Some ploc.
  Proof using.
    intros Hnth_key.
    destruct (nth_error
      (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
      (N.to_nat i)) as [[addr' ploc]|] eqn:Hnth_spine.
    2: discriminate.
    exists ploc.
    rewrite <- current_spine_snd_map.
    rewrite nth_error_map.
    rewrite Hnth_spine.
    reflexivity.
  Qed.

  Lemma current_mapModelLookup_of_spine_lookup
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address) (i : N) (ploc : ptr) :
    NoDup (map fst (map (fun '(a1, (b0, _)) => (a1, b0)) cur)) ->
    option_map fst
      (nth_error (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
        (N.to_nat i)) = Some addr ->
    nth_error (map (fun x => x.2.1) cur) (N.to_nat i) = Some ploc ->
    exists updates,
      mapModelLookup cur addr = Some (ploc, updates).
  Proof using.
    intros Hnodup Hnth_key Hnth_ploc.
    destruct (nth_error cur (N.to_nat i))
      as [[addr' [loc' updates]]|] eqn:Hnth_cur.
    {
      rewrite nth_error_map Hnth_cur in Hnth_key.
      simpl in Hnth_key.
      injection Hnth_key as Haddr.
      rewrite nth_error_map Hnth_cur in Hnth_ploc.
      simpl in Hnth_ploc.
      injection Hnth_ploc as Hloc.
      subst addr' loc'.
      exists updates.
      unfold mapModelLookup.
      apply elem_of_list_to_map_1.
      {
        rewrite <- current_spine_fst_map.
        exact Hnodup.
      }
      eapply list_elem_of_lookup_2 with (i := N.to_nat i).
      rewrite lookup_nth_error.
      exact Hnth_cur.
    }
    {
      rewrite nth_error_map Hnth_cur in Hnth_key.
      discriminate.
    }
  Qed.

  Definition current_spine_iterR_snd_mapF :=
    [FWD] current_spine_iterR_snd_map_at.
  Definition current_spine_iterR_snd_mapB :=
    [BWD] current_spine_iterR_snd_map_rev_at.
  Definition current_spine_iterR_end_mapB :=
    [BWD] current_spine_iterR_end_map_rev_at.

  #[local] Hint Resolve
    current_spine_lengthN_sym
    current_spine_not_elem
    current_find_index_not_end
    current_spine_lookup_ploc_exists
    : pure.
  #[local] Hint Resolve
    current_spine_iterR_snd_mapF
    current_spine_iterR_snd_mapB
    current_spine_iterR_end_mapB
    : sl_opacity.

  #[local] Hint Rewrite
    current_spine_snd_map
    current_spine_fst_map
    current_spine_lengthN
    : syntactic.

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
    {
      destruct Hpost as [acct [-> ->]].
      unfold mapModelLookup.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_ | Hcontra].
      2:{ contradiction Hcontra; reflexivity. }
      reflexivity.
    }
  Qed.

  #[local] Hint Resolve state_original_account_state_post_lookup : pure.

  Lemma mapModelLookup_None_of_not_elem
      {V : Type} (m : MapModel evmopsem.evm.address V)
      (addr : evmopsem.evm.address) :
    addr ∉ map fst m ->
    mapModelLookup m addr = None.
  Proof using.
    intros Hnot_elem.
    unfold mapModelLookup.
    induction m as [| [a [loc st]] tl IH]; simpl in *.
    {
      rewrite lookup_empty.
      reflexivity.
    }
    {
      rewrite lookup_insert_ne.
      {
        apply IH.
        intros Hin.
        apply Hnot_elem.
        right.
        exact Hin.
      }
      intros Heq.
      subst a.
      apply Hnot_elem.
      left.
    }
  Qed.

  Lemma state_current_account_state_post_insert
      (st : StateM) (addr : evmopsem.evm.address)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    addr ∉ map fst (newStates st) ->
    state_original_account_state_post
      (preTxAssumedState st) addr orig_final orig_loc orig_state ->
    state_current_account_state_post st addr
      (state_with_preTxAssumedState_and_newStates st orig_final
        (current_map_model addr cur_loc upd_loc orig_state (newStates st)))
      upd_loc (initial_updated_account_state orig_state).
  Proof using.
    intros Hnot Horig.
    unfold state_current_account_state_post.
    rewrite (mapModelLookup_None_of_not_elem (newStates st) addr Hnot).
    exists orig_loc, orig_final, orig_state, cur_loc.
    repeat split; try assumption; try reflexivity.
  Qed.

  Lemma state_current_account_state_post_lookup
      (st : StateM) (addr : evmopsem.evm.address)
      (loc upd_loc : ptr) (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup (newStates st) addr = Some (loc, (upd_loc, upd) :: tl) ->
    state_current_account_state_post st addr st upd_loc upd.
  Proof using.
    intro Hlookup.
    unfold state_current_account_state_post.
    rewrite Hlookup.
    repeat split; reflexivity.
  Qed.

  Lemma current_lookup_nonempty_of_validModel
      (st : StateM) (addr : evmopsem.evm.address)
      (loc : ptr) (updates : list (ptr * UpdatedAccountState)) :
    validModel st ->
    mapModelLookup (newStates st) addr = Some (loc, updates) ->
    exists upd_loc upd tl, updates = (upd_loc, upd) :: tl.
  Proof using.
    intros Hvalid Hlookup.
    destruct updates as [| [upd_loc upd] tl].
    {
      pose proof (validModel_subset st Hvalid) as Hsub.
      assert (is_Some (mapModelLookup (preTxAssumedState st) addr))
        as [[orig_loc orig_state] Horig].
      {
        apply mapModelLookup_is_Some_of_mem.
        apply Hsub.
        apply mapModelLookup_is_Some_implies_mem.
        eexists.
        exact Hlookup.
      }
      pose proof
        (validModel_post_none_of_lookup
          st addr loc [] orig_loc orig_state Hvalid Hlookup Horig) as Hfalse.
      contradiction.
    }
    {
      exists upd_loc, upd, tl.
      reflexivity.
    }
  Qed.

  #[local] Hint Resolve
    mapModelLookup_None_of_not_elem
    state_current_account_state_post_insert
    state_current_account_state_post_lookup
    : pure.

  Lemma validModel_current_account_state_insert
      (st : StateM) (addr : evmopsem.evm.address)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    validModel st ->
    addr ∉ map fst (newStates st) ->
    state_original_account_state_post
      (preTxAssumedState st) addr orig_final orig_loc orig_state ->
    validModel
      (state_with_preTxAssumedState_and_newStates st orig_final
        (current_map_model addr cur_loc upd_loc orig_state (newStates st))).
  Proof using.
  Admitted.

  Lemma stateCodeMapInvariants_current_account_state_insert
      (st : StateM) (addr : evmopsem.evm.address)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    stateCodeMapInvariants st ->
    state_original_account_state_post
      (preTxAssumedState st) addr orig_final orig_loc orig_state ->
    stateCodeMapInvariants
      (state_with_preTxAssumedState_and_newStates st orig_final
        (current_map_model addr cur_loc upd_loc orig_state (newStates st))).
  Proof using.
  Admitted.

  #[local] Hint Resolve
    validModel_current_account_state_insert
    stateCodeMapInvariants_current_account_state_insert
    : pure.

  Lemma StateCodeMapR_current_account_state_insert
      (this : ptr) (st : StateM) (addr : evmopsem.evm.address)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    state_original_account_state_post
      (preTxAssumedState st) addr orig_final orig_loc orig_state ->
    this |-> StateCodeMapR st
    |--
    this |-> StateCodeMapR
      (state_with_preTxAssumedState_and_newStates st orig_final
        (current_map_model addr cur_loc upd_loc orig_state (newStates st))).
  Proof using CU MODd Sigma.
    intro Horig.
    go.
    unfold StateCodeMapR.
    go.
  Qed.

  Definition StateCodeMapR_current_account_state_insert_B
      this st addr orig_final orig_loc cur_loc upd_loc orig_state Horig :=
    [BWD] (StateCodeMapR_current_account_state_insert
             this st addr orig_final orig_loc cur_loc upd_loc orig_state Horig).

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
      nth_error orig (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, orig_state))).
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

  Lemma reinsert_original_account_payload
      (map_ptr : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState"
         |-> OriginalAccountStateR 1 orig_state
    ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    |--
    map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 orig.
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
      nth_error orig (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, orig_state))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address AssumedPreTxAccountState _
      "monad::Address" "monad::OriginalAccountState"
      addressR OriginalAccountStateR
      orig (N.of_nat i) (addr, (loc, orig_state)) addr map_ptr
      Hnth_N eq_refl).
    unfold pairR.
    go.
  Qed.

  Definition reinsert_original_account_payload_B
      map_ptr orig addr loc orig_state Hlookup :=
    [BWD] (reinsert_original_account_payload
             map_ptr orig addr loc orig_state Hlookup).

  Lemma borrow_current_payload
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (updates : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, updates) ->
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 cur
    |--
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackR "monad::AccountState" UpdatedAccountStateR
              1 updates
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (removeKey cur addr).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, updates)) ∈ cur).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_N :
      nth_error cur (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, updates))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    rewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      cur (N.of_nat i) (addr, (loc, updates)) addr map_ptr
      Hnth_N eq_refl).
    unfold pairR.
    go.
  Qed.

  Definition borrow_current_payload_F
      map_ptr cur addr loc updates Hlookup :=
    [FWD] (borrow_current_payload
             map_ptr cur addr loc updates Hlookup).

  Lemma reinsert_current_head_payload
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** upd_loc |-> UpdatedAccountStateR 1 upd
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (removeKey cur addr)
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

  Lemma current_spine_map_replace_current_account_update_direct
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    map (fun '(a, (b, _)) => (a, b))
      (replace_current_account_update addr upd_final cur) =
    map (fun '(a, (b, _)) => (a, b)) cur.
  Proof using.
    unfold replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    {
      destruct (asbool (a = addr)); simpl; rewrite IH; reflexivity.
    }
  Qed.

  Lemma CurrentSpineR_replace_current_account_update_direct
      (p : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    p |-> AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR 1
          (map (fun '(a, (b, _)) => (a, b)) cur)
    |--
    p |-> AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR 1
          (map (fun '(a, (b, _)) => (a, b))
             (replace_current_account_update addr upd_final cur)).
  Proof using CU MODd Sigma.
    rewrite current_spine_map_replace_current_account_update_direct.
    go.
  Qed.

  Lemma removeKey_replace_current_account_update_direct
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    removeKey (replace_current_account_update addr upd_final cur) addr =
    removeKey cur addr.
  Proof using.
    unfold removeKey, replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    destruct (decide (a = addr)) as [-> | Ha].
    {
      rewrite (bool_decide_eq_true_2 (addr = addr)); [| reflexivity].
      rewrite (bool_decide_eq_false_2 (addr <> addr)); [| tauto].
      exact IH.
    }
    {
      rewrite (bool_decide_eq_false_2 (a = addr)); [| exact Ha].
      rewrite (bool_decide_eq_true_2 (a <> addr)); [| exact Ha].
      simpl.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma filter_removeKey_notin
      {V : Type}
      (cur : MapModel evmopsem.evm.address V)
      (addr : evmopsem.evm.address) :
    addr ∉ map fst cur ->
    List.filter (fun p => bool_decide (p.1 <> addr)) cur = cur.
  Proof using.
    induction cur as [| [a v] cur IH]; simpl.
    {
      reflexivity.
    }
    intros Hnotin.
    apply not_elem_of_cons in Hnotin as [Ha Hnotin].
    rewrite bool_decide_true.
    2:{
      intro Heq.
      apply Ha.
      subst a.
      reflexivity.
    }
    simpl.
    rewrite IH; [reflexivity | exact Hnotin].
  Qed.

  Lemma filter_current_payload_notin
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address) :
    addr ∉ map fst cur ->
    List.filter (fun p => bool_decide (p.1 <> addr)) cur = cur.
  Proof using.
    exact (filter_removeKey_notin cur addr).
  Qed.

  Lemma replace_current_account_update_notin_body
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    addr ∉ map fst cur ->
    map
      (fun '(a, (loc, updates)) =>
         if bool_decide (a = addr)
         then (a, (loc, replace_current_head_update upd_final updates))
         else (a, (loc, updates))) cur = cur.
  Proof using.
    unfold replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    intros Hnotin.
    apply not_elem_of_cons in Hnotin as [Ha Hnotin].
    rewrite bool_decide_false.
    2:{
      intro Heq.
      apply Ha.
      subst a.
      reflexivity.
    }
    simpl.
    rewrite IH; [reflexivity | exact Hnotin].
  Qed.

  Lemma nth_error_replace_current_account_update_direct
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState)
      (i : nat) (loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    nth_error cur i = Some (addr, (loc, (upd_loc, upd) :: tl)) ->
    nth_error (replace_current_account_update addr upd_final cur) i =
      Some (addr, (loc, (upd_loc, upd_final) :: tl)).
  Proof using.
    revert i.
    induction cur as [| [a [loc0 updates0]] cur IH]; intros [| i] Hnth;
      simpl in *; try discriminate.
    {
      destruct (bool_decide (a = addr)) eqn:Ha.
      {
        apply bool_decide_eq_true in Ha.
        subst a.
        destruct updates0 as [| [upd_loc0 upd0] tl0]; simpl in *;
          inversion Hnth; subst.
        reflexivity.
      }
      {
        apply bool_decide_eq_false in Ha.
        inversion Hnth; subst.
        contradiction.
      }
    }
    {
      exact (IH i Hnth).
    }
  Qed.

  Lemma reinsert_updated_current_head_payload_direct
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd upd_final : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** upd_loc |-> UpdatedAccountStateR 1 upd_final
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (removeKey cur addr)
    |--
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (replace_current_account_update addr upd_final cur).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, (upd_loc, upd) :: tl)) ∈ cur).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_final :
      nth_error (replace_current_account_update addr upd_final cur)
        (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, (upd_loc, upd_final) :: tl))).
    {
      rewrite Nat2N.id.
      eapply nth_error_replace_current_account_update_direct.
      exact Hnth.
    }
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      (replace_current_account_update addr upd_final cur) (N.of_nat i)
      (addr, (loc, (upd_loc, upd_final) :: tl)) addr map_ptr
      Hnth_final eq_refl).
    rewrite removeKey_replace_current_account_update_direct.
    unfold pairR, VersionStackR.
    simpl.
    go.
  Qed.

  Definition reinsert_updated_current_head_payload_direct_B
      map_ptr cur addr loc upd_loc upd upd_final tl Hlookup :=
    [BWD] (reinsert_updated_current_head_payload_direct
             map_ptr cur addr loc upd_loc upd upd_final tl Hlookup).

  Lemma reinsert_updated_inserted_current_payload
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd_final : UpdatedAccountState) :
    addr ∉ map fst cur ->
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1 [upd_loc]
    ** upd_loc |-> UpdatedAccountStateR 1 upd_final
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 cur
    |--
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 ((addr, (loc, [(upd_loc, upd_final)])) :: cur).
  Proof using CU MODd Sigma.
    intro Hnotin.
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      ((addr, (loc, [(upd_loc, upd_final)])) :: cur) 0%N
      (addr, (loc, [(upd_loc, upd_final)])) addr map_ptr
      eq_refl eq_refl).
    unfold removeKey at 1.
    simpl.
    rewrite (bool_decide_eq_false_2 (addr <> addr)); [| tauto].
    rewrite (filter_removeKey_notin cur addr Hnotin).
    unfold pairR, VersionStackR.
    simpl.
    go.
  Qed.

  Definition reinsert_updated_inserted_current_payload_B
      map_ptr cur addr loc upd_loc upd_final Hnotin :=
    [BWD] (reinsert_updated_inserted_current_payload
             map_ptr cur addr loc upd_loc upd_final Hnotin).

  Lemma mapModelLookup_current_map_model
      (addr : evmopsem.evm.address) (loc update_loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    addr ∉ map fst cur ->
    mapModelLookup (current_map_model addr loc update_loc orig_state cur) addr =
      Some (loc, [(update_loc, initial_updated_account_state orig_state)]).
  Proof using.
    intro Hnot.
    unfold current_map_model, mapModelLookup.
    rewrite lookup_insert.
    cbn.
    destruct (decide (addr = addr)) as [_ | Hcontra].
    2:{ contradiction Hcontra; reflexivity. }
    reflexivity.
  Qed.

  Lemma validModel_current_account_state_update_insert
      (st : StateM) (addr : evmopsem.evm.address)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (upd_final : UpdatedAccountState) :
    validModel st ->
    addr ∉ map fst (newStates st) ->
    state_original_account_state_post
      (preTxAssumedState st) addr orig_final orig_loc orig_state ->
    validModel
      (state_update_current_account
        (state_with_preTxAssumedState_and_newStates st orig_final
          (current_map_model addr cur_loc upd_loc orig_state (newStates st)))
        addr upd_final).
  Proof using.
  Admitted.

  Lemma validModel_current_account_state_update_lookup
      (st : StateM) (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd upd_final : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    validModel st ->
    mapModelLookup (newStates st) addr = Some (loc, (upd_loc, upd) :: tl) ->
    validModel (state_update_current_account st addr upd_final).
  Proof using.
  Admitted.

  Lemma stateCodeMapInvariants_current_account_state_update_insert
      (st : StateM) (addr : evmopsem.evm.address)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (upd_final : UpdatedAccountState) :
    stateCodeMapInvariants st ->
    addr ∉ map fst (newStates st) ->
    state_original_account_state_post
      (preTxAssumedState st) addr orig_final orig_loc orig_state ->
    stateCodeMapInvariants
      (state_update_current_account
        (state_with_preTxAssumedState_and_newStates st orig_final
          (current_map_model addr cur_loc upd_loc orig_state (newStates st)))
        addr upd_final).
  Proof using.
  Admitted.

  Lemma stateCodeMapInvariants_current_account_state_update_lookup
      (st : StateM) (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd upd_final : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    stateCodeMapInvariants st ->
    mapModelLookup (newStates st) addr = Some (loc, (upd_loc, upd) :: tl) ->
    stateCodeMapInvariants (state_update_current_account st addr upd_final).
  Proof using.
  Admitted.

  #[local] Hint Resolve
    mapModelLookup_current_map_model
    validModel_current_account_state_update_insert
    validModel_current_account_state_update_lookup
    stateCodeMapInvariants_current_account_state_update_insert
    stateCodeMapInvariants_current_account_state_update_lookup
    : pure.

  #[local] Hint Rewrite
    filter_current_payload_notin
    replace_current_account_update_notin_body
    using solve [eauto with pure]
    : syntactic.

  Lemma StateCodeMapR_current_account_state_update_insert
      (this : ptr) (st : StateM) (addr : evmopsem.evm.address)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (upd_final : UpdatedAccountState) :
    addr ∉ map fst (newStates st) ->
    state_original_account_state_post
      (preTxAssumedState st) addr orig_final orig_loc orig_state ->
    this |-> StateCodeMapR st
    |--
    this |-> StateCodeMapR
      (state_update_current_account
        (state_with_preTxAssumedState_and_newStates st orig_final
          (current_map_model addr cur_loc upd_loc orig_state (newStates st)))
        addr upd_final).
  Proof using CU MODd Sigma.
    intros Hnot Horig.
    unfold StateCodeMapR.
    go.
  Qed.

  Definition StateCodeMapR_current_account_state_update_insert_B
      this st addr orig_final orig_loc cur_loc upd_loc orig_state
      upd_final Hnot Horig :=
    [BWD] (StateCodeMapR_current_account_state_update_insert
             this st addr orig_final orig_loc cur_loc upd_loc orig_state
             upd_final Hnot Horig).

  Lemma StateCodeMapR_current_account_state_update_lookup
      (this : ptr) (st : StateM) (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd upd_final : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup (newStates st) addr = Some (loc, (upd_loc, upd) :: tl) ->
    this |-> StateCodeMapR st
    |--
    this |-> StateCodeMapR
      (state_update_current_account st addr upd_final).
  Proof using CU MODd Sigma.
    intro Hlookup.
    unfold StateCodeMapR.
    go.
  Qed.

  Definition StateCodeMapR_current_account_state_update_lookup_B
      this st addr loc upd_loc upd upd_final tl Hlookup :=
    [BWD] (StateCodeMapR_current_account_state_update_lookup
             this st addr loc upd_loc upd upd_final tl Hlookup).

  Definition current_try_emplace_spec :=
    let key_ty : type := "monad::Address"%cpp_type in
    let value_ty : type := "monad::VersionStack<monad::AccountState>"%cpp_type in
    let orig_ty : type := "monad::OriginalAccountState"%cpp_type in
    let pair_ty := anker_table_try_emplace_result_ty key_ty value_ty in
    let args := [Tref (Tconst key_ty); Tref (Tconst orig_ty); Tref Tuint] in
    templated_method
      (Ninst
        (Nscoped (anker_table_name key_ty value_ty)
          (Nfunction function_qualifiers.N "try_emplace" args))
        [Apack [Atype (Tref (Tconst orig_ty)); Atype (Tref Tuint)];
         Atype value_ty;
         Avalue (Eint 1 Tbool)])
      (anker_table_name key_ty value_ty) function_qualifiers.N pair_ty args $
      \this this
      \arg{keyp : ptr} "key" (Vref keyp)
      \arg{origp : ptr} "args" (Vref origp)
      \arg{versionp : ptr} "args" (Vref versionp)
      \prepost{qaddr addr} keyp |-> addressR qaddr addr
      \prepost{orig_state}
        origp |-> OriginalAccountStateR 1 orig_state
      \prepost versionp |-> uintR 1$m 0
      \pre{cur}
        this |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 cur
      \pre
        this |-> AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR 1
          (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
      \pre
        [| addr ∉
           map fst
             (map (fun '(a1, (b0, _)) => (a1, b0)) cur) |]
      \post{retp loc update_loc : ptr} [Vptr retp]
        let cur_final := current_map_model addr loc update_loc orig_state cur in
        retp |-> anker_table_try_emplace_resultR
          key_ty value_ty
          (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) cur_final))
          true
        ** this |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 cur_final
        ** this |-> AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR 1
          (map (fun '(a1, (b0, _)) => (a1, b0)) cur_final).

  Definition SpecFor_current_try_emplace :=
    RegisterSpec current_try_emplace_spec.
  #[local] Existing Instance SpecFor_current_try_emplace.

  Lemma state_current_account_state_proof :
    verify[state_cpp.source] state_current_account_state_update_spec.
  Proof using MODd.
    verify_spec.
    go.
    autorewrite with syntactic.
    destruct t; simpl; autorewrite with syntactic.
    {
      go using
        borrow_original_account_payload_F,
        reinsert_original_account_payload_B,
        borrow_empty_dirty_stack_F,
        type_ptr_reference_to_B_local,
        anker_iter_keep_type_ptr_C,
        current_spine_iterR_end_mapB,
        observeAnkerMapSpineTypePtrF,
        observeAnkerMapSpineTypePtrRF,
        observeAnkerIterFf,
        observeAnkerIterRFf,
        observeAnkerIterConstRFf,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C,
        wp_initialize_unfold_B,
        wp_init_mcall_minvoke_B,
        wp_minvoke_direct_I_inline_C,
        wp_minvoke_direct_I_unmaterialized_C,
        wp_init_cast_noop_B.
      unfold current_map_model.
      iExists
        (AnkerMapIterR
           "monad::Address"
           "monad::VersionStack<monad::AccountState>" false 1$m
           0 (_x_6 ::
              map snd (map (fun '(a1, (b0, _)) => (a1, b0))
                         (newStates st)))),
        (boolR 1$m true).
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m
            0 (?ploc :: ?spine)] =>
          rewrite (anker_iter_keep_type_ptr
            iterp "monad::Address" "monad::VersionStack<monad::AccountState>"
            false 0 (ploc :: spine));
          rewrite (anker_iter_head_keep_pointee_type_ptr
            iterp ploc "monad::Address"
            "monad::VersionStack<monad::AccountState>" spine);
          rewrite (anker_iter_head_keep_pointee_value_field_type_ptr
            iterp ploc "monad::Address"
            "monad::VersionStack<monad::AccountState>" spine)
      end.
      go using
        borrow_empty_dirty_stack_F,
        type_ptr_reference_to_B_local,
        observeAnkerIterPointeeF,
        observeAnkerIterPointeeValueFieldF,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C,
        wp_initialize_unfold_B,
        wp_init_mcall_minvoke_B,
        wp_minvoke_direct_I_inline_C,
        wp_minvoke_direct_I_unmaterialized_C,
        wp_init_cast_noop_B.
      iExists (list EvmAddr), SenderAuthoritiesSetR, 1%Qp.
      iExists ([] : list (ptr * list EvmAddr)).
      go using
        borrow_inserted_current_payload_F,
        reinsert_inserted_current_payload_B,
        reinsert_original_account_payload_B,
        observeAnkerIterPointeeF.
      iExists (initial_updated_account_state t).
      iExists ([] : list (ptr * UpdatedAccountState)).
      go using
        UpdatedAccountStateR_separated_fold_B,
        reinsert_inserted_current_payload_B,
        reinsert_original_account_payload_B.
      iExists
        (state_with_preTxAssumedState_and_newStates st _t_0
          (current_map_model addr _x_6 _x_7 t (newStates st))).
      iExists (initial_updated_account_state t).
      go using
        UpdatedAccountStateR_separated_fold_B,
        reinsert_updated_inserted_current_payload_B,
        reinsert_original_account_payload_B,
        StateCodeMapR_current_account_state_update_insert_B;
      repeat (rewrite (bool_decide_eq_false_2 (addr <> addr)); [| tauto]);
      repeat (rewrite (bool_decide_eq_true_2 (addr = addr)); [| reflexivity]);
      autorewrite with syntactic;
      go using reinsert_updated_inserted_current_payload_B.
    }
    {
      go using
        type_ptr_reference_to_B_local,
        anker_iter_keep_type_ptr_C,
        anker_iter_keep_const_type_ptr_C,
        anker_map_spine_keep_type_ptr_C,
        current_spine_iterR_snd_mapB,
        observeAnkerMapSpineTypePtrF,
        observeAnkerMapSpineTypePtrRF,
        observeAnkerIterFf,
        observeAnkerIterRFf,
        observeAnkerIterConstFf,
        observeAnkerIterConstRFf,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C,
        wp_initialize_unfold_B,
        wp_init_mcall_minvoke_B,
        wp_minvoke_direct_I_inline_C,
        wp_minvoke_direct_I_unmaterialized_C,
        wp_init_cast_noop_B.
      destruct (current_spine_lookup_ploc_exists (newStates st) addr i)
        as [cur_loc Hcur_loc].
      {
        assumption.
      }
      destruct (current_mapModelLookup_of_spine_lookup
        (newStates st) addr i cur_loc) as [updates Hlookup].
      {
        assumption.
      }
      {
        assumption.
      }
      {
        exact Hcur_loc.
      }
      destruct (current_lookup_nonempty_of_validModel
        st addr cur_loc updates) as [upd_loc [upd [tl Hupdates]]].
      {
        assumption.
      }
      {
        exact Hlookup.
      }
      subst updates.
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m
            i ?spine] =>
          rewrite (anker_iter_keep_type_ptr
            iterp "monad::Address" "monad::VersionStack<monad::AccountState>"
            false i spine)
      end.
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::VersionStack<monad::AccountState>" false 1$m
            i ?spine] =>
          rewrite (anker_iter_keep_pointee_type_ptr
            iterp cur_loc
            "monad::Address" "monad::VersionStack<monad::AccountState>"
            i spine Hcur_loc)
      end.
      go using
        borrow_current_payload_F,
        borrow_empty_dirty_stack_F,
        observeAnkerIterPointeeF,
        type_ptr_reference_to_B_local,
        anker_iter_keep_type_ptr_C,
        anker_iter_keep_const_type_ptr_C,
        anker_map_spine_keep_type_ptr_C,
        observeAnkerMapSpineTypePtrF,
        observeAnkerMapSpineTypePtrRF,
        observeAnkerIterFf,
        observeAnkerIterRFf,
        observeAnkerIterConstFf,
        observeAnkerIterConstRFf,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C,
        wp_initialize_unfold_B,
        wp_init_mcall_minvoke_B,
        wp_minvoke_direct_I_inline_C,
        wp_minvoke_direct_I_unmaterialized_C,
        wp_init_cast_noop_B.
      iExists (list EvmAddr), SenderAuthoritiesSetR, 1%Qp.
      iExists ([] : list (ptr * list EvmAddr)).
      go using
        type_ptr_reference_to_B_local,
        observeVersionStackSpineTypePtrF,
        version_stack_spine_keep_type_ptr_C,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C,
        wp_lval_mcall_minvoke_B,
        wp_minvoke_direct_GL_unmaterialized_C,
        UpdatedAccountStateR_separated_fold_B.
      iExists upd.
      iExists tl.
      go using
        UpdatedAccountStateR_separated_fold_B.
      iExists st.
      iExists upd.
      go using
        UpdatedAccountStateR_separated_fold_B,
        reinsert_updated_current_head_payload_direct_B,
        StateCodeMapR_current_account_state_update_lookup_B;
      try rewrite current_spine_map_replace_current_account_update_direct;
      go.
    }
  Qed.
End with_Sigma.
