Require Import monad.proofs.misc.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.const_specs.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.initialize.
Require Import skylabs.auto.cpp.hints.inline_invoke.
Require Import skylabs.auto.cpp.hints.invoke.
Require Import skylabs.auto.cpp.hints.ptrs.valid.
Require Import skylabs.auto.cpp.tactics4.

Import exec_specs.
Import linearity.

Set Default Goal Selector "!".

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

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

  #[local] Instance learn_anker_payloads {K V} :
    LearnEq6 (@AnkerMapPayloadsR _ _ Sigma K V) :=
    ltac:(solve_learnable).
  #[local] Instance learn_block_state_rfrag :
    AtLearnEq3 BlockState.Rfrag :=
    ltac:(solve_learnable).

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).

  Lemma original_spine_snd_map
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :
    map snd (map (fun '(a1, (b0, _)) => (a1, b0)) orig) =
    map (fun x => x.2.1) orig.
  Proof using.
    induction orig as [| [a [b aps]] tl IH]; simpl; [reflexivity |].
    now f_equal.
  Qed.

  Lemma original_spine_fst_map
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :
    map fst (map (fun '(a1, (b0, _)) => (a1, b0)) orig) =
    map fst orig.
  Proof using.
    induction orig as [| [a [b aps]] tl IH]; simpl; [reflexivity |].
    now f_equal.
  Qed.

  Lemma original_spine_not_elem
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) :
    addr ∉ map fst orig ->
    addr ∉ map fst (map (fun '(a1, (b0, _)) => (a1, b0)) orig).
  Proof using.
    rewrite original_spine_fst_map.
    auto.
  Qed.

  Lemma original_spine_lengthN
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :
    lengthN (map (fun '(a1, (b0, _)) => (a1, b0)) orig) =
    lengthN orig.
  Proof using.
    rewrite lengthN_map.
    reflexivity.
  Qed.

  Lemma original_spine_lengthN_sym
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :
    lengthN orig =
    lengthN (map (fun '(a1, (b0, _)) => (a1, b0)) orig).
  Proof using.
    symmetry.
    apply original_spine_lengthN.
  Qed.

  Lemma original_spine_iterR_snd_map
      (p : ptr) (i : N)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :
    p |-> AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m i
        (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) orig)) =
    p |-> AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m i
        (map (fun x => x.2.1) orig).
  Proof using.
    rewrite original_spine_snd_map.
    reflexivity.
  Qed.

  Lemma original_spine_iterR_snd_map_at
      (p : ptr) (i : N)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :
    p |-> AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m i
        (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) orig))
    |--
    p |-> AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m i
        (map (fun x => x.2.1) orig).
  Proof using.
    rewrite original_spine_snd_map.
    go.
  Qed.

  Lemma original_spine_iterR_snd_map_rev_at
      (p : ptr) (i : N)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :
    p |-> AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m i
        (map (fun x => x.2.1) orig)
    |--
    p |-> AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m i
        (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) orig)).
  Proof using.
    rewrite original_spine_snd_map.
    go.
  Qed.

  Lemma original_spine_iterR_end_map_rev_at
      (p : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :
    p |-> AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m
        (lengthN orig)
        (map (fun x => x.2.1) orig)
    |--
    p |-> AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m
        (lengthN (map (fun '(a1, (b0, _)) => (a1, b0)) orig))
        (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) orig)).
  Proof using.
    rewrite original_spine_snd_map.
    rewrite original_spine_lengthN.
    go.
  Qed.

  Lemma original_find_index_not_end
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (i : N) :
    option_map fst
      (nth_error (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
        (N.to_nat i)) = Some addr ->
    i <> lengthN (map (fun '(a1, (b0, _)) => (a1, b0)) orig).
  Proof using.
    intros Hnth Heq.
    destruct (nth_error
      (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
      (N.to_nat i)) as [[addr' loc]|] eqn:Hnth_lookup.
    2: discriminate.
    simpl in Hnth.
    subst i.
    unfold lengthN in Hnth_lookup.
    rewrite Nat2N.id in Hnth_lookup.
    pose proof
      (proj2
        (nth_error_None
          (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
          (length (map (fun '(a1, (b0, _)) => (a1, b0)) orig)))
        (Nat.le_refl _)) as Hnone.
    rewrite Hnone in Hnth_lookup.
    discriminate.
  Qed.

  Lemma original_spine_lookup_ploc_exists
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (i : N) :
    option_map fst
      (nth_error (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
        (N.to_nat i)) = Some addr ->
    exists ploc,
      nth_error (map (fun x => x.2.1) orig) (N.to_nat i) = Some ploc.
  Proof using.
    intros Hnth_key.
    destruct (nth_error
      (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
      (N.to_nat i)) as [[addr' ploc]|] eqn:Hnth_spine.
    2: discriminate.
    exists ploc.
    rewrite <- original_spine_snd_map.
    rewrite nth_error_map.
    rewrite Hnth_spine.
    reflexivity.
  Qed.

  Lemma original_mapModelLookup_of_spine_lookup
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (i : N) (ploc : ptr) :
    NoDup (map fst (map (fun '(a1, (b0, _)) => (a1, b0)) orig)) ->
    option_map fst
      (nth_error (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
        (N.to_nat i)) = Some addr ->
    nth_error (map (fun x => x.2.1) orig) (N.to_nat i) = Some ploc ->
    exists orig_state,
      mapModelLookup orig addr = Some (ploc, orig_state).
  Proof using.
    intros Hnodup Hnth_key Hnth_ploc.
    destruct (nth_error orig (N.to_nat i))
      as [[addr' [loc' orig_state]]|] eqn:Hnth_orig.
    {
      rewrite nth_error_map Hnth_orig in Hnth_key.
      simpl in Hnth_key.
      injection Hnth_key as Haddr.
      rewrite nth_error_map Hnth_orig in Hnth_ploc.
      simpl in Hnth_ploc.
      injection Hnth_ploc as Hloc.
      subst addr' loc'.
      exists orig_state.
      unfold mapModelLookup.
      apply elem_of_list_to_map_1.
      {
        rewrite <- original_spine_fst_map.
        exact Hnodup.
      }
      eapply list_elem_of_lookup_2 with (i := N.to_nat i).
      rewrite lookup_nth_error.
      exact Hnth_orig.
    }
    {
      rewrite nth_error_map Hnth_orig in Hnth_key.
      discriminate.
    }
  Qed.

  Lemma mapModelLookup_None_of_not_elem
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) :
    addr ∉ map fst orig ->
    mapModelLookup orig addr = None.
  Proof using.
    intros Hnot_elem.
    unfold mapModelLookup.
    induction orig as [| [a [loc st]] tl IH]; simpl in *.
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

  Definition original_spine_iterR_snd_mapF :=
    [FWD->] original_spine_iterR_snd_map_at.
  Definition original_spine_iterR_snd_mapB :=
    [BWD] original_spine_iterR_snd_map_rev_at.
  Definition original_spine_iterR_end_mapB :=
    [BWD] original_spine_iterR_end_map_rev_at.

  #[local] Hint Resolve
    original_spine_lengthN_sym
    original_spine_not_elem
    original_find_index_not_end
    original_spine_lookup_ploc_exists
    mapModelLookup_None_of_not_elem
    : pure.
  #[local] Hint Resolve
    original_spine_iterR_snd_mapF
    original_spine_iterR_snd_mapB
    original_spine_iterR_end_mapB
    : sl_opacity.

  #[local] Hint Rewrite
    original_spine_snd_map
    original_spine_fst_map
    original_spine_lengthN
    original_spine_iterR_snd_map
    : syntactic.

  Definition original_map_model
      (addr : evmopsem.evm.address) (loc : ptr)
      (acct : option AccountM)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState) :=
    (addr, (loc, initial_original_account_state acct)) :: orig.

  Lemma state_original_account_state_post_insert
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (loc : ptr) (acct : option AccountM) :
    addr ∉ map fst orig ->
    state_original_account_state_post orig addr
      (original_map_model addr loc acct orig) loc
      (initial_original_account_state acct).
  Proof using.
    intros Hnot.
    unfold state_original_account_state_post, original_map_model.
    rewrite (mapModelLookup_None_of_not_elem orig addr Hnot).
    exists acct.
    split; reflexivity.
  Qed.

  #[local] Hint Resolve state_original_account_state_post_insert : pure.

  Definition original_try_emplace_spec :=
    let key_ty : type := "monad::Address"%cpp_type in
    let value_ty : type := "monad::OriginalAccountState"%cpp_type in
    let account_opt_ty :=
      Tnamed ("std::optional".<< Atype "monad::Account" >>) in
    let pair_ty := anker_table_try_emplace_result_ty key_ty value_ty in
    let args := [Tref (Tconst key_ty); Tref (Tconst account_opt_ty)] in
    templated_method
      (Ninst
        (Nscoped (anker_table_name key_ty value_ty)
          (Nfunction function_qualifiers.N "try_emplace" args))
        [Apack [Atype (Tref (Tconst account_opt_ty))];
         Atype value_ty;
         Avalue (Eint 1 Tbool)])
      (anker_table_name key_ty value_ty) function_qualifiers.N pair_ty args $
      \this this
      \arg{keyp : ptr} "key" (Vref keyp)
      \arg{accountp : ptr} "args" (Vref accountp)
      \prepost{qaddr addr} keyp |-> addressR qaddr addr
      \prepost{(qacct : cQp.t) acct}
        accountp |-> optional_specs.optionR
          "monad::Account" AccountR qacct acct
      \pre{orig}
        this |-> AnkerMapPayloadsR
          "monad::Address" "monad::OriginalAccountState"
          addressR OriginalAccountStateR 1 orig
      \pre
        this |-> AnkerMapSpineR
          "monad::Address" "monad::OriginalAccountState"
          addressToN addressR 1
          (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
      \pre
        [| addr ∉
           map fst
             (map (fun '(a1, (b0, _)) => (a1, b0)) orig) |]
      \post{retp loc : ptr} [Vptr retp]
        let orig_final := original_map_model addr loc acct orig in
        retp |-> anker_table_try_emplace_resultR
          key_ty value_ty
          (map snd (map (fun '(a1, (b0, _)) => (a1, b0)) orig_final))
          true
        ** this |-> AnkerMapPayloadsR
          "monad::Address" "monad::OriginalAccountState"
          addressR OriginalAccountStateR 1 orig_final
        ** this |-> AnkerMapSpineR
          "monad::Address" "monad::OriginalAccountState"
          addressToN addressR 1
          (map (fun '(a1, (b0, _)) => (a1, b0)) orig_final).

  Definition SpecFor_original_try_emplace :=
    RegisterSpec original_try_emplace_spec.
  #[local] Existing Instance SpecFor_original_try_emplace.

  Lemma state_original_account_state_proof :
    verify[state_cpp.source] state_original_account_state_spec.
  Proof using MODd.
    verify_spec.
    go.
    autorewrite with syntactic.
    destruct t; simpl; autorewrite with syntactic.
    {
      go.
      pose proof (mapModelLookup_None_of_not_elem orig addr H) as Hlookup_none.
      go using observeAnkerIterPointeeF.
      eagerUnifyC.
      go.
      go using observeAnkerIterPointeeF.
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::OriginalAccountState" false 1$m
            (lengthN orig) ?spine] =>
          rewrite (anker_iter_keep_type_ptr
            iterp "monad::Address" "monad::OriginalAccountState"
            false (lengthN orig) spine)
      end.
      go using
        type_ptr_reference_to_B_local,
        anker_iter_keep_type_ptr_C,
        original_spine_iterR_end_mapB,
        observeAnkerMapSpineTypePtrF,
        observeAnkerMapSpineTypePtrRF,
        observeAnkerIterFf,
        observeAnkerIterRFf,
        observeAnkerIterConstRFf,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C,
        type_ptr_reference_to_B_local,
        wp_initialize_unfold_B,
        wp_init_mcall_minvoke_B,
        wp_minvoke_direct_I_inline_C,
        wp_minvoke_direct_I_unmaterialized_C,
        wp_init_cast_noop_B.
      unfold original_map_model.
      go.
      iExists
        (AnkerMapIterR "monad::Address" "monad::OriginalAccountState" false 1$m
           0 (_x_4 ::
              map snd (map (fun '(a1, (b0, _)) => (a1, b0)) orig))),
        (boolR 1$m true).
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::OriginalAccountState" false 1$m
            0 (?ploc :: ?spine)] =>
          rewrite (anker_iter_head_keep_pointee_type_ptr
            iterp ploc "monad::Address" "monad::OriginalAccountState"
            spine);
          rewrite (anker_iter_head_keep_pointee_value_field_type_ptr
            iterp ploc "monad::Address" "monad::OriginalAccountState"
            spine)
      end.
      go using
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
      go.
      iExists _x_4, (initial_original_account_state t).
      go.
    }
    {
      go.
      destruct (original_spine_lookup_ploc_exists orig addr i)
        as [ploc Hploc].
      {
        assumption.
      }
      go.
      go using observeAnkerIterPointeeF.
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::OriginalAccountState" false 1$m i ?spine] =>
          rewrite (anker_iter_keep_type_ptr
            iterp "monad::Address" "monad::OriginalAccountState"
            false i spine)
      end.
      go using
        type_ptr_reference_to_B_local,
        anker_iter_keep_type_ptr_C,
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
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::OriginalAccountState" false 1$m
            i (map (fun x => x.2.1) orig)] =>
          rewrite (anker_iter_keep_pointee_type_ptr
            iterp ploc "monad::Address" "monad::OriginalAccountState"
            i (map (fun x => x.2.1) orig) Hploc);
          rewrite (anker_iter_keep_pointee_value_field_type_ptr
            iterp ploc "monad::Address" "monad::OriginalAccountState"
            i (map (fun x => x.2.1) orig) Hploc)
      end.
      go using
        type_ptr_reference_to_B_local,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C.
      destruct (original_mapModelLookup_of_spine_lookup orig addr i ploc)
        as [orig_state Hlookup].
      {
        assumption.
      }
      {
        assumption.
      }
      {
        exact Hploc.
      }
      unfold state_original_account_state_post.
      rewrite Hlookup.
      iExists ploc.
      iExists orig_state.
      go.
    }
  Qed.
End with_Sigma.
