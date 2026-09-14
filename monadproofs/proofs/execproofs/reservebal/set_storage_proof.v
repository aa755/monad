Require Import monad.proofs.misc.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require monad.proofs.execproofs.reservebal.check_min_original_balance_proof.
Require monad.proofs.execproofs.reservebal.set_nonce_proof.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.auto.cpp.hints.initialize.
Require Import stdpp.gmap.

Import exec_specs.
Import linearity.
Import cQp_compat.

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

  #[local] Instance learn_IncarnationR : LearnEq2 IncarnationR :=
    ltac:(solve_learnable).

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).
  #[local] Hint Resolve type_ptr_reference_to_B_local : sl_opacity.

  Definition wp_init_implicit_B_local := [BWD] wp_init_implicit.
  #[local] Hint Resolve wp_init_implicit_B_local : sl_opacity.
  #[local] Hint Resolve wp.wp_init_initlist_struct_B : sl_opacity.
  #[local] Hint Resolve wp_operand_initlist_default_B : sl_opacity.
  #[local] Hint Resolve
    wp_operand_implicit_init_zero_B
    wp_init_initlist_prim_array_implicit_B
    wp_init_default_array_B : sl_opacity.

  Definition bytes32_pairR (_q : Qp) (kv : N * N) : Rep :=
    pairR "monad::bytes32_t" "monad::bytes32_t"
      (fun q => bytes32R (cQp.mut q))
      (fun q => bytes32R (cQp.mut q)) 1 1 kv.

  Lemma bytes32_pairR_fold (p : ptr) (kv : N * N) :
    p ,, pairSndOffset "monad::bytes32_t" "monad::bytes32_t"
      |-> bytes32R 1 kv.2
    ** p ,, pairFstOffset "monad::bytes32_t" "monad::bytes32_t"
      |-> bytes32R 1 kv.1
    |-- p |-> bytes32_pairR 1 kv.
  Proof using CU MODd Sigma.
    unfold bytes32_pairR, pairR.
    go.
  Qed.

  Definition bytes32_pairR_fold_B p kv :=
    [BWD] (bytes32_pairR_fold p kv).

  Lemma bytes32_pairR_unfold (p : ptr) (kv : N * N) :
    p |-> bytes32_pairR 1 kv
    |--
    p ,, pairFstOffset "monad::bytes32_t" "monad::bytes32_t"
      |-> bytes32R 1 kv.1
    ** p ,, pairSndOffset "monad::bytes32_t" "monad::bytes32_t"
      |-> bytes32R 1 kv.2.
  Proof using CU MODd Sigma.
    unfold bytes32_pairR, pairR.
    go.
  Qed.

  Definition bytes32_pairR_unfold_F p kv :=
    [FWD] (bytes32_pairR_unfold p kv).

  (* Keep the existing proof's arrayR shape using the upstream initialization
     rule; no State-specific initialization assumption is needed. *)
  Lemma wp_init_implicit_char_array_local :
    forall (tu : translation_unit) (rho : region) (base : ptr)
      (len : N) (Q : FreeTemps.t -> mpred),
    (base |-> type_ptrR (Tarray Tuchar len) -*
     base |-> arrayR Tuchar (primR Tuchar 1$m) (replicateN len (Vint 0)) -*
     Q FreeTemps.id)
    |-- wp_init tu rho (Tarray Tuchar len) base
          (Eimplicit_init (Tarray Tuchar len)) Q.
  Proof.
    intros tu rho base len Q.
    apply E.wp_init_implicit_init_array; reflexivity.
  Qed.

  Definition wp_init_implicit_char_array_local_B
      tu rho base len Q :=
    [BWD] (wp_init_implicit_char_array_local tu rho base len Q).

  #[local] Hint Resolve wp_init_implicit_char_array_local_B : sl_opacity.

  #[local] Hint Opaque
    monad_assertion_failed_spec
    bytes32_evmc_bytes32_ctor_spec
    evmc_bytes32_dtor_spec
    optional_account_bool_spec
    bytes32_assign_spec
    StorageMapR
    StateR
    UpdatedAccountStateR
    AccountStateRcore
    optional_specs.optionR : sl_opacity.

  Local Transparent AccountStateRcore OriginalAccountStateR.

  Lemma StorageMapR_unfold (p : ptr) q m :
    p |-> StorageMapR q m
    |-- p |-> immer_specs.ImmerMapR StorageMapTy
      bytes32R
      (fun q => bytes32R (cQp.mut q)) q m.
  Proof using CU MODd Sigma.
    unfold StorageMapR.
    go.
  Qed.

  Definition StorageMapR_unfold_F p q m :=
    [FWD] (StorageMapR_unfold p q m).

  Lemma StorageMapR_fold (p : ptr) q m :
    p |-> immer_specs.ImmerMapR StorageMapTy
      bytes32R
      (fun q => bytes32R (cQp.mut q)) q m
    |-- p |-> StorageMapR q m.
  Proof using CU MODd Sigma.
    unfold StorageMapR.
    go.
  Qed.

  Definition StorageMapR_fold_B p q m :=
    [BWD] (StorageMapR_fold p q m).

  Lemma use_wand_local_r (P Q : mpred) : P ** (P -* Q) |-- Q.
  Proof using.
    go.
  Qed.

  Definition use_wand_local_r_F P Q :=
    [FWD] (use_wand_local_r P Q).

  Lemma use_current_update_wand
      (p : ptr) (upd : UpdatedAccountState) (Q : mpred) :
    p |-> AccountStateRcore 1 (postTxState upd)
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
         |-> AccountSubstateR 1 (substateModel upd)
    ** (p |-> UpdatedAccountStateR 1 upd -* Q)
    |-- Q.
  Proof using CU MODd Sigma.
    go.
  Qed.

  Definition use_current_update_wand_F p upd Q :=
    [FWD] (use_current_update_wand p upd Q).

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

  Lemma use_current_update_forall_wand
      (this p : ptr) (st_current : StateM)
      (addr : evmopsem.evm.address)
      (upd : UpdatedAccountState) :
    p |-> AccountStateRcore 1 (postTxState upd)
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 (substateModel upd)
    ** (Forall F : UpdatedAccountState -> UpdatedAccountState,
        p |-> UpdatedAccountStateR 1 (F upd) -*
        this |-> StateR (state_update_current_account st_current addr (F upd)))
    |-- this |-> StateR (state_update_current_account st_current addr upd).
  Proof using CU MODd Sigma.
    go using
      UpdatedAccountStateR_separated_fold_B,
      use_wand_local_r_F.
  Qed.

  Definition use_current_update_forall_wand_F this p st_current addr upd :=
    [FWD] (use_current_update_forall_wand
      this p st_current addr upd).

  Lemma OriginalAccountStateR_separated_fold
      (p : ptr) q orig_state transient_map :
    p |-> structR "monad::OriginalAccountState"%cpp_name (cQp.mut q)
    ** p ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
        |-> boolR (cQp.mut q)
          (~~ bool_decide (is_Some (min_balance (assumExactness orig_state))))
    ** p ,, o_field CU "monad::OriginalAccountState::min_balance_"
        |-> match min_balance (assumExactness orig_state) with
            | Some n => u256R q n
            | None => Exists nb : N, u256R q nb
            end
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.optionR "monad::Account"%cpp_type
              AccountR q (preTxState orig_state)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR q (preTxStorage orig_state)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR q transient_map
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        |-> structR "monad::AccountState"%cpp_name (cQp.mut q)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR q unusedAccountSubstate
    |-- p |-> OriginalAccountStateR q orig_state.
  Proof using CU MODd Sigma.
    go.
    unfold OriginalAccountStateR, AccountStateRcore.
    go.
    iExists transient_map.
    go.
  Qed.

  Definition OriginalAccountStateR_separated_fold_B
      p q orig_state transient_map :=
    [BWD] (OriginalAccountStateR_separated_fold p q orig_state transient_map).

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
	      simpl.
	      destruct (decide (addr = addr)) as [_|Hneq];
	        [|contradiction Hneq; reflexivity].
	      reflexivity.
	    }
  Qed.

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

  Lemma removeKey_record_original_storage_read_map
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (key value : N) :
    removeKey (record_original_storage_read_map addr key value orig) addr =
    removeKey orig addr.
  Proof using.
    unfold removeKey, record_original_storage_read_map.
    induction orig as [| [a [loc aps]] orig IH]; simpl.
    {
      reflexivity.
    }
    destruct (bool_decide (a = addr)) eqn:Heq.
    {
      apply bool_decide_eq_true in Heq.
      subst a.
      simpl.
      destruct (bool_decide (addr <> addr)) eqn:Hneq.
      {
        apply bool_decide_eq_true in Hneq.
        exfalso.
        exact (Hneq eq_refl).
      }
      {
        exact IH.
      }
    }
    {
      apply bool_decide_eq_false in Heq.
      simpl.
      destruct (bool_decide (a <> addr)) eqn:Hneq.
      {
        rewrite IH.
        reflexivity.
      }
      {
        apply bool_decide_eq_false in Hneq.
        exfalso.
        exact (Hneq Heq).
      }
    }
  Qed.

  Lemma original_spine_model_record_original_storage_read_map
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (key value : N) :
    map (fun '(a, (loc, _)) => (a, loc))
      (record_original_storage_read_map addr key value orig) =
    map (fun '(a, (loc, _)) => (a, loc)) orig.
  Proof using.
    unfold record_original_storage_read_map.
    induction orig as [| [a [loc aps]] orig IH]; simpl.
    {
      reflexivity.
    }
    destruct (bool_decide (a = addr)); simpl; rewrite IH; reflexivity.
  Qed.

  Lemma nth_error_record_original_storage_read_map
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (key value : N)
      (i : nat) (loc : ptr) (orig_state : AssumedPreTxAccountState) :
    nth_error orig i = Some (addr, (loc, orig_state)) ->
    nth_error (record_original_storage_read_map addr key value orig) i =
      Some (addr,
        (loc, record_original_storage_read_assumed orig_state key value)).
  Proof using.
    revert i.
    induction orig as [| [a [loc0 aps]] orig IH]; intros [| i] Hnth;
      simpl in *; try discriminate.
    {
      inversion Hnth; subst.
      rewrite bool_decide_true; [reflexivity | reflexivity].
    }
    {
      exact (IH i Hnth).
    }
  Qed.

  Lemma reinsert_recorded_original_storage_read_payload
      (map_ptr : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (key value : N) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState"
         |-> OriginalAccountStateR 1
              (record_original_storage_read_assumed orig_state key value)
    ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    |--
    map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1
         (record_original_storage_read_map addr key value orig).
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
    pose proof
      (nth_error_record_original_storage_read_map
         orig addr key value (N.to_nat (N.of_nat i)) loc orig_state Hnth_N)
      as Hnth_recorded.
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address AssumedPreTxAccountState _
      "monad::Address" "monad::OriginalAccountState"
      addressR OriginalAccountStateR
      (record_original_storage_read_map addr key value orig) (N.of_nat i)
      (addr,
        (loc, record_original_storage_read_assumed orig_state key value))
      addr map_ptr Hnth_recorded eq_refl).
    rewrite removeKey_record_original_storage_read_map.
    unfold pairR.
    go.
  Qed.

  Definition reinsert_recorded_original_storage_read_payload_B
      map_ptr orig addr loc orig_state key value Hlookup :=
    [BWD] (reinsert_recorded_original_storage_read_payload
             map_ptr orig addr loc orig_state key value Hlookup).

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

  Lemma removeKey_replace_current_account_update_same
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState) :
    removeKey (replace_current_account_update addr upd cur) addr =
    removeKey (replace_current_account_update addr upd_final cur) addr.
  Proof using.
    unfold removeKey, replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    {
      destruct (bool_decide (a = addr)) eqn:Ha.
      {
        apply bool_decide_eq_true in Ha.
        subst a.
        cbn.
        destruct (bool_decide (addr <> addr)) eqn:Hneq.
        {
          apply bool_decide_eq_true in Hneq.
          exfalso.
          exact (Hneq eq_refl).
        }
        {
          exact IH.
        }
      }
      {
        apply bool_decide_eq_false in Ha.
        cbn.
        destruct (bool_decide (a <> addr)) eqn:Hneq.
        {
          rewrite IH.
          reflexivity.
        }
        {
          apply bool_decide_eq_false in Hneq.
          exfalso.
          exact (Hneq Ha).
        }
      }
    }
  Qed.

  Lemma nth_error_replace_current_account_update_head
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState)
      (i : nat) (loc upd_loc : ptr) (tl : list (ptr * UpdatedAccountState)) :
    nth_error (replace_current_account_update addr upd cur) i =
      Some (addr, (loc, (upd_loc, upd) :: tl)) ->
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

  Lemma reinsert_updated_current_head_payload
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd upd_final : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup (replace_current_account_update addr upd cur) addr =
      Some (loc, (upd_loc, upd) :: tl) ->
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
          1 (removeKey (replace_current_account_update addr upd cur) addr)
    |--
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (replace_current_account_update addr upd_final cur).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert
      (Hmem :
        (addr, (loc, (upd_loc, upd) :: tl)) ∈
          replace_current_account_update addr upd cur).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_N :
      nth_error (replace_current_account_update addr upd cur)
        (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, (upd_loc, upd) :: tl))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    pose proof
      (nth_error_replace_current_account_update_head
         cur addr upd upd_final (N.to_nat (N.of_nat i)) loc upd_loc tl
         Hnth_N) as Hnth_final.
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      (replace_current_account_update addr upd_final cur) (N.of_nat i)
      (addr, (loc, (upd_loc, upd_final) :: tl)) addr map_ptr
      Hnth_final eq_refl).
    rewrite <- (removeKey_replace_current_account_update_same
      cur addr upd upd_final).
    unfold pairR, VersionStackR.
    simpl.
    go.
  Qed.

  Definition reinsert_updated_current_head_payload_B
      map_ptr cur addr loc upd_loc upd upd_final tl Hlookup :=
    [BWD] (reinsert_updated_current_head_payload
             map_ptr cur addr loc upd_loc upd upd_final tl Hlookup).

  Definition current_spine_model
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :=
    map (fun '(a, (b, _)) => (a, b)) cur.

  Lemma current_spine_model_replace_current_account_update
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState) :
    current_spine_model (replace_current_account_update addr upd cur) =
    current_spine_model (replace_current_account_update addr upd_final cur).
  Proof using.
    unfold current_spine_model, replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    {
      destruct (bool_decide (a = addr)); simpl; rewrite IH; reflexivity.
    }
  Qed.

  Lemma current_spine_map_replace_current_account_update
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState) :
    map (fun '(a, (b, _)) => (a, b))
      (replace_current_account_update addr upd cur) =
    map (fun '(a, (b, _)) => (a, b))
      (replace_current_account_update addr upd_final cur).
  Proof using.
    exact (current_spine_model_replace_current_account_update
             cur addr upd upd_final).
  Qed.

  Lemma CurrentSpineR_replace_current_account_update
      (p : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState) :
    p |-> ankerl_specs.AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR 1
          (current_spine_model (replace_current_account_update addr upd cur))
    |--
    p |-> ankerl_specs.AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR 1
          (current_spine_model
             (replace_current_account_update addr upd_final cur)).
  Proof using CU MODd Sigma.
    rewrite (current_spine_model_replace_current_account_update
               cur addr upd upd_final).
    go.
  Qed.

  Lemma account_code_account_set_storage_model
      (ac : AccountM) (key value : N) :
    account_code (account_set_storage_model ac key value) = account_code ac.
  Proof using.
    destruct ac as [core inc keys bal].
    destruct core.
    reflexivity.
  Qed.

  Lemma code_entry_of_updates_set_storage
      (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (key value original : N) (status : Z)
      (retp : ptr) (tl : list (ptr * UpdatedAccountState)) :
    postTxState upd = Some ac ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    code_entry_of_updates ((retp, upd_final) :: tl) =
    code_entry_of_updates ((retp, upd) :: tl).
  Proof using.
    intros Hacct [_ [_ ->]].
    unfold code_entry_of_updates, updated_account_set_storage_model.
    simpl.
    rewrite Hacct.
    rewrite account_code_account_set_storage_model.
    reflexivity.
  Qed.

  Lemma code_entries_of_state_replace_current_account_update_set_storage
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (key value original : N) (status : Z) :
    postTxState upd = Some ac ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    code_entries_of_state
      (replace_current_account_update addr upd_final cur) =
    code_entries_of_state
      (replace_current_account_update addr upd cur).
  Proof using.
    intros Hacct Hset.
    destruct Hset as [? [_ ->]].
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    destruct (bool_decide (a = addr)); simpl.
    {
      destruct updates as [| [upd_loc upd0] tl]; simpl.
      {
        exact IH.
      }
      {
        unfold updated_account_set_storage_model.
        simpl.
        rewrite Hacct.
        rewrite account_code_account_set_storage_model.
        rewrite IH.
        reflexivity.
      }
    }
    {
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma map_fst_replace_current_account_update_same
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState) :
    map fst (replace_current_account_update addr upd_final cur) =
    map fst (replace_current_account_update addr upd cur).
  Proof using.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    destruct (bool_decide (a = addr)); simpl; rewrite IH; reflexivity.
  Qed.

  Lemma stateCodeMapInvariants_set_storage_update
      (st : StateM) (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (key value original : N) (status : Z) :
    postTxState upd = Some ac ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    stateCodeMapInvariants (state_update_current_account st addr upd) ->
    stateCodeMapInvariants (state_update_current_account st addr upd_final).
  Proof using.
    intros Hacct Hset Hcode.
    unfold state_update_current_account, state_with_preTxAssumedState_and_newStates,
      stateCodeMapInvariants, codeMapOfNewStates, all_code_entries in *.
    simpl in *.
    rewrite (code_entries_of_state_replace_current_account_update_set_storage
      (newStates st) addr upd upd_final ac key value original status Hacct Hset).
    exact Hcode.
  Qed.

  Lemma replace_current_account_update_bad_lookup
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr a : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState)
      (loc : ptr) (tl : list (ptr * UpdatedAccountState)) :
    is_Some (postTxState upd_final) ->
    mapModelLookup (replace_current_account_update addr upd_final cur) a =
      Some (loc, tl) ->
    match tl with
    | [] =>
        mapModelLookup (replace_current_account_update addr upd cur) a =
          Some (loc, [])
    | (upd_loc, head) :: tail =>
        postTxState head = None ->
        mapModelLookup (replace_current_account_update addr upd cur) a =
          Some (loc, (upd_loc, head) :: tail)
    end.
  Proof using.
    intros [ac_final Hfinal].
    unfold mapModelLookup, replace_current_account_update.
    induction cur as [| [a0 [loc0 updates0]] cur IH]; simpl;
      intro Hlookup.
    {
      rewrite lookup_empty in Hlookup.
      discriminate.
    }
    destruct (bool_decide (a0 = addr)) eqn:Haaddr.
    {
      apply bool_decide_eq_true in Haaddr.
      subst a0.
      destruct (decide (addr = a)) as [-> | Hne].
      {
        rewrite lookup_insert in Hlookup.
        destruct (decide (a = a)) as [_|Hneq] in Hlookup;
          [|contradiction Hneq; reflexivity].
        rename Hlookup into Hpayload.
        destruct updates0 as [| [upd_loc head] tail].
        {
          simpl in Hpayload.
          destruct (decide (a = a)) as [_|Hneq] in Hpayload;
            [|contradiction Hneq; reflexivity].
          inversion Hpayload; subst loc tl; clear Hpayload.
          rewrite lookup_insert.
          cbn.
          destruct (decide (a = a)) as [_|Hneq];
            [|contradiction Hneq; reflexivity].
          reflexivity.
        }
        {
          simpl in Hpayload.
          destruct (decide (a = a)) as [_|Hneq] in Hpayload;
            [|contradiction Hneq; reflexivity].
          inversion Hpayload; subst loc tl; clear Hpayload.
          simpl.
          intro Hnone.
          rewrite Hfinal in Hnone.
          discriminate.
        }
      }
      {
        rewrite lookup_insert_ne in Hlookup; [| exact Hne].
        specialize (IH Hlookup).
        destruct tl as [| [upd_loc head] tail].
        {
          rewrite lookup_insert_ne; [| exact Hne].
          exact IH.
        }
        {
          intro Hnone.
          rewrite lookup_insert_ne; [| exact Hne].
          exact (IH Hnone).
        }
      }
    }
    {
      apply bool_decide_eq_false in Haaddr.
      destruct (decide (a0 = a)) as [-> | Hne].
      {
        rewrite lookup_insert in Hlookup.
        simpl in Hlookup.
        destruct (decide (a = a)) as [_|Hneq] in Hlookup;
          [|contradiction Hneq; reflexivity].
        inversion Hlookup; subst; clear Hlookup.
        destruct tl as [| [upd_loc head] tail].
        {
          rewrite lookup_insert.
          cbn.
          destruct (decide (a = a)) as [_|Hneq];
            [|contradiction Hneq; reflexivity].
          reflexivity.
        }
        {
          intro Hnone.
          rewrite lookup_insert.
          cbn.
          destruct (decide (a = a)) as [_|Hneq];
            [|contradiction Hneq; reflexivity].
          reflexivity.
        }
      }
      {
        rewrite lookup_insert_ne in Hlookup; [| exact Hne].
        specialize (IH Hlookup).
        destruct tl as [| [upd_loc head] tail].
        {
          rewrite lookup_insert_ne; [| exact Hne].
          exact IH.
        }
        {
          intro Hnone.
          rewrite lookup_insert_ne; [| exact Hne].
          exact (IH Hnone).
        }
      }
    }
  Qed.

  Lemma validPostNone_set_storage_update
      (st : StateM) (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState) :
    is_Some (postTxState upd_final) ->
    validPostNone (state_update_current_account st addr upd) ->
    validPostNone (state_update_current_account st addr upd_final).
  Proof using.
    intros Hsome Hpost a loc tl orig_loc aps Hnew Hpre.
    pose proof
      (replace_current_account_update_bad_lookup
         (newStates st) addr a upd upd_final loc tl Hsome Hnew) as Hbad.
    destruct tl as [| [upd_loc head] tail].
    {
      exact (Hpost a loc [] orig_loc aps Hbad Hpre).
    }
    {
      intro Hnone.
      exact (Hpost a loc ((upd_loc, head) :: tail) orig_loc aps
               (Hbad Hnone) Hpre Hnone).
    }
  Qed.

  Lemma mapModelLookup_replace_current_account_update_eq_local
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    mapModelLookup (replace_current_account_update addr upd_final cur) addr =
    match mapModelLookup cur addr with
    | Some (loc, updates) =>
        Some (loc, replace_current_head_update upd_final updates)
    | None => None
    end.
  Proof using.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    unfold mapModelLookup in *; simpl in *.
    destruct (decide (a = addr)) as [-> | Hneq].
    {
      rewrite bool_decide_eq_true_2; [| reflexivity].
      simpl.
      rewrite !lookup_insert.
      destruct (decide (addr = addr)) as [_|Hcontra];
        [|contradiction Hcontra; reflexivity].
      reflexivity.
    }
    rewrite bool_decide_eq_false_2; [| exact Hneq].
    simpl.
    rewrite !lookup_insert_ne; [exact IH | exact Hneq | exact Hneq].
  Qed.

  Lemma mapModelLookup_replace_current_account_update_ne_local
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr a : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    a <> addr ->
    mapModelLookup (replace_current_account_update addr upd_final cur) a =
    mapModelLookup cur a.
  Proof using.
    intro Hneq.
    unfold replace_current_account_update, mapModelLookup.
    induction cur as [| [k [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    destruct (decide (k = a)) as [-> | Hka].
    {
      rewrite bool_decide_false; [| exact Hneq].
      simpl.
      repeat rewrite lookup_insert.
      destruct (decide (a = a)) as [_|Hcontra];
        [|contradiction Hcontra; reflexivity].
      reflexivity.
    }
    destruct (decide (k = addr)) as [-> | Hkaddr].
    {
      rewrite bool_decide_eq_true_2; [| reflexivity].
      simpl.
      repeat (rewrite lookup_insert_ne; [| exact Hka]).
      exact IH.
    }
    rewrite bool_decide_eq_false_2; [| exact Hkaddr].
    simpl.
    repeat (rewrite lookup_insert_ne; [| exact Hka]).
    exact IH.
  Qed.

  Lemma validSliceInvariants_set_storage_update
      (st : StateM) (addr : evmopsem.evm.address)
      (upd : UpdatedAccountState)
      (ac : AccountM) (key value : N) :
    postTxState upd = Some ac ->
    validSliceInvariants (state_update_current_account st addr upd) ->
    validSliceInvariants
      (state_update_current_account st addr
         (updated_account_set_storage_model upd ac key value)).
  Proof using.
    intros Hacct Hslice a au Hau.
    unfold assumptionAndUpdateOfAddr, state_update_current_account,
      state_with_preTxAssumedState_and_newStates in Hau |- *.
    simpl in Hau |- *.
    destruct (preTxAssumedState st !! a) as [[orig_loc aps] |] eqn:Hpre;
      [| discriminate].
    destruct (decide (a = addr)) as [Heq | Hneq].
    {
      subst a.
      change ((replace_current_account_update addr
                 (updated_account_set_storage_model upd ac key value)
                 (newStates st)) !! addr)
        with (mapModelLookup
                (replace_current_account_update addr
                   (updated_account_set_storage_model upd ac key value)
                   (newStates st)) addr) in Hau.
      rewrite mapModelLookup_replace_current_account_update_eq_local in Hau.
      destruct (mapModelLookup (newStates st) addr)
        as [[cur_loc updates] |] eqn:Hcur.
      {
        destruct updates as [| [upd_loc old_upd] tl].
        {
          simpl in Hau.
          inversion Hau; subst au; clear Hau.
          unfold sliceInvariants; simpl.
          destruct (min_balance (assumExactness aps)); exact I.
        }
        simpl in Hau.
        inversion Hau; subst au; clear Hau.
        assert (Hold_slice :
          sliceInvariants
            {| preAssumption := aps;
               originalLoc := orig_loc;
               txUpdates := Some (cur_loc, (upd_loc, upd)) |}).
        {
          apply Hslice with (addr := addr).
          unfold assumptionAndUpdateOfAddr, state_update_current_account,
            state_with_preTxAssumedState_and_newStates.
          simpl.
          rewrite Hpre.
          change ((replace_current_account_update addr upd (newStates st)) !! addr)
            with (mapModelLookup
                    (replace_current_account_update addr upd (newStates st)) addr).
          rewrite mapModelLookup_replace_current_account_update_eq_local.
          rewrite Hcur.
          reflexivity.
        }
        unfold sliceInvariants in Hold_slice |- *.
        simpl in Hold_slice |- *.
        destruct (min_balance (assumExactness aps)) as [minbal |]; [| exact I].
        rewrite Hacct in Hold_slice.
        simpl in Hold_slice.
        destruct (preTxState aps) as [assumed |]; [| exact I].
        simpl in Hold_slice |- *.
        exact Hold_slice.
      }
      simpl in Hau.
      inversion Hau; subst au; clear Hau.
      unfold sliceInvariants; simpl.
      destruct (min_balance (assumExactness aps)); exact I.
    }
    apply Hslice with (addr := a).
    unfold assumptionAndUpdateOfAddr, state_update_current_account,
      state_with_preTxAssumedState_and_newStates.
    simpl.
    rewrite Hpre.
    change ((replace_current_account_update addr upd (newStates st)) !! a)
      with (mapModelLookup
              (replace_current_account_update addr upd (newStates st)) a).
    change ((replace_current_account_update addr
               (updated_account_set_storage_model upd ac key value)
               (newStates st)) !! a)
      with (mapModelLookup
              (replace_current_account_update addr
                 (updated_account_set_storage_model upd ac key value)
                 (newStates st)) a) in Hau.
    rewrite mapModelLookup_replace_current_account_update_ne_local in Hau;
      [| exact Hneq].
    rewrite mapModelLookup_replace_current_account_update_ne_local;
      [| exact Hneq].
    exact Hau.
  Qed.

  Lemma validStateM_set_storage_update
      (st : StateM) (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState) :
    validStateM (state_update_current_account st addr upd) ->
    validStateM (state_update_current_account st addr upd_final).
  Proof using.
    intros Hvalid a.
    specialize (Hvalid a).
    unfold validStateM, assumptionAndUpdateOfAddr,
      state_update_current_account, state_with_preTxAssumedState_and_newStates
      in *.
    simpl in *.
    destruct (preTxAssumedState st !! a) as [[loc aps] |]; simpl in *;
      exact Hvalid.
  Qed.

  Lemma StateCodeMapR_set_storage_update
      (p : ptr) (st : StateM) (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (key value original : N) (status : Z) :
    postTxState upd = Some ac ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    p |-> StateCodeMapR (state_update_current_account st addr upd)
    |--
    p |-> StateCodeMapR (state_update_current_account st addr upd_final).
  Proof using CU MODd Sigma.
    intros Hacct Hset.
    pose proof
      (stateCodeMapInvariants_set_storage_update
         st addr upd upd_final ac key value original status Hacct Hset)
      as Hcode.
    unfold StateCodeMapR.
    go.
  Qed.

  Definition StateCodeMapR_set_storage_update_F
      p st addr upd upd_final ac key value original status Hacct Hset :=
    [FWD] (StateCodeMapR_set_storage_update
      p st addr upd upd_final ac key value original status Hacct Hset).

  Lemma validModel_set_storage_update
      (st : StateM) (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (key value original : N) (status : Z) :
    postTxState upd = Some ac ->
    validModel (state_update_current_account st addr upd) ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    validModel (state_update_current_account st addr upd_final).
  Proof using.
    intros Hacct [Hsub [Hstate [Hpost Hslice]]] [_ [_ ->]].
    unfold validModel.
    split.
    {
      unfold state_update_current_account,
        state_with_preTxAssumedState_and_newStates in *.
      simpl in *.
      rewrite (map_fst_replace_current_account_update_same
        (newStates st) addr upd
        (updated_account_set_storage_model upd ac key value)).
      exact Hsub.
    }
    split.
    {
      exact (validStateM_set_storage_update st addr upd
               (updated_account_set_storage_model upd ac key value) Hstate).
    }
    split.
    {
      eapply (validPostNone_set_storage_update
        st addr upd (updated_account_set_storage_model upd ac key value)).
      {
        eexists.
        reflexivity.
      }
      exact Hpost.
    }
    {
      eapply validSliceInvariants_set_storage_update; eauto.
    }
  Qed.

  Lemma map_fst_record_original_storage_read_map
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (key value : N) :
    map fst (record_original_storage_read_map addr key value orig) =
    map fst orig.
  Proof using.
    unfold record_original_storage_read_map.
    induction orig as [| [a [loc aps]] orig IH]; simpl.
    {
      reflexivity.
    }
    destruct (bool_decide (a = addr)); simpl; rewrite IH; reflexivity.
  Qed.

  Lemma mapModelLookup_record_original_storage_read_map
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (key value : N)
      (a : evmopsem.evm.address) :
    mapModelLookup (record_original_storage_read_map addr key value orig) a =
    match mapModelLookup orig a with
    | Some (loc, aps) =>
        if bool_decide (a = addr)
        then Some (loc, record_original_storage_read_assumed aps key value)
        else Some (loc, aps)
    | None => None
    end.
  Proof using.
    induction orig as [| [addr0 [loc0 aps0]] orig IH]; simpl.
    {
      reflexivity.
    }
    unfold mapModelLookup in *.
    cbn [record_original_storage_read_map list_to_map].
    destruct (decide (a = addr0)) as [Heq | Hneq].
    {
      subst a.
      destruct (bool_decide (addr0 = addr)) eqn:Haddr; simpl.
      {
        rewrite lookup_insert.
        replace (<[addr0 := (loc0, aps0)]> (list_to_map orig) !! addr0)
          with (Some (loc0, aps0)).
        {
          destruct (decide (addr0 = addr0)) as [_|Hcontra];
            [|contradiction Hcontra; reflexivity].
          reflexivity.
        }
        rewrite lookup_insert.
        destruct (decide (addr0 = addr0)) as [_|Hcontra];
          [|contradiction Hcontra; reflexivity].
        reflexivity.
      }
      {
        rewrite lookup_insert.
        replace (<[addr0 := (loc0, aps0)]> (list_to_map orig) !! addr0)
          with (Some (loc0, aps0)).
        {
          destruct (decide (addr0 = addr0)) as [_|Hcontra];
            [|contradiction Hcontra; reflexivity].
          reflexivity.
        }
        rewrite lookup_insert.
        destruct (decide (addr0 = addr0)) as [_|Hcontra];
          [|contradiction Hcontra; reflexivity].
        reflexivity.
      }
    }
    {
      destruct (bool_decide (addr0 = addr)); simpl.
      {
        replace
          (<[addr0 :=
              (loc0, record_original_storage_read_assumed aps0 key value)]>
             (list_to_map
                (record_original_storage_read_map addr key value orig)
              : gmap evmopsem.evm.address
                  (ModelWithPtr AssumedPreTxAccountState)) !! a)
          with
          ((list_to_map
             (record_original_storage_read_map addr key value orig)
            : gmap evmopsem.evm.address
                (ModelWithPtr AssumedPreTxAccountState)) !! a).
        2:
        {
          rewrite lookup_insert_ne.
          {
            reflexivity.
          }
          intro Heq.
          apply Hneq.
          symmetry.
          exact Heq.
        }
        replace
          (<[addr0 := (loc0, aps0)]>
             (list_to_map orig
              : gmap evmopsem.evm.address
                  (ModelWithPtr AssumedPreTxAccountState)) !! a)
          with
          ((list_to_map orig
            : gmap evmopsem.evm.address
                (ModelWithPtr AssumedPreTxAccountState)) !! a).
        2:
        {
          rewrite lookup_insert_ne.
          {
            reflexivity.
          }
          intro Heq.
          apply Hneq.
          symmetry.
          exact Heq.
        }
        exact IH.
      }
      {
        replace
          (<[addr0 := (loc0, aps0)]>
             (list_to_map
                (record_original_storage_read_map addr key value orig)
              : gmap evmopsem.evm.address
                  (ModelWithPtr AssumedPreTxAccountState)) !! a)
          with
          ((list_to_map
             (record_original_storage_read_map addr key value orig)
            : gmap evmopsem.evm.address
                (ModelWithPtr AssumedPreTxAccountState)) !! a).
        2:
        {
          rewrite lookup_insert_ne.
          {
            reflexivity.
          }
          intro Heq.
          apply Hneq.
          symmetry.
          exact Heq.
        }
        replace
          (<[addr0 := (loc0, aps0)]>
             (list_to_map orig
              : gmap evmopsem.evm.address
                  (ModelWithPtr AssumedPreTxAccountState)) !! a)
          with
          ((list_to_map orig
            : gmap evmopsem.evm.address
                (ModelWithPtr AssumedPreTxAccountState)) !! a).
        2:
        {
          rewrite lookup_insert_ne.
          {
            reflexivity.
          }
          intro Heq.
          apply Hneq.
          symmetry.
          exact Heq.
        }
        exact IH.
      }
    }
  Qed.

  Lemma validStateM_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address) (key value : N) :
    validStateM st ->
    validStateM (state_record_original_storage_read st addr key value).
  Proof using.
    intros Hvalid a.
    specialize (Hvalid a).
    unfold validStateM, assumptionAndUpdateOfAddr,
      state_record_original_storage_read,
      state_with_preTxAssumedState_and_newStates in *.
    simpl in *.
    change (record_original_storage_read_map addr key value
              (preTxAssumedState st) !! a) with
      (mapModelLookup
         (record_original_storage_read_map addr key value
            (preTxAssumedState st)) a).
    rewrite mapModelLookup_record_original_storage_read_map.
    change (preTxAssumedState st !! a) with
      (mapModelLookup (preTxAssumedState st) a) in Hvalid.
    destruct (mapModelLookup (preTxAssumedState st) a)
      as [[loc aps] |]; simpl in *.
    {
      destruct (bool_decide (a = addr)); simpl; exact Hvalid.
    }
    {
      exact Hvalid.
    }
  Qed.

  Lemma validPostNone_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address) (key value : N) :
    validPostNone st ->
    validPostNone (state_record_original_storage_read st addr key value).
  Proof using.
    intros Hpost a loc tl orig_loc aps Hnew Hpre.
    unfold state_record_original_storage_read,
      state_with_preTxAssumedState_and_newStates in Hnew, Hpre.
    simpl in Hnew, Hpre.
    change (record_original_storage_read_map addr key value
              (preTxAssumedState st) !! a) with
      (mapModelLookup
         (record_original_storage_read_map addr key value
            (preTxAssumedState st)) a) in Hpre.
    rewrite mapModelLookup_record_original_storage_read_map in Hpre.
    destruct (mapModelLookup (preTxAssumedState st) a)
      as [[orig_loc0 aps0] |] eqn:Hpre0; [| discriminate].
    destruct (bool_decide (a = addr)) eqn:Ha.
    {
      inversion Hpre; subst orig_loc aps; clear Hpre.
      specialize (Hpost a loc tl orig_loc0 aps0 Hnew Hpre0).
      destruct tl as [| [upd_loc upd] tail].
      {
        exact Hpost.
      }
      {
        intro Hnone.
        simpl.
        exact (Hpost Hnone).
      }
    }
    {
      inversion Hpre; subst orig_loc aps; clear Hpre.
      exact (Hpost a loc tl orig_loc0 aps0 Hnew Hpre0).
    }
  Qed.

  Lemma validSliceInvariants_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address) (key value : N) :
    validSliceInvariants st ->
    validSliceInvariants (state_record_original_storage_read st addr key value).
  Proof using.
    intros Hslice a au Hau.
    unfold assumptionAndUpdateOfAddr, state_record_original_storage_read,
      state_with_preTxAssumedState_and_newStates in Hau.
    simpl in Hau.
    change (record_original_storage_read_map addr key value
              (preTxAssumedState st) !! a) with
      (mapModelLookup
         (record_original_storage_read_map addr key value
            (preTxAssumedState st)) a) in Hau.
    rewrite mapModelLookup_record_original_storage_read_map in Hau.
    destruct (mapModelLookup (preTxAssumedState st) a)
      as [[orig_loc aps] |] eqn:Hpre0; [| discriminate].
    destruct (bool_decide (a = addr)) eqn:Ha.
    {
      inversion Hau; subst au; clear Hau.
      assert (Hold_slice :
        sliceInvariants
          {| preAssumption := aps;
             originalLoc := orig_loc;
             txUpdates :=
               (newStates st !! a) ≫=
                 (fun a : ptr * list (ptr * UpdatedAccountState) =>
                    match head a.2 with
                    | Some (loc0, upd) => Some (a.1, (loc0, upd))
                    | None => None
                    end) |}).
      {
        apply Hslice with (addr := a).
        unfold assumptionAndUpdateOfAddr.
        change (preTxAssumedState st !! a)
          with (mapModelLookup (preTxAssumedState st) a).
        rewrite Hpre0.
        reflexivity.
      }
      unfold record_original_storage_read_assumed.
      unfold sliceInvariants in Hold_slice |- *.
      simpl in Hold_slice |- *.
      exact Hold_slice.
    }
    inversion Hau; subst au; clear Hau.
    apply Hslice with (addr := a).
    unfold assumptionAndUpdateOfAddr.
    change (preTxAssumedState st !! a)
      with (mapModelLookup (preTxAssumedState st) a).
    rewrite Hpre0.
    reflexivity.
  Qed.

  Lemma validModel_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address) (key value : N) :
    validModel st ->
    validModel (state_record_original_storage_read st addr key value).
  Proof using.
    intros [Hsub [Hstate [Hpost Hslice]]].
    unfold validModel.
    split.
    {
      unfold state_record_original_storage_read,
        state_with_preTxAssumedState_and_newStates.
      simpl.
      rewrite map_fst_record_original_storage_read_map.
      exact Hsub.
    }
    split.
    {
      exact (validStateM_record_original_storage_read st addr key value Hstate).
    }
    split.
    {
      exact (validPostNone_record_original_storage_read st addr key value Hpost).
    }
    {
      exact (validSliceInvariants_record_original_storage_read
               st addr key value Hslice).
    }
  Qed.

  Lemma validModel_set_storage_update_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (key value original : N) (status : Z) :
    postTxState upd = Some ac ->
    validModel (state_update_current_account st addr upd) ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    validModel
      (state_record_original_storage_read
         (state_update_current_account st addr upd_final)
         addr key original).
  Proof using.
    intros Hacct Hvalid Hset.
    apply validModel_record_original_storage_read.
    exact (validModel_set_storage_update
      st addr upd upd_final ac key value original status
      Hacct Hvalid Hset).
  Qed.

  Lemma code_entry_of_assumed_record_original_storage_read
      (aps : AssumedPreTxAccountState) (key value : N) :
    code_entry_of_assumed
      (record_original_storage_read_assumed aps key value) =
    code_entry_of_assumed aps.
  Proof using.
    unfold code_entry_of_assumed, record_original_storage_read_assumed.
    reflexivity.
  Qed.

  Lemma code_entries_of_preTxAssumed_record_original_storage_read_map
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) (key value : N) :
    code_entries_of_preTxAssumed
      (record_original_storage_read_map addr key value orig) =
    code_entries_of_preTxAssumed orig.
  Proof using.
    unfold record_original_storage_read_map.
    induction orig as [| [a [loc aps]] orig IH]; simpl.
    {
      reflexivity.
    }
    destruct (bool_decide (a = addr)); simpl;
      rewrite ?code_entry_of_assumed_record_original_storage_read;
      rewrite IH; reflexivity.
  Qed.

  Lemma codeMapOfPreTxAssumedAccounts_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address) (key value : N) :
    codeMapOfPreTxAssumedAccounts
      (state_record_original_storage_read st addr key value) =
    codeMapOfPreTxAssumedAccounts st.
  Proof using.
    unfold codeMapOfPreTxAssumedAccounts,
      state_record_original_storage_read,
      state_with_preTxAssumedState_and_newStates.
    simpl.
    rewrite code_entries_of_preTxAssumed_record_original_storage_read_map.
    reflexivity.
  Qed.

  Lemma codeMapOfNewStates_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address) (key value : N) :
    codeMapOfNewStates
      (state_record_original_storage_read st addr key value) =
    codeMapOfNewStates st.
  Proof using.
    unfold codeMapOfNewStates,
      state_record_original_storage_read,
      state_with_preTxAssumedState_and_newStates.
    reflexivity.
  Qed.

  Lemma all_code_entries_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address) (key value : N) :
    all_code_entries
      (state_record_original_storage_read st addr key value) =
    all_code_entries st.
  Proof using.
    unfold all_code_entries, state_record_original_storage_read,
      state_with_preTxAssumedState_and_newStates.
    simpl.
    rewrite codeMapOfPreTxAssumedAccounts_record_original_storage_read.
    reflexivity.
  Qed.

  Lemma stateCodeMapInvariants_record_original_storage_read
      (st : StateM) (addr : evmopsem.evm.address) (key value : N) :
    stateCodeMapInvariants st ->
    stateCodeMapInvariants
      (state_record_original_storage_read st addr key value).
  Proof using.
    intros Hcode.
    unfold stateCodeMapInvariants in *.
    simpl.
    rewrite codeMapOfNewStates_record_original_storage_read.
    rewrite codeMapOfPreTxAssumedAccounts_record_original_storage_read.
    rewrite all_code_entries_record_original_storage_read.
    exact Hcode.
  Qed.

  Lemma StateCodeMapR_record_original_storage_read
      (p : ptr) (st : StateM)
      (addr : evmopsem.evm.address) (key value : N) :
    p |-> StateCodeMapR st
    |--
    p |-> StateCodeMapR
      (state_record_original_storage_read st addr key value).
  Proof using CU MODd Sigma.
    pose proof
      (stateCodeMapInvariants_record_original_storage_read st addr key value)
      as Hcode.
    unfold StateCodeMapR.
    go.
  Qed.

  Lemma StateCodeMapR_set_storage_update_record_original_storage_read
      (p : ptr) (st : StateM) (addr : evmopsem.evm.address)
      (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (key value original : N) (status : Z) :
    postTxState upd = Some ac ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    p |-> StateCodeMapR (state_update_current_account st addr upd)
    |--
    p |-> StateCodeMapR
      (state_record_original_storage_read
         (state_update_current_account st addr upd_final)
         addr key original).
  Proof using CU MODd Sigma.
    intros Hacct Hset.
    try solve [go].
    etrans.
    {
      exact (StateCodeMapR_set_storage_update
        p st addr upd upd_final ac key value original status Hacct Hset).
    }
    {
      exact (StateCodeMapR_record_original_storage_read
        p (state_update_current_account st addr upd_final)
        addr key original).
    }
  Qed.

  Definition StateCodeMapR_set_storage_update_record_original_storage_read_F
      p st addr upd upd_final ac key value original status Hacct Hset :=
    [FWD] (StateCodeMapR_set_storage_update_record_original_storage_read
      p st addr upd upd_final ac key value original status Hacct Hset).

  Lemma mapModelLookup_replace_current_account_update_head
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc retp : ptr)
      (old_upd upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (retp, old_upd) :: tl) ->
    mapModelLookup (replace_current_account_update addr upd cur) addr =
      Some (loc, (retp, upd) :: tl).
  Proof using.
    unfold mapModelLookup, replace_current_account_update.
    induction cur as [| [a [loc0 updates0]] cur IH]; simpl.
    {
      rewrite lookup_empty.
      discriminate.
    }
    destruct (bool_decide (a = addr)) eqn:Ha.
    {
      apply bool_decide_eq_true in Ha.
      subst a.
      cbn.
      intro Hlookup.
      rewrite lookup_insert in Hlookup.
      destruct (decide (addr = addr)) as [_|Hcontra] in Hlookup;
        [|contradiction Hcontra; reflexivity].
      inversion Hlookup; subst; clear Hlookup.
      cbn.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_|Hcontra];
        [|contradiction Hcontra; reflexivity].
      reflexivity.
    }
    {
      apply bool_decide_eq_false in Ha.
      cbn.
      intro Hlookup.
      rewrite lookup_insert_ne in Hlookup; [| exact Ha].
      rewrite lookup_insert_ne; [| exact Ha].
      exact (IH Hlookup).
    }
  Qed.

  Lemma state_current_account_state_post_updated_lookup
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (retp : ptr) (upd : UpdatedAccountState) :
    state_current_account_state_post st addr st_current retp upd ->
    exists cur_loc tl,
      mapModelLookup
        (replace_current_account_update addr upd (newStates st_current)) addr =
      Some (cur_loc, (retp, upd) :: tl).
  Proof using.
    unfold state_current_account_state_post.
    destruct (mapModelLookup (newStates st) addr)
      as [[cur_loc updates] |] eqn:Hlookup.
    {
      destruct updates as [| [upd_loc upd0] tl]; simpl; [tauto |].
      intros [-> [-> ->]].
      exists cur_loc, tl.
      eapply mapModelLookup_replace_current_account_update_head.
      exact Hlookup.
    }
    {
      intros [orig_loc [orig_final [orig_state [cur_loc [Horig [-> ->]]]]]].
      exists cur_loc, [].
      unfold mapModelLookup, replace_current_account_update.
      simpl.
      destruct (bool_decide (addr = addr)) eqn:Haddr.
      {
        simpl.
        rewrite lookup_insert.
        cbn.
        destruct (decide (addr = addr)) as [_|Hcontra];
          [|contradiction Hcontra; reflexivity].
        reflexivity.
      }
      {
        apply bool_decide_eq_false in Haddr.
        exfalso.
        apply Haddr.
        reflexivity.
      }
    }
  Qed.

  Lemma state_current_account_state_post_blockStatePtr
      (st st_final : StateM) (addr : evmopsem.evm.address)
      (retp : ptr) (upd : UpdatedAccountState) :
    state_current_account_state_post st addr st_final retp upd ->
    blockStatePtr st_final = blockStatePtr st.
  Proof using.
    unfold state_current_account_state_post.
    destruct (mapModelLookup (newStates st) addr)
      as [[cur_loc updates] |] eqn:Hlookup.
    {
      destruct updates as [| [upd_loc upd0] tl]; simpl; [tauto |].
      intros [-> [-> ->]].
      reflexivity.
    }
    {
      intros [orig_loc [orig_final [orig_state [cur_loc [Horig [-> ->]]]]]].
      reflexivity.
    }
  Qed.

  Lemma state_original_account_state_post_noop_of_is_some
      (orig orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr) (orig_state : AssumedPreTxAccountState) :
    is_Some (mapModelLookup orig addr) ->
    state_original_account_state_post orig addr orig_final loc orig_state ->
    orig_final = orig.
  Proof using.
    unfold state_original_account_state_post.
    destruct (mapModelLookup orig addr) as [[old_loc old_state] |].
    {
      intros _ [-> _].
      reflexivity.
    }
    {
      intros [[x Hlookup]] _.
      discriminate.
    }
  Qed.

  Lemma validModel_subset_local (st : StateM) :
    validModel st ->
    map fst (newStates st) ⊆ map fst (preTxAssumedState st).
  Proof using.
    intros [Hsub _].
    exact Hsub.
  Qed.

  Lemma validModel_original_lookup_of_current_lookup
      (st : StateM) (addr : evmopsem.evm.address)
      (loc : ptr) (updates : list (ptr * UpdatedAccountState)) :
    validModel st ->
    mapModelLookup (newStates st) addr = Some (loc, updates) ->
    is_Some (mapModelLookup (preTxAssumedState st) addr).
  Proof using.
    intros Hvalid Hlookup.
    apply mapModelLookup_is_Some_of_mem.
    apply (validModel_subset_local st Hvalid).
    apply mapModelLookup_is_Some_implies_mem.
    eexists.
    exact Hlookup.
  Qed.

  Lemma validModel_original_lookup_of_replaced_current_lookup
      (st : StateM) (addr : evmopsem.evm.address)
      (upd : UpdatedAccountState) (loc retp : ptr)
      (tl : list (ptr * UpdatedAccountState)) :
    validModel (state_update_current_account st addr upd) ->
    mapModelLookup (replace_current_account_update addr upd (newStates st)) addr =
      Some (loc, (retp, upd) :: tl) ->
    is_Some (mapModelLookup (preTxAssumedState st) addr).
  Proof using.
    intros Hvalid Hlookup.
    pose proof
      (validModel_original_lookup_of_current_lookup
         (state_update_current_account st addr upd) addr loc ((retp, upd) :: tl)
         Hvalid) as Hsome.
    simpl in Hsome.
    exact (Hsome Hlookup).
  Qed.

  Lemma state_set_storage_post_update_current_account
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (key value : N) (status : Z)
      (retp : ptr) (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (original : N) :
    state_current_account_state_post st addr st_current retp upd ->
    postTxState upd = Some ac ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    state_set_storage_post st addr key value status
      (state_update_current_account st_current addr upd_final).
  Proof using.
    intros Hpost Hpost_tx Hset_storage.
    unfold state_set_storage_post.
    exists st_current, retp, upd, ac, original, upd_final.
    repeat split; eauto; reflexivity.
  Qed.

  Lemma state_set_storage_post_update_current_account_mpred
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (key value : N) (status : Z)
      (retp : ptr) (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (original : N) :
    (([| state_current_account_state_post st addr st_current retp upd |]
    ** [| postTxState upd = Some ac |]
    ** [| account_state_set_storage_post
           upd ac key value original status upd_final |]) : mpred)
    |--
    [| state_set_storage_post st addr key value status
         (state_update_current_account st_current addr upd_final) |].
  Proof using.
    go.
    assert (Hpost :
      state_set_storage_post st addr key value status
        (state_update_current_account st_current addr upd_final)).
    {
      eapply state_set_storage_post_update_current_account; eauto.
    }
    go.
  Qed.

  Definition state_set_storage_post_update_current_account_B
      st st_current addr key value status retp upd upd_final ac original :=
    [BWD] (state_set_storage_post_update_current_account_mpred
      st st_current addr key value status retp upd upd_final ac original).

  Definition state_set_storage_post_update_current_account_F
      st st_current addr key value status retp upd upd_final ac original :=
    [FWD] (state_set_storage_post_update_current_account_mpred
      st st_current addr key value status retp upd upd_final ac original).

  #[local] Hint Resolve validModel_set_storage_update
    validModel_set_storage_update_record_original_storage_read : pure.

  Lemma state_set_storage_post_record_original_storage_read
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (key value : N) (status : Z)
      (retp : ptr) (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (original : N) :
    state_current_account_state_post st addr st_current retp upd ->
    postTxState upd = Some ac ->
    account_state_set_storage_post
      upd ac key value original status upd_final ->
    state_set_storage_post st addr key value status
      (state_record_original_storage_read
         (state_update_current_account st_current addr upd_final)
         addr key original).
  Proof using.
    intros Hpost Hpost_tx Hset_storage.
    unfold state_set_storage_post.
    exists st_current, retp, upd, ac, original, upd_final.
    repeat split; eauto.
  Qed.

  Lemma state_set_storage_post_record_original_storage_read_mpred
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (key value : N) (status : Z)
      (retp : ptr) (upd upd_final : UpdatedAccountState)
      (ac : AccountM) (original : N) :
    (([| state_current_account_state_post st addr st_current retp upd |]
    ** [| postTxState upd = Some ac |]
    ** [| account_state_set_storage_post
           upd ac key value original status upd_final |]) : mpred)
    |--
    [| state_set_storage_post st addr key value status
         (state_record_original_storage_read
            (state_update_current_account st_current addr upd_final)
            addr key original) |].
  Proof using.
    go.
    assert (Hpost :
      state_set_storage_post st addr key value status
        (state_record_original_storage_read
           (state_update_current_account st_current addr upd_final)
           addr key original)).
    {
      eapply state_set_storage_post_record_original_storage_read; eauto.
    }
    go.
  Qed.

  Definition state_set_storage_post_record_original_storage_read_B
      st st_current addr key value status retp upd upd_final ac original :=
    [BWD] (state_set_storage_post_record_original_storage_read_mpred
      st st_current addr key value status retp upd upd_final ac original).

  Definition state_set_storage_post_record_original_storage_read_F
      st st_current addr key value status retp upd upd_final ac original :=
    [FWD] (state_set_storage_post_record_original_storage_read_mpred
      st st_current addr key value status retp upd upd_final ac original).

  #[local] cpp.spec "monad::bytes32_t::bytes32_t()"
    from state_cpp.source inline.

  Lemma prf_state_set_storage :
    verify[state_cpp.source] state_set_storage_spec.
  Proof using MODd.
    verify_spec.
    match goal with
    | H : exists ac, _ |- _ =>
        destruct H as [ac Hrecent]
    end.
    go.
    go using evmc_bytes32R_zero_fold_B, evmc_bytes32R_zero_unfold_F.
    iExists preBlockState, bs, qb.
    go.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd |- _ =>
        pose proof
          (set_nonce_proof.state_current_account_state_post_recent_some
             st st_current addr retp upd ac Hpost Hrecent)
          as Hacct;
        rename Hpost into Hcurrent_post;
        rename st_current into st_after_current;
        rename retp into current_accountp;
        rename upd into upd_current
    end.
    rewrite Hacct.
    cbv delta [AccountStateRcore].
    go.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd |- _ =>
        pose proof
          (check_min_original_balance_proof.AccountStateRcore_separated_fold
             retp 1 (Some ac) transient_map) as Hfold_current_core_ent;
        wapply Hfold_current_core_ent
    end.
    go.
    rewrite <- Hacct.
    go using use_current_update_forall_wand_F.
    match goal with
    | Hvalid : validModel
        (state_update_current_account
           st_after_current addr upd_current) |- _ =>
        rename Hvalid into Hvalid_current
    end.
    pose proof
      (state_current_account_state_post_blockStatePtr
         _ _ _ _ _ Hcurrent_post)
      as Hblock_state.
    rewrite Hblock_state.
    iExists _, preBlockState, bs, qb.
    go.
    match goal with
    | Horig : state_original_account_state_post ?orig addr ?orig_final ?loc ?orig_state |- _ =>
        pose proof
          (state_original_account_state_post_lookup
             orig orig_final addr loc orig_state Horig)
          as Horig_lookup;
        rename loc into orig_entryp;
        rename orig_state into orig_account_state
    end.
    go using borrow_original_account_payload_F, reinsert_original_account_payload_B.
    unfold OriginalAccountStateR, AccountStateRcore.
    iExists N, _, bytes32R, key,
      N, 1%Qp, (fun q => bytes32R (cQp.mut q)), qkey,
      (preTxStorage orig_account_state).
    go using StorageMapR_unfold_F.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd |- _ =>
        destruct
          (state_current_account_state_post_updated_lookup
             st st_current addr retp upd Hpost)
          as [cur_loc [cur_tl Hcur_lookup]]
    end.
    match goal with
    | Hvalid : validModel (state_update_current_account ?st0 addr ?upd0),
      Hcur : mapModelLookup ?cur addr = Some (?cur_loc0, (?retp, ?upd_head) :: ?cur_tl0),
      Horig : state_original_account_state_post
                (preTxAssumedState ?st0) addr ?orig_final ?orig_loc
                ?orig_state |- _ =>
        let Horig_some := fresh "Horig_some" in
        let Horig_noop := fresh "Horig_noop" in
        pose proof
          (validModel_original_lookup_of_replaced_current_lookup
             st0 addr upd0 cur_loc0 retp cur_tl0 Hvalid Hcur)
          as Horig_some;
        pose proof
          (state_original_account_state_post_noop_of_is_some
             (preTxAssumedState st0) orig_final addr orig_loc orig_state
             Horig_some Horig)
          as Horig_noop;
        subst orig_final
    end.
    go using borrow_current_payload_F.
    assert (Hzero :
      original_value_addr |-> structR "monad::bytes32_t" 1$m **
      original_value_addr ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
        |-> evmc_bytes32R 1
      |-- original_value_addr |-> bytes32R 1 0).
    {
      Local Transparent bytes32R evmc_bytes32R.
      unfold bytes32R, evmc_bytes32R.
      go.
      Local Opaque bytes32R evmc_bytes32R.
    }
    pose (Hzero_B := [BWD] Hzero).
    wp_if.
    {
      intro Hnonnull_it.
      replace (asbool (_x_10 = nullptr)) with false by
        exact (eq_sym (bool_decide_false (_x_10 = nullptr) Hnonnull_it)).
      go.
      iExists 0%N.
      go using Hzero_B, evmc_bytes32R_zero_fold_B.
      iExists upd_current.
      iExists ac.
      go using
        use_wand_local_r_F,
        UpdatedAccountStateR_separated_fold_B,
        StorageMapR_fold_B,
        OriginalAccountStateR_separated_fold_B,
        reinsert_original_account_payload_B,
        reinsert_updated_current_head_payload_B,
        StateCodeMapR_set_storage_update_F,
        state_set_storage_post_update_current_account_F.
      rewrite <-
        (current_spine_map_replace_current_account_update
           (newStates st_after_current) addr upd_current t).
      iExists st_after_current, current_accountp, upd_current, ac, value, t.
      match goal with
      | Hset : account_state_set_storage_post
                 upd_current ?ac0 ?key0 ?written ?original ?status ?upd_final |- _ =>
          pose proof
            (state_set_storage_post_update_current_account
               st st_after_current addr key0 written status current_accountp
               upd_current upd_final ac0 original Hcurrent_post Hacct Hset)
      end.
      go.
    }
    {
      rewrite Hacct.
      cbv delta [AccountStateRcore].
      go using optional_specs.trivial_optional_some_split_F,
        check_min_original_balance_proof.unfoldAccountR.
      iExists ac.
      go.
      iExists (cQp.mut 1), (incarnation ac).
      go using optional_specs.trivial_optional_some_split_F,
        check_min_original_balance_proof.unfoldAccountR.
      iExists preBlockState, bs, qb.
      go.
      rename t into original_storage_value.
      iExists N, _, bytes32R,
        N, (fun q => bytes32R (cQp.mut q)),
        (key, original_storage_value), 1%Qp,
        (preTxStorage orig_account_state).
      go.
      iExists (bytes32R 1 key), (bytes32R 1 original_storage_value).
      go.
      iExists N, bytes32R,
        N, (fun q => bytes32R (cQp.mut q)),
        (preTxStorage orig_account_state),
        (immer_specs.immer_map_insert key original_storage_value
           (preTxStorage orig_account_state)).
      go.
      iExists N, N,
        bytes32R,
        (fun q => bytes32R (cQp.mut q)), 1%Qp,
        (immer_specs.immer_map_insert key original_storage_value
           (preTxStorage orig_account_state)).
      go.
      iExists 0%N.
      go using Hzero_B, evmc_bytes32R_zero_fold_B.
      iExists upd_current, ac.
      rewrite Hacct.
      pose proof
        (check_min_original_balance_proof.AccountStateRcore_separated_fold
           current_accountp 1 (Some ac) transient_map)
        as Hfold_current_core_ent_after_insert.
      wapply Hfold_current_core_ent_after_insert.
      go using
        use_wand_local_r_F,
        UpdatedAccountStateR_separated_fold_B,
        StateCodeMapR_set_storage_update_record_original_storage_read_F,
        state_set_storage_post_record_original_storage_read_F.
      rewrite <-
        (current_spine_map_replace_current_account_update
           (newStates st_after_current) addr upd_current t).
      match goal with
      | Hset : account_state_set_storage_post
                 upd_current ?ac0 ?key0 ?written ?original ?status ?upd_final |- _ =>
          pose proof
            (validModel_set_storage_update_record_original_storage_read
               st_after_current addr upd_current upd_final ac0 key0 written
               original status Hacct Hvalid_current Hset);
          pose proof
            (state_set_storage_post_record_original_storage_read
               st st_after_current addr key0 written status current_accountp
               upd_current upd_final ac0 original Hcurrent_post Hacct Hset)
      end.
      pose (Hfold_original_account_after_insert_B :=
        OriginalAccountStateR_separated_fold_B
          (orig_entryp ,,
           pairSndOffset "monad::Address" "monad::OriginalAccountState")
          1
          (record_original_storage_read_assumed
             orig_account_state key original_storage_value)
          _transient_map_0).
      rewrite
        (original_spine_model_record_original_storage_read_map
           (preTxAssumedState st_after_current)
           addr key original_storage_value).
      go using
        use_wand_local_r_F,
        StorageMapR_fold_B,
        Hfold_original_account_after_insert_B,
        reinsert_recorded_original_storage_read_payload_B,
        reinsert_updated_current_head_payload_B,
        StateCodeMapR_set_storage_update_record_original_storage_read_F,
        state_set_storage_post_record_original_storage_read_F.
      iExists st_after_current, current_accountp, upd_current, ac,
        original_storage_value, t.
      go.
    }
  Qed.
End with_Sigma.
