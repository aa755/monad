Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.

Transparent
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve
    wp_init_implicit_B_local
    wp.wp_init_initlist_struct_B
    wp_operand_initlist_default_B
    wp_init_default_array_B
    wp_init_bytes32_array_zero_local_B
    observeStoragePageLength_F : sl_opacity.
  #[local] Hint Opaque StoragePageR : sl_opacity.
  Opaque root page_slots_model page_subtree_root_model
    pair_bitmap_word pair_bitmap_prefix.

  Lemma bytes32R_to_raw_digest_field
      (base : ptr) (q : cQp.t) digest :
    base |-> exec_specs.bytes32R q
      (blake3model.bytes32_to_N digest)
    |--
    base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
      o_field CU "evmc_bytes32::bytes"
      |-> type_ptrR (Tarray Tuchar 32)
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
      o_field CU "evmc_bytes32::bytes"
      |-> blake3specs.RawDigestBytesR q digest
    ** base |-> structR "monad::bytes32_t"%cpp_name q
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
      |-> structR "evmc_bytes32"%cpp_name q.
  Proof using CU MODd Sigma.
    rewrite /exec_specs.bytes32R
      /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR
      /blake3specs.RawDigestBytesR
      /blake3specs.bytes32_byte_values
      /blake3_impl_h_specs.bytes32_byte_values
      /exec_specs.bytes32_be_values.
    go.
  Qed.

  Definition bytes32R_to_raw_digest_field_F base q digest :=
    [FWD] (bytes32R_to_raw_digest_field base q digest).

  Lemma type_ptrR_nonnull (base : ptr) ty :
    base |-> type_ptrR ty
    |-- base |-> type_ptrR ty ** [| base <> nullptr |].
  Proof using CU MODd Sigma.
    rewrite <- (_at_nonnullR base).
    rewrite <- _at_sep.
    exact (observe_elim_rep nonnullR (type_ptrR ty) base
             (type_ptrR_observe_nonnull ty)).
  Qed.

  Definition type_ptrR_nonnull_F base ty :=
    [FWD] (type_ptrR_nonnull base ty).

  Lemma raw_digest_field_to_bytes32R
      (base : ptr) (q : cQp.t) digest :
    base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
      o_field CU "evmc_bytes32::bytes"
      |-> blake3specs.RawDigestBytesR q digest
    ** base |-> structR "monad::bytes32_t"%cpp_name q
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
      |-> structR "evmc_bytes32"%cpp_name q
    |--
    base |-> exec_specs.bytes32R q
      (blake3model.bytes32_to_N digest).
  Proof using CU MODd Sigma.
    rewrite /exec_specs.bytes32R
      /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR
      /blake3specs.RawDigestBytesR
      /blake3specs.bytes32_byte_values
      /blake3_impl_h_specs.bytes32_byte_values
      /exec_specs.bytes32_be_values.
    rewrite (only_provable_True _
               (blake3model.bytes32_to_N_range digest)).
    go.
  Qed.

  Definition raw_digest_field_to_bytes32R_B base q digest :=
    [BWD] (raw_digest_field_to_bytes32R base q digest).

  Definition raw_digest_field_to_bytes32R_F base q digest :=
    [FWD] (raw_digest_field_to_bytes32R base q digest).

  Lemma prf_page_commit :
    verify[source] page_commit_spec.
  Proof using MODd.
    verify_spec.
    (* The spec uses [commitment.v] through the centralized BLAKE3 boundary in
       [blake3model.v].  [StoragePageR] has a fractional instance, so the
       initial const method call can borrow the page without exposing the field
       array by hand. *)
    name_locals.
    match goal with
    | Hlen : length page = page_slot_count |- _ =>
        pose proof Hlen as Hpage_len
    end.
    go.
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro page).
    go.
    wp_if.
    {
        intro Hempty_branch.
        replace (~~ ready && ~~ true) with false in *
          by (destruct ready; reflexivity).
		        unfold blake3specs.StorageLeafDomainKeyMaybeR.
		        pose proof
		          (page_commit_root_empty page Hpage_len Hempty_branch)
		          as Hpage_root.
        go1 using wp_seq_B.
        go1 using invoke.wp_invoke_O_unmaterialized_C.
        go1 using eval.eval_l_nd_2_B.
        go1 using wp.wp_f2p_gvar_B.
        go1 using eval.UNSOUND_eval_nd_B.
        rewrite <- (wp_operand_int_zero source _ _).
        go1 using simplify.simplify_intro_B.
        go1 using wp_null_B.
        rewrite <- (bi.exist_intro None).
        rewrite /blake3specs.SealRootArgR.
        go.
        rewrite Hempty_branch.
        replace (~~ ready && ~~ true) with false
          by (destruct ready; reflexivity).
        unfold blake3specs.StorageLeafDomainKeyMaybeR.
        go.
    }
    intro Hnonempty_branch.
    {
        go.
        rewrite <- (bi.exist_intro q).
        rewrite <- (bi.exist_intro page).
        go.
        rewrite <- (bi.exist_intro q).
        rewrite <- (bi.exist_intro page).
        go.
        replace (~~ ready && true) with (~~ ready) in *
          by (destruct ready; reflexivity).
        rewrite <- (bi.exist_intro ready).
        rewrite <- (bi.exist_intro qleafcache).
        rewrite <- (bi.exist_intro qleafiv).
        rewrite <- (bi.exist_intro qdomain).
        rewrite <- (bi.exist_intro q).
        rewrite <- (bi.exist_intro page).
        go.
        rewrite <-
          (bi.exist_intro (Some (page_subtree_root_model page))).
        rewrite /blake3specs.SealRootArgR.
        go using bytes32R_to_raw_digest_field_F, type_ptrR_nonnull_F.
        go using raw_digest_field_to_bytes32R_B, type_ptrR_nonnull_F.
        rewrite Hnonempty_branch.
        replace (~~ ready && ~~ false) with (~~ ready)
          by (destruct ready; reflexivity).
        rewrite <-
          (bi.exist_intro
             (blake3model.bytes32_to_N
                (page_subtree_root_model page))).
        rewrite
          (page_commit_root_nonempty
             page Hpage_len Hnonempty_branch).
        go using raw_digest_field_to_bytes32R_F.
    }
    Unshelve.
    all: try solve [go | lia | reflexivity].
  Qed.
End with_Sigma.

#[global] Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R.
#[global] Hint Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R : sl_opacity.
