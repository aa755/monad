Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve
    wp_init_implicit_B_local
    wp_init_implicit_char_array_local_B
    wp.wp_init_initlist_struct_B
    wp_operand_initlist_default_B
    wp_init_default_array_B : sl_opacity.

  Lemma fupd_emp_frame (E1 E2 : coPset) (P : mpred) :
    (|={E1,E2}=> emp) ** P |-- |={E1,E2}=> P.
  Proof.
    etransitivity.
    {
      apply fupd_frame_r.
    }
    apply fupd_mono.
    rewrite bi.emp_sep.
    reflexivity.
  Qed.

  Definition fupd_emp_frame_B E1 E2 P :=
    [BWD] (fupd_emp_frame E1 E2 P).

  Definition primR_anyR_F ty q v :=
    [FWD] (primR_anyR ty q v).

  Definition blake3_const_key_words_to_bytes_F
      p q words Hlen Hrange :=
    [FWD]
      (byte_bridges.blake3_const_key_words_to_bytes
         p q words Hlen Hrange storage_page_cpp_little_endian).

  Definition blake3_const_key_words_from_bytes_B
      p q words Hlen Hrange :=
    [BWD]
      (byte_bridges.blake3_const_key_words_from_bytes
         p q words Hlen Hrange storage_page_cpp_little_endian).

  Definition uint32_array8_uninit_to_byte_any_F p :=
    [FWD] (byte_bridges.uint32_array8_uninit_to_byte_any p).

  Lemma byte_arrayLR_to_arrayR
      (base : ptr) q bytes len :
    length bytes = Z.to_nat len ->
    (0 <= len)%Z ->
    base |-> arrayLR Tuchar 0 len
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes
    |--
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes.
  Proof using CU MODd Sigma.
    intros Hlen Hlen_nonneg.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite lengthZ_correct Hlen.
    replace (Z.of_nat (Z.to_nat len)) with len by lia.
    go.
  Qed.

  Lemma mip8_leaf_domain_block_byte_values :
    blake3_impl_h_specs.bytes64_byte_values
      blake3model.mip8_leaf_domain_block =
    blake3specs.storage_leaf_domain_key_values ++
    replicateN 32 (Vint 0).
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma mip8_leaf_domain_blockR (base : ptr) :
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      blake3specs.storage_leaf_domain_key_values
    ** base |-> arrayLR Tuchar 32 64
      (fun byte : val => primR Tuchar 1$m byte)
      (replicateN 32 (Vint 0))
    |-- base |-> blake3specs.Blake3BlockR 1
      blake3model.mip8_leaf_domain_block.
  Proof using CU MODd Sigma.
    unfold blake3specs.Blake3BlockR,
      blake3_impl_h_specs.Blake3BlockR,
      blake3specs.BlockR,
      blake3_impl_h_specs.BlockR.
    rewrite mip8_leaf_domain_block_byte_values.
    rewrite <-
      (@array_sliceR_app'
         _ _ _ _ val Tuchar base 0 32 64
         (fun byte : val => primR Tuchar 1$m byte)
         blake3specs.storage_leaf_domain_key_values
         (replicateN 32 (Vint 0))
         ltac:(vm_compute; reflexivity)
         ltac:(lia)
         ltac:(lia)).
    apply byte_arrayLR_to_arrayR.
    {
      vm_compute.
      reflexivity.
    }
    {
      lia.
    }
  Qed.

  Definition mip8_leaf_domain_blockR_F base :=
    [FWD] (mip8_leaf_domain_blockR base).

  Lemma uchar_arrayR_values_forget (base : ptr) values :
    base |-> arrayR Tuchar (primR Tuchar 1$m) values |--
    base |-> arrayLR Tuchar 0 (Z.of_nat (length values))
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN (N.of_nat (length values)) ()).
  Proof using CU MODd Sigma.
    revert base.
    induction values as [| value rest IH]; intro base.
    {
      go using _at_arrayR_nil_F.
    }
    {
      cbn [length].
      rewrite Nat2Z.inj_succ.
      rewrite Nat2N.inj_succ.
      replace (N.succ (N.of_nat (length rest)))
        with (N.of_nat (length rest) + 1)%N by lia.
      rewrite replicateN_succ.
      pose (IH_F := [FWD] (IH (base .[ Tuchar ! 1 ]))).
      rewrite array_sliceR_cons.
      go using _at_arrayR_cons_F, IH_F.
      rewrite (offset_ptr_sub_0 base Tuchar).
      2: {
        apply has_size.
        exact _.
      }
      go using primR_anyR_F.
    }
  Qed.

  Lemma bytes64_byte_values_length block :
    length (blake3_impl_h_specs.bytes64_byte_values block) = 64%nat.
  Proof.
    unfold blake3_impl_h_specs.bytes64_byte_values,
      blake3_impl_h_specs.bytes32_byte_values.
    rewrite List.length_app.
    change (length (exec_specs.bytes32_be_values
                      (model.bytes32_to_N (fst block)))) with 32%nat.
    change (length (exec_specs.bytes32_be_values
                      (model.bytes32_to_N (snd block)))) with 32%nat.
    reflexivity.
  Qed.

  Lemma blake3_blockR_to_any_arrayLR
      (base : ptr) block :
    base |-> blake3specs.Blake3BlockR 1 block
    |--
    base |-> arrayLR Tuchar 0 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateZ 64 ()).
  Proof using CU MODd Sigma.
    unfold blake3specs.Blake3BlockR,
      blake3_impl_h_specs.Blake3BlockR,
      blake3specs.BlockR,
      blake3_impl_h_specs.BlockR.
    rewrite (uchar_arrayR_values_forget
               base
               (blake3_impl_h_specs.bytes64_byte_values block)).
    replace (Z.of_nat
               (length
                  (blake3_impl_h_specs.bytes64_byte_values block)))
      with 64%Z.
    2: {
      rewrite bytes64_byte_values_length.
      reflexivity.
    }
    replace (replicateN
               (N.of_nat
                  (length
                     (blake3_impl_h_specs.bytes64_byte_values block)))
               ())
      with (replicateZ 64 ()).
    2: {
      rewrite bytes64_byte_values_length.
      reflexivity.
    }
    go.
  Qed.

  Definition blake3_blockR_to_any_arrayLR_F base block :=
    [FWD] (blake3_blockR_to_any_arrayLR base block).

  Lemma blake3_key_words_from_bytes_arrayR
      (p : ptr) q words :
    length words = 8%nat ->
    List.Forall model.blake3_word_in_range words ->
    p |-> typed_sliceR Tuint 0 8
    ** p |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar (cQp.mut q) byte)
      (blake3_impl_h_specs.blake3_cv_byte_values words)
    |--
    p |-> arrayR Tuint
      (fun word => uintR (cQp.mut q) (Z.of_N word)) words.
  Proof using CU MODd Sigma.
    intros Hlen Hrange.
    rewrite (byte_bridges.blake3_key_words_from_bytes
               p q words Hlen Hrange storage_page_cpp_little_endian).
    unfold blake3specs.Blake3KeyWordsR,
      blake3_impl_h_specs.Blake3KeyWordsR.
    go.
  Qed.

  Definition blake3_key_words_from_bytes_arrayR_F
      p q words Hlen Hrange :=
    [FWD]
      (blake3_key_words_from_bytes_arrayR
         p q words Hlen Hrange).

  Lemma blake3_key_words_to_const_half
      (p : ptr) words :
    length words = 8%nat ->
    p |-> blake3specs.Blake3KeyWordsR 1 words
    |--
    p |-> blake3specs.Blake3ConstKeyWordsR (1 / 2)%Qp words.
  Proof using CU MODd Sigma.
    intro Hlen.
    unfold blake3specs.Blake3KeyWordsR,
      blake3_impl_h_specs.Blake3KeyWordsR,
      blake3specs.Blake3ConstKeyWordsR,
      blake3_impl_h_specs.Blake3ConstKeyWordsR.
    transitivity
      (__at.body p (arrayR Tuint
         (fun word : N => uintR (cQp.mut 1%Qp) (Z.of_N word))
         words)).
    {
      go.
    }
    transitivity
      (__at.body p (arrayR Tuint
         (fun word : N =>
            uintR (cQp.const (1 / 2)%Qp) (Z.of_N word)) words)
       ** __at.body p (arrayR Tuint
            (fun word : N =>
               uintR (cQp.mut (1 / 2)%Qp) (Z.of_N word)) words)).
    {
      apply
        (cfractional_split
           (fun q =>
              p |-> arrayR Tuint
                (fun word : N => uintR q (Z.of_N word)) words)
           _
           (cQp.mut 1%Qp)
           (cQp.mut (1 / 2)%Qp)
           (cQp.const (1 / 2)%Qp)).
      unfold split_cfrac.SplitCFrac.
      rewrite <- cQp.mut_const'.
      rewrite Qp.div_2.
      reflexivity.
    }
    go.
  Qed.

  Definition blake3_key_words_to_const_half_F p words Hlen :=
    [FWD] (blake3_key_words_to_const_half p words Hlen).

  Lemma prf_storage_get_leaf_iv :
    verify[source] storage_get_leaf_iv_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    go.
    destruct ready.
    {
      rewrite /blake3specs.StorageLeafIvCacheR.
      cbn.
      go.
      proveAuAc.
      go.
      rewrite <- (bi.exist_intro initialized).
      go using sep_later_B, wp.wp_decls_nil_B, wp.wp_block_cons_B.
      match goal with
      | |- environments.envs_entails _ (|={?E1,?E2}=> ?P) =>
          rewrite <- (fupd_emp_frame E1 E2 P)
      end.
      go using sep_later_B, wp.wp_block_cons_B.
    }
    {
      rewrite /blake3specs.StorageLeafIvCacheR.
      cbn.
      go.
      proveAuAc.
      go.
      rewrite <- (bi.exist_intro uninitialized).
      go using sep_later_B, wp.wp_decls_nil_B, wp.wp_block_cons_B.
      match goal with
      | |- environments.envs_entails _ (|={?E1,?E2}=> ?P) =>
          rewrite <- (fupd_emp_frame E1 E2 P)
      end.
      go using wp_init_lambda_B.
      proveAuAc.
      go.
      rewrite <- (bi.exist_intro uninitialized).
      go using sep_later_B, wp.wp_decls_nil_B, wp.wp_block_cons_B.
      match goal with
      | |- environments.envs_entails _ (|={?E1,?E2}=> ?P) =>
          rewrite <- (fupd_emp_frame E1 E2 P)
      end.
      go using sep_later_B, wp.wp_block_cons_B.
      proveAuAc.
      go.
      rewrite <- (bi.exist_intro initializing).
      go using sep_later_B, wp.wp_decls_nil_B, wp.wp_block_cons_B.
      match goal with
      | |- environments.envs_entails _ (|={?E1,?E2}=> ?P) =>
          rewrite <- (fupd_emp_frame E1 E2 P)
      end.
      go.
      go.
      change (replicateN 64 (Vint 0))
        with (replicateN 32 (Vint 0) ++ replicateN 32 (Vint 0)).
      rewrite
        (@array_sliceR_app'
           _ _ _ _ val Tuchar block_addr 0 32 64
           (primR Tuchar 1$m)
           (replicateN 32 (Vint 0))
           (replicateN 32 (Vint 0))
           ltac:(vm_compute; reflexivity)
           ltac:(lia)
           ltac:(lia)).
      unfold blake3specs.StorageLeafIvInitInputsR,
        blake3specs.StorageLeafDomainKeyR,
        blake3specs.storage_leaf_domain_key_name.
      rewrite <- (bi.exist_intro (cQp.const qdomain)).
      rewrite <-
        (bi.exist_intro
          (map (fun b => Z.of_N (fin.to_N b)) blake3model.mip8_leaf_domain_bytes)).
      rewrite <- (bi.exist_intro (A := list unit) (replicateN 32 tt)).
      change (33 - 1)%Z with 32%Z.
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar qdomain$c) Vint).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
      have ? := _global_nonnull CU blake3specs.storage_leaf_domain_key_name.
      have ? := _global_nonnull CU "IV"%cpp_name.
      go using primR_anyR_F.
      rewrite <- (bi.exist_intro (cQp.const qiv)).
      rewrite <-
        (bi.exist_intro
           (map (fun b => Z.of_N (fin.to_N b))
              (model.blake3_cv_bytes model.blake3_iv_words))).
      rewrite <- (bi.exist_intro (A := list unit) (replicateN 32 tt)).
      go using
        (blake3_const_key_words_to_bytes_F
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (uint32_array8_uninit_to_byte_any_F
           (_global
              blake3specs.storage_get_leaf_iv_static_iv_name)).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar qiv$c) Vint).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
      go.
      change (Z.to_N (33 - 1)) with 32%N in *.
      rewrite <- (bi.exist_intro model.blake3_iv_words).
      rewrite <-
        (bi.exist_intro blake3model.mip8_leaf_domain_block).
      go using
        (blake3_key_words_from_bytes_arrayR_F
           (_global blake3specs.storage_get_leaf_iv_static_iv_name)
           1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (mip8_leaf_domain_blockR_F block_addr).
      go using
        (blake3_blockR_to_any_arrayLR_F
           block_addr blake3model.mip8_leaf_domain_block).
      proveAuAc.
      rewrite <- (bi.exist_intro initializing).
      go.
      match goal with
      | |- environments.envs_entails _ (|={?E1,?E2}=> ?P) =>
          rewrite <- (fupd_emp_frame E1 E2 P)
      end.
      go using sep_later_B, wp.wp_decls_nil_B, wp.wp_block_cons_B.
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_to_const_half_F
           (_global blake3specs.storage_get_leaf_iv_static_iv_name)
           blake3model.mip8_leaf_iv_words
           blake3model.mip8_leaf_iv_words_length).
    }
  Qed.
End with_Sigma.
