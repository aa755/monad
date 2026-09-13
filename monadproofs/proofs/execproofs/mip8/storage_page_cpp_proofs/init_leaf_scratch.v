Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.blake3specs.
Require Import monad.proofs.libspecs.blake3.blake3_impl_h_specs.
Require monad.proofs.libspecs.blake3.model.
Require Import skylabs.lang.cpp.logic.object_repr.
Require Import skylabs.auto.cpp.hints.cast.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.init_leaf_scratch_support.
Import linearity.

Set Warnings "+sl-impossible-patterns".

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve leaf_loop_state_init leaf_loop_state_step : pure.

  #[local] Hint Resolve
    wp_init_implicit_B_local
    wp.wp_init_initlist_struct_B
    wp_operand_initlist_default_B
    wp_init_default_array_B
    wp_init_bytes32_array_zero_local_B
    observeStoragePageLength_F
    observeStoragePageTypePtr_F
    leaf_index_arrayR_empty_pack_F
    type_ptr_reference_to_B_local
    type_ptr_elim_type_ptr_C
    type_ptr_elim_reference_to_C
    typed_sliceR_elim_type_ptr_C
    typed_sliceR_elim_reference_to_C
    UNSAFE_read_prim_cancel : sl_opacity.
  #[local] Hint Opaque
    StoragePageR ScratchR init_leaf_scratch_model
    leaf_index_arrayR leaf_inputs_arrayR
    leaf_indices leaf_loop_indices leaf_clear_lowbit
    leaf_loop_state : sl_opacity.
  Opaque
    blake3_impl_h_specs.RawDigestBytesR
    blake3_impl_h_specs.byte_values
    blake3_impl_h_specs.bytes32_byte_values
    blake3_impl_h_specs.bytes64_byte_values
    blake3_impl_h_specs.blake3_cv_byte_values
    blake3_impl_h_specs.output_word_byte_values
    blake3_impl_h_specs.output_words_byte_values
    blake3_impl_h_specs.Blake3KeyWordsR
    blake3_impl_h_specs.Blake3ConstKeyWordsR
    blake3_impl_h_specs.blake3_hash_many_call_params
    blake3_impl_h_specs.blake3_hash_many_outputs_from_params
    blake3_impl_h_specs.blake3_flags_of_Z
    blake3_impl_h_specs.blake3_flag_is_set
    blake3_impl_h_specs.all_blake3_flags
    blake3_impl_h_specs.BlockR
    blake3_impl_h_specs.Blake3BlockR
    blake3_impl_h_specs.Blake3InputBlocksR
    blake3_impl_h_specs.Blake3InputBlocksDataR
    blake3_impl_h_specs.Blake3OutputBytesR
    blake3specs.blake3_hash_many_outputs
    blake3model.mip8_leaf_iv_words
    blake3model.leaf_hash_many_params
    blake3model.merge_hash_many_params
    blake3model.params_for_hash_mode.
  #[local] Hint Opaque
    blake3_impl_h_specs.RawDigestBytesR
    blake3_impl_h_specs.byte_values
    blake3_impl_h_specs.bytes32_byte_values
    blake3_impl_h_specs.bytes64_byte_values
    blake3_impl_h_specs.blake3_cv_byte_values
    blake3_impl_h_specs.output_word_byte_values
    blake3_impl_h_specs.output_words_byte_values
    blake3_impl_h_specs.Blake3KeyWordsR
    blake3_impl_h_specs.Blake3ConstKeyWordsR
    blake3_impl_h_specs.blake3_hash_many_call_params
    blake3_impl_h_specs.blake3_hash_many_outputs_from_params
    blake3_impl_h_specs.blake3_flags_of_Z
    blake3_impl_h_specs.blake3_flag_is_set
    blake3_impl_h_specs.all_blake3_flags
    blake3_impl_h_specs.BlockR
    blake3_impl_h_specs.Blake3BlockR
    blake3_impl_h_specs.Blake3InputBlocksR
    blake3_impl_h_specs.Blake3InputBlocksDataR
    blake3_impl_h_specs.Blake3OutputBytesR
    blake3specs.blake3_hash_many_outputs
    blake3model.mip8_leaf_iv_words
    blake3model.leaf_hash_many_params
    blake3model.merge_hash_many_params
    blake3model.params_for_hash_mode : sl_opacity.
  Transparent
    blake3_impl_h_specs.Blake3OutputWordsR
    blake3specs.RawDigestBytesR
    blake3specs.bytes32_byte_values
    blake3specs.bytes64_byte_values
    blake3specs.BlockR
    blake3specs.Blake3BlockR
    blake3specs.Blake3InputBlocksR
    blake3specs.Blake3InputBlocksDataR
    blake3specs.Blake3KeyWordsR
    blake3specs.Blake3ConstKeyWordsR
    blake3specs.Blake3OutputWordsR
    blake3specs.Blake3OutputBytesR.
  Opaque
    exec_specs.bytes32_be_values_from
    exec_specs.bytes32_be_values
    exec_specs.evmc_bytes32_wordR
    exec_specs.bytes32R
    exec_specs.evmc_bytes32R.
  #[local] Hint Opaque
    exec_specs.bytes32_be_values_from
    exec_specs.bytes32_be_values
    exec_specs.evmc_bytes32_wordR
    exec_specs.bytes32R
    exec_specs.evmc_bytes32R : sl_opacity.
  Opaque
    countr_zero64
    countr_zero_fuel
    popcount64
    popcount_fuel.
  #[local] Hint Opaque
    countr_zero64
    countr_zero_fuel
    popcount64
    popcount_fuel : sl_opacity.

  Lemma storage_leaf_iv_init_inputs_split ready qiv qdomain :
    type_ptr (Tarray Tuint 8) (_global "IV") **
    _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
      qiv model.blake3_iv_words
    ** blake3specs.StorageLeafDomainKeyMaybeR (negb ready) qdomain
    |--
    blake3specs.StorageLeafIvInitInputsR
      (negb ready) qiv qdomain
    ** (if ready
        then
          _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
            qiv model.blake3_iv_words
          ** blake3specs.StorageLeafDomainKeyMaybeR false qdomain
        else emp).
  Proof using.
    unfold blake3specs.StorageLeafIvInitInputsR,
      blake3specs.StorageLeafDomainKeyMaybeR.
    destruct ready; cbn [negb]; go.
  Qed.

  Definition storage_leaf_iv_init_inputs_split_F ready qiv qdomain :=
    [FWD] (storage_leaf_iv_init_inputs_split ready qiv qdomain).

	  Opaque
	    uninitR_anyR_F
    primR_anyR_F
    primR_input_ptr_anyR_store_F
    input_ptr_arrayR_forget_store_F
    input_ptr_null_arrayR_forget_store_at_F
    use_wand_local_r_F
    const_input_ptr_array_type_ptr_erase_F
    at_sep_F
    offsetR_sep_F
    at_offsetR_F
    leaf_index_tail_head_F
    leaf_inputs_tail_head_F
    leaf_inputs_uninit_tail_head_F
    arrayR_read_cell_with_wand_F
    arrayR_update_cell_with_wand_F
    wp_destroy_leaf_hash_outputs64_B
    leaf_inputs_prefix_forget_F
    leaf_inputs_split_anyR_array_F
    input_ptr_typed_slice_cell_type_F
    wp_destroy_leaf_inputs_array_split_cleanup_local_B
    anyR_arrayLR_destroy_run_local_B
    leaf_index_prefix_forget_F
    leaf_index_arrayR_forget_F
    destroy_run_leaf_index_array_cleanup_local_B
    observeStoragePageTypePtr_F
    type_ptr_leaf_pair_block_valid_F
    observeLeafPairBlockValid_F
    StoragePageR_unpack_F
    StoragePageR_pack_B
    observeScratchRLength_F
    leaf_index_arrayR_empty_pack_F
    leaf_inputs_arrayR_empty_pack_F
    leaf_inputs_arrayR_zero_pack_F
    leaf_inputs_arrayR_blake3_unpack_F
    leaf_inputs_arrayR_blake3_pack_B
    leaf_inputs_arrayR_blake3_inputs_pack_F
    leaf_inputs_arrayR_blake3_inputs_unpack_F
    leaf_input_blocks_ptr_array_to_input_ptrs_F
    leaf_inputs_prefix_arrayR_blake3_pack_F
    leaf_inputs_prefix_arrayR_blake3_pack_for_page_F
    leaf_pair_block_rows_blake3_unpack_F
    leaf_pair_block_rows_blake3_pack_F
    leaf_hash_many_post_pack_F
    leaf_arrays_step_pack_F.

  Lemma prf_init_leaves :
    verify[source] storage_init_leaves_spec.
  Proof using MODd.
    verify_spec.
    go using
      wp_init_initlist_prim_array_implicit_erased_B,
      default_initialize_array_of_arrays_uninit_local_B,
      leaf_pair_block_any_rows_init_F,
      array_sliceR_hints.wp_initlist_nil_C.
    go.
    name_locals.
    wp_for (fun _ =>
      Exists seen : list nat,
      Exists bits : N,
        [| leaf_loop_state pair_bitmap seen bits |]
        ** [| length old_scratch = page_pair_count |]
        ** pagep |-> StoragePageR q page
        ** scratchp |-> ScratchR 1 old_scratch
        ** valid_pairs_addr |-> arrayLR leaf_pair_block_ty 0 64
             leaf_pair_block_rowR (leaf_pair_block_rows page seen)
        ** inputs_addr |-> leaf_inputs_arrayR valid_pairs_addr seen
        ** indices_addr |-> leaf_index_arrayR seen
        ** n_addr |-> ulongR 1$m (N.of_nat (length seen))
        ** bits_addr |-> ulongR 1$m bits).
    rewrite <- (bi.exist_intro (@nil nat)).
	    go using
	      (observeScratchRLength_F scratchp 1 old_scratch),
	      (leaf_inputs_arrayR_empty_pack_F inputs_addr valid_pairs_addr),
	      (leaf_inputs_arrayR_zero_pack_F inputs_addr valid_pairs_addr).
	    go.
	    wp_if.
	    {
        intro Hloop.
        unfold leaf_index_arrayR, leaf_inputs_arrayR.
        lazymatch goal with
        | Hstate : leaf_loop_state ?bitmap ?seen ?bits |- _ =>
          let seen_loop := fresh "seen_loop" in
          let bits_loop := fresh "bits_loop" in
          set (seen_loop := seen) in *;
          set (bits_loop := bits) in *;
          pose proof
            (leaf_loop_state_active_length_lt
               bitmap seen_loop bits_loop Hstate Hloop)
            as Hseen_lt;
          pose proof
            (leaf_loop_state_bits_bound
               bitmap seen_loop bits_loop Hstate)
            as Hbits_bound
        end.
    pose proof
      (countr_zero64_nonzero_lt bits_loop Hloop Hbits_bound)
      as Hidx_lt.
    assert
      (Htail :
        SolveArith
          (Z.of_nat (length seen_loop) <= Z.of_nat (length seen_loop) /\
           Z.of_nat (length seen_loop) < 64)%Z)
      by (constructor; unfold page_pair_count in Hseen_lt; lia).
    go using (leaf_index_tail_head_F indices_addr seen_loop _ Htail).
    assert
      (Hslot_index :
        SolveArith
          (0 <= Z.of_N (countr_zero64 bits_loop) * 2 < 128)%Z)
      by (constructor; lia).
    assert
      (Hidx_nat :
        (N.to_nat (countr_zero64 bits_loop) < page_pair_count)%nat)
      by (unfold page_pair_count; lia).
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro page).
    go.
    lazymatch goal with
    | Hrange : (_ < 2 ^ 256)%N |- _ =>
        pose proof Hrange as Hleft_value_range
    end.
    go using
      (leaf_pair_block_rows_current_split_F
         valid_pairs_addr page seen_loop Hseen_lt).
    go using
      (leaf_pair_block_uninit_split_first_F
         (leaf_pair_bytesp valid_pairs_addr (length seen_loop))).
    rewrite
      (ptr_o_sub_N_of_nat
         leaf_pair_block_ty valid_pairs_addr (length seen_loop)).
    rewrite <- (bi.exist_intro (cQp.m 1)).
    rewrite <- (bi.exist_intro (Z.of_N <$>
      z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
        (Z.of_N (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)))).
    rewrite <- (bi.exist_intro (replicateN 32 ())).
    rewrite (array_sliceR_const_proper (replicateN 32 ())
      (replicateN 32 (Vint 0)) (i:=0) (j:=32) (R:=anyR Tuchar 1$m) eq_refl).
    rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
    rewrite (eq_trans
      (eq_sym (list_fmap_compose Z.of_N Vint
        (z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
          (Z.of_N (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)))))
      (eq_sym (bytes32_be_values_to_Z_to_bytes
        (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)))).
    go using
      (bytes32R_to_bytes_field_F
         _x_11
         1
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)).
    go using
      (typed_slice_nonempty_nonnull_B
         (_x_11 ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
           o_field CU "evmc_bytes32::bytes") Tuchar 32 ltac:(lia)),
      (bytes_field_to_bytes32R_B
         _x_11
         1
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)
         Hleft_value_range),
      (leaf_pair_block_left_from_first_copy_F
         (leaf_pair_bytesp valid_pairs_addr (length seen_loop))
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)
         Hleft_value_range).
    go using
      (bytes_field_to_bytes32R_B
         _x_11
         1
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)
         Hleft_value_range),
      (leaf_pair_block_left_from_first_copy_F
         (leaf_pair_bytesp valid_pairs_addr (length seen_loop))
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)
         Hleft_value_range),
      (leaf_pair_block_left_split_second_F
         (leaf_pair_bytesp valid_pairs_addr (length seen_loop))
         (blake3model.bytes32_of_N
            (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N))).
    rewrite <-
      (bi.exist_intro
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)).
    step using
      (bytes_field_to_bytes32R_B
         _x_11
         1
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)
         Hleft_value_range).
    step.
    step.
    step.
    step.
    go using
      (bytes32R_to_bytes_field_F
         _x_11
         1
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)),
      wp_operand_cast_integral_B,
      wp_operand_int_B.
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro page).
    go using observeStoragePageRange_F.
    lazymatch goal with
    | Hpage_range :
        List.Forall (fun word => (word < 2 ^ 256)%N) page,
      Hpage_len : length page = page_slot_count |- _ =>
        assert
          (Hright_value_range :
            (nth
               (Z.to_nat (2 * countr_zero64 bits_loop + 1))
               page 0 < 2 ^ 256)%N)
        by
          (apply List.Forall_forall with
             (x :=
                nth
                  (Z.to_nat (2 * countr_zero64 bits_loop + 1))
                  page 0%N) in Hpage_range;
           [ exact Hpage_range
           | apply nth_In;
             rewrite Hpage_len;
             unfold page_slot_count;
             lia ])
    end.
    rewrite
      (ptr_o_sub_N_of_nat
         leaf_pair_block_ty valid_pairs_addr (length seen_loop)).
    rewrite <- (bi.exist_intro (cQp.m 1)).
    rewrite <- (bi.exist_intro (Z.of_N <$>
      z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
        (Z.of_N (nth (Z.to_nat (2 * countr_zero64 bits_loop + 1)) page 0%N)))).
    rewrite <- (bi.exist_intro (replicateN 32 ())).
    rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
    rewrite (eq_trans
      (eq_sym (list_fmap_compose Z.of_N Vint
        (z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
          (Z.of_N (nth (Z.to_nat (2 * countr_zero64 bits_loop + 1)) page 0%N)))))
      (eq_sym (bytes32_be_values_to_Z_to_bytes
        (nth (Z.to_nat (2 * countr_zero64 bits_loop + 1)) page 0%N)))).
    go using
      (bytes32R_to_bytes_field_F
         _x_12
         1
         (nth
            (Z.to_nat (2 * countr_zero64 bits_loop + 1))
            page 0%N)).
    go using (typed_slice_nonempty_nonnull_B
      (_x_12 ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
        o_field CU "evmc_bytes32::bytes") Tuchar 32 ltac:(lia)).
    rewrite <-
      (bi.exist_intro
         (nth
            (Z.to_nat (2 * countr_zero64 bits_loop + 1))
            page 0%N)).
    go using
      (bytes_field_to_bytes32R_B
         _x_12
         1
         (nth
            (Z.to_nat (2 * countr_zero64 bits_loop + 1))
            page 0%N)
         Hright_value_range),
      (leaf_pair_block_full_from_offset_halves_F
         (leaf_pair_bytesp valid_pairs_addr (length seen_loop))
         (nth (Z.to_nat (2 * countr_zero64 bits_loop)) page 0%N)
         (nth
            (Z.to_nat (2 * countr_zero64 bits_loop + 1))
            page 0%N)
         Hleft_value_range Hright_value_range).
    rewrite
      (ptr_o_sub_N_of_nat
         Tuchar indices_addr (length seen_loop)).
    go.
    go using
      (leaf_inputs_tail_head_F
         inputs_addr seen_loop
         (replicateN
            (Z.to_N (64 - Z.of_nat (length seen_loop))) ()) Htail).
    rewrite
      (ptr_o_sub_N_of_nat
         blake3specs.blake3_input_ptr_store_ty
         inputs_addr (length seen_loop));
    go;
    replace (64 - Z.of_nat (length seen_loop) - 1)%Z
      with (64 - (Z.of_nat (length seen_loop) + 1))%Z by lia;
    assert
      (Hstep :
        leaf_loop_state pair_bitmap
          (List.app seen_loop [N.to_nat (countr_zero64 bits_loop)])
          (Z.to_N (Z.land bits_loop (bits_loop - 1))))
      by (rewrite leaf_clear_lowbit_machine;
          eapply leaf_loop_state_step; eauto);
    rewrite <-
      (bi.exist_intro
         (List.app seen_loop [N.to_nat (countr_zero64 bits_loop)]));
    replace
      (N.of_nat
         (length
            (List.app seen_loop [N.to_nat (countr_zero64 bits_loop)])))
      with (N.of_nat (length seen_loop) + 1)%N
      by (rewrite List.length_app; cbn [length]; lia);
    replace
      (Z.of_nat
         (length
            (List.app seen_loop [N.to_nat (countr_zero64 bits_loop)])) -
       1)%Z
      with (Z.of_nat (length seen_loop))
      by (rewrite List.length_app; cbn [length]; lia);
	    pose
	      (full_from_countr_zero :=
	         leaf_pair_block_full_from_countr_zero_F
	           (leaf_pair_bytesp valid_pairs_addr (length seen_loop))
	           page bits_loop Hleft_value_range Hright_value_range).
	    go using full_from_countr_zero.
	    pose
	      (pack_current_pair :=
	         leaf_pair_block_rows_current_pack_block_from_slice_F
	           valid_pairs_addr page seen_loop
	           (N.to_nat (countr_zero64 bits_loop)) Hseen_lt).
	    rewrite
	      (sliceZ_replicateZ_drop_one
	         (Z.of_nat (length seen_loop)) 64 ());
	    [ |
	      unfold page_pair_count in Hseen_lt;
	      lia
	    ].
	    go using pack_current_pair.
	    rewrite
	      (ptr_o_sub_N_of_nat
	         leaf_pair_block_ty valid_pairs_addr (length seen_loop)).
	    change (valid_pairs_addr
	              .[ leaf_pair_block_ty ! Z.of_nat (length seen_loop)])
	      with (leaf_pair_bytesp valid_pairs_addr (length seen_loop)).
		    pose
		      (pack_leaf_arrays :=
		         leaf_arrays_step_pack_current_tail_F
		           valid_pairs_addr inputs_addr indices_addr seen_loop
		           (countr_zero64 bits_loop)).
		    go using pack_leaf_arrays.
		    }
    {
      intro Hdone.
      match goal with
      | Hstate : leaf_loop_state pair_bitmap ?seen ?bits |- _ =>
          set (done_indices := seen) in *
      end.
      step.
      subst t.
      match goal with
      | Hstate : leaf_loop_state pair_bitmap done_indices 0 |- _ =>
          pose proof
            (leaf_loop_state_done pair_bitmap done_indices Hstate)
            as Hdone_indices_eq;
          pose proof
            (leaf_loop_state_bitmap_bound
               pair_bitmap done_indices 0 Hstate)
            as Hdone_bitmap_bound;
          pose proof Hstate as Hdone_state_forall;
          destruct Hdone_state_forall
            as [_ [Hdone_indices_bound [Hdone_len_plus _]]]
      end.
      assert (Hdone_indices_nodup : List.NoDup done_indices).
      {
        rewrite <- Hdone_indices_eq.
        apply leaf_indices_NoDup.
        exact Hdone_bitmap_bound.
      }
      assert (Hdone_len_le : (length done_indices <= 64)%nat).
      {
        unfold page_pair_count in Hdone_len_plus.
        lia.
      }
      rewrite <-
        (type_ptr_erase (Tarray (Tptr (Qconst Tuchar)) 64%N)
           inputs_addr).
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
	      set (input_ptrs := leaf_input_ptrs valid_pairs_addr done_indices).
      go using wp_operand_cast_integral_B, wp_operand_int_B.
      rewrite <-
        (type_ptr_erase (Tarray (Tptr (Qconst Tuchar)) 64%N)
           inputs_addr).
      go using wp_operand_cast_integral_B, wp_operand_int_B.
		      rewrite <- (bi.exist_intro ready).
		      rewrite <- (bi.exist_intro qleafcache).
		      rewrite <- (bi.exist_intro qleafiv).
		      rewrite <- (bi.exist_intro qiv).
		      rewrite <- (bi.exist_intro qdomain).
		      go using invoke.wp_invoke_O_unmaterialized_C.
	      go using
          (storage_leaf_iv_init_inputs_split_F ready qiv qdomain).
	      rewrite /blake3specs.StorageLeafIvCacheR.
		      rewrite <-
		        (bi.exist_intro true).
		      rewrite <-
		        (bi.exist_intro
		           (blake3specs.storage_leaf_iv_cache_qleaf_after
                  ready qleafiv)).
	      rewrite <- (bi.exist_intro 1%Qp).
	      rewrite <-
	        (bi.exist_intro blake3model.mip8_leaf_iv_words).
	      rewrite <-
	        (bi.exist_intro
	           (leaf_input_blocks valid_pairs_addr page done_indices)).
      set (old_outputs_prefix :=
        firstn (length done_indices) (replicateN 64 0%N)).
      assert (Hold_outputs_prefix_length :
        length old_outputs_prefix = length done_indices).
      {
        subst old_outputs_prefix.
        rewrite length_take_le.
        {
          reflexivity.
        }
	        {
	          rewrite rwdb.length_replicateN.
	          exact Hdone_len_le.
	        }
		      }
		      go.
		      rewrite <- (bi.exist_intro old_outputs_prefix).
	      lazymatch goal with
      | |- context[
             interp source 1
               (validP<"void"> Vvoid -* ?K)] =>
          set (hash_many_cont := K)
      end.
	      rewrite
	        (leaf_inputs_arrayR_blake3_unpack
	           inputs_addr valid_pairs_addr done_indices).
	      rewrite
	        (leaf_pair_block_rows_blake3_unpack
	           valid_pairs_addr page done_indices Hdone_len_le).
	      rewrite <-
	        (leaf_inputs_arrayR_blake3_inputs_pack
	           inputs_addr valid_pairs_addr 1 page done_indices) at 1.
      go using (leaf_output_words64_zero_pack_cells_F flat_out_addr).
	      go using
	        Hold_outputs_prefix_length,
	        (blake3_output_words_split_prefix_to_bytes_F
	           flat_out_addr (replicateN 64 0%N)
	           (length done_indices) Hdone_len_le).
      assert
	        (Hblocks_len :
	          length (leaf_input_blocks
	                    valid_pairs_addr page done_indices) =
	          length done_indices).
	      {
	        unfold leaf_input_blocks.
	        rewrite leaf_input_blocks_length.
	        reflexivity.
	      }
      rewrite Hblocks_len.
      rewrite Hold_outputs_prefix_length.
      go using blake3model.mip8_leaf_iv_words_length.
      subst hash_many_cont.
      rewrite leaf_input_blocks_data.
      rewrite leaf_hash_outputs_from_call_params.
      assert
        (Hleaf_output_range :
          List.Forall (fun x => (x < 2 ^ 256)%N)
            (blake3specs.blake3_hash_many_outputs
               blake3model.leaf_mode
               (map (page_pair_leaf_model page) done_indices))).
      {
        apply blake3specs.blake3_hash_many_outputs_range.
      }
		      go using
		        (leaf_hash_many_post_pack_F
		           (blake3specs.storage_leaf_iv_cache_qleaf_after
                  ready qleafiv)
		           (_global blake3specs.storage_get_leaf_iv_static_iv_name)
	           inputs_addr flat_out_addr valid_pairs_addr
	           page done_indices (replicateN 64 0%N)
	           Hdone_len_le
	           (Forall_range_zero_replicateN 64)),
	        (leaf_input_blocks_ptr_array_to_input_ptrs_F
	           inputs_addr valid_pairs_addr page done_indices),
        (blake3_output_bytes_prefix_tail_to_words_F
           flat_out_addr
           (blake3specs.blake3_hash_many_outputs
              blake3model.leaf_mode
              (map (page_pair_leaf_model page) done_indices))
           (skipn (length done_indices) (replicateN 64 0%N))
		           (length done_indices)
		           Hleaf_output_range
		           (eq_sym (leaf_hash_outputs_length page done_indices))).
		      wp_for (fun _ =>
        Exists processed : nat,
          [| (processed <= length done_indices)%nat |]
          ** [| length
                 (apply_leaf_hashes_to_scratch
                    page old_scratch (take processed done_indices)) =
               page_pair_count |]
          ** pagep |-> StoragePageR q page
          ** scratchp |-> ScratchR 1
               (apply_leaf_hashes_to_scratch
                  page old_scratch (take processed done_indices))
	          ** indices_addr |-> leaf_index_arrayR done_indices
	          ** n_addr |-> ulongR 1$m
	               (N.of_nat (length done_indices))
          ** inputs_addr |-> arrayLR
               blake3specs.blake3_input_ptr_store_ty
               0 (Z.of_nat (length done_indices))
               (fun inputp : ptr =>
                  primR blake3specs.blake3_input_ptr_value_ty
                    1$m (Vptr inputp))
               input_ptrs
          ** inputs_addr |-> arrayLR
               blake3specs.blake3_input_ptr_store_ty
               (Z.of_nat (length done_indices)) 64
               (fun _ : unit =>
                  anyR blake3specs.blake3_input_ptr_store_ty 1$m)
               (replicateZ
                  (64 - Z.of_nat (length done_indices)) ())
          ** flat_out_addr |-> blake3specs.Blake3OutputWordsR
               1
               (blake3specs.blake3_hash_many_outputs
                  blake3model.leaf_mode
                  (map (page_pair_leaf_model page) done_indices) ++
                drop (length done_indices) (replicateN 64 0%N))
              ** i_addr |-> ulongR 1$m (N.of_nat processed)).
      rewrite <- (bi.exist_intro 0%nat).
      go using
        leaf_inputs_arrayR_blake3_inputs_unpack_F,
        leaf_input_blocks_ptr_array_to_input_ptrs_F.
      wp_if.
      {
        intro Hcopy.
        match goal with
        | Hbound : (?processed <= length done_indices)%nat |- _ =>
            set (copy_index := processed) in *
        end.
        unfold leaf_index_arrayR.
        go.
        unfold ScratchR, blake3specs.Blake3OutputWordsR,
          blake3_impl_h_specs.Blake3OutputWordsR.
        go.
        match goal with
        | Hlookup : ?lhs = Some t |- _ =>
            pose proof
              (lookup_nat_of_lookupZ_of_N_local
                 done_indices (N.of_nat copy_index) t Hlookup)
              as Hlookup_nat'
        end.
        rewrite Nat2N.id in Hlookup_nat'.
        rename Hlookup_nat' into Hlookup_nat.
        match goal with
        | Hstate : leaf_loop_state pair_bitmap done_indices ?bits |- _ =>
            pose proof
              (leaf_loop_state_lookup_bound
                 pair_bitmap done_indices bits
                 copy_index t Hstate Hlookup_nat)
              as Hidx_bound
        end.
        pose proof
          (leaf_hash_outputs_lookup
             page done_indices copy_index t Hlookup_nat)
          as Hout_lookup.
        pose proof
          (apply_leaf_hashes_to_scratch_take_succ
             page old_scratch done_indices
             copy_index t Hlookup_nat)
          as Hscratch_step.
        assert
          (Hscratch_bound :
            (t <
             length
               (apply_leaf_hashes_to_scratch
                  page old_scratch
                  (take copy_index done_indices)))%nat) by
          (match goal with
           | Hlength :
               length
                 (apply_leaf_hashes_to_scratch
                    page old_scratch
                    (take copy_index done_indices)) =
               page_pair_count |- _ =>
               rewrite Hlength;
               exact Hidx_bound
           end).
        destruct
          (lookup_lt_is_Some_2
             (apply_leaf_hashes_to_scratch
                page old_scratch
                (take copy_index done_indices))
             t Hscratch_bound)
          as [old_cell Hscratch_lookup].
        go using
          (arrayR_update_cell_with_wand_F
             bytes32_ty (exec_specs.bytes32R 1) scratchp
             (apply_leaf_hashes_to_scratch
                page old_scratch (take copy_index done_indices))
             t old_cell (leaf_pair_hash page t) Hscratch_lookup),
          (arrayR_read_cell_with_wand_F
             blake3specs.bytes32_ty (exec_specs.bytes32R 1)
             flat_out_addr
             (blake3specs.blake3_hash_many_outputs
                blake3model.leaf_mode
                (map (page_pair_leaf_model page) done_indices) ++
              drop (length done_indices) (replicateN 64 0%N))
             copy_index (leaf_pair_hash page t)
             Hout_lookup).
        rewrite <- (bi.exist_intro (cQp.mut 1)).
        rewrite <- (bi.exist_intro (leaf_pair_hash page t)).
        rewrite
          (ptr_o_sub_N_of_nat
             blake3specs.bytes32_ty flat_out_addr copy_index).
        go.
        rewrite <- (bi.exist_intro (S copy_index)).
        rewrite Hscratch_step.
        go using use_wand_local_r_F.
        rewrite length_insert.
        go.
      }
      {
        intro Hcopied.
        assert
          (Hcopied_N : N.of_nat t = N.of_nat (length done_indices)).
        {
          apply N2Z.inj.
          exact Hcopied.
        }
        assert (Hcopied_nat : t = length done_indices) by
          (apply Nat2N.inj; exact Hcopied_N).
        subst t.
        assert
          (Htake_done :
            take (length done_indices) done_indices = done_indices).
        {
          apply take_ge.
          lia.
        }
        rewrite Htake_done.
        match goal with
        | Hstate : leaf_loop_state pair_bitmap done_indices 0 |- _ =>
            pose proof
              (leaf_loop_state_done pair_bitmap done_indices Hstate)
            as Hdone_indices
        end.
        assert (Hpair_bound : (pair_bitmap < 2 ^ 64)%N).
        {
          type.has_type_prop.
        }
        match goal with
        | Hscratch_len : length old_scratch = page_pair_count |- _ =>
            rewrite
              (apply_leaf_hashes_to_scratch_done_model
                 page pair_bitmap old_scratch done_indices
                 Hpair_bound Hdone_indices Hscratch_len)
        end.
        assert
          (Hdone_len : (length done_indices <= page_pair_count)%nat).
        {
          unfold page_pair_count.
          lia.
        }
        go using
          (leaf_index_arrayR_forget_F
             indices_addr done_indices Hdone_len),
          (wp_destroy_leaf_hash_outputs64_B
             source flat_out_addr page done_indices _ Hdone_len),
          (destroy_run_leaf_index_array_cleanup_local_B
             source indices_addr done_indices _ Hdone_len),
          (wp_destroy_leaf_inputs_array_split_cleanup_local_B
             source inputs_addr done_indices input_ptrs _ Hdone_len),
          (wp_destroy_leaf_pair_blocks_array_cleanup_local_B
             source valid_pairs_addr page done_indices _ Hdone_len).
        unfold blake3specs.StorageLeafIvCacheR,
          blake3specs.StorageLeafIvInitInputsR,
          blake3specs.StorageLeafDomainKeyMaybeR,
          blake3specs.storage_leaf_iv_cache_qcache_after,
          blake3specs.storage_leaf_iv_cache_qleaf_after.
        destruct ready; cbn [negb].
        {
          go.
        }
        go.
	      }
    }
  Qed.
End with_Sigma.
