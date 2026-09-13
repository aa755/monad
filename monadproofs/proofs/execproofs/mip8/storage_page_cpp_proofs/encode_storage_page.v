Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_size.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_index_const.
Require Import monad.proofs.execproofs.mip8.storage_page_encoding.
Require Import monad.proofs.libspecs.byte_string_specs.
Require Import monad.proofs.libspecs.evmc_specs.
Require Import monad.proofs.libspecs.rlp_specs.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Import linearity.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
#[local] Hint Resolve observeStoragePageLength_F : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Require Import monad.proofs.execproofs.mip8.storage_page_indexed_encoding.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_values_index_const.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.compute_nonempty_subtree_root.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.lowest_offset.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.merge_scratch_level.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_set.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.indexed_encoding_support.

(* Main now emits one ascending slot index followed by its compact RLP word.
   Monad's values() and bitmap() accessors are checked inline; indexing the
   returned span uses the generic library contract. *)
Local Remove Hints SpecFor_span_size SpecFor_span_ctor SpecFor_span_dtor
  SpecFor_storage_page_values_size_const storage_page_bitmap_spec_spec_instance
  : typeclass_instances.

cpp.spec "monad::storage_page_t::values() const" from storage_page_cpp.source inline.
cpp.spec "monad::storage_page_t::bitmap() const" from storage_page_cpp.source inline.
cpp.spec "boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>::size() const" from storage_page_cpp.source inline.
cpp.spec "boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>::data() const" from storage_page_cpp.source inline.
cpp.spec "boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>::priv_raw_begin() const" from storage_page_cpp.source inline.
cpp.spec "boost::movelib::to_raw_pointer<monad::bytes32_t>(monad::bytes32_t*)" from storage_page_cpp.source inline.
cpp.spec "std::to_address<const monad::bytes32_t>(const monad::bytes32_t*)" from storage_page_cpp.source inline.
cpp.spec "std::span<const monad::bytes32_t, 18446744073709551615ul>::span<const monad::bytes32_t*>(const monad::bytes32_t*, unsigned long)" from storage_page_cpp.source inline.
cpp.spec "std::__detail::__extent_storage<18446744073709551615ul>::__extent_storage(unsigned long)" from storage_page_cpp.source inline.
cpp.spec "std::__detail::__extent_storage<18446744073709551615ul>::_M_extent() const" from storage_page_cpp.source inline.
cpp.spec "std::__detail::__extent_storage<18446744073709551615ul>::~__extent_storage()" from storage_page_cpp.source inline.
cpp.spec "std::span<const monad::bytes32_t, 18446744073709551615ul>::size() const" from storage_page_cpp.source inline.
cpp.spec "std::span<const monad::bytes32_t, 18446744073709551615ul>::~span()" from storage_page_cpp.source inline.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Instance learn_byte_string :
    LearnEq2 ByteStringR := ltac:(solve_learnable).

  Lemma prf_encode_storage_page :
    verify[source] encode_storage_page_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    go using byte_string_ctor_spec.
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro page).
    go using storage_page_size_spec.
    go using byte_string_reserve_spec.
    go using StoragePageR_index_unpack_F.
    unfold boost_small_vector.SmallVectorR,
      boost_small_vector.SmallVectorCapR,
      boost_small_vector.SmallVectorSpineR,
      boost_small_vector.SmallVectorPayloadR,
      boost_small_vector.vector_holder_field,
      storage_page_values_vector_ty,
      storage_page_values_vector_field,
      storage_page_values_field,
      storage_page_values_name,
      storage_page_values_small_vector_base_name,
      storage_page_values_vector_name.
    unfold Field'', Ndependent'.
    rewrite !offset_ptr_dot.
    go.
    change
      ("boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>"%cpp_name
       .:: field_name.Id "m_holder")
      with
      "boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>::m_holder"%cpp_name.
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro base).
    rewrite <- (bi.exist_intro (N.of_nat (length (storage_page_dense_values page)))).
    rewrite <- (bi.exist_intro capacity).
    go.
    unfold boost_small_vector.SmallVectorHolderR,
      boost_small_vector.holder_start_field,
      boost_small_vector.holder_size_field,
      boost_small_vector.holder_capacity_field.
    unfold Field'', Ndependent'.
    go.
    wp_for (fun _ =>
      (Exists (remaining : list N) (dense : nat) (encoded : list Z),
        [| length remaining = page_slot_count |] **
        [| (dense <= length (storage_page_dense_values page))%nat |] **
        [| skipn dense (storage_page_dense_values page) =
             storage_page_dense_values remaining |] **
        [| encoded ++ encode_storage_page_model remaining =
             encode_storage_page_model page |] **
        encoded_addr |-> ByteStringR 1$m encoded **
        dense_addr |-> ulongR 1$m (Z.of_nat dense) **
        bits_addr |-> primR "uint128_t" 1$m (Vn (slot_bitmap_word remaining)))).
    rewrite <- (bi.exist_intro page).
    rewrite <- (bi.exist_intro 0%nat).
    rewrite <- (bi.exist_intro ([] : list Z)).
    go.
    wp_if.
    {
      intro Hbits.
      match type of Hbits with slot_bitmap_word ?r <> _ => rename r into remaining end.
      match goal with
      | H : skipn ?d (storage_page_dense_values page) = _ |- _ =>
          rename d into dense; rename H into Hsuffix
      end.
      match goal with
      | H : ?e ++ encode_storage_page_model remaining = _ |- _ =>
          rename e into encoded; rename H into Hencoded
      end.
      match goal with
      | H : length remaining = page_slot_count |- _ =>
          destruct (indexed_encoding_step remaining H Hbits)
            as (index & value & next & Hindex & Hvalue & Hnextlen &
                Hlowest & Hclear & Hdense & Hencode)
      end.
      rewrite Hdense in Hsuffix.
      destruct (dense_suffix_head _ _ _ _ Hsuffix)
        as (Hdense_bound & Hnth & Hnextsuffix).
      go.
      rewrite <- (bi.exist_intro (cQp.const 1)).
      rewrite <- (bi.exist_intro base).
      rewrite <- (bi.exist_intro
        (N.of_nat (length (storage_page_dense_values page)))).
      rewrite <- (bi.exist_intro false).
      unfold SpanRbase, Field'', Ndependent'.
      go.
      rewrite <- (bi.exist_intro (cQp.mut q)).
      rewrite <- (bi.exist_intro
        (nth dense (storage_page_dense_values page) 0%N)).
      replace (Z.of_N (Z.to_N (Z.of_nat dense))) with (Z.of_nat dense) by lia.
      assert (Hijk : SolveArith
        (0 <= Z.of_nat dense /\
         Z.of_nat dense < Z.of_nat (length (storage_page_dense_values page)))).
      { constructor. lia. }
      go using (merge_scratch_level.arrayLR_extract_middle_lookup_local_F
        storage_page_specs.bytes32_ty base 0 (Z.of_nat dense)
        (Z.of_nat (length (storage_page_dense_values page)))
        (bytes32R (cQp.mut q)) (storage_page_dense_values page) Hijk).
      assert (Hread : nth dense (storage_page_dense_values page) 0%N = x).
      {
        assert (Hlookup : storage_page_dense_values page !!
          (Z.of_N (N.of_nat dense)) = Some x).
        { replace (Z.of_N (N.of_nat dense)) with (Z.of_nat dense - 0) by lia.
          assumption. }
        pose proof (nth_of_lookupZ_of_N_local
          (storage_page_dense_values page) (N.of_nat dense) x 0%N Hlookup) as Hnthx.
        rewrite Nat2N.id in Hnthx. exact Hnthx.
      }
      rewrite Hread.
      go.
      rewrite <- (bi.exist_intro next).
      rewrite <- (bi.exist_intro (S dense)).
      rewrite Hlowest.
      replace (Z.of_N (N.of_nat index)) with (Z.of_nat index) by lia.
      replace (Z.of_N (slot_bitmap_word remaining) - 1)
        with (Z.of_N (slot_bitmap_word remaining - 1)) by lia.
      rewrite N2Z_land.
      rewrite Hclear.
      rewrite Hencode in Hencoded.
      go using (storage_page_values_index_const.arrayLR_combine_middle_lookup_local_B
        storage_page_specs.bytes32_ty base 0 (Z.of_nat dense)
        (Z.of_nat (length (storage_page_dense_values page)))
        (bytes32R (cQp.mut q)) (storage_page_dense_values page) Hijk).
    }
    {
      intro Hempty.
      go.
      destruct (indexed_encoding_bitmap_zero _ Hempty) as [Hdone _].
      rewrite Hdone app_nil_r in H.
      rewrite <- H.
      unfold StoragePageR,
        boost_small_vector.SmallVectorR,
        boost_small_vector.SmallVectorCapR,
        boost_small_vector.SmallVectorSpineR,
        boost_small_vector.SmallVectorPayloadR,
        boost_small_vector.vector_holder_field,
        storage_page_values_vector_ty,
        storage_page_values_vector_field,
        storage_page_values_field,
        storage_page_values_name,
        storage_page_values_small_vector_base_name,
        storage_page_values_vector_name.
      unfold Field'', Ndependent'.
      go.
      rewrite <- (bi.exist_intro base).
      rewrite <- (bi.exist_intro capacity).
      unfold boost_small_vector.SmallVectorHolderR,
        boost_small_vector.holder_start_field,
        boost_small_vector.holder_size_field,
        boost_small_vector.holder_capacity_field.
      unfold Field'', Ndependent'.
      go.
      normalize_ptrs.
      go.
    }
  Qed.
End with_Sigma.
