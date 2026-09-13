Set Default Goal Selector "!".

(*
  Import and linking point for the split [storage_page.cpp] proofs.

  Each concrete C++ proof is in a file named after the function it verifies.
  This file keeps the MIP-8 aggregate import short and gives downstream users a
  single path for the currently checked top-level page-commit C++ proof.
  Every specification of a function defined in [storage_page.cpp] or
  [storage_page.hpp] is backed by a body proof imported here.  The linking
  theorems discharge those local specs and expose only calls outside those two
  files.

  The page-commit proof below covers the read/commit path from an already-owned
  [StoragePageR].  The encode/decode combiners also link the storage-page-owned
  constructor, destructor, [set], bit mutators, dense-index helper, [size], and
  index helper proofs.  Their external interfaces contain two different kinds
  of trusted call contracts: third-party-library boundaries (BLAKE3, Boost
  Outcome,
  Boost small_vector, libstdc++, and compiler intrinsics), and Monad-owned
  helpers outside the storage-page files (bytes32 operations, assertions, and
  compact RLP).  Keeping both categories explicit below makes the residual TCB
  visible rather than silently treating all callees as third-party code.

  These theorems are conditional on those call contracts.  They do not verify
  allocation-failure or exception paths inside the external libraries, and do
  not prove termination.  The decoder's explicit [DecodeError] results describe
  format errors, not allocation failures.
*)

Require Import skylabs.auto.cpp.linking_proof.
Require Import monad.proofs.libspecs.byte_string_specs.
Require Import monad.proofs.libspecs.evmc_specs.
Require Import monad.proofs.libspecs.rlp_decode_error_specs.
Require Import monad.proofs.libspecs.rlp_specs.
Require Import monad.proofs.libspecs.span_specs.
Require Import monad.proofs.libspecs.stdlib_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.libspecs.u256_conversion_specs.
Require Import monad.proofs.libspecs.blake3.byte_bridges.
Require Import monad.proofs.execproofs.mip8.blake3specs.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_byte_bridges.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.bytes32.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_ctor.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_dtor.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_is_empty.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_bitmap.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_pair_bitmap.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.init_leaf_scratch.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.merge_scratch_level.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.compute_nonempty_subtree_root.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_get_leaf_iv.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_has_bit.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_dense_index.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_bit_mutators.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_index_const.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_values_index_const.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_size.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_set.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.compute_page_key.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.compute_slot_offset.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.compute_slot_key.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_blake3_seal.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.encode_storage_page.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.lowest_offset.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.decode_storage_page.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.page_commit.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Definition prf_evmc_bytes32_dtor_B :=
    spec_bwd prf_evmc_bytes32_dtor.
  Definition prf_storage_page_ctor_B :=
    spec_bwd prf_storage_page_ctor.
  Definition prf_storage_page_dtor_B :=
    spec_bwd prf_storage_page_dtor.
  Definition prf_storage_page_is_empty_B :=
    spec_bwd prf_storage_page_is_empty.
  Definition prf_storage_page_bitmap_B :=
    spec_bwd prf_storage_page_bitmap.
  Definition prf_storage_page_pair_bitmap_B :=
    spec_bwd prf_storage_page_pair_bitmap.
  Definition prf_init_leaves_B :=
    spec_bwd prf_init_leaves.
  Definition prf_merge_at_level_B :=
    spec_bwd prf_merge_at_level.
  Definition prf_compute_nonempty_subtree_root_B :=
    spec_bwd prf_compute_nonempty_subtree_root.
  Definition prf_storage_blake3_seal_B :=
    spec_bwd prf_storage_blake3_seal.
  Definition prf_storage_page_has_bit_B :=
    spec_bwd prf_storage_page_has_bit.
  Definition prf_storage_page_dense_index_B :=
    spec_bwd prf_storage_page_dense_index.
  Definition prf_storage_page_set_bit_B :=
    spec_bwd prf_storage_page_set_bit.
  Definition prf_storage_page_clear_bit_B :=
    spec_bwd prf_storage_page_clear_bit.
  Definition prf_storage_page_values_holder_start_const_B :=
    spec_bwd prf_storage_page_values_holder_start_const.
  Definition prf_storage_page_values_index_const_B :=
    spec_bwd prf_storage_page_values_index_const.
  Definition prf_storage_page_size_B :=
    spec_bwd prf_storage_page_size.
  Definition prf_storage_page_set_B :=
    spec_bwd prf_storage_page_set.
  Definition prf_encode_storage_page_B :=
    spec_bwd prf_encode_storage_page.
  Definition prf_decode_storage_page_B :=
    spec_bwd prf_decode_storage_page.
  Definition prf_page_commit_B :=
    spec_bwd prf_page_commit.

  Lemma link_init_leaf_scratch_requirements :
    denoteModule storage_page_cpp.source **
    blake3_compress_in_place_spec **
    memcpy_spec **
    std_popcount_ulong_spec **
    ▷ exec_specs.monad_assertion_failed_spec **
    exec_specs.bytes32_copy_ctor_spec **
    evmc_specs.bytes32_default_ctor_spec
    |-- ▷ storage_get_leaf_iv_spec **
        ▷ storage_page_index_const_spec.
  Proof using MODd.
    wapply prf_storage_get_leaf_iv.
    go.
    wapply prf_storage_page_index_const.
    go using
      prf_storage_page_has_bit_B,
      prf_storage_page_dense_index_B,
      prf_storage_page_values_holder_start_const_B,
      prf_storage_page_values_index_const_B.
  Qed.

  (** These interfaces contain only Monad-owned integer conversion and
      arithmetic callees implemented outside [storage_page.hpp].  The three
      theorems below discharge the bodies of the key-splitting helpers
      themselves. *)
  Definition compute_page_key_cpp_monad_interface : mpred :=
    (▷ load_be_uint256_bytes32_spec ∗
     ▷ store_be_as_bytes32_uint256_spec ∗
     ▷ u256_shr_spec ∗
     ▷ uint256_copy_ctor_spec ∗
     ▷ uint256constr ∗
     ▷ uint256dtor)%I.

  Definition compute_slot_key_cpp_monad_interface : mpred :=
    (▷ load_be_uint256_bytes32_spec ∗
     ▷ store_be_as_bytes32_uint256_spec ∗
     ▷ u256_or_spec ∗
     ▷ u256_shl_ulong_spec ∗
     ▷ uint256_copy_ctor_spec ∗
     ▷ uint256_uchar_ctor_spec ∗
     ▷ uint256dtor)%I.

  Theorem compute_page_key_cpp_proof_ok :
    denoteModule storage_page_cpp.source **
    compute_page_key_cpp_monad_interface
    |-- compute_page_key_spec.
  Proof using MODd.
    rewrite /compute_page_key_cpp_monad_interface.
    wapply prf_compute_page_key.
    go.
  Qed.

  Theorem compute_slot_offset_cpp_proof_ok :
    denoteModule storage_page_cpp.source
    |-- compute_slot_offset_spec.
  Proof using MODd.
    exact prf_compute_slot_offset.
  Qed.

  Theorem compute_slot_key_cpp_proof_ok :
    denoteModule storage_page_cpp.source **
    compute_slot_key_cpp_monad_interface
    |-- compute_slot_key_spec.
  Proof using MODd.
    rewrite /compute_slot_key_cpp_monad_interface.
    wapply prf_compute_slot_key.
    go.
  Qed.

  (* These are exactly the call contracts left assumed by the [page_commit]
     combiner.  The [▷] matches the shape expected at C++ call sites. *)
  Definition storage_page_cpp_third_party_interface : mpred :=
    (▷ blake3_compress_in_place_spec ∗
     ▷ blake3_hash_many_spec ∗
     ▷ memcpy_spec ∗
     ▷ pext_u64_spec ∗
     ▷ std_countr_zero_ulong_spec ∗
     ▷ std_popcount_ulong_spec)%I.

  Definition storage_page_cpp_monad_interface : mpred :=
    (▷ exec_specs.bytes32_copy_ctor_spec ∗
     ▷ exec_specs.bytes32_assign_spec ∗
     ▷ evmc_specs.bytes32_default_ctor_spec ∗
     ▷ exec_specs.bytes32_dtor_spec ∗
     ▷ exec_specs.monad_assertion_failed_spec)%I.

  Definition storage_page_cpp_external_interface : mpred :=
    (storage_page_cpp_third_party_interface ∗
     storage_page_cpp_monad_interface)%I.

  (* Byte strings, Boost small_vector, span indexing, and the standard bit
     operations are third-party boundaries. [lowest_offset] itself is linked
     below, not assumed. *)
  Definition encode_storage_page_cpp_third_party_interface : mpred :=
    (▷ byte_string_ctor_spec ∗
     ▷ byte_string_reserve_spec ∗
     ▷ byte_string_push_back_spec ∗
     ▷ byte_string_append_spec ∗
     ▷ byte_string_move_ctor_spec ∗
     ▷ byte_string_dtor_spec ∗
     ▷ storage_page_values_size_const_spec ∗
     ▷ span_index_spec (Qconst bytes32_ty) 18446744073709551615 ∗
     ▷ std_countr_zero_ulong_spec ∗
     ▷ std_popcount_ulong_spec)%I.

  (* Compact RLP is implemented by Monad outside the storage-page files.
     The indexed encoder no longer needs the bytes32 operations used by the
     former RLE scan. *)
  Definition encode_storage_page_cpp_monad_interface : mpred :=
    (▷ rlp_encode_bytes32_compact_spec)%I.

  Definition encode_storage_page_cpp_external_interface : mpred :=
    (encode_storage_page_cpp_third_party_interface ∗
     encode_storage_page_cpp_monad_interface)%I.

  (* String views, Boost Outcome, Boost small_vector, and [std::popcount] are
     third-party boundaries for the decoder. *)
  Definition decode_storage_page_cpp_third_party_interface : mpred :=
    (▷ string_view_remove_prefix_spec ∗
     ▷ string_view_index_spec ∗
     ▷ string_view_empty_spec ∗
     ▷ outcome_try_has_value_spec
         rlp_specs.bytes32_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            rlp_specs.bytes32_ty outcome_error_ty) ∗
     ▷ outcome_try_return_as_spec
         rlp_specs.bytes32_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            rlp_specs.bytes32_ty outcome_error_ty) ∗
     ▷ outcome_try_extract_value_spec
         rlp_specs.bytes32_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            rlp_specs.bytes32_ty outcome_error_ty) ∗
     ▷ outcome_result_dtor_spec
         rlp_specs.bytes32_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            rlp_specs.bytes32_ty outcome_error_ty) ∗
     ▷ outcome_failure_dtor_spec outcome_error_ty ∗
     ▷ outcome_has_value_overload_dtor_spec ∗
     ▷ outcome_as_failure_overload_dtor_spec ∗
     ▷ outcome_assume_value_overload_dtor_spec ∗
     ▷ outcome_value_tag_ctor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ outcome_value_tag_dtor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ outcome_error_tag_ctor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ outcome_error_tag_dtor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ outcome_explicit_move_tag_ctor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ outcome_explicit_move_tag_dtor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ outcome_result_error_ctor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty)
         decode_error_ty ∗
     ▷ outcome_result_value_ctor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ outcome_result_failure_ctor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ outcome_result_dtor_spec
         storage_page_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty
            storage_page_ty outcome_error_ty) ∗
     ▷ storage_page_values_dtor_spec ∗
     ▷ storage_page_values_default_ctor_spec ∗
     ▷ storage_page_values_begin_spec ∗
     ▷ storage_page_values_const_iterator_ctor_spec ∗
     ▷ storage_page_values_const_iterator_dtor_spec ∗
     ▷ storage_page_values_erase_spec ∗
     ▷ storage_page_values_index_mut_spec ∗
     ▷ storage_page_values_insert_spec ∗
     ▷ storage_page_values_iterator_dtor_spec ∗
     ▷ storage_page_values_iterator_plus_spec ∗
     ▷ std_popcount_ulong_spec)%I.

  (* Compact RLP and the remaining bytes32/assertion operations are Monad-owned
     dependencies outside the storage-page files.  The exact DecodeError enum
     representation and the System Error 2 status-code adapter are logical
     representation/typeclass assumptions, so they appear in [Print
     Assumptions] rather than as call-contract conjuncts here. *)
  Definition decode_storage_page_cpp_monad_interface : mpred :=
    (▷ exec_specs.bytes32_copy_ctor_spec ∗
     ▷ exec_specs.bytes32_assign_spec ∗
     ▷ evmc_specs.bytes32_default_ctor_spec ∗
     ▷ exec_specs.bytes32_dtor_spec ∗
     ▷ exec_specs.monad_assertion_failed_spec ∗
     ▷ evmc_specs.bytes32_eq_spec ∗
     ▷ rlp_decode_bytes32_compact_spec)%I.

  Definition decode_storage_page_cpp_external_interface : mpred :=
    (decode_storage_page_cpp_third_party_interface ∗
     decode_storage_page_cpp_monad_interface)%I.

  Theorem page_commit_cpp_proof_ok :
    denoteModule storage_page_cpp.source **
    storage_page_cpp_external_interface
    |-- page_commit_spec.
  Proof using MODd.
    rewrite /storage_page_cpp_external_interface
      /storage_page_cpp_third_party_interface
      /storage_page_cpp_monad_interface.
    wapply prf_page_commit.
    go.
    go using
      prf_storage_page_is_empty_B,
      prf_storage_page_bitmap_B,
      prf_storage_page_pair_bitmap_B.
    go using prf_storage_blake3_seal_B.
    go using prf_compute_nonempty_subtree_root_B.
    go using prf_merge_at_level_B.
    go using prf_init_leaves_B.
    wapply link_init_leaf_scratch_requirements.
    go using later_spec_bwd.
  Qed.

  Theorem encode_storage_page_cpp_proof_ok :
    denoteModule storage_page_cpp.source **
    encode_storage_page_cpp_external_interface
    |-- encode_storage_page_spec.
  Proof using MODd.
    rewrite /encode_storage_page_cpp_external_interface
      /encode_storage_page_cpp_third_party_interface
      /encode_storage_page_cpp_monad_interface.
    wapply prf_encode_storage_page.
    go.
    wapply prf_storage_page_size.
    go.
    wapply prf_lowest_offset.
    go using
      prf_storage_page_values_holder_start_const_B,
      later_spec_bwd.
  Qed.

  Theorem decode_storage_page_cpp_proof_ok :
    denoteModule storage_page_cpp.source **
    decode_storage_page_cpp_external_interface
    |-- decode_storage_page_spec.
  Proof using MODd.
    rewrite /decode_storage_page_cpp_external_interface
      /decode_storage_page_cpp_third_party_interface
      /decode_storage_page_cpp_monad_interface.
    wapply prf_decode_storage_page.
    go using
      prf_storage_page_ctor_B,
      prf_storage_page_dtor_B,
      prf_storage_page_set_B,
      later_spec_bwd.
    go using
      prf_storage_page_has_bit_B,
      prf_storage_page_dense_index_B,
      prf_storage_page_set_bit_B,
      prf_storage_page_clear_bit_B,
      prf_storage_page_values_holder_start_const_B,
      prf_storage_page_values_index_const_B,
      later_spec_bwd.
  Qed.

End with_Sigma.
