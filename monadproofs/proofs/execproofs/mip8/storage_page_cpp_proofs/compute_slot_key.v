Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.libspecs.u256_conversion_specs.

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
  Lemma prf_compute_slot_key :
    verify[source] compute_slot_key_spec.
  Proof using MODd.
    (* This is the inverse direction of the key split: shift the page key left
       by 7 bits, OR in a bounded slot offset, and store as bytes32.  The mask
       lemma discharges the fact that a valid slot offset is already below 128. *)
    verify_spec'.
    name_locals.
    go using
      storage_page_byte_bridges.bytes32R_to_bytes_field_F,
      storage_page_byte_bridges.byte_arrayLR32_to_arrayR_F,
      u256_conversion_specs.uint256_be_bytesR_fold_F,
      storage_page_byte_bridges.bytes_field_to_bytes32R_B.
    unfold slot_key_model.
    unfold u256_specs.uint256_word_modulus.
    rewrite (slot_offset_mask_small slot_offset).
    2: lia.
    go using storage_page_byte_bridges.bytes_field_to_bytes32R_B.
    go using
      u256_conversion_specs.uint256_be_bytesR_unfold_F,
      storage_page_byte_bridges.byte_arrayR_to_arrayLR32_F.
    Unshelve.
    all: try solve [go | lia | reflexivity].
  Qed.
End with_Sigma.

#[global] Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R.
#[global] Hint Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R : sl_opacity.
