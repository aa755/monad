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

  Lemma prf_compute_slot_offset :
    verify[source] compute_slot_offset_spec.
  Proof using MODd.
    (* This helper is the one place where the C++ directly indexes
       storage_key.bytes[31].  The local array split exposes exactly that byte;
       [slot_offset_low_byte] then connects the byte-level read to the abstract
       low-7-bit slot-offset model. *)
    verify_spec'.
    name_locals.
    go.
    rewrite /exec_specs.bytes32R /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR.
    go.
    rewrite (_at_arrayR_cellN 31%N).
    2: {
      unfold exec_specs.bytes32_be_values.
      cbn.
      rewrite N.shiftr_0_r.
      reflexivity.
    }
    go.
    iSplit.
    {
      iPureIntro.
      change 127%Z with (Z.of_N 127%N).
      rewrite <- N2Z.inj_land.
      rewrite slot_offset_low_byte.
      reflexivity.
    }
    (* After reading one byte, the array ownership is split around cell 31.
       The postcondition wants the original bytes32 ownership back, so we split
       the target in the same way and let cancellation recombine the pieces. *)
    hideLhs.
    rewrite (_at_arrayR_cellN 31%N).
    2: {
      unfold exec_specs.bytes32_be_values.
      cbn.
      rewrite N.shiftr_0_r.
      reflexivity.
    }
    unhideAllFromWork.
    go.
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
