Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.libspecs.evmc_specs.

Import linearity.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Local Transparent
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Definition primR_anyR_F ty q v :=
    [FWD] (primR_anyR ty q v).

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
        vm_compute.
        eauto.
      }
      go using primR_anyR_F.
    }
  Qed.

  Definition uchar_arrayR_values_forget_F base values :=
    [FWD] (uchar_arrayR_values_forget base values).

  Lemma prf_evmc_bytes32_dtor :
    verify[source] exec_specs.evmc_bytes32_dtor_spec.
  Proof using MODd.
    verify_spec.
    rewrite /exec_specs.evmc_bytes32R /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR.
    go using uchar_arrayR_values_forget_F.
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
