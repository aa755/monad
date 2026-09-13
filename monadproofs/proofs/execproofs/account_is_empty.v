Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.u256_specs.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Import linearity.
Opaque Zdigits.binary_value Zdigits.Z_to_binary w256_to_Z.
Set Default Goal Selector "!".
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

(** [monad::is_empty] reads the account fields, not an optional wrapper.
    The global precondition identifies the actual empty-code hash being
    compared; no memory is obtained from [denoteModule]. *)
Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  Local Transparent AccountR.

  Lemma prf_account_is_empty : verify[state_cpp.source] is_empty_spec.
  Proof using MODd.
    verify_spec.
    unfold AccountR.
    go.
    destruct (N.eqb
      (code_hash_of_program (block.block_account_code (coreAc ac)))
      null_code_hash) eqn:Hcode.
    {
      go.
      case_bool_decide as Hnonce.
      {
        go.
        change (Z.to_N (0 mod uint64_word_modulus)%Z) with 0%N.
        rewrite Hnonce /= N_eqb_bool_decide.
        go.
      }
      {
        go.
      }
    }
    {
      go.
    }
  Qed.
End with_Sigma.
