Require Import monad.asts.state_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import skylabs.auto.cpp.proof.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Set Default Goal Selector "!".
Import linearity.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  Lemma u256_or_assign_proof :
    verify[state_cpp.source] u256_or_assign_spec.
  Proof using MODd.
    verify_spec.
    go.
  Qed.
End with_Sigma.
