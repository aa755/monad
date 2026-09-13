Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Import linearity.
Set Default Goal Selector "!".
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

(** [monad::is_dead] treats a missing account as dead and otherwise calls
    [monad::is_empty]. The optional spine is retained while its payload is
    passed to that helper. *)
Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  Lemma prf_account_is_dead : verify[state_cpp.source] is_dead_spec.
  Proof using MODd.
    verify_spec.
    destruct oas as [ac|].
    {
      go.
      iExists evmmisc.AccountM, AccountR, ac.
      go.
    }
    {
      go.
    }
  Qed.
End with_Sigma.
