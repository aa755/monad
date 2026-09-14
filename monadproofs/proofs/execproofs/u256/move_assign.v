Require Import monad.asts.state_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.libspecs.std_array_specs.
Require Import skylabs.auto.cpp.proof.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Set Default Goal Selector "!".
Import linearity.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Local Transparent u256R u256_words_arrayR u256_word_cellsR u256_words.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  Lemma u256_words_arrayR_layout q n :
    u256_words_arrayR q n -|-
    scalar_array.R Tulong 4 q (Vn <$> u256_words n).
  Proof.
    unfold u256_words_arrayR, u256_word_cellsR, scalar_array.R.
    rewrite arrayR_map'.
    unfold u256_words.
    rewrite pureR_only_provable.
    split'; go.
  Qed.

  Lemma u256_move_assign_proof :
    verify[state_cpp.source] u256_move_assign_spec.
  Proof using MODd.
    verify_spec.
    rewrite PostCondition.unlock.
    unfold u256R.
    setoid_rewrite u256_words_arrayR_layout.
    go.
  Qed.
End with_Sigma.
