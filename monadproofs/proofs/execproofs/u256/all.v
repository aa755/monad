Set Default Goal Selector "!".

Require Import monad.asts.state_cpp.
Require Import monad.proofs.libspecs.u256_specs.
Require Export monad.proofs.libspecs.std_array_specs.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.linking_proof.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Require Export monad.proofs.execproofs.u256.move_assign.
Require Export monad.proofs.execproofs.u256.assign.
Require Export monad.proofs.execproofs.u256.add_assign.
Require Export monad.proofs.execproofs.u256.sub_assign.
Require Export monad.proofs.execproofs.u256.mul_assign.
Require Export monad.proofs.execproofs.u256.div_assign.
Require Export monad.proofs.execproofs.u256.mod_assign.
Require Export monad.proofs.execproofs.u256.xor_assign.
Require Export monad.proofs.execproofs.u256.or_assign.
Require Export monad.proofs.execproofs.u256.and_assign.
Require Export monad.proofs.execproofs.u256.shl_assign.
Require Export monad.proofs.execproofs.u256.shr_assign.

Import linearity.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  (* Discharge the Monad copy/move assignments using their body proofs.
     The remaining callees are the third-party array assignment boundary,
     Monad binary operators, and temporary destruction. *)
  Lemma u256_assignments_linked :
    denoteModule state_cpp.source **
    scalar_array.assign_spec false Tulong 4 **
    scalar_array.assign_spec true Tulong 4 **
    u256_plus_spec ** u256_minus_spec ** u256_mul_spec **
    u256_div_spec ** u256_mod_spec ** u256_xor_spec **
    u256_or_spec ** u256_and_spec ** u256_shl_spec ** u256_shr_spec **
    uint256dtor
    |-- u256_assign_spec ** u256_move_assign_spec **
        u256_add_assign_spec ** u256_sub_assign_spec **
        u256_mul_assign_spec ** u256_div_assign_spec **
        u256_mod_assign_spec ** u256_xor_assign_spec **
        u256_or_assign_spec ** u256_and_assign_spec **
        u256_shl_assign_spec ** u256_shr_assign_spec.
  Proof using MODd.
    go using (spec_bwd u256_assign_proof),
      (spec_bwd u256_move_assign_proof),
      (spec_bwd u256_add_assign_proof),
      (spec_bwd u256_sub_assign_proof),
      (spec_bwd u256_mul_assign_proof),
      (spec_bwd u256_div_assign_proof),
      (spec_bwd u256_mod_assign_proof),
      (spec_bwd u256_xor_assign_proof),
      (spec_bwd u256_or_assign_proof),
      (spec_bwd u256_and_assign_proof),
      (spec_bwd u256_shl_assign_proof),
      (spec_bwd u256_shr_assign_proof).
  Qed.
End with_Sigma.
