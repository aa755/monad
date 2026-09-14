From Coq Require Import ZArith NArith Lia.
From stdpp Require Import base.

Set Implicit Arguments.
Local Open Scope N_scope.

Definition U256_modulus : N := N.pow 2 256.

Record U256 := { u256_val : N }.

Definition u256_wrap (z : N) : U256 :=
  {| u256_val := z mod U256_modulus |}.

Definition u256_zero : U256 := u256_wrap 0.
Definition u256_one : U256 := u256_wrap 1.

Definition u256_of_N (n : N) : U256 := u256_wrap  n.
Definition u256_to_N (x : U256) : N := (u256_val x).

Definition u256_add (x y : U256) : U256 :=
  u256_wrap (u256_val x + u256_val y).

Definition u256_sub (x y : U256) : U256 :=
  u256_wrap (u256_val x - u256_val y).

Definition u256_mul (x y : U256) : U256 :=
  u256_wrap (u256_val x * u256_val y).

Definition u256_min (x y : U256) : U256 :=
  u256_wrap (N.min (u256_val x) (u256_val y)).

Declare Scope u256_scope.
Delimit Scope u256_scope with u256.

Notation "0%u256" := u256_zero.
Notation "1%u256" := u256_one.
Notation "x ⊕ y" := (u256_add x y) (at level 50, left associativity) : u256_scope.
(*
Notation "x ⊖ y" := (u256_sub x y) (at level 50, left associativity) : u256_scope.
*)
Notation "x ⊗ y" := (u256_mul x y) (at level 40, left associativity) : u256_scope.

#[global] Instance eqdec_u256 : EqDecision U256.
Proof.
  unfold EqDecision.
  intros x y.
  destruct x as [xv], y as [yv].
  destruct (N.eq_dec xv yv); [left; subst; constructor|right; congruence].
Defined.

(*
Lemma u256_wrap_range z :
  0 <= u256_val (u256_wrap z) < U256_modulus.
Proof.
  unfold u256_wrap, U256_modulus.
  simpl. 
  apply N.mod_pos_bound; lia.
Qed.

Lemma u256_of_Z_range z :
  0 <= u256_val (u256_of_Z z) < U256_modulus.
Proof. apply u256_wrap_range. Qed.

Lemma u256_of_N_range n :
  0 <= u256_val (u256_of_N n) < U256_modulus.
Proof. apply u256_wrap_range. Qed.

Section WithScope.
  Local Open Scope u256_scope.
  Local Open Scope Z_scope.

  Lemma u256_add_range x y :
    0 <= u256_val (x ⊕ y) < U256_modulus.
  Proof. apply u256_wrap_range. Qed.

  Lemma u256_sub_range x y :
    0 <= u256_val (x ⊖ y) < U256_modulus.
  Proof. apply u256_wrap_range. Qed.

  Lemma u256_mul_range x y :
    0 <= u256_val (x ⊗ y) < U256_modulus.
  Proof. apply u256_wrap_range. Qed.
End WithScope.
*)
