Set Default Goal Selector "!".

(*
  Small C/C++ standard-library specs used by C++ proofs.

  These are not specific to MIP-8.  The current declarations are specialized
  to the symbols present in [storage_page.cpp]'s generated AST, but the models
  are ordinary library behavior: unsigned-long bit scans/counts and byte-copying
  [memcpy].
*)

From Stdlib Require Import Lia List NArith ZArith.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.cpp.
Require Export skylabs.brick.libstdcpp.cstring.spec.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.exec_specs.

Import cQp_compat.

Local Open Scope N_scope.

Fixpoint countr_zero_fuel (fuel : nat) (word : N) : N :=
  match fuel with
  | O => 64
  | S fuel' =>
      if N.eqb word 0
      then 64
      else if N.odd word
           then 0
           else 1 + countr_zero_fuel fuel' (N.shiftr word 1)
  end.

Definition countr_zero64 (word : N) : N :=
  countr_zero_fuel 64 word.

Fixpoint popcount_fuel (fuel : nat) (word : N) : N :=
  match fuel with
  | O => 0
  | S fuel' =>
      (if N.odd word then 1 else 0)
      + popcount_fuel fuel' (N.shiftr word 1)
  end.

Definition popcount64 (word : N) : N :=
  popcount_fuel 64 word.

(** [_pext_u64] is a BMI2/compiler intrinsic, not Monad code.  The generic
    model below scans the low [fuel] bits of [mask].  Whenever a mask bit is
    set, the corresponding input bit is appended to the next output position.
    The 64-bit intrinsic is [pext_fuel] with 64 steps. *)
Fixpoint pext_fuel (fuel : nat) (word mask : N) : N :=
  match fuel with
  | O => 0
  | S fuel' =>
      let tail :=
        pext_fuel fuel' (N.shiftr word 1) (N.shiftr mask 1) in
      if N.odd mask
      then N.b2n (N.odd word) + 2 * tail
      else tail
  end.

Definition pext64 (word mask : N) : N :=
  pext_fuel 64 word mask.

Definition pext_u64_even_mask : N :=
  6148914691236517205.

Fixpoint pext_even_mask_fuel (fuel : nat) : N :=
  match fuel with
  | O => 0
  | S fuel' => N.succ_double (N.double (pext_even_mask_fuel fuel'))
  end.

Lemma N_odd_succ_double_double n :
  N.odd (N.succ_double (N.double n)) = true.
Proof.
  destruct n; reflexivity.
Qed.

Lemma N_shiftr1_succ_double_double n :
  N.shiftr (N.succ_double (N.double n)) 1 = N.double n.
Proof.
  rewrite <- N.div2_spec.
  apply N.div2_succ_double.
Qed.

Lemma N_odd_double n :
  N.odd (N.double n) = false.
Proof.
  destruct n; reflexivity.
Qed.

Lemma N_shiftr1_double n :
  N.shiftr (N.double n) 1 = n.
Proof.
  rewrite <- N.div2_spec.
  apply N.div2_double.
Qed.

(** The storage-page code uses the mask [0x5555...5555], which keeps exactly
    the even input bits.  This derived model is convenient for the MIP-8 proof
    because its bit-level lemmas can mention input bit [2 * i] directly. *)
Fixpoint pext_even_fuel (fuel : nat) (word : N) : N :=
  match fuel with
  | O => 0
  | S fuel' =>
      N.b2n (N.odd word) +
      2 * pext_even_fuel fuel' (N.shiftr word 2)
  end.

Definition pext_even64 (word : N) : N :=
  pext_even_fuel 32 word.

Lemma pext_fuel_bound fuel word mask :
  pext_fuel fuel word mask < 2 ^ N.of_nat fuel.
Proof.
  revert word mask.
  induction fuel as [| fuel IH]; intros word mask.
  {
    simpl.
    lia.
  }
  simpl.
  pose proof (IH (N.shiftr word 1) (N.shiftr mask 1)) as Htail.
  rewrite Nat2N.inj_succ.
  rewrite N.pow_succ_r'; try lia.
  destruct (N.odd mask); destruct (N.odd word); simpl; nia.
Qed.

Lemma pext64_bound word mask :
  pext64 word mask < 2 ^ 64.
Proof.
  unfold pext64.
  pose proof (pext_fuel_bound 64 word mask) as Hbound.
  change (N.of_nat 64) with 64%N in Hbound.
  exact Hbound.
Qed.

Lemma pext_even_fuel_bound fuel word :
  pext_even_fuel fuel word < 2 ^ N.of_nat fuel.
Proof.
  revert word.
  induction fuel as [| fuel IH]; intro word.
  {
    simpl.
    lia.
  }
  simpl.
  pose proof (IH (N.shiftr word 2)) as Htail.
  rewrite Nat2N.inj_succ.
  rewrite N.pow_succ_r'; try lia.
  destruct (N.odd word); simpl; nia.
Qed.

Lemma pext_even64_bound word :
  pext_even64 word < 2 ^ 64.
Proof.
  unfold pext_even64.
  pose proof (pext_even_fuel_bound 32 word).
  change (N.of_nat 32) with 32%N in H.
  assert (2 ^ 32 < 2 ^ 64)%N.
  {
    apply N.pow_lt_mono_r; lia.
  }
  lia.
Qed.

Lemma pext_fuel_even_mask fuel word :
  pext_fuel (2 * fuel)%nat word (pext_even_mask_fuel fuel) =
  pext_even_fuel fuel word.
Proof.
  revert word.
  induction fuel as [| fuel IH]; intro word.
  {
    reflexivity.
  }
  replace (2 * S fuel)%nat with (S (S (2 * fuel)))%nat by lia.
  cbn [pext_even_mask_fuel pext_fuel pext_even_fuel].
  rewrite N_odd_succ_double_double.
  rewrite N_shiftr1_succ_double_double.
  cbn [pext_fuel].
  rewrite N_odd_double.
  rewrite N_shiftr1_double.
  rewrite IH.
  rewrite N.shiftr_shiftr.
  reflexivity.
Qed.

Lemma pext_even_mask_fuel_32 :
  pext_even_mask_fuel 32 = pext_u64_even_mask.
Proof.
  reflexivity.
Qed.

Lemma pext64_even_mask word :
  pext64 word pext_u64_even_mask = pext_even64 word.
Proof.
  unfold pext64, pext_even64.
  rewrite <- pext_even_mask_fuel_32.
  change 64%nat with (2 * 32)%nat.
  apply pext_fuel_even_mask.
Qed.

#[global] Hint Resolve pext_even64_bound : pure.
#[global] Hint Resolve pext64_bound : pure.
#[global] Hint Opaque
  pext_fuel pext64 pext_even_mask_fuel pext_even_fuel pext_even64
  : sl_opacity.
Opaque pext_fuel pext64 pext_even_mask_fuel pext_even_fuel pext_even64.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  (** A nonempty typed slice discharges [memcpy]'s nonnull requirement even
      when its base is a nested field pointer. *)
  Lemma typed_slice_nonempty_nonnull (p : ptr) ty (len : Z) :
    (0 < len)%Z ->
    p |-> typed_sliceR ty 0 len |-- [| p <> nullptr |].
  Proof.
    intro Hlen.
    destruct (decide (p = nullptr)) as [-> | Hnonnull].
    {
      rewrite typed_sliceR.unlock nullptr_array_sliceR.
      go.
      lia.
    }
    go.
  Qed.

  Definition typed_slice_nonempty_nonnull_B p ty len Hlen :=
    [BWD] (typed_slice_nonempty_nonnull p ty len Hlen).

  cpp.spec "std::countr_zero<unsigned long>(unsigned long)"
    from storage_page_cpp.source as std_countr_zero_ulong_spec
    with (
      \arg{x : N} "__x" (Vn x)
      \post [Vint (Z.of_N (countr_zero64 x))] emp
    ).

  cpp.spec "std::popcount<unsigned long>(unsigned long)"
    from storage_page_cpp.source as std_popcount_ulong_spec
    with (
      \arg{x : N} "__x" (Vn x)
      \post [Vint (Z.of_N (popcount64 x))] emp
    ).

  cpp.spec "_pext_u64(unsigned long long, unsigned long long)"
    from storage_page_cpp.source as pext_u64_spec
    with (
      \arg{x : N} "__X" (Vn x)
      \arg{mask : N} "__Y" (Vn mask)
      \post{result : N} [Vn result]
        [| result = pext64 x mask |] **
        [| result < 2 ^ 64 |]
    ).

End with_Sigma.
