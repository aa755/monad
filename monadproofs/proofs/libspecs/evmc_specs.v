Set Default Goal Selector "!".

(*
  Specs and proof support for small EVMC value-type operations shared by C++
  proofs.

  The concrete representation [bytes32R] is defined in [exec_specs.v].  This
  file keeps generic [monad::bytes32_t] equality/move specs and reusable
  [monad::bytes32_t] initialization/destruction plumbing out of the MIP-8
  storage-page spec file.
*)

From Stdlib Require Import List NArith.

Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.cpp.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.const_specs.

Import cQp_compat.
Import linearity.

Definition bytes32_ty : type := "monad::bytes32_t"%cpp_type.
Definition evmc_bytes32_ty : type := "evmc_bytes32"%cpp_type.

Definition bytes32_evmc_bytes32_ctor_name : name :=
  "monad::bytes32_t::bytes32_t(const evmc_bytes32&)".

Definition bytes32_default_ctor_name : name :=
  "monad::bytes32_t::bytes32_t()".

Definition bytes32_default_init_expr : Expr :=
  Econstructor bytes32_default_ctor_name [] bytes32_ty.

Definition bytes32_zero_init_expr : Expr :=
  Econstructor
    bytes32_evmc_bytes32_ctor_name
    (Eimplicit
       (Einitlist
          (Eimplicit_init (Tarray Tuchar 32%N) :: nil)
          None evmc_bytes32_ty) :: nil)
    bytes32_ty.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  cpp.spec "monad::operator==(const monad::bytes32_t&, const monad::bytes32_t&)"
    from storage_page_cpp.source as bytes32_eq_spec
    with (
      \arg{ap : ptr} "a" (Vref ap)
      \arg{bp : ptr} "b" (Vref bp)
      \prepost{qa av} ap |-> bytes32R qa av
      \prepost{qb bv} bp |-> bytes32R qb bv
      \post [Vbool (N.eqb av bv)] emp
    ).

  cpp.spec "monad::bytes32_t::bytes32_t()"
    from storage_page_cpp.source as bytes32_default_ctor_spec
    with (
      fun this : ptr =>
        \post this |-> bytes32R 1 0
    ).

End with_Sigma.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Lemma wp_destroy_bytes32_value
      (tu : translation_unit) (base : ptr) (value : N) (Q : epred) :
    □ exec_specs.bytes32_dtor_spec
    ** base |-> exec_specs.bytes32R 1 value ** Q
    |-- wp_destroy_val tu QM bytes32_ty base Q.
  Proof.
    unfold bytes32_ty.
    go using exec_specs.bytes32_dtor_spec.
  Qed.

  Lemma destroy_run_bytes32_array :
    forall (tu : translation_unit) (base : ptr) (len : nat)
      (values : list N) (Q : epred),
      length values = len ->
      □ exec_specs.bytes32_dtor_spec
      ** base |-> arrayR bytes32_ty (exec_specs.bytes32R 1) values
      ** Q
      |-- destroy.run_array tu QM bytes32_ty base len Q.
  Proof.
    intros tu base len.
    induction len as [| len IH].
    {
      intros values Q Hlen.
      destruct values as [| value values].
      2: {
        cbn in Hlen.
        discriminate Hlen.
      }
      rewrite arrayR_nil.
      go.
    }
    intros values Q Hlen.
    destruct values as [| first rest].
    {
      cbn in Hlen.
      discriminate Hlen.
    }
    assert (Hnonempty : first :: rest <> []) by discriminate.
    destruct (exists_last (l := first :: rest) Hnonempty)
      as [prefix [last Hvalues]].
    rewrite Hvalues in Hlen.
    rewrite Hvalues.
    rewrite app_length in Hlen.
    cbn in Hlen.
    assert (Hprefix_len : length prefix = len).
    {
      lia.
    }
    rewrite arrayR_snoc !_at_sep !_at_offsetR.
    rewrite Hprefix_len.
    cbn [destroy.run_array].
    change (erase_qualifiers bytes32_ty) with bytes32_ty.
    iIntros "[#D [[A [_ B]] Rest]]"%string.
    iApply wp_destroy_bytes32_value.
    iFrame "D B"%string.
    iApply (IH prefix Q Hprefix_len with "[$D $A $Rest]"%string).
  Qed.

  (* Destruction of arrays whose element destructor is semantically inert for
     the represented bytes.  The local storage-page proofs own these arrays as
     [arrayR bytes32_ty (bytes32R 1) values], not as whole-array [anyR], so the
     generic [wp_destroy_val_array] optimization does not apply directly.

     The proof follows BRiCk's array-destruction semantics: split off the last
     element, destroy it with [bytes32_dtor_spec], and recurse on the remaining
     prefix. *)
  Lemma wp_destroy_bytes32_array :
    forall (tu : translation_unit) (base : ptr) (len : N)
      (values : list N) (Q : epred),
      length values = N.to_nat len ->
      □ exec_specs.bytes32_dtor_spec
      ** base |-> arrayR bytes32_ty (exec_specs.bytes32R 1) values
      ** Q
      |-- wp_destroy_array tu QM bytes32_ty len base Q.
  Proof.
    intros tu base len values Q Hlen.
    etrans.
    {
      apply destroy_run_bytes32_array.
      exact Hlen.
    }
    apply destroy.run_array_ok.
  Qed.
End with_Sigma.
