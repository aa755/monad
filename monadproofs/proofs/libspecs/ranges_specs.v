Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.brick.libstdcpp.vector.spec.

Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.optional_specs.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}.

  Definition templated_method
      (name class: name) (qs: function_qualifiers.t) (ret: type) (args: list type)
      (spec: ptr -> WpSpec_cpp_val) : mpred :=
    _global name |-> unmaterialized_specR
      (tMethod class (function_qualifiers.to_type_qualifiers qs) ret args) spec.

  Definition std_ranges_contains_spec : mpred :=
    specify
      {| info_name := "std::ranges::contains"%cpp_name;
         info_type := tFunction
                        (Tref
                           (Tconst "std::ranges::__contains_fn"%cpp_type)) [] |}
      (\post [Vptr (_global "std::ranges::contains")] emp).

  Definition SpecFor_std_ranges_contains := RegisterSpec std_ranges_contains_spec.

  Definition ranges_contains_optional_address_spec
      {A : Type} `{!EqDecision A}
      (vecR : Qp -> list (option A) -> Rep)
      (keyR : Qp -> A -> Rep) :=
    templated_method
      "std::ranges::__contains_fn::operator()<const std::vector<std::optional<monad::Address>, std::allocator<std::optional<monad::Address>>>&, std::identity, monad::Address>(const std::vector<std::optional<monad::Address>, std::allocator<std::optional<monad::Address>>>&, const monad::Address&, std::identity) const"%cpp_name
      "std::ranges::__contains_fn"%cpp_name function_qualifiers.Nc Tbool
      [Tref
         (Tconst
            (std.vector.T
               "std::optional<monad::Address>"
               (std.allocator.T "std::optional<monad::Address>")));
       Tref (Tconst "monad::Address");
       "std::identity"%cpp_type] $
      \this this
      \arg{vecp: ptr} "__r" (Vref vecp)
      \arg{needlep: ptr} "__value" (Vref needlep)
      \arg{projp: ptr} "__proj" (Vptr projp)
      \prepost{q xs} vecp |-> vecR q xs
      \prepost{qk k} needlep |-> keyR qk k
      \prepost{qp} projp |-> structR "std::identity" qp
      \post[Vbool (bool_decide (Some k ∈ xs))] emp.

  Definition identity_ctor_spec :=
    specify.template.ctor "std::identity"%cpp_name [] $
      \this this
      \pre emp
      \post this |-> structR "std::identity" 1.

  Definition SpecFor_identity_ctor := RegisterSpec identity_ctor_spec.

  Definition identity_dtor_spec :=
    specify.template.dtor "std::identity"%cpp_name $
      \this this
      \pre this |-> structR "std::identity" 1
      \post emp.

  Definition SpecFor_identity_dtor := RegisterSpec identity_dtor_spec.

  Lemma identity_half_combine (p : ptr) :
    p |-> structR "std::identity" ((1 / 4)$m) **
    p |-> structR "std::identity" ((1 / 4)$m)
    |-- p |-> structR "std::identity" ((1 / 2)$m).
  Proof.
    rewrite <- _at_sep.
    rewrite <- (cfractional ((1 / 4)$m) ((1 / 4)$m)
                  (P := fun q => structR "std::identity" q)).
    apply _at_mono.
    f_equiv.
    solveCqpeq.
  Qed.

  Lemma identity_full_combine (p : ptr) :
    p |-> structR "std::identity" ((1 / 2)$m) **
    p |-> structR "std::identity" ((1 / 2)$m)
    |-- p |-> structR "std::identity" 1$m.
  Proof.
    rewrite <- _at_sep.
    rewrite <- (cfractional ((1 / 2)$m) ((1 / 2)$m)
                  (P := fun q => structR "std::identity" q)).
    apply _at_mono.
    f_equiv.
    solveCqpeq.
  Qed.

  Definition identity_half_combineC := [CANCEL] identity_half_combine.

  Definition identity_full_combineC := [CANCEL] identity_full_combine.
End with_Sigma.

#[global] Existing Instance SpecFor_std_ranges_contains.
#[global] Existing Instance SpecFor_identity_ctor.
#[global] Existing Instance SpecFor_identity_dtor.
#[global] Hint Resolve identity_half_combineC : sl_opacity.
#[global] Hint Resolve identity_full_combineC : sl_opacity.
#[global] Hint Opaque identity_ctor_spec : sl_opacity.
#[global] Hint Opaque identity_dtor_spec : sl_opacity.
