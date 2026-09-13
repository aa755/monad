Require Import skylabs.auto.cpp.proof.
Require Export skylabs.auto.cpp.spec.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.cpp.spec.concepts.experimental.
Require Import skylabs.brick.libstdcpp.vector.spec.

Section with_Sigma.
  Import own.
  Import frac.

  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}.

  Section vector_at_specs.
    Context (ty : type).
    Context {A : Type}.
    Context {cb : concepts.BundledRep ty A}.

    Definition vector_at_const_spec :=
      specify.template.method
        ("std::vector".<< Atype ty, Atype (std.allocator.T ty) >>)%cpp_name
        "at" function_qualifiers.Nc (Tref (Tconst ty)) [Tulong] $
        \this this
        \arg{i} "__n" (Vint i)
        \prepost{q size st}
          this |-> std.vector.spineR ty (std.allocator.T ty) q size st
        \prepost{qelt xs}
          std.vector.base_pointer st
          |-> arrayLR ty 0 size (concepts.objR ty qelt) xs
        \require (0 ≤ i < size)%Z
        \post[Vref (std.vector.base_pointer st .[ ty ! i])] emp.
  End vector_at_specs.

  Definition SpecFor_vector_at_const := RegisterSpec (@vector_at_const_spec).
End with_Sigma.

#[global] Existing Instance SpecFor_vector_at_const.
#[global] Arguments vector_at_const_spec : simpl never.
#[global] Hint Opaque vector_at_const_spec : sl_opacity.
