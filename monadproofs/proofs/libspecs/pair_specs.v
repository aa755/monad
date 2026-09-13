Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.

Set Default Goal Selector "!".

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Definition pairOffsets (aty bty : type) (fst : bool) : offset :=
    _field
      (Nscoped
         (Ninst "std::pair" [Atype aty; Atype bty])
         (Nid (if fst then "first"%pstring else "second"%pstring))).

  Definition pairFstOffset (tykey tyval : type) : offset :=
    pairOffsets tykey tyval true.

  Definition pairSndOffset (tykey tyval : type) : offset :=
    pairOffsets tykey tyval false.

  Definition pairR {K V : Type}
      (tykey tyval : type)
      (krep : Qp -> K -> Rep)
      (vrep : Qp -> V -> Rep)
      (qk qv : Qp) (v : K * V) : Rep :=
    pairFstOffset tykey tyval |-> krep qk v.1
    ** pairSndOffset tykey tyval |-> vrep qv v.2.

  Definition pair_name (tykey tyval : type) : name :=
    ("std::pair".<< Atype tykey, Atype tyval >>)%cpp_name.

  Definition pair_ty (tykey tyval : type) : type :=
    Tnamed (pair_name tykey tyval).

  Section pair_specs.
    Context (ty1 ty2 : type).

    (* Fixed element models at the library boundary; their copy constructors
       must preserve these models. BundledRep itself does not establish this. *)
    Definition pair_const_ref_ctor_spec
        {K V : Type}
        {cb1 : concepts.BundledRep ty1 K}
        {cb2 : concepts.BundledRep ty2 V} :=
      specify.template.ctor (pair_name ty1 ty2)
        [Tref (Tconst ty1); Tref (Tconst ty2)] $
        fun this : ptr =>
        \arg{firstp : ptr} "__x" (Vref firstp)
        \arg{secondp : ptr} "__y" (Vref secondp)
        \prepost{(qfirst qsecond : cQp.t) (first : K) (second : V)}
          firstp |-> concepts.objR ty1 qfirst first
          ** secondp |-> concepts.objR ty2 qsecond second
        \post this |-> pairR ty1 ty2
          (fun q => concepts.objR ty1 (cQp.mut q))
          (fun q => concepts.objR ty2 (cQp.mut q))
          1 1 (first, second).

    Definition pair_get0_spec :=
      specify.template.func "std::get"%cpp_name
        [Avalue (Eint 0 Tulong); Atype ty1; Atype ty2]
        (Tref (Tconst ty1)) [Tref (Tconst (pair_ty ty1 ty2))] $
        \arg{pp : ptr} "p" (Vref pp)
        \post[Vref (pp ,, pairFstOffset ty1 ty2)] emp.

    Definition pair_get1_spec :=
      specify.template.func "std::get"%cpp_name
        [Avalue (Eint 1 Tulong); Atype ty1; Atype ty2]
        (Tref (Tconst ty2)) [Tref (Tconst (pair_ty ty1 ty2))] $
        \arg{pp : ptr} "p" (Vref pp)
        \post[Vref (pp ,, pairSndOffset ty1 ty2)] emp.

    Definition pair_dtor_spec :=
      specify.template.dtor (pair_name ty1 ty2) $
        \this this
        \pre{firstR secondR}
          this ,, pairFstOffset ty1 ty2 |-> firstR
          ** this ,, pairSndOffset ty1 ty2 |-> secondR
        \post emp.
  End pair_specs.
End with_Sigma.

#[global] Arguments pair_name /.
#[global] Arguments pair_ty /.
#[global] Hint Opaque pairR pairFstOffset pairSndOffset : sl_opacity.
#[global] Hint Opaque
  pair_const_ref_ctor_spec pair_get0_spec pair_get1_spec pair_dtor_spec
  : sl_opacity.

Definition SpecFor_pair_const_ref_ctor :=
  RegisterSpec (@pair_const_ref_ctor_spec).
#[global] Existing Instance SpecFor_pair_const_ref_ctor.

Definition SpecFor_pair_dtor := RegisterSpec (@pair_dtor_spec).
#[global] Existing Instance SpecFor_pair_dtor.

Definition SpecFor_pair_get0 := RegisterSpec (@pair_get0_spec).
#[global] Existing Instance SpecFor_pair_get0.

Definition SpecFor_pair_get1 := RegisterSpec (@pair_get1_spec).
#[global] Existing Instance SpecFor_pair_get1.
