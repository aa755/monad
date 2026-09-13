Require Import skylabs.auto.cpp.proof.
Require Export skylabs.auto.cpp.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition DequeSpineR (ty alloc_ty : type) (q : Qp) (elts : list ptr) : Rep.
  Proof using.
    Admitted.

  Definition DequeR {A : Type} (ty alloc_ty : type)
      (elemR : Qp -> A -> Rep) (q : Qp) (elts : list (ptr * A)) : Rep :=
    DequeSpineR ty alloc_ty q (map fst elts)
    ** pureR ([∗ list] elt ∈ elts,
         let '(loc, v) := elt in (loc : ptr) |-> elemR q v).

  #[global] Instance learnDequeSpineR ty alloc_ty :
    LearnEq2 (DequeSpineR ty alloc_ty) := ltac:(solve_learnable).

  #[global] Instance learnDequeR {A : Type} ty alloc_ty elemR :
    LearnEq2 (@DequeR A ty alloc_ty elemR) := ltac:(solve_learnable).

  Section deque_specs.
    Context (ty alloc_ty : type).

    #[local] Notation deque :=
      ("std::deque".<< Atype ty, Atype alloc_ty >>)%cpp_name.

    Definition deque_empty_spec :=
      specify.template.method deque "empty" function_qualifiers.Nc Tbool [] $
        \this this
        \prepost{{A : Type} (elemR : Qp -> A -> Rep) q elts}
          this |-> DequeR ty alloc_ty elemR q elts
        \post[Vbool (match elts with [] => true | _ => false end)] emp.

    Definition deque_back_spec :=
      specify.template.method deque "back" function_qualifiers.N (Tref ty) [] $
        \this this
        \pre{{A : Type} (elemR : Qp -> A -> Rep) q prefix lastp last}
          this |-> DequeR ty alloc_ty elemR q (prefix ++ [(lastp, last)])
        \post[Vref lastp]
          lastp |-> elemR q last
          ** Forall last' : A,
               lastp |-> elemR q last'
               -* this |-> DequeR ty alloc_ty elemR q (prefix ++ [(lastp, last')]).
  End deque_specs.

  Definition SpecFor_deque_empty := RegisterSpec (@deque_empty_spec).
  #[global] Existing Instance SpecFor_deque_empty.

  Definition SpecFor_deque_back := RegisterSpec (@deque_back_spec).
  #[global] Existing Instance SpecFor_deque_back.
End with_Sigma.

#[global] Hint Opaque DequeSpineR DequeR : sl_opacity.
#[global] Hint Opaque deque_empty_spec deque_back_spec : sl_opacity.
#[global] Arguments deque_empty_spec : simpl never.
#[global] Arguments deque_back_spec : simpl never.
