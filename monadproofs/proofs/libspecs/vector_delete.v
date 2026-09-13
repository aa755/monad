Require Import skylabs.auto.cpp.proof.
Require Export skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.hints.array.
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.cpp.spec.concepts.experimental.
Require Import skylabs.brick.libstdcpp.vector.spec.

Require Import monad.asts.exb.
Require Import monad.proofs.misc.

(* Deprecated compatibility layer for older local vector proofs. New specs should
   prefer the upstream std.vector library directly. *)
Section cp.
  Import own.
  Import frac.

  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}.
  Context {MODd : exb.source ⊧ CU}.

  Definition VectorRbase (cppType: type) (q:Qp) (base: ptr) (size: N): Rep.
  Proof using.
  Admitted.

  Definition VectorR {ElemType} (cppType: type) (elemRep: ElemType -> Rep) (q:Qp) (lt:list ElemType): Rep :=
    Exists (base: ptr), VectorRbase cppType q base (lengthN lt)
                      ** pureR (base |-> arrayR cppType elemRep lt).

  cpp.spec
    "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    as tvector_spec with
      (fun (this:ptr) =>
         \prepost{q base size} this |-> VectorRbase (Tnamed "::monad::Transaction") q base size
         \post[Vn size] (emp:mpred)
      ).

  Lemma vectorbase_loopinv {T} ty base q (l: list T) (i:nat) (Heq: i = 0):
    VectorRbase ty q base (lengthN l) -|-
    (VectorRbase ty (q * Qp.inv (N_to_Qp (1 + lengthN l))) base (lengthN l) **
     ([∗ list] _ ∈ (drop i l), VectorRbase ty (q * Qp.inv (N_to_Qp (1 + lengthN l))) base (lengthN l))).
  Proof using. Admitted.

  Lemma learnVUnsafe e t (r:e -> Rep): LearnEq2 (VectorR t r).
  Proof. solve_learnable. Qed.
  #[global] Instance learnVUnsafe2 e t: LearnEq3 (@VectorR e t) := ltac:(solve_learnable).
  #[global] Instance learnpArrUnsafe e t: LearnEq2 (@parrayR _ _ _ _ e t) := ltac:(solve_learnable).
  #[global] Instance learnVectorRbase: LearnEq4 VectorRbase := ltac:(solve_learnable).

  Definition vector_opg (cppType: type) (this:ptr): WpSpec mpredI val val :=
    \arg{index} "index" (Vn index)
    \prepost{qb base size} this |-> VectorRbase cppType qb base size
    \require (index < size)%Z
    \post [Vref (base ,, .[cppType!index])] emp.

End cp.

Opaque VectorR.
