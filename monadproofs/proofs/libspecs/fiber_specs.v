Require Import skylabs.auto.cpp.proof.

Require Import monad.asts.exb.
Require Import monad.proofs.misc.

Definition PriorityPool: Type. Proof using. Admitted.

Section cp.
  Import own.
  Import frac.

  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}.
  Context {MODd : exb.source ⊧ CU}.

  Definition PriorityPoolR (q: Qp) (c: PriorityPool): Rep. Proof using. Admitted.

  (* set_value() passes the resource/assertion P to the one calling get_future->wait() *)
  Definition PromiseR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseProducerR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseConsumerR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseUnusableR: Rep. Proof using. Admitted.

  Lemma sharePromise g P: PromiseR g P -|- PromiseProducerR g P ** PromiseConsumerR g P.
  Proof using. Admitted.

  Lemma changePromisedResource g P P': PromiseR g P |-- |==> PromiseR g P'.
  Proof. Admitted.

  Definition promise_constructor_spec (this:ptr) : WpSpec mpredI val val :=
    \pre{P:mpred} emp
    \post Exists g:gname, this |-> PromiseR g P.

  cpp.spec "boost::fibers::promise<void>::set_value()" as set_value with
    (fun (this:ptr) =>
      \pre{(P:mpred) (g:gname)} this |-> PromiseProducerR g P
      \pre P
      \post emp).

  #[local] Definition fork_task_namei :=
    Eval vm_compute in (firstEntryName (findBodyOfFnNamed2 exb.source (isFunctionNamed2 "fork_task"))).

  Definition all_but_last {T:Type} (l: list T) := take (length l - 1)%nat l.

  Definition fork_task_nameg (taskLamStructTy: core.name) :=
    match fork_task_namei with
    | Ninst (Nscoped (Nglobal (Nid scopename)) (Nfunction q base argTypes)) templateArgs =>
        let argTypes' := all_but_last argTypes ++ [Tref (Tqualified QC (Tnamed taskLamStructTy))] in
        Ninst (Nscoped (Nglobal (Nid scopename)) (Nfunction q base argTypes')) [Atype (Tnamed taskLamStructTy)]
    | _ => Nunsupported "no match"
    end.

  Definition taskOpName : atomic_name := (Nop function_qualifiers.Nc OOCall) [].

  Definition taskOpSpec (lamStructName: core.name) (objOwnership: Rep) (taskPre: mpred) :=
    specify {| info_name := (Nscoped lamStructName taskOpName);
               info_type := tMethod lamStructName QC "void" [] |}
      (fun (this:ptr) =>
         \prepost this |-> objOwnership
         \pre taskPre
         \post emp).

  Definition forkTaskSpec (lamStructName: core.name) : WpSpec mpredI val val :=
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \arg{priority} "i" (Vint priority)
    \arg{task:ptr} "func" (Vref task)
    \pre{objOwnership taskPre} taskOpSpec lamStructName objOwnership taskPre
    \prepost task |-> objOwnership
    \pre taskPre
    \post emp.

  Definition fork_taskg (lamStructTyName: core.name) :=
    λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
      specify
        {|
          info_name :=
            Ninst
              (Nscoped (Nglobal (Nid "monad"))
                 (Nfunction function_qualifiers.N "fork_task"
                    [Tref (Tnamed (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "fiber")) (Nid "PriorityPool")));
                     "unsigned long"%cpp_type;
                     Tref (Tconst (Tnamed lamStructTyName))]))
              [Atype (Tnamed lamStructTyName)];
          info_type :=
            tFunction "void"
              [Tref (Tnamed (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "fiber")) (Nid "PriorityPool")));
               "unsigned long"%cpp_type;
               Tref (Tconst (Tnamed lamStructTyName))]
        |}
        (forkTaskSpec lamStructTyName).

  #[global] Instance learnPpool : LearnEq2 PriorityPoolR := ltac:(solve_learnable).
  #[global] Instance : LearnEq2 PromiseR := ltac:(solve_learnable).
  #[global] Instance : LearnEq2 PromiseProducerR := ltac:(solve_learnable).
  #[global] Instance : LearnEq2 PromiseConsumerR := ltac:(solve_learnable).
End cp.
