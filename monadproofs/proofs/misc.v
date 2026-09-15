Require Import QArith.
From Stdlib Require Import Lia.
Require Import skylabs.auto.cpp.proof.
Require skylabs.upstream.cpp.hw_utils.
Require skylabs.upstream.cpp.misc_tactics.
(* [misc_tactics] globally changes both settings. Restore the client defaults;
   strict goal selection remains local to this file, as before the import. *)
#[global] Set Warnings "-sl-transparent-constants".
#[global] Set Default Goal Selector "1".
Set Default Goal Selector "!".
(* Restore stdpp's policy, also overridden by [misc_tactics]: symbolic lengths
   must remain arithmetic expressions rather than nested binary-number matches. *)
#[global] Arguments N.sub : simpl never.

Require Import stdpp.gmap.
Require Import skylabs.auto.cpp.tactics4.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import cQp_compat.
Notation logicalR := (to_frac_ag).
Notation asbool := bool_decide.
#[global] Hint Rewrite @repeat_length: syntactic.
#[global] Hint Rewrite @length_cons: syntactic.
#[global] Hint Rewrite @firstn_0: syntactic.
#[global] Hint Rewrite @lengthN_app: syntactic.
#[global] Hint Rewrite length_seq: syntactic.
#[global] Hint Rewrite Z2N.id using lia: syntactic.
#[global] Hint Rewrite @inj_iff using (typeclasses eauto): iff.
#[global] Hint Rewrite negb_if: syntactic.
#[global] Hint Rewrite bool_decide_eq_true_2 using (auto; fail): syntactic.
#[global] Hint Rewrite bool_decide_eq_false_2 using (auto; fail): syntactic.
#[global] Hint Rewrite @elem_of_cons: iff.
#[global] Hint Rewrite N.sub_diag : syntactic.
#[global] Hint Rewrite seqN_lengthN @lengthN_nil @seqN_S_start: syntactic.
#[global] Hint Rewrite orb_true_r: syntactic.
#[global] Hint Rewrite N_nat_Z: syntactic.
#[global] Hint Rewrite @left_id using (exact _): equiv.
#[global] Hint Rewrite @right_id using (exact _): equiv.
#[global] Hint Rewrite @list_elem_of_difference: iff.
#[global] Hint Rewrite @propset_singleton_equiv: equiv.
#[global] Hint Resolve array_combine_C: sl_opacity.
#[global] Hint Rewrite @length_drop: syntactic.
#[global] Hint Rewrite @lengthN_map: syntactic.

Require Import Btauto.

#[global] Hint Rewrite @takeN_lengthN using lia : syntactic.

Lemma sizeLen {A : Type} (foo : list A) size (p : 0 <= size) :
  (lengthN foo = Z.to_N (size - 0)) <-> (size = lengthZ foo).
Proof using.
  intros.
  unfold lengthN in *.
  autorewrite with syntactic.
  ring_simplify_goal_hyps Z.
  split; lia.
Qed.

#[global] Hint Rewrite @sizeLen using lia : iff.

Import linearity.
Hint Rewrite @firstn_all: syntactic.
Hint Rewrite Nat.add_0_r Z.add_0_r :syntactic.
Hint Rewrite @drop_all: syntactic.
Hint Rewrite nat_N_Z: syntactic.
Hint Rewrite @offset_ptr_sub_0 using (auto; apply has_size; exact _): syntactic.
Hint Rewrite @skipn_0: syntactic.

#[local] Open Scope Z_scope.

Import cancelable_invariants.

Ltac wapplyObserve lemma:=
  try intros;
  misc_tactics.wapplyObserve lemma.
Section tacLemmas.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}. (* some standard assumptions about the c++ logic *)

  Lemma observe_elim_rep (Q P : Rep) (p:ptr): Observe Q P → p |-> P ⊢ p|->(P ∗ Q).
  Proof using.
    intros Ho.
    apply _at_mono.
    wapplyObserve Ho.
    go.
  Qed.

End tacLemmas.

Opaque coPset_difference.

Section cp.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}. (* some standard assumptions about the c++ logic *)

  Definition offsetR_only_fwd := ([BWD->] _offsetR_only_provable).
  Hint Resolve offsetR_only_fwd: sl_opacity. (* repeat at the end *)

  Lemma arrDecompose {T} (p:ptr) ltr (R: T -> Rep) (ty:type):
    p |-> arrayR ty R ltr
   -|- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
     ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) ∗
      ([∗ list] k↦t ∈ ltr, p .[ ty ! k ] |-> R t).
  Proof using.
    rewrite arrayR_eq.
    unfold arrayR_def.
    rewrite arrR_eq.
    unfold arrR_def.
    repeat rewrite length_fmap.
    repeat rewrite big_opL_fmap.
    iSplit; go.
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
      iClear "#".
      iStopProof.
      f_equiv.
      go.
    }
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
       hideLhs.
       rewrite big_sepL_proper; try go.
       2:{ intros. iSplit. 2:{go.  evartacs.maximallyInstantiateLhsEvar. }  go. }
       simpl.
       unhideAllFromWork.
       go.
    }
  Qed.

  Lemma arrayR_nils{T} ty (R:T->_) : arrayR ty R [] = (.[ ty ! 0%nat ] |-> validR ∗ [| is_Some (size_of CU ty) |] ∗ emp)%I.
  Proof. rewrite arrayR_eq /arrayR_def arrR_eq /arrR_def. simpl. reflexivity. Qed.

  Lemma primr_split (p:ptr) ty (q:Qp) v :
    p|-> primR ty (cQp.mut q) v -|- (p |-> primR ty (cQp.mut q/2) v) ** p |-> primR ty (cQp.mut q/2) v.
  Proof using.
    rewrite -> cfractional_split_half with (R := fun q => primR ty q v).
    2:{ exact _. }
    rewrite _at_sep.
    f_equiv; f_equiv; f_equiv;
    simpl;
      rewrite cQp.scale_mut;
      f_equiv;
    destruct q; simpl in *;
      solveQpeq;
      solveQeq.
  Qed.
  Definition primR_split_C := [CANCEL] primr_split.

  Open Scope Z_scope.
  Lemma spurious {T:Type} {ing: Inhabited T} (P: mpred) :
  P |-- Exists a:T, P.
  Proof using.
    work.
    iExists (@inhabitant T _).
    work.
  Qed.

  Lemma arrayR_combinep {T} ty (R: T->Rep) i xs (p:ptr):
    p |-> arrayR ty R (take i xs) **
      p .[ ty ! i ] |-> arrayR ty R (drop i xs)
           |-- p |-> arrayR ty R xs.
  Proof using.
    go.
    hideLhs.
    rewrite <- arrayR_combine.
    unhideAllFromWork.
    go.
  Qed.
  Definition arrayR_combineC := [CANCEL] @arrayR_combinep. (* this hint will apply once we state everything in Z terms *)

  #[global] Instance learnArrUnsafe e t: LearnEq2 (@arrayR _ _ _ e _ t) := ltac:(solve_learnable).

End cp.

Hint Resolve prefix_app_r: list.

Hint Rewrite @arrayR_nils: syntactic.

Hint Rewrite @length_take_le using lia: syntactic.

Hint Resolve primR_split_C : sl_opacity.

Require Import skylabs.prelude.propset.

Ltac unhideAllFromWork :=  tactics.unhideAllFromWork;
                           try match goal with
                               H := _ |- _ => subst H
                             end.

    Hint Rewrite Nat2Z.inj_div : syntactic.
    Hint Rewrite Nat2Z.inj_sub using lia: syntactic.
    Hint Rewrite Z.quot_div_nonneg using lia : syntactic.

#[global] Hint Rewrite <- @spurious using exact _: slbwd.
#[global] Hint Resolve arrayR_combineC : sl_opacity.

Hint Rewrite bool_decide_spec: iff.

Hint Resolve list_subseteq_app_r : listset.
Hint Resolve list_subseteq_app_l : listset.
Hint Rewrite Z.min_l  using lia: syntactic.
Hint Rewrite Z.min_r  using lia: syntactic.
Hint Rewrite N.min_l  using lia: syntactic.
Hint Rewrite N.min_r  using lia: syntactic.

Hint Rewrite @elem_of_cons: syntactic.
Hint Rewrite orb_true_iff andb_true_iff: iff.
Hint Rewrite -> bool_decide_eq_true : iff.

From stdpp Require Import fin_maps.

Hint Rewrite @gmap.lookup_insert_iff : syntactic.

Section wp_const_compat.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}.

  (* Preserves the old libspecs backward hint for eliminating trivial wp_const goals. *)
  Lemma wp_const_const_delete tu ty from to p Q :
    const.type_is_const ty ->
    Q |-- wp_const tu from to p ty Q.
  Proof using.
    apply const.wp_const_const.
  Qed.

  Definition constRemB := [BWD<-]wp_const_const_delete.
End wp_const_compat.

Require Export monad.proofs.disableIPMtacs_use_go_instead.
