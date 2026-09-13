Require Import skylabs.auto.cpp.proof.
Require Import stdpp.gmap.
Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.pair_specs.
Require Import skylabs.auto.cpp.hints.const.

Set Default Goal Selector "!".

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}.

  Definition templated_method
      (name class: name) (qs: function_qualifiers.t) (ret: type) (args: list type)
      (spec: ptr -> WpSpec_cpp_val) : mpred :=
    _global name |-> unmaterialized_specR
      (tMethod class (function_qualifiers.to_type_qualifiers qs) ret args) spec.

  Definition ModelWithPtr (ModelType : Type) : Type := ptr * ModelType.
  Definition MapModel K V := list (K * ModelWithPtr V).

  Definition anker_set_hash_name (key_ty : type) : name :=
    ("ankerl::unordered_dense::v4_1_0::hash".<<
        Atype key_ty, Atype Tvoid
    >>)%cpp_name.

  Definition anker_set_equal_to_name (key_ty : type) : name :=
    ("std::equal_to".<< Atype key_ty >>)%cpp_name.

  Definition anker_set_allocator_name (key_ty : type) : name :=
    ("std::allocator".<< Atype key_ty >>)%cpp_name.

  Definition anker_set_table_name (key_ty : type) : name :=
    ("ankerl::unordered_dense::v4_1_0::detail::table".<<
        Atype key_ty,
        Atype Tvoid,
        Atype (Tnamed (anker_set_hash_name key_ty)),
        Atype (Tnamed (anker_set_equal_to_name key_ty)),
        Atype (Tnamed (anker_set_allocator_name key_ty)),
        Atype "ankerl::unordered_dense::v4_1_0::bucket_type::standard",
        Avalue (Eint 1 Tbool)
    >>)%cpp_name.

  Definition anker_set_table_ty (key_ty : type) : type :=
    Tnamed (anker_set_table_name key_ty).

  Definition anker_set_segvec_name (key_ty : type) : name :=
    ("ankerl::unordered_dense::v4_1_0::segmented_vector".<<
        Atype key_ty,
        Atype (Tnamed (anker_set_allocator_name key_ty)),
        Avalue (Eint 4096 Tulong)
    >>)%cpp_name.

  Definition anker_set_iter_name (key_ty : type) (const_elements : bool) : name :=
    Ninst (Nscoped (anker_set_segvec_name key_ty) (Nid "iter_t"))
      [Avalue (Eint (if const_elements then 1 else 0) Tbool)].

  Definition anker_set_iter_ty (key_ty : type) (const_elements : bool) : type :=
    Tnamed (anker_set_iter_name key_ty const_elements).

  Definition anker_set_emplace_result_ty (key_ty : type) : type :=
    Tnamed ("std::pair".<<
      Atype (anker_set_iter_ty key_ty true), Atype Tbool
    >>)%cpp_name.

  (* The iterator half of emplace's result points into ankerl's segmented-vector
     internals. Current callers only destroy this pair, so keep that layout
     opaque until a caller needs to inspect the iterator or bool field. *)
  Definition anker_set_emplace_resultR
      (_key_ty : type) (_inserted : bool) : Rep.
  Proof using.
    Admitted.

  (** Contains q/2 ownership of the Key cells of the stored entries, but no
      ownership of associated value cells. [locs] is in iteration order. *)
  Definition AnkerMapSpineR {K : Type} (_tykey _tyval : type)
      (_khash : K -> N) {eqd : EqDecision K} (_keyR : Qp -> K -> Rep)
      (_q : Qp) (_locs : list (K * ptr)) : Rep.
  Proof using.
    Admitted.

  Definition AnkerSetR {K : Type} (key_ty : type) (khash : K -> N)
      `{!EqDecision K} (keyR : Qp -> K -> Rep) (q : Qp)
      (keys : list K) : Rep :=
    type_ptrR (anker_set_table_ty key_ty)
    ** Exists (locs : list (K * ptr)),
         [| map fst locs = keys |]
         ** AnkerMapSpineR key_ty Tvoid khash keyR q locs.

  Definition AnkerMapR {K V : Type} (tykey tyval : type)
      (khash : K -> N)
      (krep : Qp -> K -> Rep)
      (vrep : Qp -> V -> Rep)
      (q : Qp)
      (m : MapModel K V) : Rep.
  Proof using.
    Admitted.

  (** Contains [q/2] ownership of the key cells of the stored pairs, and [q]
      ownership of the value cells.  The list is in ankerl iteration order, but
      clients should normally use [AnkerMapR] and split only when they need a
      borrowed payload. *)
  Definition AnkerMapPayloadsR {K V : Type} (tykey tyval : type)
      (krep : Qp -> K -> Rep)
      (vrep : Qp -> V -> Rep)
      (q : Qp)
      (m : MapModel K V) : Rep.
  Proof using.
    Admitted.

  Definition removeKey {K V : Type} {eqd : EqDecision K}
      (m : MapModel K V) (k : K) :=
    List.filter (fun p => bool_decide (p.1 <> k)) m.

  Lemma borrowIndex {K V : Type} {eqd : EqDecision K}
      (tykey tyval : type)
      (krep : Qp -> K -> Rep)
      (vrep : Qp -> V -> Rep)
      (q : Qp)
      (m : MapModel K V) (borrowIndex : N) bt :
    nth_error m (N.to_nat borrowIndex) = Some bt ->
    AnkerMapPayloadsR tykey tyval krep vrep q m -|-
      AnkerMapPayloadsR tykey tyval krep vrep q (removeKey m bt.1)
      ** pureR (bt.2.1 |-> pairR tykey tyval krep vrep (q / 2) q
                   (bt.1, bt.2.2)).
  Proof using.
    Admitted.

  Lemma AnkerMapSplit {K V : Type} (tykey tyval : type) (khash : K -> N)
      {eqd : EqDecision K}
      (krep : Qp -> K -> Rep)
      (vrep : Qp -> V -> Rep)
      (q : Qp)
      (m : MapModel K V) :
    AnkerMapR tykey tyval khash krep vrep q m -|-
      AnkerMapSpineR tykey tyval khash krep q
        (map (fun p => let '(a, (b, _)) := p in (a, b)) m)
      ** AnkerMapPayloadsR tykey tyval krep vrep q m.
  Proof using.
    Admitted.

  Lemma AnkerMapSplit_at {K V : Type} (tykey tyval : type)
      (khash : K -> N) {eqd : EqDecision K}
      (krep : Qp -> K -> Rep) (vrep : Qp -> V -> Rep)
      (q : Qp) (m : MapModel K V) (p : ptr) :
    p |-> AnkerMapR tykey tyval khash krep vrep q m -|-
      p |-> AnkerMapSpineR tykey tyval khash krep q
        (map (fun kv => let '(a, (b, _)) := kv in (a, b)) m)
      ** p |-> AnkerMapPayloadsR tykey tyval krep vrep q m.
  Proof.
    rewrite AnkerMapSplit.
    iSplit; go.
  Qed.

  Definition asplitF {K V} := [FWD->] (@AnkerMapSplit_at K V).
  Definition asplitB {K V} := [BWD->] (@AnkerMapSplit_at K V).

  (** [i] is the index into the ordered list of tuple locations in
      [AnkerMapSpineR].  [spine] is the corresponding list of [std::pair]
      locations.  [i = length spine] is the one-past-end iterator; dereference
      specs require a successful [nth_error]. *)
  (* [const_elements] selects iter_t<IsConst>, i.e. whether dereferencing the iterator
     gives const elements. [q] separately tracks constness and ownership of
     the iterator object itself. Const-qualifying an iterator does not change
     which element it denotes or const-qualify that element.

     This is an abstract third-party boundary. A concrete implementation would
     own iter_t's structR, m_data pointer and m_idx size_t at [q], and relate
     m_data's segmented directory and m_idx to [spine] and [i]. *)
  Definition AnkerMapIterR (ktycpp vtycpp : type)
      (const_elements : bool) (q : cQp.t) (i : N)
      (spine : list ptr) : Rep.
  Proof using.
    Admitted.

  Definition anker_pair_name (ktycpp vtycpp : type) : name :=
    pair_name ktycpp vtycpp.

  Definition anker_pair_ty (ktycpp vtycpp : type) : type :=
    pair_ty ktycpp vtycpp.

  Definition anker_allocator_name (ktycpp vtycpp : type) : name :=
    ("std::allocator".<< Atype (anker_pair_ty ktycpp vtycpp) >>)%cpp_name.

  Definition anker_hash_name (ktycpp : type) : name :=
    ("ankerl::unordered_dense::v4_1_0::hash".<<
        Atype ktycpp, Atype Tvoid
    >>)%cpp_name.

  Definition anker_equal_to_name (ktycpp : type) : name :=
    ("std::equal_to".<< Atype ktycpp >>)%cpp_name.

  Definition anker_table_name (ktycpp vtycpp : type) : name :=
    ("ankerl::unordered_dense::v4_1_0::detail::table".<<
        Atype ktycpp,
        Atype vtycpp,
        Atype (Tnamed (anker_hash_name ktycpp)),
        Atype (Tnamed (anker_equal_to_name ktycpp)),
        Atype (Tnamed (anker_allocator_name ktycpp vtycpp)),
        Atype "ankerl::unordered_dense::v4_1_0::bucket_type::standard",
        Avalue (Eint 1 Tbool)
    >>)%cpp_name.

  Definition anker_segvec_name (ktycpp vtycpp : type) : name :=
    ("ankerl::unordered_dense::v4_1_0::segmented_vector".<<
        Atype (anker_pair_ty ktycpp vtycpp),
        Atype (Tnamed (anker_allocator_name ktycpp vtycpp)),
        Avalue (Eint 4096 Tulong)
    >>)%cpp_name.

  Definition anker_iter_name (ktycpp vtycpp : type)
      (const_elements : bool) : name :=
    Ninst (Nscoped (anker_segvec_name ktycpp vtycpp) (Nid "iter_t"))
      [Avalue (Eint (if const_elements then 1 else 0) Tbool)].

  Definition anker_iter_ty (ktycpp vtycpp : type)
      (const_elements : bool) : type :=
    Tnamed (anker_iter_name ktycpp vtycpp const_elements).

  (* Library representation law: conversion requires full ownership of the
     iterator, transforms its field permissions, and preserves its position.
     Unlike constRemB, this cannot erase a conversion without owning its object. *)
  Axiom AnkerMapIterR_const : forall tu ktycpp vtycpp const_elements i spine,
    const.CONST tu (anker_iter_ty ktycpp vtycpp const_elements)
      (fun q => AnkerMapIterR ktycpp vtycpp const_elements q i spine).

  Lemma AnkerMapIterR_wp_const (tu : translation_unit)
      ktycpp vtycpp const_elements i spine
      (p : ptr) (from to : bool) (Q : mpred) :
    p |-> AnkerMapIterR ktycpp vtycpp const_elements (cQp.mk from 1) i spine
    |--
    (p |-> AnkerMapIterR ktycpp vtycpp const_elements (cQp.mk to 1) i spine
       -* Q) -*
    wp_const tu (cQp.mk from 1) (cQp.mk to 1) p
      (anker_iter_ty ktycpp vtycpp const_elements) Q.
  Proof.
    apply (AnkerMapIterR_const tu ktycpp vtycpp const_elements i spine
      p from to tu Q).
    reflexivity.
  Qed.

  Definition AnkerMapIterR_const_C := [CANCEL] AnkerMapIterR_wp_const.

  #[global] Arguments anker_pair_name /.
  #[global] Arguments anker_pair_ty /.
  #[global] Arguments anker_allocator_name /.
  #[global] Arguments anker_hash_name /.
  #[global] Arguments anker_equal_to_name /.
  #[global] Arguments anker_table_name /.
  #[global] Arguments anker_segvec_name /.
  #[global] Arguments anker_iter_name /.
  #[global] Arguments anker_iter_ty /.

  Definition anker_iter_pair_firstR
      (ktycpp vtycpp : type) (_ : Qp) (m : N * list ptr) : Rep :=
    AnkerMapIterR ktycpp vtycpp false 1$m (fst m) (snd m).

  Definition anker_iter_pair_boolR (_ : Qp) (b : bool) : Rep :=
    boolR 1$m b.

  Definition anker_table_try_emplace_result_ty
      (ktycpp vtycpp : type) : type :=
    pair_ty (anker_iter_ty ktycpp vtycpp false) Tbool.

  Definition anker_table_try_emplace_resultR
      (ktycpp vtycpp : type) (spine : list ptr)
      (inserted : bool) : Rep :=
    let iter_ty := anker_iter_ty ktycpp vtycpp false in
    pairR
      iter_ty
      Tbool
      (anker_iter_pair_firstR ktycpp vtycpp)
      anker_iter_pair_boolR
      1 1
      ((0%N, spine), inserted).

  Section iterator_observations.
  Context {qi : cQp.t} {ic : bool}.

  Lemma observeAnkerIter (iter_addr : ptr) (ktycpp vtycpp : type)
      (const_elements : bool) i spine :
    Observe (type_ptr (anker_iter_ty ktycpp vtycpp const_elements) iter_addr)
            (iter_addr |-> AnkerMapIterR ktycpp vtycpp const_elements qi i spine).
  Proof using.
    Admitted.

  Lemma observeAnkerIterConst (iter_addr : ptr) (ktycpp vtycpp : type)
      (const_elements : bool) i spine :
    Observe
      (type_ptr (Tconst (anker_iter_ty ktycpp vtycpp const_elements)) iter_addr)
      (iter_addr |-> AnkerMapIterR ktycpp vtycpp const_elements qi i spine).
  Proof using.
    Admitted.

  Lemma observeAnkerIterR (ktycpp vtycpp : type)
      (const_elements : bool) i spine :
    Observe (type_ptrR (anker_iter_ty ktycpp vtycpp const_elements))
            (AnkerMapIterR ktycpp vtycpp const_elements qi i spine).
  Proof using.
    Admitted.

  Lemma observeAnkerIterConstR (ktycpp vtycpp : type)
      (const_elements : bool) i spine :
    Observe (type_ptrR (Tconst (anker_iter_ty ktycpp vtycpp const_elements)))
            (AnkerMapIterR ktycpp vtycpp const_elements qi i spine).
  Proof using.
    Admitted.

  Lemma observeAnkerTryEmplaceResultFirst
      (retp : ptr) (ktycpp vtycpp : type)
      (spine : list ptr) (inserted : bool) :
    Observe
      (type_ptr
        (anker_iter_ty ktycpp vtycpp false)
        (retp ,,
          pairFstOffset (anker_iter_ty ktycpp vtycpp false) Tbool))
      (retp |-> anker_table_try_emplace_resultR
        ktycpp vtycpp spine inserted).
  Proof using.
    Admitted.

  Lemma observeAnkerIterPointee
      (iter_addr ploc : ptr) (ktycpp vtycpp : type) i spine :
    nth_error spine (N.to_nat i) = Some ploc ->
    Observe (type_ptr (anker_pair_ty ktycpp vtycpp) ploc)
            (iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi i spine).
  Proof using.
    Admitted.

  Lemma observeAnkerIterPointeeValueField
      (iter_addr ploc : ptr) (ktycpp vtycpp : type) i spine :
    nth_error spine (N.to_nat i) = Some ploc ->
    Observe (type_ptr vtycpp (ploc ,, pairSndOffset ktycpp vtycpp))
            (iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi i spine).
  Proof using.
    Admitted.

  Lemma observeAnkerIterHeadPointee
      (iter_addr ploc : ptr) (ktycpp vtycpp : type) spine :
    Observe (type_ptr (anker_pair_ty ktycpp vtycpp) ploc)
            (iter_addr |-> AnkerMapIterR
              ktycpp vtycpp ic qi 0 (ploc :: spine)).
  Proof using.
    exact (observeAnkerIterPointee
      iter_addr ploc ktycpp vtycpp 0 (ploc :: spine) eq_refl).
  Qed.

  Lemma observeAnkerIterHeadPointeeValueField
      (iter_addr ploc : ptr) (ktycpp vtycpp : type) spine :
    Observe (type_ptr vtycpp (ploc ,, pairSndOffset ktycpp vtycpp))
            (iter_addr |-> AnkerMapIterR
              ktycpp vtycpp ic qi 0 (ploc :: spine)).
  Proof using.
    exact (observeAnkerIterPointeeValueField
      iter_addr ploc ktycpp vtycpp 0 (ploc :: spine) eq_refl).
  Qed.

  Definition observeAnkerIterFt r ktycpp vtycpp i spine :=
    @observe_fwd _ _ _ (observeAnkerIter r ktycpp vtycpp true i spine).

  Definition observeAnkerIterFf r ktycpp vtycpp i spine :=
    @observe_fwd _ _ _ (observeAnkerIter r ktycpp vtycpp false i spine).

  Definition observeAnkerIterConstFt r ktycpp vtycpp i spine :=
    @observe_fwd _ _ _
      (observeAnkerIterConst r ktycpp vtycpp true i spine).

  Definition observeAnkerIterConstFf r ktycpp vtycpp i spine :=
    @observe_fwd _ _ _
      (observeAnkerIterConst r ktycpp vtycpp false i spine).

  Definition observeAnkerIterPointeeF r ploc ktycpp vtycpp i spine Hnth :=
    @observe_fwd _ _ _
      (observeAnkerIterPointee r ploc ktycpp vtycpp i spine Hnth).

  Definition observeAnkerIterPointeeValueFieldF
      r ploc ktycpp vtycpp i spine Hnth :=
    @observe_fwd _ _ _
      (observeAnkerIterPointeeValueField
        r ploc ktycpp vtycpp i spine Hnth).

  Definition observeAnkerIterHeadPointeeF
      r ploc ktycpp vtycpp spine :=
    @observe_fwd _ _ _
      (observeAnkerIterHeadPointee
        r ploc ktycpp vtycpp spine).

  Definition observeAnkerIterHeadPointeeValueFieldF
      r ploc ktycpp vtycpp spine :=
    @observe_fwd _ _ _
      (observeAnkerIterHeadPointeeValueField
        r ploc ktycpp vtycpp spine).

  Definition observeAnkerTryEmplaceResultFirstF
      retp ktycpp vtycpp spine inserted :=
    @observe_fwd _ _ _
      (observeAnkerTryEmplaceResultFirst
        retp ktycpp vtycpp spine inserted).

  Definition observeAnkerIterRFt
      (ktycpp vtycpp : type) (i : N) (spine : list ptr) :=
    ltac:(mk_at_obs_fwd
      (@observeAnkerIterR ktycpp vtycpp true i spine)).

  Definition observeAnkerIterRFf
      (ktycpp vtycpp : type) (i : N) (spine : list ptr) :=
    ltac:(mk_at_obs_fwd
      (@observeAnkerIterR ktycpp vtycpp false i spine)).

  Definition observeAnkerIterConstRFt
      (ktycpp vtycpp : type) (i : N) (spine : list ptr) :=
    ltac:(mk_at_obs_fwd
      (@observeAnkerIterConstR ktycpp vtycpp true i spine)).

  Definition observeAnkerIterConstRFf
      (ktycpp vtycpp : type) (i : N) (spine : list ptr) :=
    ltac:(mk_at_obs_fwd
      (@observeAnkerIterConstR ktycpp vtycpp false i spine)).

  Lemma anker_iter_keep_type_ptr (iter_addr : ptr)
      (ktycpp vtycpp : type) (const_elements : bool) i spine :
    iter_addr |-> AnkerMapIterR ktycpp vtycpp const_elements qi i spine
    |--
    iter_addr |-> AnkerMapIterR ktycpp vtycpp const_elements qi i spine
    ** type_ptr (anker_iter_ty ktycpp vtycpp const_elements) iter_addr.
  Proof using.
    rewrite <- _at_type_ptrR.
    rewrite <- _at_sep.
    apply _at_mono.
    apply (@observe_elim _ _
      (AnkerMapIterR ktycpp vtycpp const_elements qi i spine)
      (observeAnkerIterR ktycpp vtycpp const_elements i spine)).
  Qed.

  Definition anker_iter_keep_type_ptr_C
      iter_addr ktycpp vtycpp const_elements i spine :=
    [CANCEL] (anker_iter_keep_type_ptr
      iter_addr ktycpp vtycpp const_elements i spine).

  End iterator_observations.

  Lemma anker_table_try_emplace_resultR_split_first_type_ptr
      (retp : ptr) (ktycpp vtycpp : type)
      (spine : list ptr) (inserted : bool) :
    retp |-> anker_table_try_emplace_resultR ktycpp vtycpp spine inserted
    |--
    retp ,, pairFstOffset (anker_iter_ty ktycpp vtycpp false) Tbool
      |-> AnkerMapIterR ktycpp vtycpp false 1$m 0%N spine
    ** retp ,, pairSndOffset (anker_iter_ty ktycpp vtycpp false) Tbool
      |-> boolR 1$m inserted
    ** type_ptr (anker_iter_ty ktycpp vtycpp false)
        (retp ,, pairFstOffset (anker_iter_ty ktycpp vtycpp false) Tbool).
  Proof using.
    unfold anker_table_try_emplace_resultR, pairR,
      anker_iter_pair_firstR, anker_iter_pair_boolR.
    rewrite _at_sep.
    repeat rewrite _at_offsetR.
    simpl.
    set (iterp :=
      retp ,, pairFstOffset (anker_iter_ty ktycpp vtycpp false) Tbool).
    set (boolp :=
      retp ,, pairSndOffset (anker_iter_ty ktycpp vtycpp false) Tbool).
    set (P := iterp |-> AnkerMapIterR ktycpp vtycpp false 1$m 0%N spine).
    set (Q := boolp |-> boolR 1$m inserted).
    set (R := type_ptr (anker_iter_ty ktycpp vtycpp false) iterp).
    change (P ** Q |-- P ** Q ** R).
    etransitivity.
    {
      apply bi.sep_mono_l.
      unfold P, R, iterp.
      exact (anker_iter_keep_type_ptr
        (retp ,, pairFstOffset (anker_iter_ty ktycpp vtycpp false) Tbool)
        ktycpp vtycpp false 0%N spine).
    }
    change ((P ** R) ** Q |-- P ** Q ** R).
    go.
  Qed.

  Definition anker_table_try_emplace_resultR_split_first_type_ptr_F
      retp ktycpp vtycpp spine inserted :=
    [FWD] (anker_table_try_emplace_resultR_split_first_type_ptr
      retp ktycpp vtycpp spine inserted).

  Section iterator_observations_more.
  Context {qi : cQp.t} {ic : bool}.

  Lemma anker_iter_head_keep_pointee_type_ptr
      (iter_addr ploc : ptr) (ktycpp vtycpp : type) spine :
    iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi 0 (ploc :: spine)
    |--
    iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi 0 (ploc :: spine)
    ** type_ptr (anker_pair_ty ktycpp vtycpp) ploc.
  Proof using.
    exact (@observe_elim _ _ _
      (observeAnkerIterHeadPointee iter_addr ploc ktycpp vtycpp spine)).
  Qed.

  Definition anker_iter_head_keep_pointee_type_ptr_C
      iter_addr ploc ktycpp vtycpp spine :=
    [CANCEL] (anker_iter_head_keep_pointee_type_ptr
      iter_addr ploc ktycpp vtycpp spine).

  Lemma anker_iter_head_keep_pointee_value_field_type_ptr
      (iter_addr ploc : ptr) (ktycpp vtycpp : type) spine :
    iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi 0 (ploc :: spine)
    |--
    iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi 0 (ploc :: spine)
    ** type_ptr vtycpp (ploc ,, pairSndOffset ktycpp vtycpp).
  Proof using.
    exact (@observe_elim _ _ _
      (observeAnkerIterHeadPointeeValueField
        iter_addr ploc ktycpp vtycpp spine)).
  Qed.

  Definition anker_iter_head_keep_pointee_value_field_type_ptr_C
      iter_addr ploc ktycpp vtycpp spine :=
    [CANCEL] (anker_iter_head_keep_pointee_value_field_type_ptr
      iter_addr ploc ktycpp vtycpp spine).

  Lemma anker_iter_keep_pointee_type_ptr
      (iter_addr ploc : ptr) (ktycpp vtycpp : type) i spine :
    nth_error spine (N.to_nat i) = Some ploc ->
    iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi i spine
    |--
    iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi i spine
    ** type_ptr (anker_pair_ty ktycpp vtycpp) ploc.
  Proof using.
    intros Hnth.
    exact (@observe_elim _ _ _
      (observeAnkerIterPointee
        iter_addr ploc ktycpp vtycpp i spine Hnth)).
  Qed.

  Lemma anker_iter_keep_pointee_value_field_type_ptr
      (iter_addr ploc : ptr) (ktycpp vtycpp : type) i spine :
    nth_error spine (N.to_nat i) = Some ploc ->
    iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi i spine
    |--
    iter_addr |-> AnkerMapIterR ktycpp vtycpp ic qi i spine
    ** type_ptr vtycpp (ploc ,, pairSndOffset ktycpp vtycpp).
  Proof using.
    intros Hnth.
    exact (@observe_elim _ _ _
      (observeAnkerIterPointeeValueField
        iter_addr ploc ktycpp vtycpp i spine Hnth)).
  Qed.

  Lemma anker_iter_keep_const_type_ptr (iter_addr : ptr)
      (ktycpp vtycpp : type) (const_elements : bool) i spine :
    iter_addr |-> AnkerMapIterR ktycpp vtycpp const_elements qi i spine
    |--
    iter_addr |-> AnkerMapIterR ktycpp vtycpp const_elements qi i spine
    ** type_ptr (Tconst (anker_iter_ty ktycpp vtycpp const_elements)) iter_addr.
  Proof using.
    rewrite <- _at_type_ptrR.
    rewrite <- _at_sep.
    apply _at_mono.
    apply (@observe_elim _ _
      (AnkerMapIterR ktycpp vtycpp const_elements qi i spine)
      (observeAnkerIterConstR ktycpp vtycpp const_elements i spine)).
  Qed.

  Definition anker_iter_keep_const_type_ptr_C
      iter_addr ktycpp vtycpp const_elements i spine :=
    [CANCEL] (anker_iter_keep_const_type_ptr
      iter_addr ktycpp vtycpp const_elements i spine).

  #[global] Instance intoSepAnkerIterTypePtrR
      (ktycpp vtycpp : type) (const_elements : bool) i spine :
    IntoSep
      (AnkerMapIterR ktycpp vtycpp const_elements qi i spine)
      (type_ptrR (anker_iter_ty ktycpp vtycpp const_elements))
      (AnkerMapIterR ktycpp vtycpp const_elements qi i spine).
  Proof using.
    rewrite /IntoSep.
    rewrite comm.
    apply (@observe_elim _ _
      (AnkerMapIterR ktycpp vtycpp const_elements qi i spine)
      (observeAnkerIterR ktycpp vtycpp const_elements i spine)).
  Qed.

  #[global] Instance intoSepAnkerIterConstTypePtrR
      (ktycpp vtycpp : type) (const_elements : bool) i spine :
    IntoSep
      (AnkerMapIterR ktycpp vtycpp const_elements qi i spine)
      (type_ptrR (Tconst (anker_iter_ty ktycpp vtycpp const_elements)))
      (AnkerMapIterR ktycpp vtycpp const_elements qi i spine).
  Proof using.
    rewrite /IntoSep.
    rewrite comm.
    apply (@observe_elim _ _
      (AnkerMapIterR ktycpp vtycpp const_elements qi i spine)
      (observeAnkerIterConstR ktycpp vtycpp const_elements i spine)).
  Qed.

  End iterator_observations_more.

  Lemma type_ptr_const_erase (ty : type) (p : ptr) :
    type_ptr (erase_qualifiers (Tconst ty)) p |--
    type_ptr (Tconst ty) p.
  Proof using.
    rewrite <- (type_ptr_erase (Tconst ty) p).
    go.
  Qed.

  Definition type_ptr_const_erase_B (ty : type) (p : ptr) :=
    [BWD] (type_ptr_const_erase ty p).

  Lemma type_ptrR_const_erase_at (ty : type) (p : ptr) :
    p |-> type_ptrR (erase_qualifiers (Tconst ty)) |--
    p |-> type_ptrR (Tconst ty).
  Proof using.
    rewrite !_at_type_ptrR.
    apply type_ptr_const_erase.
  Qed.

  Definition type_ptrR_const_erase_at_B (ty : type) (p : ptr) :=
    [BWD] (type_ptrR_const_erase_at ty p).

  Lemma observeAnkerMapSpineNoDup
      {K : Type} {eqd : EqDecision K} (p : ptr)
      (tykey tyval : type) (khash : K -> N)
      (krep : Qp -> K -> Rep) (q : Qp)
      (locs : list (K * ptr)) :
    Observe [| NoDup (map fst locs) |]
            (p |-> AnkerMapSpineR tykey tyval khash (eqd:=eqd)
                    krep q locs).
  Proof using.
    Admitted.

  Definition observeAnkerMapSpineNoDupF
      {K : Type} {eqd : EqDecision K} (p : ptr)
      (tykey tyval : type) (khash : K -> N)
      (krep : Qp -> K -> Rep) (q : Qp)
      (locs : list (K * ptr)) :=
    @observe_fwd _ _ _
      (observeAnkerMapSpineNoDup p tykey tyval khash krep q locs).

  Lemma observeAnkerMapSpineTypePtr
      {K : Type} {eqd : EqDecision K} (p : ptr)
      (tykey tyval : type) (khash : K -> N)
      (krep : Qp -> K -> Rep) (q : Qp)
      (locs : list (K * ptr)) :
    Observe (type_ptr (Tnamed (anker_table_name tykey tyval)) p)
            (p |-> AnkerMapSpineR tykey tyval khash krep q locs).
  Proof using.
    Admitted.

  Definition observeAnkerMapSpineTypePtrF
      {K : Type} {eqd : EqDecision K} (p : ptr)
      (tykey tyval : type) (khash : K -> N)
      (krep : Qp -> K -> Rep) (q : Qp)
      (locs : list (K * ptr)) :=
    @observe_fwd _ _ _
      (observeAnkerMapSpineTypePtr p tykey tyval khash krep q locs).

  Lemma observeAnkerMapSpineTypePtrR
      {K : Type} {eqd : EqDecision K}
      (tykey tyval : type) (khash : K -> N)
      (krep : Qp -> K -> Rep) (q : Qp)
      (locs : list (K * ptr)) :
    Observe (type_ptrR (Tnamed (anker_table_name tykey tyval)))
            (AnkerMapSpineR tykey tyval khash krep q locs).
  Proof using.
    Admitted.

  Definition observeAnkerMapSpineTypePtrRF
      {K : Type} {eqd : EqDecision K}
      (tykey tyval : type) (khash : K -> N)
      (krep : Qp -> K -> Rep) (q : Qp)
      (locs : list (K * ptr)) :=
    ltac:(mk_at_obs_fwd
      (@observeAnkerMapSpineTypePtrR K eqd tykey tyval khash krep q locs)).

  Lemma anker_map_spine_keep_type_ptr
      {K : Type} {eqd : EqDecision K} (p : ptr)
      (tykey tyval : type) (khash : K -> N)
      (krep : Qp -> K -> Rep) (q : Qp)
      (locs : list (K * ptr)) :
    p |-> AnkerMapSpineR tykey tyval khash krep q locs
    |--
    p |-> AnkerMapSpineR tykey tyval khash krep q locs
    ** type_ptr (Tnamed (anker_table_name tykey tyval)) p.
  Proof using.
    rewrite <- _at_type_ptrR.
    rewrite <- _at_sep.
    apply _at_mono.
    apply (@observe_elim _ _
      (AnkerMapSpineR tykey tyval khash krep q locs)
      (observeAnkerMapSpineTypePtrR tykey tyval khash krep q locs)).
  Qed.

  Definition anker_map_spine_keep_type_ptr_C
      {K : Type} {eqd : EqDecision K} p
      tykey tyval khash krep q locs :=
    [CANCEL] (@anker_map_spine_keep_type_ptr K eqd p
      tykey tyval khash krep q locs).

  #[global] Instance intoSepAnkerMapSpineTypePtrR
      {K : Type} {eqd : EqDecision K}
      (tykey tyval : type) (khash : K -> N)
      (krep : Qp -> K -> Rep) (q : Qp)
      (locs : list (K * ptr)) :
    IntoSep
      (AnkerMapSpineR tykey tyval khash krep q locs)
      (type_ptrR (Tnamed (anker_table_name tykey tyval)))
      (AnkerMapSpineR tykey tyval khash krep q locs).
  Proof using.
    rewrite /IntoSep.
    rewrite comm.
    apply (@observe_elim _ _
      (AnkerMapSpineR tykey tyval khash krep q locs)
      (observeAnkerMapSpineTypePtrR tykey tyval khash krep q locs)).
  Qed.

  Definition anker_table_end_spec (const_elements : bool)
      (ktycpp vtycpp : type) :=
    let qf := if const_elements then function_qualifiers.Nc
              else function_qualifiers.N in
    specify.template.method (anker_table_name ktycpp vtycpp) "end" qf
      (anker_iter_ty ktycpp vtycpp const_elements) [] $
      \this this
      \prepost{K khash (kR : Qp -> K -> Rep) q
          (locs : list (K * ptr)) (eqd : EqDecision K)}
        this |-> AnkerMapSpineR ktycpp vtycpp khash (eqd:=eqd) kR q locs
      \post{retp : ptr} [Vptr retp]
        retp |-> AnkerMapIterR ktycpp vtycpp const_elements 1$m (lengthN locs) (map snd locs).

  Definition anker_table_begin_const_spec (ktycpp vtycpp : type) :=
    specify.template.method (anker_table_name ktycpp vtycpp) "begin"
      function_qualifiers.Nc (anker_iter_ty ktycpp vtycpp true) [] $
      \this this
      \prepost{K khash (kR : Qp -> K -> Rep) q
          (locs : list (K * ptr)) (eqd : EqDecision K)}
        this |-> AnkerMapSpineR ktycpp vtycpp khash (eqd:=eqd) kR q locs
      \post{retp : ptr} [Vptr retp]
        retp |-> AnkerMapIterR ktycpp vtycpp true 1$m 0%N (map snd locs).

  Definition anker_table_find_spec (ktycpp vtycpp : type) :=
    specify.template.method (anker_table_name ktycpp vtycpp) "find"
      function_qualifiers.N (anker_iter_ty ktycpp vtycpp false)
      [Tref (Tconst ktycpp)] $
      \this this
      \arg{keyp : ptr} "key" (Vref keyp)
      \prepost{K khash (kR : Qp -> K -> Rep) q
          (locs : list (K * ptr)) (eqd : EqDecision K)}
        this |-> AnkerMapSpineR ktycpp vtycpp khash (eqd:=eqd) kR q locs
      \prepost{qk k} keyp |-> kR qk k
      \post{retp : ptr} [Vptr retp]
        (Exists (missing : bool),
          if missing
          then retp |-> AnkerMapIterR ktycpp vtycpp false 1$m (lengthN locs)
                         (map snd locs)
               ** [| k ∉ map fst locs |]
          else Exists i,
               retp |-> AnkerMapIterR ktycpp vtycpp false 1$m i (map snd locs)
               ** [| option_map fst (nth_error locs (N.to_nat i)) = Some k |]).

  Definition anker_table_contains_spec (ktycpp vtycpp : type) :=
    specify.template.method (anker_table_name ktycpp vtycpp) "contains"
      function_qualifiers.Nc Tbool [Tref (Tconst ktycpp)] $
      \this this
      \arg{keyp : ptr} "key" (Vref keyp)
      \prepost{K khash (kR : Qp -> K -> Rep) q
          (locs : list (K * ptr)) (eqd : EqDecision K)}
        this |-> AnkerMapSpineR ktycpp vtycpp khash (eqd:=eqd) kR q locs
      \prepost{qk k} keyp |-> kR qk k
      \post[Vbool (bool_decide (k ∈ map fst locs))] emp.

  Definition anker_table_at_spec (ktycpp vtycpp : type) :=
    let qf := function_qualifiers.Nc in
    let args := [Tref (Tconst ktycpp)] in
    templated_method
      (Ninst (Nscoped (anker_table_name ktycpp vtycpp)
        (Nfunction qf "at" args))
        [Atype vtycpp; Avalue (Eint 1 Tbool)])
      (anker_table_name ktycpp vtycpp) qf (Tref (Tconst vtycpp)) args $
      \this this
      \arg{keyp : ptr} "key" (Vref keyp)
      \prepost{K khash (kR : Qp -> K -> Rep) q
          (locs : list (K * ptr)) (eqd : EqDecision K)}
        this |-> AnkerMapSpineR ktycpp vtycpp khash kR q locs
      \prepost{qk k} keyp |-> kR qk k
      \pre{i vloc} [| nth_error locs (N.to_nat i) = Some (k, vloc) |]
      \post [Vref vloc] emp.

  Definition anker_iter_neq_spec
      (ktycpp vtycpp : type) (bexpr : Expr) :=
    let qf := function_qualifiers.Nc in
    let iter_name :=
      Ninst (Nscoped (anker_segvec_name ktycpp vtycpp) (Nid "iter_t"))
        [Avalue bexpr] in
    let iter_ty := Tnamed iter_name in
    let args := [Tref (Tconst iter_ty)] in
      templated_method
        (Ninst (Nscoped iter_name (Nop qf OOExclaimEqual args)) [Avalue bexpr])
        iter_name qf Tbool args $
        \this this
      \arg{otherp : ptr} "other" (Vref otherp)
      \pre{const_elements : bool}
        [| bexpr = Eint (if const_elements then 1 else 0) Tbool |]
      \prepost{i1 i2 spine qthis qother}
        this |-> AnkerMapIterR ktycpp vtycpp const_elements qthis i1 spine
        ** otherp |-> AnkerMapIterR ktycpp vtycpp const_elements qother i2 spine
      \post[Vbool (negb (bool_decide (i1 = i2)))] emp.

  Definition anker_iter_eq_spec
      (ktycpp vtycpp : type) (bexpr : Expr) :=
    let qf := function_qualifiers.Nc in
    let iter_name :=
      Ninst (Nscoped (anker_segvec_name ktycpp vtycpp) (Nid "iter_t"))
        [Avalue bexpr] in
    let iter_ty := Tnamed iter_name in
    let args := [Tref (Tconst iter_ty)] in
    templated_method
      (Ninst (Nscoped iter_name (Nop qf OOEqualEqual args)) [Avalue bexpr])
      iter_name qf Tbool args $
      \this this
      \arg{otherp : ptr} "other" (Vref otherp)
      \pre{const_elements : bool}
        [| bexpr = Eint (if const_elements then 1 else 0) Tbool |]
      \prepost{i1 i2 spine qthis qother}
        this |-> AnkerMapIterR ktycpp vtycpp const_elements qthis i1 spine
        ** otherp |-> AnkerMapIterR ktycpp vtycpp const_elements qother i2 spine
      \post[Vbool (bool_decide (i1 = i2))] emp.

  Definition anker_iter_assign_spec
      (is_const_arg : bool) (ktycpp vtycpp : type) :=
    let iter_ty := anker_iter_ty ktycpp vtycpp false in
    let arg_ty :=
      if is_const_arg then Tref (Tconst iter_ty) else Trv_ref iter_ty in
    specify.template.op
      (anker_iter_name ktycpp vtycpp false) OOEqual
      function_qualifiers.N (Tref iter_ty) [arg_ty] $
      \this this
      \arg{otherp : ptr} "other" (Vref otherp)
      \pre{i_old i_new spine_old spine_new qother}
        this |-> AnkerMapIterR ktycpp vtycpp false 1$m i_old spine_old
        ** otherp |-> AnkerMapIterR ktycpp vtycpp false qother i_new spine_new
      \post[Vref this]
        this |-> AnkerMapIterR ktycpp vtycpp false 1$m i_new spine_new
        ** otherp |-> AnkerMapIterR ktycpp vtycpp false qother i_new spine_new.

  Definition anker_iter_dtor_spec
      (const_elements : bool) (ktycpp vtycpp : type) :=
    specify.template.dtor (anker_iter_name ktycpp vtycpp const_elements) $
      \this this
      \pre{i spine} this |-> AnkerMapIterR ktycpp vtycpp const_elements 1$m i spine
      \post emp.

  Definition anker_iter_star_spec_core const_elements ktycpp vtycpp
      (this : ptr) : WpSpec mpredI val val :=
    \prepost{i spine q} this |-> AnkerMapIterR ktycpp vtycpp const_elements q i spine
    \pre{ploc} [| nth_error spine (N.to_nat i) = Some ploc |]
    \post [Vptr ploc] emp.

  Definition anker_iter_star_spec
      (const_elements : bool) (ktycpp vtycpp : type) :=
    let qf := function_qualifiers.Nc in
    specify.template.op (anker_iter_name ktycpp vtycpp const_elements) OOStar qf
      (Tref (Tconst_if const_elements (anker_pair_ty ktycpp vtycpp))) [] $
      anker_iter_star_spec_core const_elements ktycpp vtycpp.

  Definition anker_iter_arrow_spec
      (const_elements : bool) (ktycpp vtycpp : type) :=
    let qf := function_qualifiers.Nc in
    specify.template.op (anker_iter_name ktycpp vtycpp const_elements) OOArrow qf
      (Tptr (Tconst_if const_elements (anker_pair_ty ktycpp vtycpp))) [] $
      anker_iter_star_spec_core const_elements ktycpp vtycpp.

  Definition anker_iter_inc_spec
      (const_elements : bool) (ktycpp vtycpp : type) :=
    specify.template.op (anker_iter_name ktycpp vtycpp const_elements) OOPlusPlus
      function_qualifiers.N
      (Tref (anker_iter_ty ktycpp vtycpp const_elements)) [] $
      \this this
      \pre{(spine : list ptr) (i : N)}
        this |-> AnkerMapIterR ktycpp vtycpp const_elements 1$m i spine
      \post[Vref this]
        this |-> AnkerMapIterR ktycpp vtycpp const_elements 1$m (1 + i) spine.

  Definition set_emplace_post {K : Type} `{!EqDecision K}
      (key : K) (before after : list K) : Prop :=
    if bool_decide (key ∈ before)
    then after = before
    else forall x, x ∈ after <-> x = key \/ x ∈ before.

  Definition anker_set_contains_spec (key_ty : type) :=
    specify.template.method
      (anker_set_table_name key_ty)
      "contains" function_qualifiers.Nc Tbool [Tref (Tconst key_ty)] $
      \this this
      \arg{keyp: ptr} "key" (Vref keyp)
      \prepost{{K} (eqd : EqDecision K) (khash : K -> N)
          (keyR : Qp -> K -> Rep) (q : Qp) (keys : list K)}
        this |-> AnkerSetR key_ty khash keyR q keys
      \prepost{qk k} keyp |-> keyR qk k
      \post[Vbool (bool_decide (k ∈ keys))] emp.

  Definition anker_set_emplace_spec (key_ty : type) :=
    let args := [Tref (Tconst key_ty)] in
    templated_method
      (Ninst
        (Nscoped (anker_set_table_name key_ty)
          (Nfunction function_qualifiers.N "emplace" args))
        [Apack [Atype (Tref (Tconst key_ty))]])
      (anker_set_table_name key_ty) function_qualifiers.N
      (anker_set_emplace_result_ty key_ty) args $
      \this this
      \arg{keyp: ptr} "args" (Vref keyp)
      \pre{{K} (eqd : EqDecision K) (khash : K -> N)
          (keyR : Qp -> K -> Rep) (keys : list K)}
        this |-> AnkerSetR key_ty khash keyR 1%Qp keys
      \prepost{qk k} keyp |-> keyR qk k
      \post{retp : ptr} [Vptr retp]
        Exists keys_final,
        this |-> AnkerSetR key_ty khash keyR 1%Qp keys_final
        ** retp |-> anker_set_emplace_resultR key_ty
             (negb (bool_decide (k ∈ keys)))
        ** [| set_emplace_post k keys keys_final |].

  Definition anker_set_emplace_result_dtor_spec (key_ty : type) :=
    specify.template.dtor
      ("std::pair".<<
        Atype (anker_set_iter_ty key_ty true), Atype Tbool
      >>)%cpp_name $
      \this this
      \pre{inserted} this |-> anker_set_emplace_resultR key_ty inserted
      \post emp.
End with_Sigma.

Definition SpecFor_anker_set_contains :=
  RegisterSpec (@anker_set_contains_spec).
#[global] Existing Instance SpecFor_anker_set_contains.

Definition SpecFor_anker_set_emplace :=
  RegisterSpec (@anker_set_emplace_spec).
#[global] Existing Instance SpecFor_anker_set_emplace.

Definition SpecFor_anker_set_emplace_result_dtor :=
  RegisterSpec (@anker_set_emplace_result_dtor_spec).
#[global] Existing Instance SpecFor_anker_set_emplace_result_dtor.

Section anker_map_register.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition SpecFor_anker_table_end_const :=
    RegisterSpec (anker_table_end_spec true).
  #[global] Existing Instance SpecFor_anker_table_end_const.

  Definition SpecFor_anker_table_end_mut :=
    RegisterSpec (anker_table_end_spec false).
  #[global] Existing Instance SpecFor_anker_table_end_mut.

  Definition SpecFor_anker_table_begin_const :=
    RegisterSpec (@anker_table_begin_const_spec).
  #[global] Existing Instance SpecFor_anker_table_begin_const.

  Definition SpecFor_anker_table_find :=
    RegisterSpec (@anker_table_find_spec).
  #[global] Existing Instance SpecFor_anker_table_find.

  Definition SpecFor_anker_table_contains :=
    RegisterSpec (@anker_table_contains_spec).
  #[global] Existing Instance SpecFor_anker_table_contains.

  Definition SpecFor_anker_table_at :=
    RegisterSpec (@anker_table_at_spec).
  #[global] Existing Instance SpecFor_anker_table_at.

  Definition SpecFor_iter_dtor_const :=
    RegisterSpec (anker_iter_dtor_spec true).
  #[global] Existing Instance SpecFor_iter_dtor_const.

  Definition SpecFor_iter_dtor_mut :=
    RegisterSpec (anker_iter_dtor_spec false).
  #[global] Existing Instance SpecFor_iter_dtor_mut.

  Definition SpecFor_iter_arrow_const :=
    RegisterSpec (anker_iter_arrow_spec true).
  #[global] Existing Instance SpecFor_iter_arrow_const.

  Definition SpecFor_iter_arrow_mut :=
    RegisterSpec (anker_iter_arrow_spec false).
  #[global] Existing Instance SpecFor_iter_arrow_mut.

  Definition SpecFor_iter_inc_const :=
    RegisterSpec (anker_iter_inc_spec true).
  #[global] Existing Instance SpecFor_iter_inc_const.

  Definition SpecFor_iter_inc_mut :=
    RegisterSpec (anker_iter_inc_spec false).
  #[global] Existing Instance SpecFor_iter_inc_mut.

  Definition SpecFor_iter_star_const :=
    RegisterSpec (anker_iter_star_spec true).
  #[global] Existing Instance SpecFor_iter_star_const.

  Definition SpecFor_iter_star_mut :=
    RegisterSpec (anker_iter_star_spec false).
  #[global] Existing Instance SpecFor_iter_star_mut.

End anker_map_register.

Section anker_iter_neq_register.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.
  Context (ktycpp vtycpp : type) (bexpr : Expr).

  Definition SpecFor_anker_iter_neq :=
    RegisterSpec (anker_iter_neq_spec ktycpp vtycpp bexpr).
  #[global] Existing Instance SpecFor_anker_iter_neq.
End anker_iter_neq_register.

Section anker_iter_eq_register.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.
  Context (ktycpp vtycpp : type) (bexpr : Expr).

  Definition SpecFor_anker_iter_eq :=
    RegisterSpec (anker_iter_eq_spec ktycpp vtycpp bexpr).
  #[global] Existing Instance SpecFor_anker_iter_eq.
End anker_iter_eq_register.

Section anker_iter_assign_register.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition SpecFor_anker_iter_copy_assign :=
    RegisterSpec (anker_iter_assign_spec true).
  #[global] Existing Instance SpecFor_anker_iter_copy_assign.

  Definition SpecFor_anker_iter_move_assign :=
    RegisterSpec (anker_iter_assign_spec false).
  #[global] Existing Instance SpecFor_anker_iter_move_assign.

End anker_iter_assign_register.

#[global] Hint Unfold ModelWithPtr : unfold.
#[global] Opaque AnkerMapIterR.
#[global] Hint Opaque
  AnkerMapPayloadsR AnkerMapR AnkerMapSpineR AnkerMapIterR
  anker_table_try_emplace_resultR
  anker_iter_dtor_spec anker_iter_inc_spec anker_iter_neq_spec
  anker_iter_eq_spec anker_iter_assign_spec anker_iter_star_spec
  anker_table_begin_const_spec
  anker_table_contains_spec anker_table_at_spec
  : sl_opacity.
#[global] Hint Resolve
  AnkerMapIterR_const_C
  observeAnkerIterFt observeAnkerIterFf
  observeAnkerIterConstFt observeAnkerIterConstFf
  observeAnkerTryEmplaceResultFirstF
  observeAnkerIterPointeeF observeAnkerIterPointeeValueFieldF
  observeAnkerIterHeadPointeeF observeAnkerIterHeadPointeeValueFieldF
  anker_table_try_emplace_resultR_split_first_type_ptr_F
  observeAnkerIterRFt observeAnkerIterRFf
  observeAnkerIterConstRFt observeAnkerIterConstRFf
  anker_iter_keep_type_ptr_C anker_iter_keep_const_type_ptr_C
  anker_iter_head_keep_pointee_type_ptr_C
  anker_iter_head_keep_pointee_value_field_type_ptr_C
  observeAnkerMapSpineNoDupF observeAnkerMapSpineTypePtrF
  observeAnkerMapSpineTypePtrRF
  anker_map_spine_keep_type_ptr_C
  type_ptr_const_erase_B type_ptrR_const_erase_at_B
  : sl_opacity.
#[global] Hint Resolve asplitF asplitB : sl_opacity.
#[global] Hint Opaque AnkerSetR : sl_opacity.
#[global] Hint Opaque anker_set_emplace_spec : sl_opacity.
#[global] Hint Opaque anker_set_emplace_result_dtor_spec : sl_opacity.
#[global] Arguments anker_table_contains_spec : simpl never.
#[global] Arguments anker_table_begin_const_spec : simpl never.
#[global] Arguments anker_set_emplace_spec : simpl never.
#[global] Opaque anker_table_try_emplace_resultR.
#[global] Arguments anker_table_try_emplace_resultR : simpl never.

Section anker_learnable_instances.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  #[global] Instance learnAnkerMapIterR :
    LearnEq6 AnkerMapIterR := ltac:(solve_learnable).

  #[global] Instance lanker {K V} :
    LearnEq7 (@AnkerMapR _ _ _ K V) := ltac:(solve_learnable).

  #[global] Instance anksp {K V} :
    LearnEq7 (@AnkerMapSpineR _ _ K V) := ltac:(solve_learnable).

  #[global] Instance LearnEq7p K1 V1 K2 V2
      a a' b b' c c' d d' e e' f f' g g' :
    learn_exist_interface.Learnable
      (@AnkerMapSpineR _ _ K1 V1 a b c d e f g)
      (@AnkerMapSpineR _ _ K2 V2 a' b' c' d' e' f' g')
      [K1 = K2; V1 = V2] := ltac:(solve_learnable).
End anker_learnable_instances.
