Set Default Goal Selector "!".

(*
  Generic BRiCk/C++-WP rules that the storage-page proofs currently need but
  that are not available from the checked-out upstream libraries in a directly
  usable form.

  This file is intentionally limited to framework-level C++ proof gaps:
  generated array initialization/destruction, primitive expression evaluation,
  and object-representation cleanup.  It must not contain assumptions about
  project libraries such as BLAKE3, EVMC, or Monad storage pages; those belong
  beside the corresponding library/spec interface.
*)

From Stdlib Require Import List NArith ZArith.

Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import monad.proofs.libspecs.brick_upstream.

Import linearity.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  (** ** Array initialization *)

  Lemma type_ptr_empty_arrayLR :
    forall (A : Type) (ty : type) (base : ptr) (R : A -> Rep),
      HasSize ty ->
      base |-> type_ptrR (Tarray ty 0)
      |-- base |-> arrayLR ty 0 0 R [].
  Proof.
    intros A ty base R Hsize.
    rewrite array_sliceR.unlock arrayR_nil.
    rewrite _at_sep _at_only_provable _at_offsetR.
    rewrite (only_provable_True _ Hsize).
    go using type_ptr_array_end_valid_O.
  Qed.

  Definition type_ptr_empty_arrayLR_F
      (A : Type) ty base (R : A -> Rep) Hsize :=
    [FWD] (@type_ptr_empty_arrayLR A ty base R Hsize).

  Lemma type_ptr_empty_arrayLR_with_type :
    forall (A : Type) (ty : type) (base : ptr) (R : A -> Rep),
      HasSize ty ->
      type_ptr (Tarray ty 0) base
      |--
      base |-> type_ptrR (Tarray ty 0)
      ** base |-> arrayLR ty 0 0 R [].
  Proof.
    intros A ty base R Hsize.
    rewrite -(_at_type_ptrR base (Tarray ty 0)).
    rewrite array_sliceR.unlock arrayR_nil.
    rewrite _at_sep _at_only_provable _at_offsetR.
    rewrite (only_provable_True _ Hsize).
    go using type_ptr_array_end_valid_O.
  Qed.

  Definition type_ptr_empty_arrayLR_with_type_F
      (A : Type) ty base (R : A -> Rep) Hsize :=
    [FWD] (@type_ptr_empty_arrayLR_with_type A ty base R Hsize).

  Lemma type_ptr_empty_arrayLR_finish :
    forall (A : Type) (ty : type) (base : ptr) (R : A -> Rep)
      (Q : mpred),
      HasSize ty ->
      type_ptr (Tarray ty 0) base
      ** (base |-> type_ptrR (Tarray ty 0) -*
          base |-> arrayLR ty 0 0 R [] -*
          Q)
      |-- Q.
  Proof.
    intros A ty base R Q Hsize.
    etrans.
    {
      apply bi.sep_mono_l.
      exact (type_ptr_empty_arrayLR_with_type A ty base R Hsize).
    }
    rewrite bi.wand_curry.
    apply bi.wand_elim_r.
  Qed.

  Definition type_ptr_empty_arrayLR_finish_F
      (A : Type) ty base (R : A -> Rep) Q Hsize :=
    [FWD] (@type_ptr_empty_arrayLR_finish A ty base R Q Hsize).

  Definition type_ptr_erase_B_local ty p :=
    [BWD] (type_ptr_erase ty p).

  Definition uninitR_anyR_F ty q :=
    [FWD] (uninitR_anyR ty q).

  Lemma arrayLR_uninit_any
      (base : ptr) (ty : type) (lo hi : Z)
      (items : list unit) :
    base |-> arrayLR ty lo hi
      (fun _ : unit => uninitR ty 1$m) items
    |--
    base |-> arrayLR ty lo hi
      (fun _ : unit => anyR ty 1$m) items.
  Proof.
    go using uninitR_anyR_F.
  Qed.

  Definition arrayLR_uninit_any_F base ty lo hi items :=
    [FWD] (arrayLR_uninit_any base ty lo hi items).

  Lemma type_ptr_array_end_valid_entails
      (ty : type) (base : ptr) (len : N) :
    HasSize ty ->
    base |-> type_ptrR (Tarray ty len)
    |-- valid_ptr (base .[ ty ! Z.of_N len ]).
  Proof.
    intros Hsize.
    rewrite _at_type_ptrR.
    go using type_ptr_array_end_valid_O.
  Qed.

  Lemma wp_array_init_prim_implicit_erased
      (tu : translation_unit) ρ
      (full_len len : N) (ty_prim : type) (cur : N)
      (base : ptr) (Q : FreeTemps.t -> mpred) c v :
    HasSize (erase_qualifiers ty_prim) ->
    zero_init_val tu ty_prim = Some v ->
    zero_init_val tu (erase_qualifiers ty_prim) = Some v ->
    wp.zero_init_val_auto tu ty_prim = Some (c, v) ->
    full_len = (len + cur)%N ->
    ((base |-> type_ptrR (Tarray (erase_qualifiers ty_prim) full_len) -*
      base .[ erase_qualifiers ty_prim ! Z.of_N cur ]
        |-> arrayR (erase_qualifiers ty_prim)
              (primR (erase_qualifiers ty_prim) (cQp.mk c 1))
              (replicateN len v)) -*
     Q FreeTemps.id)
    |-- wp_array_init tu ρ ty_prim base
          (replicateN len (Eimplicit_init ty_prim)) cur
          (fun free => Q free).
  Proof.
    intros Hsize Hzero Hzero_erase Hauto.
    induction len using N.peano_ind in cur |- *;
      rewrite !(replicateN_0, replicateN_S);
      iIntros (Hfull_len) "Q /=".
    {
      iApply "Q".
      have -> : cur = full_len by lia.
      iIntros "T".
      rewrite arrayR_nil _at_sep _at_only_provable.
      iSplitL "T";
        first
          (rewrite _at_validR;
           iApply (type_ptr_array_end_valid_entails with "T");
           exact Hsize).
      {
        iPureIntro.
        exact Hsize.
      }
    }
    erewrite wp.wp_initialize_zero_initializable => //.
    rewrite -expr.E.wp_operand_implicit_init //.
    rewrite -interp_intro_id.
    iIntros "A /=".
    assert (Htail_len : full_len = (len + N.succ cur)%N) by lia.
    specialize (IHlen _ Htail_len).
    have -> : (Z.succ cur = N.succ cur) by lia.
    iApply IHlen.
    iIntros "R".
    iApply "Q".
    iIntros "T".
    rewrite arrayR_cons_obs _at_sep _at_sub_succ.
    iSplitL "A".
    {
      iStopProof.
      apply _at_mono.
      exact
        (wp.tptsto_fuzzyR_primR_zero_init_val
           tu (erase_qualifiers ty_prim) (cQp.mk c 1) v
           Hzero_erase).
    }
    have -> : Z.succ cur = N.succ cur by lia.
    iApply ("R" with "T").
  Qed.

  Lemma wp_init_initlist_prim_array_implicit_erased
      (tu : translation_unit) ρ (base : ptr)
      arr_ty Q ty_prim len c init_val :
    zero_init_val tu ty_prim = Some init_val ->
    zero_init_val tu (erase_qualifiers ty_prim) = Some init_val ->
    wp.zero_init_val_auto tu ty_prim = Some (c, init_val) ->
    HasSize (erase_qualifiers ty_prim) ->
    (0 < len)%N ->
    is_array_of arr_ty ty_prim ->
    (base |-> type_ptrR (Tarray (erase_qualifiers ty_prim) len) -*
     base |-> arrayR (erase_qualifiers ty_prim)
       (primR (erase_qualifiers ty_prim) (cQp.mk c 1))
       (replicateN len init_val) -*
     Q FreeTemps.id)
    |-- wp_init tu ρ (Tarray ty_prim len) base
          (Einitlist [] (Some (Eimplicit_init ty_prim)) arr_ty) Q.
  Proof.
    intros Hzero Hzero_erase Hauto Hsize Hpos Harr.
    rewrite -wp_init_initlist_array /wp_array_init_fill //= {arr_ty Harr}.
    destruct len.
    {
      lia.
    }
    rewrite /fill_initlist /=.
    replace (N.pos p - 0)%N with (N.pos p) by lia.
    iIntros "K".
    iApply
      (wp_array_init_prim_implicit_erased
         tu ρ (N.pos p) (N.pos p) ty_prim 0 base
         (fun free : FreeTemps.t =>
            base |-> type_ptrR
              (Tarray (erase_qualifiers ty_prim) (N.pos p)) -*
            Q free)
         c init_val);
      try eassumption; try lia.
    iIntros "A #T".
    iApply ("K" with "T").
    rewrite offset_ptr_sub_0.
    {
      iApply ("A" with "T").
    }
    exact Hsize.
  Qed.

  Definition wp_init_initlist_prim_array_implicit_erased_B
      tu ρ base arr_ty Q ty_prim len c init_val
      Hzero Hzero_erase Hauto Hsize Hpos Harr :=
    [BWD] (wp_init_initlist_prim_array_implicit_erased
             tu ρ base arr_ty Q ty_prim len c init_val
             Hzero Hzero_erase Hauto Hsize Hpos Harr).

  Lemma persistent_wand_apply
      (P R Q : mpred)
      `{!TCOr (Affine P) (Absorbing P)} `{!Persistent P} :
    P |-- R ->
    (R -* P -* Q) ** P |-- Q.
  Proof.
    intro HPR.
    rewrite bi.sep_comm.
    etrans.
    {
      apply bi.sep_mono_l.
      rewrite {1}(bi.persistent_sep_dup P).
      apply bi.sep_mono_l.
      exact HPR.
    }
    rewrite bi.wand_curry.
    apply bi.wand_elim_r.
  Qed.

  Lemma build_tail_cont_from_head
      (HeadType Head Tail Valid Q : mpred) :
    Head |-- HeadType ** Head ->
    (((HeadType ** Head) ** Tail -* Valid -* Q) ** Head)
    |-- Tail -* Valid -* Q.
  Proof.
    intro Hhead.
    apply bi.wand_intro_r.
    apply bi.wand_intro_r.
    set (R := (HeadType ** Head) ** Tail).
    change ((((R -* Valid -* Q) ** Head) ** Tail) ** Valid |-- Q).
    etrans.
    {
      apply bi.sep_mono_l.
      apply bi.sep_mono_l.
      apply bi.sep_mono_r.
      exact Hhead.
    }
    rewrite bi.wand_curry.
    subst R.
    go.
  Qed.

  Lemma build_tail_cont_from_split_head
      (HeadType Head Tail Valid Q : mpred) :
    ((((HeadType ** Head) ** Tail -* Valid -* Q) ** Head)
     ** HeadType)
    |-- Tail -* Valid -* Q.
  Proof.
    apply bi.wand_intro_r.
    apply bi.wand_intro_r.
    set (R := (HeadType ** Head) ** Tail).
    change ((((((R -* Valid -* Q) ** Head) ** HeadType) ** Tail)
              ** Valid) |-- Q).
    subst R.
    rewrite bi.wand_curry.
    go.
  Qed.

  Lemma build_tail_cont_from_split_head_fwds
      (HeadTypeHave HeadType HeadHave Head Tail Valid Q : mpred) :
    HeadHave |-- Head ->
    HeadTypeHave |-- HeadType ->
    ((((HeadType ** Head) ** Tail -* Valid -* Q) ** HeadHave)
     ** HeadTypeHave)
    |-- Tail -* Valid -* Q.
  Proof.
    intros Hhead Hheadtype.
    etrans.
    {
      apply bi.sep_mono.
      {
        apply bi.sep_mono_r.
        exact Hhead.
      }
      {
        exact Hheadtype.
      }
    }
    apply build_tail_cont_from_split_head.
  Qed.

  Lemma apply_two_wands_after_fwd
      (First Have Need Q : mpred) :
    Have |-- Need ->
    (((First -* Need -* Q) ** Have) ** First) |-- Q.
  Proof.
    intro Hhave.
    etrans.
    {
      apply bi.sep_mono_l.
      apply bi.sep_mono_r.
      exact Hhave.
    }
    rewrite -bi.sep_assoc.
    rewrite (bi.sep_comm Need First).
    rewrite bi.wand_curry.
    apply bi.wand_elim_l.
  Qed.

  Lemma apply_two_wands_after_two_fwds
      (FirstHave FirstNeed SecondHave SecondNeed Q : mpred) :
    FirstHave |-- FirstNeed ->
    SecondHave |-- SecondNeed ->
    (((SecondNeed -* FirstNeed -* Q) ** FirstHave) ** SecondHave)
    |-- Q.
  Proof.
    intros Hfirst Hsecond.
    etrans.
    {
      apply bi.sep_mono.
      {
        apply bi.sep_mono_r.
        exact Hfirst.
      }
      {
        exact Hsecond.
      }
    }
    rewrite -bi.sep_assoc.
    rewrite (bi.sep_comm FirstNeed SecondNeed).
    rewrite bi.wand_curry.
    apply bi.wand_elim_l.
  Qed.

  Lemma build_head_init_cont_from_tail
      (tu : translation_unit)
      (HeadType Head Tail End Q TailFold : mpred) :
    (Tail -* End -* Q |-- TailFold) ->
    (((HeadType ** Head) ** Tail -* End -* Q)
     |-- HeadType -* Head -* interp tu FreeTemps.id TailFold).
  Proof.
    intro Htail.
    apply bi.wand_intro_r.
    apply bi.wand_intro_r.
    transitivity TailFold.
    {
      transitivity (Tail -* End -* Q).
      {
        apply bi.wand_intro_r.
        apply bi.wand_intro_r.
        set (R := (HeadType ** Head) ** Tail).
        change (((((R -* End -* Q) ** HeadType) ** Head) ** Tail) ** End
                |-- Q).
        subst R.
        rewrite bi.wand_curry.
        go.
      }
      exact Htail.
    }
    apply interp_intro_id.
  Qed.

  Lemma sep_with_wand_refl
      (K P A : mpred) :
    K |-- P ->
    K |-- P ** (A -* A).
  Proof.
    intro HKP.
    etrans.
    {
      exact HKP.
    }
    go.
  Qed.

  Lemma finish_row_init_after_wapply
      (tu : translation_unit)
      (HeadType Head Tail End Q TailFold A : mpred) :
    (Tail -* End -* Q |-- TailFold) ->
    (((HeadType ** Head) ** Tail -* End -* Q)
     |-- (HeadType -* Head -* interp tu FreeTemps.id TailFold)
         ** (A -* A)).
  Proof.
    intro Htail.
    apply sep_with_wand_refl.
    apply build_head_init_cont_from_tail.
    exact Htail.
  Qed.

  (* Interactive review: [Search default_initialize_array arrayLR] and
     [Check default_initialize_array_fusion] find the upstream fusion theorem.
     Its element type must be a primitive/scalar/pointer shape and must satisfy
     [erase_qualifiers ty = ty].

     This generated declaration is a two-dimensional byte array.  The outer
     element type is itself [Tarray Tuchar cols], so it fails the
     scalar/pointer shape test in [default_initialize_array_fusion].  The
     existing theorem can initialize one primitive array, but it does not
     recursively fuse default initialization through an array-of-arrays
     footprint. *)
  Lemma default_initialize_uchar_array_any :
    forall (tu : translation_unit) (base : ptr)
      (cols : N) (Q : FreeTemps.t -> mpred),
    (0 < cols)%N ->
    (type_ptr (Tarray Tuchar cols) base -*
     base |-> arrayLR Tuchar 0 (Z.of_N cols)
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateN cols tt) -*
     Q FreeTemps.id)
    |-- default_initialize tu (Tarray Tuchar cols) base Q.
  Proof.
    intros tu base cols Q Hcols.
    rewrite (default_initialize_unfold (Tarray Tuchar cols) tu).
    cbn.
    rewrite bool_decide_true; last lia.
    transitivity
      (base |-> arrayLR Tuchar 0 (Z.of_N cols)
        (fun _ : unit => uninitR Tuchar 1$m)
        (replicateN cols tt) -*
       base |-> type_ptrR (Tarray Tuchar cols) -*
       Q FreeTemps.id).
    {
      apply bi.wand_intro_r.
      apply bi.wand_intro_r.
      apply apply_two_wands_after_two_fwds.
      {
        exact (arrayLR_uninit_any base Tuchar
          0 (Z.of_N cols) (replicateN cols tt)).
      }
      {
        rewrite _at_type_ptrR.
        go.
      }
    }
    apply (array_sliceR_hints.default_initialize_array_fusion
      tu (fun _ : FreeTemps => Q FreeTemps.id)
      cols base Tuchar); [reflexivity | apply _].
  Qed.

  Definition default_initialize_uchar_array_any_B
      tu base cols Q Hcols :=
    [BWD] (default_initialize_uchar_array_any
             tu base cols Q Hcols).

  (* BRiCk issue #145.  [default_initialize_array_fusion] handles primitive and
     pointer arrays when the array element type is already its erased heap type.
     A source element such as [unsigned char const *] fails that side condition:
     the default initializer leaves an uninitialized pointer object at the
     erased heap type [unsigned char *], but the generated array initializer is
     phrased over the source type [unsigned char const *]. *)
  Axiom default_initialize_array_erased_pointer_uninit :
    forall (tu : translation_unit) (base : ptr)
      (pointee : type) (len : N) (Q : FreeTemps.t -> mpred),
    (base |-> arrayLR (erase_qualifiers (Tptr pointee))
       0 (Z.of_N len)
       (fun _ : unit =>
          uninitR (erase_qualifiers (Tptr pointee)) 1$m)
       (replicateN len tt) -*
     base |-> type_ptrR (Tarray (Tptr pointee) len) -*
     Q FreeTemps.id)
    |-- default_initialize_array
          (default_initialize tu (Tptr pointee)) tu
          (Tptr pointee) len base Q.

  Definition default_initialize_array_erased_pointer_uninit_B
      tu base pointee len Q :=
    [BWD] (default_initialize_array_erased_pointer_uninit
             tu base pointee len Q).

  Definition uchar_array_rowR (cols : N) : Rep :=
    arrayLR Tuchar 0 (Z.of_N cols)
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN cols tt).

  Lemma default_initialize_array_of_arrays_uninit_aux :
    forall (tu : translation_unit) (base : ptr)
      (start len cols : N) (End Q : mpred),
    (0 < cols)%N ->
    TCOr (Affine End) (Absorbing End) ->
    Persistent End ->
    (End |--
     valid_ptr
       (base .[ Tarray Tuchar cols !
          Z.of_N (start + len) ])) ->
    (base |-> arrayLR (Tarray Tuchar cols)
       (Z.of_N start) (Z.of_N (start + len))
       (fun _ : unit => uchar_array_rowR cols)
       (replicateN len tt) -*
     End -*
     Q)
    |--
    foldr
      (fun (i : N) (PP : epred) =>
         default_initialize tu (Tarray Tuchar cols)
           (base .[ Tarray Tuchar cols ! Z.of_N i ])
           (fun free' : FreeTemps => interp tu free' PP))
      (End -* Q)
      (seqN start len).
  Proof.
    intros tu base start len.
    revert start base.
    induction len using N.peano_ind; intros start base cols End Q
      Hcols Hend_tc Hend_persistent Hend_valid.
    {
      rewrite seqN_0 replicateN_0.
      cbn [foldr].
      replace (start + 0)%N with start by lia.
      rewrite array_sliceR_nil.
      apply bi.wand_intro_r.
      apply persistent_wand_apply; try apply _.
      replace start with (start + 0)%N by lia.
      etrans.
      {
        exact Hend_valid.
      }
      go.
    }
    {
      replace (start + N.succ len)%N
        with (N.succ start + len)%N by lia.
      rewrite -cons_seqN replicateN_S.
      cbn [foldr].
      assert (Hend_valid_tail :
        End |--
        valid_ptr
          (base .[ Tarray Tuchar cols !
             Z.of_N (N.succ start + len) ])).
      {
        replace (N.succ start + len)%N
          with (start + N.succ len)%N by lia.
        exact Hend_valid.
      }
      pose (IH_F :=
        [FWD]
          (IHlen (N.succ start) base cols End Q
             Hcols Hend_tc Hend_persistent Hend_valid_tail)).
      rewrite array_sliceR_cons.
      replace (Z.of_N start + 1)%Z
        with (Z.of_N (N.succ start)) by lia.
      pose (tail_fold :=
        foldr
          (fun (i : N) (PP : epred) =>
             default_initialize tu (Tarray Tuchar cols)
               (base .[ Tarray Tuchar cols ! Z.of_N i ])
               (fun free'' : FreeTemps =>
                  interp tu free'' PP))
          (End -* Q)
          (seqN (N.succ start) len)).
      wapply
        (default_initialize_uchar_array_any
           tu
           (base .[ Tarray Tuchar cols ! Z.of_N start ])
           cols
           (fun free' : FreeTemps => interp tu free' tail_fold)
           Hcols).
      apply (finish_row_init_after_wapply
        tu
        (type_ptr (Tarray Tuchar cols)
          (base .[ Tarray Tuchar cols ! Z.of_N start ]))
        (base .[ Tarray Tuchar cols ! Z.of_N start ]
          |-> uchar_array_rowR cols)
        (base |-> arrayLR (Tarray Tuchar cols)
          (Z.of_N (N.succ start))
          (Z.of_N (N.succ start + len))
          (fun _ : unit => uchar_array_rowR cols)
          (replicateN len tt))
        End Q tail_fold).
      go using IH_F.
    }
  Qed.

  Lemma default_initialize_array_of_arrays_uninit :
    forall (tu : translation_unit) (base : ptr)
      (rows cols : N) (Q : FreeTemps.t -> mpred),
    (0 < cols)%N ->
    (base |-> type_ptrR (Tarray (Tarray Tuchar cols) rows) -*
     base |-> arrayLR (Tarray Tuchar cols) 0 (Z.of_N rows)
       (fun _ : unit =>
          arrayLR Tuchar 0 (Z.of_N cols)
            (fun _ : unit => anyR Tuchar 1$m)
            (replicateN cols tt))
       (replicateN rows tt) -*
     Q FreeTemps.id)
    |-- default_initialize_array
          (default_initialize tu (Tarray Tuchar cols)) tu
          (Tarray Tuchar cols) rows base Q.
  Proof.
    intros tu base rows cols Q Hcols.
    rewrite -default_initialize_array_intro.
    pose proof
      (type_ptr_array_end_valid_entails
         (Tarray Tuchar cols) base rows _) as Hend_valid.
    rewrite (bi.wand_wand
      (base |-> type_ptrR
        (Tarray (Tarray Tuchar cols) rows))
      (base |-> arrayLR (Tarray Tuchar cols)
        0 (Z.of_N rows)
        (fun _ : unit => uchar_array_rowR cols)
        (replicateN rows tt))
      (Q FreeTemps.id)).
    eapply
      (default_initialize_array_of_arrays_uninit_aux
         tu base 0 rows cols
         (base |-> type_ptrR
            (Tarray (Tarray Tuchar cols) rows))
         (Q FreeTemps.id)).
    {
      exact Hcols.
    }
    {
      apply _.
    }
    {
      apply _.
    }
    {
      exact Hend_valid.
    }
  Qed.

  (** ** Array destruction *)

  Lemma destroy_run_array_from_arrayLR :
    forall (A : Type) (tu : translation_unit) (cv : type_qualifiers)
      (ty : type) (len : nat) (base : ptr)
      (R : A -> Rep) (xs : list A) (Q : epred),
      length xs = len ->
      erase_qualifiers ty = ty ->
      (forall (cellp : ptr) x (Qcell : epred),
        type_ptr ty cellp ** cellp |-> R x ** Qcell
        |-- wp_destroy_val tu cv ty cellp Qcell) ->
      base |-> arrayLR ty 0 (Z.of_nat len) R xs
      ** Q
      |-- destroy.run_array tu cv ty base len Q.
  Proof.
    intros A tu cv ty len base R xs Q Hlen Herase Hcell.
    revert len base Q Hlen.
    induction xs as [| x xs IH] using rev_ind.
    {
      intros len base Q Hlen.
      destruct len.
      {
        cbn [destroy.run_array].
        go.
      }
      {
        discriminate Hlen.
      }
    }
    {
      intros len base Q Hlen.
      rewrite List.app_length /= in Hlen.
      subst len.
      replace (length xs + 1)%nat
        with (S (length xs)) by lia.
      cbn [destroy.run_array].
      rewrite array_sliceR_snoc.
      replace (Z.of_nat (S (length xs)) - 1)%Z
        with (Z.of_nat (length xs)) by lia.
      rewrite Herase.
      pose (IH_F := [FWD] (IH (length xs) base Q eq_refl)).
      pose (Hcell_B :=
        [BWD]
          (Hcell
             (base .[ ty ! Z.of_nat (length xs) ])
             x
             (destroy.run_array tu cv ty base (length xs) Q))).
      go using Hcell_B, IH_F.
    }
  Qed.

  (** ** Primitive expression evaluation *)

  (* Interactive review: [Search operators.wp_eval_binop.body Badd Tuchar
     Tint] finds only local rules in this file.  The generic arithmetic
     automation can handle promoted integer operations, but generated compound
     assignments expose the mixed operation [Badd Tuchar Tint Tuchar].  C++
     semantically promotes the [unsigned char] lhs for addition and converts the
     result back to [unsigned char] before storing.  This bounded rule captures
     the no-wrap case needed by the storage-page proofs. *)
  Axiom wp_eval_uchar_add_int_bounded :
    forall (tu : translation_unit) (av bv : Z) (Q : val -> mpred),
      0 <= av ->
      0 <= bv ->
      av + bv < 256 ->
      Q (Vint (av + bv))
      |-- operators.wp_eval_binop.body
            tu Badd Tuchar Tint Tuchar
            (Vint av) (Vint bv) Q.

  Lemma wp_eval_uchar_add_int_16_32 :
    forall (tu : translation_unit) (Q : val -> mpred),
      Q (Vint 48)
      |-- operators.wp_eval_binop.body
            tu Badd Tuchar Tint Tuchar
            (Vint 16) (Vint 32) Q.
  Proof.
    intros tu Q.
    change (Vint 48) with (Vint (16 + 32)).
    apply wp_eval_uchar_add_int_bounded; lia.
  Qed.

End with_Sigma.
