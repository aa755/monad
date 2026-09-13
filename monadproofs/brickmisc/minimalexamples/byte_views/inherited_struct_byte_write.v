(** Reproducer for https://github.com/SkyLabsAI/BRiCk/issues/156.

    Scalar arrays and structs with direct byte members already have checked
    conversions. This example isolates inheritance: a byte write through the
    derived object's address must be visible through the inherited member.
    There are no external C++ libraries or Monad proof imports.

    First we try the C++ proof without an additional hypothesis. The cast
    succeeds, but the proof stops at [p[1] = 7]: ownership through the
    inherited member does not yet justify writing through the flat pointer.
    The second proof reaches the same point, then uses one explicit
    base-offset hypothesis to complete the write and inherited-member read.
    It does not install a new global axiom.
    Checked against BRiCk c06f8e47 and auto-release eb03a710. *)
From Stdlib Require Import List NArith ZArith.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.lang.cpp.logic.object_repr.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Import ListNotations linearity.
Set Default Goal Selector "!".
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

cpp.prog source prog cpp:{{
  struct Base { unsigned char bytes[2]; };
  struct Word : Base {};
  unsigned char inherited_byte_write(Word &word) {
    auto p = reinterpret_cast<unsigned char *>(&word);
    p[1] = 7;
    return word.bytes[1];
  }
}}.

Section specification.
  Context `{Sigma : cpp_logic} {CU : genv} {MODd : source ⊧ CU}.

  Definition WordR q (bytes : list N) : Rep :=
    structR "Word" q **
    _base "Word" "Base" |->
      (structR "Base" q **
       _field "Base::bytes" |->
         (type_ptrR (Tarray Tuchar 2) **
          arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes)).
  #[local] Hint Opaque WordR : sl_opacity.

  cpp.spec "inherited_byte_write(Word&)" as inherited_byte_write_spec with (
    \arg{wordp : ptr} "word" (Vref wordp)
    \pre wordp |-> WordR 1$m [0%N;0%N]
    \post [Vint 7] wordp |-> WordR 1$m [0%N;7%N]
  ).
End specification.
#[local] Hint Opaque WordR : sl_opacity.

Section without_base_offset.
  Context `{Sigma : cpp_logic} {CU : genv} {MODd : source ⊧ CU}.

  Lemma inherited_byte_write_without_base_offset :
    verify[source] inherited_byte_write_spec.
  Proof using MODd.
    verify_spec.
    unfold WordR.
    go using _at_arrayR_cons_F.
    normalize_ptrs.
    go.
    (** The cast has completed: the context contains
<<
  p_addr |-> ptrR<Tuchar> 1$m wordp
>>
        At [p[1] = 7], we own the second inherited byte:
<<
  wordp ,, o_base CU "Word" "Base" ,,
    o_field CU "Base::bytes" .[Tuchar ! 1]
    |-> primR Tuchar 1$m (Vn 0)
>>
        But the remaining goal requires ownership at the flat byte address:
<<
  valid_ptr (wordp .[Tuchar ! 1]) **
  wordp .[Tuchar ! 1] |-> anyR Tuchar 1$m **
  (wordp .[Tuchar ! 1] |-> ucharR 1$m 7 -* ...)
>>
        Other resources and the continuation are omitted here. Neither byte
        ownership nor either struct witness has been discarded. What is
        missing is a justified conversion between these two byte addresses.
        This is an unfinished C++ proof, not a failed auxiliary offset goal. *)
    Fail solve [go].
  Abort.
End without_base_offset.

Section layout.
  Context {CU : genv} {MODd : source ⊧ CU}.

  (** [parent_offset] looks up the base subobject's displacement in bytes in
      the compiled class-layout table. This lookup already succeeds. *)
  Lemma base_layout_offset : parent_offset CU "Word" "Base" = Some 0%Z.
  Proof using MODd.
    apply (parent_offset_genv_compat (tu := source)).
    vm_compute. reflexivity.
  Qed.
End layout.

Section conditional_proof.
  Context `{Sigma : cpp_logic} {CU : genv} {MODd : source ⊧ CU}.

  (** [o_base] is the semantic offset used to reach the base subobject.
      This hypothesis gives its numeric displacement. We can prove the
      layout-table lookup above, but have not derived this connection to
      [eval_offset]. [eval_o_field] supplies the corresponding member rule. *)
  Hypothesis Hbase : eval_offset CU (o_base CU "Word" "Base") = Some 0%Z.

  (** [ptr_cong] means that two pointers have a common pointer prefix and
      suffix offsets evaluating to the same number of bytes. It is not
      pointer equality and does not permit arbitrary ownership substitution.
      The byte-transport rule below also requires destination typing. *)
  Lemma inherited_field_congruent (p : ptr) :
    ptr_cong CU (p ,, o_base CU "Word" "Base" ,,
      o_field CU "Base::bytes") p.
  Proof using MODd Hbase.
    rewrite -offset_ptr_dot.
    rewrite -{2}(offset_ptr_sub_0 p Tuchar ltac:(eauto)).
    apply offset_ptr_cong.
    unfold offset_cong.
    apply same_property_iff.
    exists 0%Z.
    split.
    {
      apply (eval_offset_dot (s1 := 0%Z) (s2 := 0%Z)); first exact Hbase.
      erewrite eval_o_field; try reflexivity.
      2: { eauto with pure. }
      2: { left; reflexivity. }
      unfold offset_of.
      erewrite glob_def_genv_compat_struct; last (vm_compute; reflexivity).
      reflexivity.
    }
    { rewrite eval_o_sub; done. }
  Qed.

  (** Byte transport needs destination typing, not merely matching addresses. *)
  Lemma bytes_at_congruent_pointer p p' q (bytes : list N) :
    ptr_cong CU p p' ->
    p' |-> arrayR Tuchar (fun _ : N => emp) bytes **
    p |-> arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes
    |-- p' |-> arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes.
  Proof.
    revert p p'.
    induction bytes as [| b bytes IH]; intros p p' Hcong.
    { rewrite !arrayR_nil. go. }
    rewrite !arrayR_cons.
    wapply (_at_primR_ptr_congP_transport p p' Tuchar q (Vn b)).
    unfold ptr_congP.
    go.
    wapply (IH (p .[Tuchar ! 1]) (p' .[Tuchar ! 1])).
    { apply ptr_cong_offset; last exact Hcong. rewrite eval_o_sub; done. }
    go.
  Qed.

  Lemma two_byte_typing ty p (a b : N) :
    size_of CU ty = Some 2%N ->
    type_ptr ty p |-- p |-> arrayR Tuchar (fun _ : N => emp) [a;b].
  Proof.
    intro Hsize.
    rewrite (type_ptr_raw_type_ptrs ty p ltac:(eauto)).
    rewrite (raw_type_ptrs_arrayR_Tbyte_emp [a;b] ty p 2 Hsize
      eq_refl ltac:(discriminate)).
    reflexivity.
  Qed.

  (** Neither direction creates or discards the derived/base object witnesses.
      Only byte ownership changes its pointer expression. *)
  Lemma word_byte_view q a b :
    WordR q [a;b] -|-
      structR "Word" q **
      _base "Word" "Base" |->
        (structR "Base" q **
         _field "Base::bytes" |-> type_ptrR (Tarray Tuchar 2)) **
      arrayR Tuchar (fun n : N => primR Tuchar q (Vn n)) [a;b].
  Proof using MODd Hbase.
    apply Rep_equiv_at; intro p.
    assert (Hsize : size_of CU "Word" = Some 2%N).
    { apply (sizeof.prove_size_named source). vm_compute. reflexivity. }
    unfold WordR.
    split'.
    {
      go.
      wapply (bytes_at_congruent_pointer
        (p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes")
        p q [a;b] (inherited_field_congruent p)).
      go using ([BWD] two_byte_typing "Word" p a b Hsize).
    }
    {
      go.
      wapply (bytes_at_congruent_pointer p
        (p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes")
        q [a;b] (symmetry (inherited_field_congruent p))).
      go using ([BWD] two_byte_typing (Tarray Tuchar 2)
        (p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes") a b eq_refl).
    }
  Qed.

  Lemma written_bytes_to_word (p : ptr) :
    p |-> structR "Word" 1$m **
    p ,, o_base CU "Word" "Base" |-> structR "Base" 1$m **
    p |-> ucharR 1$m 0 ** p .[Tuchar ! 1] |-> ucharR 1$m 7
    |-- p |-> WordR 1$m [0%N;7%N].
  Proof using MODd Hbase.
    rewrite (word_byte_view 1$m 0 7).
    rewrite !arrayR_cons !arrayR_nil.
    go.
  Qed.

  Lemma inherited_byte_write_ok : verify[source] inherited_byte_write_spec.
  Proof using MODd Hbase.
    verify_spec.
    unfold WordR.
    go using _at_arrayR_cons_F.
    normalize_ptrs.
    go.
    (** Same blocked write as above. The prefix did not use [Hbase].
        Now [word_byte_view], whose proof uses [Hbase], transports the
        existing byte ownership to the flat pointer. *)
    pose proof (word_byte_view 1$m 0 0) as Hview.
    unfold WordR in Hview.
    rewrite !arrayR_cons !arrayR_nil in Hview.
    wapply (_at_proper (p := wordp) _ _ Hview).
    (** The write succeeds. Restore the inherited-member view, retaining
        the new byte [7], so that [return word.bytes[1]] can read it. *)
    go using ([FWD] written_bytes_to_word wordp).
    unfold WordR.
    go using _at_arrayR_cons_F.
    normalize_ptrs.
    go using _at_arrayR_cons_B, _at_arrayR_nil_B.
    unfold WordR.
    rewrite !arrayR_cons !arrayR_nil.
    go.
  Qed.
End conditional_proof.

(* The missing offset fact is an explicit argument of this theorem, not an
   axiom hidden behind [Print Assumptions]. *)
Set Printing Fully Qualified.
Check inherited_byte_write_ok.
Print Assumptions inherited_byte_write_ok.
Unset Printing Fully Qualified.
