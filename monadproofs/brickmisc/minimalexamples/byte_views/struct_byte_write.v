(** Minimal struct-array byte write for BRiCk #156.  Two two-byte objects
    suffice to exercise a write beyond the first object's byte member. *)
From Stdlib Require Import List NArith ZArith.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import monad.brickmisc.upstream.scalar_bytes.
Import ListNotations linearity.
Set Default Goal Selector "!".
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

cpp.prog source prog cpp:{{
  struct Word { unsigned char bytes[2]; };
  unsigned char struct_byte_write(Word (&words)[2]) {
    auto p = reinterpret_cast<unsigned char *>(&words);
    p[2] = 7;
    return words[1].bytes[0];
  }
}}.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : source ⊧ CU}.

  Definition WordR q (bytes : list N) : Rep :=
    structR "Word" q **
    _field "Word::bytes" |->
      (type_ptrR (Tarray Tuchar 2) **
       arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes).
  #[local] Hint Opaque WordR : sl_opacity.

  Lemma word_field_congruent p :
    ptr_cong CU (p ,, o_field CU "Word::bytes") p.
  Proof using MODd.
    rewrite -{2}(offset_ptr_sub_0 p Tuchar ltac:(eauto)).
    apply offset_ptr_cong.
    unfold offset_cong.
    apply same_property_iff.
    exists 0%Z.
    split.
    {
      erewrite eval_o_field; try reflexivity.
      2: { eauto with pure. }
      2: { left; reflexivity. }
      unfold offset_of.
      erewrite glob_def_genv_compat_struct; last (vm_compute; reflexivity).
      reflexivity.
    }
    { rewrite eval_o_sub; done. }
  Qed.
  Lemma word_bytes q bytes :
    length bytes = 2%nat ->
    WordR q bytes -|-
      structR "Word" q **
      _field "Word::bytes" |-> type_ptrR (Tarray Tuchar 2) **
      arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes.
  Proof using MODd.
    intro Hlength.
    apply Rep_equiv_at; intro p.
    assert (Hnonempty : bytes <> []) by (intro H; subst; discriminate).
    assert (Hsize : size_of CU "Word" = Some (N.of_nat (length bytes))).
    {
      rewrite Hlength.
      apply (sizeof.prove_size_named source).
      vm_compute. reflexivity.
    }
    assert (Hfieldsize : size_of CU (Tarray Tuchar 2) = Some (N.of_nat (length bytes))).
    { rewrite Hlength. reflexivity. }
    unfold WordR.
    split'.
    {
      go.
      wapply (byte_array_at_congruent_pointer
        (p ,, o_field CU "Word::bytes") p q bytes (word_field_congruent p)).
      go using ([BWD] object_byte_array_witness "Word" p bytes Hnonempty Hsize).
    }
    {
      go.
      wapply (byte_array_at_congruent_pointer p
        (p ,, o_field CU "Word::bytes") q bytes (symmetry (word_field_congruent p))).
      go using ([BWD] object_byte_array_witness (Tarray Tuchar 2)
        (p ,, o_field CU "Word::bytes") bytes Hnonempty Hfieldsize).
    }
  Qed.
  Lemma word_array_fields q chunks :
    List.Forall (fun bs : list N => length bs = 2%nat) chunks ->
    arrayR "Word" (WordR q) chunks -|-
    arrayR "Word" (fun bs : list N =>
      (structR "Word" q **
       _field "Word::bytes" |-> type_ptrR (Tarray Tuchar 2)) **
      arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bs) chunks.
  Proof using MODd.
    intro Hlengths.
    induction Hlengths as [| bs chunks Hbs Hchunks IH].
    { rewrite !arrayR_nil. reflexivity. }
    rewrite !arrayR_cons (word_bytes q bs Hbs) IH.
    rewrite !bi.sep_assoc.
    reflexivity.
  Qed.

  Lemma arrayR_constant {A : Type} ty (R : Rep) (xs : list A) :
    arrayR ty (fun _ : A => R) xs -|-
    arrayR ty (fun _ : unit => R) (repeat tt (length xs)).
  Proof.
    rewrite -(map_const tt xs) arrayR_map'. reflexivity.
  Qed.

  Lemma words_to_bytes (p : ptr) q chunks :
    chunks <> [] ->
    List.Forall (fun bs : list N => length bs = 2%nat) chunks ->
    type_ptr (Tarray "Word" (N.of_nat (length chunks))) p **
    p |-> arrayR "Word" (WordR q) chunks
    |--
    p |-> arrayR "Word" (fun _ : unit =>
      structR "Word" q **
      _field "Word::bytes" |-> type_ptrR (Tarray Tuchar 2)) (repeat tt (length chunks)) **
    p |-> arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) (concat chunks).
  Proof using MODd.
    intros Hnonempty Hlengths.
    assert (Hsize : size_of CU "Word" = Some 2%N).
    { apply (sizeof.prove_size_named source). vm_compute. reflexivity. }
    assert (Hlength : length (concat chunks) = (2 * length chunks)%nat).
    {
      clear Hnonempty.
      induction Hlengths; cbn [concat length]; rewrite ?length_app; lia.
    }
    assert (Hbytes : concat chunks <> []).
    { intro H. rewrite H in Hlength. destruct chunks; cbn in *; congruence || lia. }
    assert (Harraysize : size_of CU (Tarray "Word" (N.of_nat (length chunks))) =
                        Some (N.of_nat (length (concat chunks)))).
    { rewrite (size_of_array _ _ _ Hsize) Hlength Nat2N.inj_mul. f_equal. lia. }
    rewrite (word_array_fields q chunks Hlengths) arrayR_sep.
    rewrite (arrayR_constant "Word" _ chunks).
    go.
    wapply (flatten_byte_arrays "Word" 2 q chunks p p Hsize Hlengths (reflexivity p)).
    go using ([BWD] object_byte_array_witness
      (Tarray "Word" (N.of_nat (length chunks))) p (concat chunks) Hbytes Harraysize).
  Qed.
  Lemma bytes_to_words (p : ptr) q chunks :
    List.Forall (fun bs : list N => length bs = 2%nat) chunks ->
    p |-> arrayR "Word" (fun _ : unit =>
      structR "Word" q **
      _field "Word::bytes" |-> type_ptrR (Tarray Tuchar 2)) (repeat tt (length chunks)) **
    p |-> arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) (concat chunks)
    |-- p |-> arrayR "Word" (WordR q) chunks.
  Proof using MODd.
    intro Hlengths.
    assert (Hsize : size_of CU "Word" = Some 2%N).
    { apply (sizeof.prove_size_named source). vm_compute. reflexivity. }
    assert (typing : forall {A : Type} (R : A -> Rep) (xs : list A),
      arrayR "Word" R xs -|-
      arrayR "Word" R xs ** arrayR "Word" (fun _ : A => emp) xs).
    {
      intros A R xs.
      rewrite -arrayR_sep.
      f_equiv; intro x.
      rewrite bi.sep_emp. reflexivity.
    }
    rewrite -(arrayR_constant "Word" _ chunks).
    rewrite (word_array_fields q chunks Hlengths) arrayR_sep.
    rewrite {1}typing.
    go.
    wapply (unflatten_byte_arrays "Word" 2 q chunks p p Hsize
      ltac:(lia) Hlengths (reflexivity p)).
    rewrite !arrayR_sep.
    go.
  Qed.
  Lemma written_cells_to_words (p : ptr) :
    p |-> structR "Word" 1$m **
    p .["Word" ! 1] |-> structR "Word" 1$m **
    p |-> ucharR 1$m 0 **
    p .[Tuchar ! 1] |-> ucharR 1$m 0 **
    p .[Tuchar ! 2] |-> ucharR 1$m 7 **
    p .[Tuchar ! 3] |-> ucharR 1$m 0
    |-- p |-> arrayR "Word" (WordR 1$m) [[0%N;0%N]; [7%N;0%N]].
  Proof using MODd.
    wapply (bytes_to_words p 1$m [[0%N;0%N]; [7%N;0%N]] ltac:(repeat constructor)).
    cbn [length repeat concat].
    rewrite !arrayR_cons !arrayR_nil.
    go.
    normalize_ptrs.
    go.
  Qed.

  cpp.spec "struct_byte_write(Word[2]&)" as struct_byte_write_spec with (
    \arg{wordsp : ptr} "words" (Vref wordsp)
    \prepost type_ptr (Tarray "Word" 2) wordsp
    \pre wordsp |-> arrayR "Word" (WordR 1$m) [[0%N;0%N]; [0%N;0%N]]
    \post [Vint 7]
      wordsp |-> arrayR "Word" (WordR 1$m) [[0%N;0%N]; [7%N;0%N]]
  ).

  Lemma struct_byte_write_ok : verify[source] struct_byte_write_spec.
  Proof using MODd.
    verify_spec.
    go.
    go using ([FWD] words_to_bytes wordsp 1$m [[0%N;0%N]; [0%N;0%N]]
      ltac:(discriminate) ltac:(repeat constructor)).
    go using _at_arrayR_cons_F.
    normalize_ptrs.
    go.
    go using ([FWD] written_cells_to_words wordsp), _at_arrayR_cons_F.
    unfold WordR.
    go using _at_arrayR_cons_F.
    normalize_ptrs.
    go using _at_arrayR_cons_B, _at_arrayR_nil_B.
    unfold WordR.
    rewrite !arrayR_cons !arrayR_nil.
    go.
  Qed.
End with_Sigma.

Set Printing Fully Qualified.
Print Assumptions struct_byte_write_ok.
Unset Printing Fully Qualified.
