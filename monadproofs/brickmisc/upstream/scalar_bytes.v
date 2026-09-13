(** Object-representation rules derived from BRiCk, for issue #156.
    The typed witness is retained while a writer owns the bytes: writing an
    existing integer is not a rule for creating an integer in arbitrary storage.
    No application model or locally assumed conversion rule is imported. *)

From Stdlib Require Import List NArith ZArith.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.lang.cpp.logic.object_repr.

Import ListNotations linearity z_to_bytes.
Set Default Goal Selector "!".

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Lemma decodes_uint_unique bytes bytes' value :
    decodes_uint bytes value ->
    decodes_uint bytes' value ->
    length bytes = length bytes' ->
    bytes = bytes'.
  Proof.
    intros [Hbytes Hvalue] [Hbytes' Hvalue'] Hlength.
    assert (bounds : forall bs : list N,
      List.Forall (fun b => has_type_prop (Vn b) Tuchar) bs ->
      List.Forall (fun b => (b < 256)%N) bs).
    {
      intros bs Hbs.
      induction Hbs as [| b bs Hb Hbs IH].
      { constructor. }
      constructor.
      {
        rewrite -has_int_type in Hb.
        unfold bitsize.bound, bitsize.min_val, bitsize.max_val in Hb.
        cbn in Hb. lia.
      }
      exact IH.
    }
    pose proof (_Z_to_from_bytes_roundtrip bytes Unsigned
      (genv_byte_order CU) (length bytes) (bounds bytes Hbytes) eq_refl) as H.
    pose proof (_Z_to_from_bytes_roundtrip bytes' Unsigned
      (genv_byte_order CU) (length bytes) (bounds bytes' Hbytes') Hlength) as H'.
    rewrite Hvalue in H.
    rewrite Hvalue' in H'.
    congruence.
  Qed.

  Lemma scalar_bytes_exact rank q value bytes :
    decodes_uint bytes value ->
    length bytes = N.to_nat (int_rank.bytesN rank) ->
    primR (Tnum rank Unsigned) q (Vint value) -|-
      type_ptrR (Tnum rank Unsigned) **
      arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes.
  Proof.
    intros Hdecode Hlength.
    rewrite decode_uint_primR.
    split'.
    {
      go.
      assert (t = bytes) as -> by
        (eapply decodes_uint_unique; eauto; lia).
      rewrite arrayR_map'.
      go.
    }
    {
      rewrite -(bi.exist_intro (raw_int_byte <$> bytes)).
      rewrite -(bi.exist_intro bytes) arrayR_map'.
      go.
    }
  Qed.

  Lemma byte_at_congruent_pointer p p' q b :
    ptr_cong CU p p' ->
    type_ptr Tuchar p' ** p |-> primR Tuchar q (Vn b)
    |-- p' |-> primR Tuchar q (Vn b).
  Proof.
    intro Hcong.
    wapply (_at_primR_ptr_congP_transport p p' Tuchar q (Vn b)).
    unfold ptr_congP.
    go.
  Qed.

  Lemma byte_array_at_congruent_pointer p p' q bytes :
    ptr_cong CU p p' ->
    p' |-> arrayR Tuchar (fun _ : N => emp) bytes **
    p |-> arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes
    |-- p' |-> arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes.
  Proof.
    revert p p'.
    induction bytes as [| b bytes IH]; intros p p' Hcong.
    { rewrite !arrayR_nil. go. }
    rewrite !arrayR_cons.
    go using ([FWD] byte_at_congruent_pointer p p' q b Hcong).
    wapply (IH (p .[Tuchar ! 1]) (p' .[Tuchar ! 1])).
    { apply ptr_cong_offset; last exact Hcong. rewrite eval_o_sub; done. }
    go.
  Qed.
  Lemma object_byte_array_witness ty p (bytes : list N) :
    bytes <> [] ->
    size_of CU ty = Some (N.of_nat (length bytes)) ->
    type_ptr ty p |-- p |-> arrayR Tuchar (fun _ : N => emp) bytes.
  Proof.
    intros Hnonempty Hsize.
    rewrite (type_ptr_raw_type_ptrs ty p ltac:(eauto)).
    rewrite (raw_type_ptrs_arrayR_Tbyte_emp bytes ty p
      (N.of_nat (length bytes)) Hsize eq_refl Hnonempty).
    reflexivity.
  Qed.
  (** Flattening changes the indexing type, not the bytes.  The destination
      typing premise is explicit; an arbitrary numerically equal address is
      not thereby a valid C++ pointer. *)
  Lemma flatten_byte_arrays ty width q chunks p flat :
    size_of CU ty = Some width ->
    List.Forall (fun bs : list N => length bs = N.to_nat width) chunks ->
    ptr_cong CU p flat ->
    flat |-> arrayR Tuchar (fun _ : N => emp) (concat chunks) **
    p |-> arrayR ty
      (fun bs => arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bs) chunks
    |-- flat |-> arrayR Tuchar
      (fun b : N => primR Tuchar q (Vn b)) (concat chunks).
  Proof.
    intros Hsize Hlengths.
    revert p flat.
    induction Hlengths as [| bs chunks Hbs Hchunks IH]; intros p flat Hcong.
    { cbn [concat]. rewrite !arrayR_nil. go. }
    cbn [concat].
    rewrite !arrayR_app arrayR_cons.
    go using ([FWD] byte_array_at_congruent_pointer p flat q bs Hcong).
    wapply (IH (p .[ty ! 1]) (flat .[Tuchar ! Z.of_nat (length bs)])).
    {
      apply ptr_cong_offset2; last exact Hcong.
      apply (offset_cong_subs width 1); try done.
      lia.
    }
    go.
  Qed.
  Lemma unflatten_byte_arrays ty width q chunks p flat :
    size_of CU ty = Some width ->
    (0 < width)%N ->
    List.Forall (fun bs : list N => length bs = N.to_nat width) chunks ->
    ptr_cong CU p flat ->
    p |-> arrayR ty (fun _ : list N => emp) chunks **
    flat |-> arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) (concat chunks)
    |-- p |-> arrayR ty
      (fun bs => arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bs) chunks.
  Proof.
    intros Hsize Hwidth Hlengths.
    revert p flat.
    induction Hlengths as [| bs chunks Hbs Hchunks IH]; intros p flat Hcong.
    { cbn [concat]. rewrite !arrayR_nil. go. }
    assert (Hnonempty : bs <> []) by (intro H; subst bs; cbn in Hbs; lia).
    assert (Hsizebs : size_of CU ty = Some (N.of_nat (length bs)))
      by (rewrite Hbs N2Nat.id; exact Hsize).
    cbn [concat].
    rewrite !arrayR_cons arrayR_app.
    go.
    wapply (byte_array_at_congruent_pointer flat p q bs (symmetry Hcong)).
    go using ([BWD] object_byte_array_witness ty p bs Hnonempty Hsizebs).
    wapply (IH (p .[ty ! 1]) (flat .[Tuchar ! Z.of_nat (length bs)])).
    {
      apply ptr_cong_offset2; last exact Hcong.
      apply (offset_cong_subs width 1); try done.
      lia.
    }
    go.
  Qed.
  Lemma byte_any_array_at_congruent_pointer p p' q (cells : list unit) :
    ptr_cong CU p p' ->
    p' |-> arrayR Tuchar (fun _ : unit => emp) cells **
    p |-> arrayR Tuchar (fun _ : unit => anyR Tuchar q) cells
    |-- p' |-> arrayR Tuchar (fun _ : unit => anyR Tuchar q) cells.
  Proof.
    revert p p'.
    induction cells as [| cell cells IH]; intros p p' Hcong.
    { rewrite !arrayR_nil. go. }
    rewrite !arrayR_cons.
    wapply (_at_anyR_ptr_congP_transport p p' Tuchar q).
    unfold ptr_congP.
    go.
    wapply (IH (p .[Tuchar ! 1]) (p' .[Tuchar ! 1])).
    { apply ptr_cong_offset; last exact Hcong. rewrite eval_o_sub; done. }
    go.
  Qed.

  Lemma flatten_byte_any_arrays ty width q chunks p flat :
    size_of CU ty = Some width ->
    List.Forall (fun bs : list unit => length bs = N.to_nat width) chunks ->
    ptr_cong CU p flat ->
    flat |-> arrayR Tuchar (fun _ : unit => emp) (concat chunks) **
    p |-> arrayR ty
      (fun bs => arrayR Tuchar (fun _ : unit => anyR Tuchar q) bs) chunks
    |-- flat |-> arrayR Tuchar
      (fun _ : unit => anyR Tuchar q) (concat chunks).
  Proof.
    intros Hsize Hlengths.
    revert p flat.
    induction Hlengths as [| bs chunks Hbs Hchunks IH]; intros p flat Hcong.
    { cbn [concat]. rewrite !arrayR_nil. go. }
    cbn [concat].
    rewrite !arrayR_app arrayR_cons.
    go using ([FWD] byte_any_array_at_congruent_pointer p flat q bs Hcong).
    wapply (IH (p .[ty ! 1]) (flat .[Tuchar ! Z.of_nat (length bs)])).
    {
      apply ptr_cong_offset2; last exact Hcong.
      apply (offset_cong_subs width 1); try done.
      lia.
    }
    go.
  Qed.

  (** The enclosing array witness is supplied by C++ initialization. It is
      not inferred from the element [arrayR], which only types native cells.
      The old scalar witnesses remain available for the subsequent typed read. *)
  Lemma unsigned_array_uninit_bytes rank p q n :
    type_ptr (Tarray (Tnum rank Unsigned) n) p **
    p |-> arrayR (Tnum rank Unsigned)
      (fun _ : unit => uninitR (Tnum rank Unsigned) q) (repeat tt (N.to_nat n))
    |-- p |-> arrayR Tuchar (fun _ : unit => anyR Tuchar q)
      (repeat tt (N.to_nat (int_rank.bytesN rank * n))).
  Proof.
    assert (Hfields : forall k,
      arrayR (Tnum rank Unsigned)
        (fun _ : unit => uninitR (Tnum rank Unsigned) q) (repeat tt k)
      |-- arrayR (Tnum rank Unsigned)
        (fun bs => arrayR Tuchar (fun _ : unit => anyR Tuchar q) bs)
        (repeat (repeat tt (N.to_nat (int_rank.bytesN rank))) k)).
    {
      intro k. induction k as [| k IH].
      { rewrite !arrayR_nil. reflexivity. }
      cbn [repeat]. rewrite !arrayR_cons.
      rewrite -(anyR_array Tuchar (int_rank.bytesN rank) q).
      go using ([FWD] uninitR_anyR (Tnum rank Unsigned) q),
        ([FWD->] decode_uint_anyR q rank), ([FWD] IH).
      rewrite IH. go.
    }
    set (width := int_rank.bytesN rank).
    set (chunks := repeat (repeat tt (N.to_nat width)) (N.to_nat n)).
    assert (Hchunks : List.Forall
      (fun bs : list unit => length bs = N.to_nat width) chunks).
    { unfold chunks. induction (N.to_nat n); constructor; auto using repeat_length. }
    assert (Hflat : concat chunks = repeat tt (N.to_nat (width * n))).
    {
      unfold chunks.
      clear Hchunks chunks.
      rewrite N2Nat.inj_mul Nat.mul_comm.
      induction (N.to_nat n) as [| k IH].
      { reflexivity. }
      cbn [repeat concat Nat.mul]. rewrite IH repeat_app. reflexivity.
    }
    rewrite -Hflat.
    wapply (flatten_byte_any_arrays (Tnum rank Unsigned) width q chunks p p
      eq_refl Hchunks (reflexivity p)).
    rewrite Hfields.
    fold width chunks.
    {
      destruct n as [| n].
      { cbn [chunks]. rewrite !arrayR_nil. go. }
      rewrite (type_ptr_raw_type_ptrs (Tarray (Tnum rank Unsigned) (N.pos n)) p
        ltac:(eexists; reflexivity)).
      rewrite (raw_type_ptrs_arrayR_Tbyte_emp (concat chunks)
        (Tarray (Tnum rank Unsigned) (N.pos n)) p (width * N.pos n)).
      { go. }
      { cbn. unfold width. f_equal. lia. }
      { rewrite /lengthN Hflat repeat_length N2Nat.id. reflexivity. }
      { rewrite Hflat. intro Hnil. apply (f_equal (@length unit)) in Hnil.
        rewrite repeat_length in Hnil. unfold width in Hnil.
        destruct rank; cbn in Hnil; lia. }
    }
  Qed.
End with_Sigma.
