Set Default Goal Selector "!".

(*
  Generic BRiCk/C++-WP rules needed by library specs.

  These are framework-level assumptions about the C++ weakest-precondition
  semantics, not Monad-, EVMC-, or BLAKE3-specific facts.  Keep this file small:
  when a rule is only needed by one implementation proof, prefer proving it
  there or keeping it in the corresponding proof-local upstream-gap file.
*)

From Stdlib Require Import List NArith ZArith.

Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import monad.brickmisc.upstream.scalar_bytes.

Import linearity.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  (** ** Array initialization *)

  (* Compatibility with existing clients; the rule is now provided by BRiCk. *)
  Lemma wp_init_implicit_init_array :
    forall (tu : translation_unit) (rho : region)
      (sz : N) (ety : type) (base : ptr) aty default
      (Q : FreeTemps.t -> mpred),
      is_array_of aty ety ->
      get_default ety = Some default ->
      (base |-> type_ptrR (Tarray ety sz) -*
       base |-> arrayR ety (primR ety 1$m) (replicateN sz default) -*
       Q FreeTemps.id)
      |-- wp_init tu rho (Tarray ety sz) base
            (Eimplicit_init aty) Q.
  Proof.
    exact E.wp_init_implicit_init_array.
  Qed.

  (** ** Scalar object-representation byte views *)

  Fixpoint little_endian_byte_values_from
      (len : nat) (word : N) : list val :=
    match len with
    | O => []
    | S len' =>
        Vint (Z.of_N (word mod 256)) ::
        little_endian_byte_values_from len' (N.shiftr word 8)
    end.

  Definition unsigned_scalar_int_word_byte_values
      (rank : int_rank.t) (word : N) : list val :=
    little_endian_byte_values_from
      (N.to_nat (int_rank.bytesN rank)) word.

  Definition unsigned_scalar_int_words_little_endian_byte_values
      (rank : int_rank.t) (words : list N) : list val :=
    concat (map (unsigned_scalar_int_word_byte_values rank) words).

  Definition uint32_words_little_endian_byte_values
      (words : list N) : list val :=
    unsigned_scalar_int_words_little_endian_byte_values
      int_rank.Iint words.

  Definition unsigned_scalar_int_word_in_range
      (rank : int_rank.t) (word : N) : Prop :=
    has_type_prop
      (Vint (Z.of_N word)) (Tnum rank Unsigned).

  Lemma little_endian_byte_values_Z_to_bytes len word :
    little_endian_byte_values_from len word =
    map Vn (z_to_bytes._Z_to_bytes len Little Unsigned (Z.of_N word)).
  Proof.
    rewrite z_to_bytes._Z_to_bytes_eq.
    unfold z_to_bytes._Z_to_bytes_def, z_to_bytes._Z_to_bytes_le,
      z_to_bytes._Z_to_bytes_unsigned_le.
    revert word.
    induction len as [| len IH]; intro word.
    { reflexivity. }
    cbn [little_endian_byte_values_from].
    rewrite IH.
    change (Vn (word mod 256) ::
      map Vn (z_to_bytes._Z_to_bytes_unsigned_le' 0 len (Z.of_N (N.shiftr word 8))) =
      Vn (Z.to_N (builtins._get_byte (Z.of_N word) 0)) ::
      map Vn (z_to_bytes._Z_to_bytes_unsigned_le' 1 len (Z.of_N word))).
    f_equal.
    {
      rewrite z_to_bytes._get_byte_0_small_id Z2N.inj_mod; try lia.
      rewrite N2Z.id. reflexivity.
    }
    {
      change (map Vn (z_to_bytes._Z_to_bytes_unsigned_le' 0 len
        (Z.of_N (N.shiftr word 8))) =
        map Vn (z_to_bytes._Z_to_bytes_unsigned_le' 1 len (Z.of_N word))).
      rewrite z_to_bytes._Z_to_bytes_unsigned_le'_S_idx.
      2: { lia. }
      rewrite Z_of_N_shiftr; last lia.
      reflexivity.
    }
  Qed.

  Lemma scalar_array_byte_fields rank q words :
    genv_byte_order CU = Little ->
    List.Forall (unsigned_scalar_int_word_in_range rank) words ->
    arrayR (Tnum rank Unsigned)
      (fun word => primR (Tnum rank Unsigned) q (Vn word)) words -|-
    arrayR (Tnum rank Unsigned)
      (fun word => arrayR Tuchar (fun b : N => primR Tuchar q (Vn b))
        (z_to_bytes._Z_to_bytes (N.to_nat (int_rank.bytesN rank))
          Little Unsigned (Z.of_N word))) words.
  Proof.
    intros Hlittle Hrange.
    induction Hrange as [| word words Hword Hwords IH].
    { rewrite !arrayR_nil. reflexivity. }
    assert (Hdecode : decodes_uint
      (z_to_bytes._Z_to_bytes (N.to_nat (int_rank.bytesN rank))
        Little Unsigned (Z.of_N word)) (Z.of_N word)).
    {
      unfold decodes_uint. rewrite Hlittle.
      apply (Endian.decodes_Z_to_bytes_Unsigned rank); last exact Hword.
      reflexivity.
    }
    rewrite !arrayR_cons (scalar_bytes_exact rank q _ _ Hdecode
      (z_to_bytes._Z_to_bytes_length _ _ _ _)) IH.
    split'.
    { go. }
    { go. }
  Qed.

  (** The enclosing array witness licenses the flat-byte indexing. It comes
      from initialization, not from [arrayR], which also describes spans inside
      larger arrays. The original cell typing survives conversion and is used
      by the inverse rule after a byte writer changes the contents. *)
  Lemma unsigned_scalar_int_arrayR_to_little_endian_byte_arrayLR :
    forall (rank : int_rank.t) (p : ptr) (q : cQp.t)
      (words : list N),
      genv_byte_order CU = Little ->
      List.Forall (unsigned_scalar_int_word_in_range rank) words ->
      type_ptr (Tarray (Tnum rank Unsigned) (N.of_nat (length words))) p **
      p |-> arrayR (Tnum rank Unsigned)
        (fun word => primR (Tnum rank Unsigned) q (Vn word)) words
      |--
      p |-> typed_sliceR (Tnum rank Unsigned) 0 (Z.of_nat (length words)) **
      p |-> arrayLR Tuchar 0
        (Z.of_nat (N.to_nat (int_rank.bytesN rank) * length words))
        (fun byte : val => primR Tuchar q byte)
        (unsigned_scalar_int_words_little_endian_byte_values rank words).
  Proof.
    intros rank p q words Hlittle Hrange.
    set (chunks := map (fun word =>
      z_to_bytes._Z_to_bytes (N.to_nat (int_rank.bytesN rank))
        Little Unsigned (Z.of_N word)) words).
    assert (Hchunks : List.Forall
      (fun bs : list N => length bs = N.to_nat (int_rank.bytesN rank)) chunks).
    {
      apply List.Forall_forall. intros bs Hin.
      apply List.in_map_iff in Hin as [word [<- _]].
      apply z_to_bytes._Z_to_bytes_length.
    }
    assert (Hbytes : unsigned_scalar_int_words_little_endian_byte_values rank words =
      map Vn (concat chunks)).
    {
      unfold unsigned_scalar_int_words_little_endian_byte_values, chunks.
      rewrite concat_map map_map.
      f_equal. apply map_ext; intro word.
      apply little_endian_byte_values_Z_to_bytes.
    }
    assert (Hlength : length (concat chunks) =
      (N.to_nat (int_rank.bytesN rank) * length words)%nat).
    {
      unfold chunks. clear Hchunks Hbytes chunks Hrange.
      induction words as [| word words IH].
      { cbn. lia. }
      cbn [map concat]. rewrite app_length z_to_bytes._Z_to_bytes_length IH.
      cbn [length]. lia.
    }
    assert (Htyping : replicateZ (Z.of_nat (length words) - 0) tt =
      map (fun _ : N => tt) words).
    {
      rewrite map_const. unfold replicateZ, replicateN.
      rewrite -repeat_replicate. f_equal. lia.
    }
    assert (Hkeep : arrayR (Tnum rank Unsigned)
      (fun word => primR (Tnum rank Unsigned) q (Vn word)) words -|-
      arrayR (Tnum rank Unsigned) (fun _ : N => emp) words **
      arrayR (Tnum rank Unsigned)
        (fun word => primR (Tnum rank Unsigned) q (Vn word)) words).
    {
      rewrite -arrayR_sep.
      f_equiv. intro word. rewrite bi.emp_sep. reflexivity.
    }
    rewrite Hbytes typed_sliceR.unlock !array_sliceR.unlock !_at_sep !_at_offsetR.
    rewrite (offset_ptr_sub_0 p Tuchar ltac:(eexists; reflexivity))
      (offset_ptr_sub_0 p (Tnum rank Unsigned) ltac:(eexists; reflexivity)).
    rewrite Htyping !arrayR_map' Hkeep !_at_sep.
    rewrite (scalar_array_byte_fields rank q words Hlittle Hrange).
    rewrite -(arrayR_map' (Tnum rank Unsigned)
      (fun bs => arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bs)
      (fun word => z_to_bytes._Z_to_bytes (N.to_nat (int_rank.bytesN rank))
        Little Unsigned (Z.of_N word)) words).
    fold chunks.
    rewrite /lengthN !map_length Hlength.
    wapply (flatten_byte_arrays (Tnum rank Unsigned) (int_rank.bytesN rank)
      q chunks p p eq_refl Hchunks (reflexivity p)).
    go.
    destruct words as [| word words].
    { cbn [chunks map concat]. rewrite !arrayR_nil. go. }
    assert (Hnonempty : concat chunks <> []).
    {
      intro Hnil. apply (f_equal (@length N)) in Hnil.
      rewrite Hlength in Hnil. destruct rank; cbn in Hnil; lia.
    }
    wapply (object_byte_array_witness
      (Tarray (Tnum rank Unsigned) (N.of_nat (length (word :: words))))
      p (concat chunks) Hnonempty).
    { cbn [size_of]. rewrite Hlength Nat2N.inj_mul N2Nat.id /=. f_equal. lia. }
    go.
  Qed.

  Lemma little_endian_byte_arrayLR_to_unsigned_scalar_int_arrayR :
    forall (rank : int_rank.t) (p : ptr) (q : cQp.t)
      (words : list N),
      genv_byte_order CU = Little ->
      List.Forall (unsigned_scalar_int_word_in_range rank) words ->
      p |-> typed_sliceR (Tnum rank Unsigned) 0 (Z.of_nat (length words))
      ** p |-> arrayLR Tuchar 0
        (Z.of_nat (N.to_nat (int_rank.bytesN rank) * length words))
        (fun byte : val => primR Tuchar q byte)
        (unsigned_scalar_int_words_little_endian_byte_values
           rank words)
      |--
      p |-> arrayR (Tnum rank Unsigned)
        (fun word => primR (Tnum rank Unsigned) q (Vint (Z.of_N word)))
        words.
  Proof.
    intros rank p q words Hlittle Hrange.
    rewrite (scalar_array_byte_fields rank q words Hlittle Hrange).
    set (chunks := map (fun word =>
      z_to_bytes._Z_to_bytes (N.to_nat (int_rank.bytesN rank))
        Little Unsigned (Z.of_N word)) words).
    assert (Hchunks : List.Forall
      (fun bs : list N => length bs = N.to_nat (int_rank.bytesN rank)) chunks).
    {
      apply List.Forall_forall.
      intros bs Hin.
      apply List.in_map_iff in Hin as [word [<- _]].
      apply z_to_bytes._Z_to_bytes_length.
    }
    assert (Hbytes : unsigned_scalar_int_words_little_endian_byte_values rank words =
      map Vn (concat chunks)).
    {
      unfold unsigned_scalar_int_words_little_endian_byte_values, chunks.
      rewrite concat_map map_map.
      f_equal. apply map_ext; intro word.
      apply little_endian_byte_values_Z_to_bytes.
    }
    rewrite Hbytes.
    rewrite typed_sliceR.unlock !array_sliceR.unlock.
    rewrite !_at_sep !_at_offsetR.
    rewrite (offset_ptr_sub_0 p (Tnum rank Unsigned) ltac:(eexists; reflexivity))
      (offset_ptr_sub_0 p Tuchar ltac:(eexists; reflexivity)).
    rewrite arrayR_map'.
    rewrite -(arrayR_map' (Tnum rank Unsigned)
      (fun bs => arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bs)
      (fun word => z_to_bytes._Z_to_bytes (N.to_nat (int_rank.bytesN rank))
        Little Unsigned (Z.of_N word)) words).
    fold chunks.
    assert (Htyping : replicateZ (Z.of_nat (length words) - 0) tt =
      map (fun _ : list N => tt) chunks).
    {
      rewrite map_const. unfold chunks. rewrite map_length.
      unfold replicateZ, replicateN.
      rewrite -repeat_replicate. f_equal. lia.
    }
    rewrite Htyping (arrayR_map' (Tnum rank Unsigned)
      (fun _ : unit => emp) (fun _ : list N => tt) chunks).
    wapply (unflatten_byte_arrays (Tnum rank Unsigned)
      (int_rank.bytesN rank) q chunks p p eq_refl
      ltac:(destruct rank; reflexivity) Hchunks (reflexivity p)).
    unfold chunks. rewrite !arrayR_map'. go.
  Qed.

  Lemma unsigned_scalar_int_uninit_arrayLR_to_uchar_any_arrayLR :
    forall (rank : int_rank.t) (p : ptr) (q : cQp.t) (n : N),
      type_ptr (Tarray (Tnum rank Unsigned) n) p **
      p |-> arrayLR (Tnum rank Unsigned) 0 (Z.of_N n)
        (fun _ : unit => uninitR (Tnum rank Unsigned) q)
        (replicateN n tt)
      |--
      p |-> arrayLR Tuchar 0
        (Z.of_N (int_rank.bytesN rank * n))
        (fun _ : unit => anyR Tuchar q)
        (replicateN (int_rank.bytesN rank * n) tt).
  Proof.
    intros rank p q n.
    rewrite !array_sliceR.unlock !_at_sep !_at_offsetR.
    rewrite (offset_ptr_sub_0 p (Tnum rank Unsigned) ltac:(eexists; reflexivity))
      (offset_ptr_sub_0 p Tuchar ltac:(eexists; reflexivity)).
    rewrite -!repeatN_replicateN.
    wapply (unsigned_array_uninit_bytes rank p q n).
    go.
    rewrite /lengthN repeat_length N2Nat.id. go.
  Qed.

  Lemma uint32_arrayR_to_little_endian_byte_arrayLR :
    forall (p : ptr) (q : cQp.t) (words : list N),
      genv_byte_order CU = Little ->
      List.Forall (unsigned_scalar_int_word_in_range int_rank.Iint) words ->
      type_ptr (Tarray Tuint (N.of_nat (length words))) p **
      p |-> arrayR Tuint
        (fun word => uintR q (Z.of_N word)) words
      |--
      p |-> typed_sliceR Tuint 0 (Z.of_nat (length words))
      ** p |-> arrayLR Tuchar 0 (Z.of_nat (4 * length words))
        (fun byte : val => primR Tuchar q byte)
        (uint32_words_little_endian_byte_values words).
  Proof.
    intros p q words Hlittle Hrange.
    change Tuint with (Tnum int_rank.Iint Unsigned).
    change (fun word => uintR q (Z.of_N word))
      with
      (fun word : N =>
         primR (Tnum int_rank.Iint Unsigned) q
           (Vint (Z.of_N word))).
    change (Z.of_nat (4 * length words))
      with
      (Z.of_nat
         (N.to_nat (int_rank.bytesN int_rank.Iint) * length words)).
    apply unsigned_scalar_int_arrayR_to_little_endian_byte_arrayLR.
    { exact Hlittle. }
    exact Hrange.
  Qed.

  Lemma little_endian_byte_arrayLR_to_uint32_arrayR :
    forall (p : ptr) (q : cQp.t) (words : list N),
      genv_byte_order CU = Little ->
      List.Forall
        (unsigned_scalar_int_word_in_range int_rank.Iint) words ->
      p |-> typed_sliceR Tuint 0 (Z.of_nat (length words))
      ** p |-> arrayLR Tuchar 0 (Z.of_nat (4 * length words))
        (fun byte : val => primR Tuchar q byte)
        (uint32_words_little_endian_byte_values words)
      |--
      p |-> arrayR Tuint
        (fun word => uintR q (Z.of_N word)) words.
  Proof.
    intros p q words Hlittle Hrange.
    change Tuint with (Tnum int_rank.Iint Unsigned).
    change (fun word => uintR q (Z.of_N word))
      with
      (fun word : N =>
         primR (Tnum int_rank.Iint Unsigned) q
           (Vint (Z.of_N word))).
    change (Z.of_nat (4 * length words))
      with
      (Z.of_nat
         (N.to_nat (int_rank.bytesN int_rank.Iint) * length words)).
    apply little_endian_byte_arrayLR_to_unsigned_scalar_int_arrayR.
    {
      exact Hlittle.
    }
    exact Hrange.
  Qed.

  Lemma little_endian_byte_arrayLR_to_const_uint32_arrayR :
    forall (p : ptr) (q : cQp.t) (words : list N),
      genv_byte_order CU = Little ->
      List.Forall
        (unsigned_scalar_int_word_in_range int_rank.Iint) words ->
      p |-> typed_sliceR Tuint 0 (Z.of_nat (length words))
      ** p |-> arrayLR Tuchar 0 (Z.of_nat (4 * length words))
        (fun byte : val => primR Tuchar q byte)
        (uint32_words_little_endian_byte_values words)
      |--
      p |-> arrayR Tuint
        (fun word => uintR q (Z.of_N word)) words.
  Proof.
    intros p q words Hlittle Hrange.
    apply little_endian_byte_arrayLR_to_uint32_arrayR.
    {
      exact Hlittle.
    }
    exact Hrange.
  Qed.

  Lemma little_endian_byte_arrayLR_to_mut_uint32_arrayR :
    forall (p : ptr) (q : cQp.t) (words : list N),
      genv_byte_order CU = Little ->
      List.Forall
        (unsigned_scalar_int_word_in_range int_rank.Iint) words ->
      p |-> typed_sliceR Tuint 0 (Z.of_nat (length words))
      ** p |-> arrayLR Tuchar 0 (Z.of_nat (4 * length words))
        (fun byte : val => primR Tuchar q byte)
        (uint32_words_little_endian_byte_values words)
      |--
      p |-> arrayR Tuint
        (fun word => uintR q (Z.of_N word)) words.
  Proof.
    intros p q words Hlittle Hrange.
    apply little_endian_byte_arrayLR_to_uint32_arrayR.
    {
      exact Hlittle.
    }
    exact Hrange.
  Qed.

  Lemma uint32_uninit_arrayLR_to_uchar_any_arrayLR :
    forall (p : ptr) (n : N),
      type_ptr (Tarray Tuint n) p **
      p |-> arrayLR Tuint 0 (Z.of_N n)
        (fun _ : unit => uninitR Tuint 1$m) (replicateN n tt)
      |--
      p |-> arrayLR Tuchar 0 (Z.of_N (4 * n))
        (fun _ : unit => anyR Tuchar 1$m) (replicateN (4 * n) tt).
  Proof.
    intros p n.
    change Tuint with (Tnum int_rank.Iint Unsigned).
    change (Z.of_N (4 * n))
      with (Z.of_N (int_rank.bytesN int_rank.Iint * n)).
    apply unsigned_scalar_int_uninit_arrayLR_to_uchar_any_arrayLR.
  Qed.
End with_Sigma.
