Set Default Goal Selector "!".

(** * Byte-layout bridges for the BLAKE3 internal key words

    The internal [blake3_impl.h] entry points expose chaining values as
    [uint32_t[8]], while some C call sites temporarily view that same storage as
    [uint8_t[32]].  This file contains only that generic BLAKE3/C boundary.

    Bridges involving caller-specific digest object layouts belong with those
    callers' proofs; they are not part of the generic BLAKE3 interface.
*)

From Stdlib Require Import List NArith ZArith Lia.

Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import monad.proofs.libspecs.brick_upstream.
Require Import monad.proofs.libspecs.blake3.blake3_impl_h_specs.
Require monad.proofs.libspecs.blake3.model.

Import linearity.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Lemma byte_value_byte_of_N word :
    blake3_impl_h_specs.byte_value (model.byte_of_N word) =
    Vint (Z.of_N (word mod 256)).
  Proof using.
    unfold blake3_impl_h_specs.byte_value, model.byte_of_N.
    change (model.pow2N 8) with 256%N.
    rewrite (fin.to_of_N' (model.pow2N_pos 8) (word mod 256)).
    {
      reflexivity.
    }
    {
      apply N.mod_upper_bound.
      discriminate.
    }
  Qed.

  Lemma byte_values_bytes_of_N_le len word :
    blake3_impl_h_specs.byte_values
      (model.bytes_of_N_le len word) =
    brick_upstream.little_endian_byte_values_from len word.
  Proof using.
    revert word.
    induction len as [| len IH]; intro word.
    {
      reflexivity.
    }
    {
      cbn.
      rewrite byte_value_byte_of_N.
      change
        (map blake3_impl_h_specs.byte_value
           (model.bytes_of_N_le len (N.shiftr word 8)))
        with
        (blake3_impl_h_specs.byte_values
           (model.bytes_of_N_le len (N.shiftr word 8))).
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma byte_values_app xs ys :
    blake3_impl_h_specs.byte_values (xs ++ ys) =
    blake3_impl_h_specs.byte_values xs ++
    blake3_impl_h_specs.byte_values ys.
  Proof using.
    unfold blake3_impl_h_specs.byte_values.
    rewrite map_app.
    reflexivity.
  Qed.

  Lemma byte_values_concat_bytes_of_N_le words :
    blake3_impl_h_specs.byte_values
      (concat (map (model.bytes_of_N_le 4) words)) =
    concat
      (map (brick_upstream.little_endian_byte_values_from 4) words).
  Proof using.
    induction words as [| word rest IH].
    {
      reflexivity.
    }
    {
      cbn [map concat].
      rewrite byte_values_app.
      rewrite byte_values_bytes_of_N_le.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma blake3_cv_byte_values_as_uint32_words_le words :
    length words = 8%nat ->
    List.Forall model.blake3_word_in_range words ->
    blake3_impl_h_specs.blake3_cv_byte_values words =
    brick_upstream.uint32_words_little_endian_byte_values words.
  Proof using.
    intros Hlen Hrange.
    unfold blake3_impl_h_specs.blake3_cv_byte_values,
      brick_upstream.uint32_words_little_endian_byte_values,
      model.blake3_cv_bytes.
    rewrite model.normalize_blake3_cv_id.
    2: exact Hlen.
    2: exact Hrange.
    apply byte_values_concat_bytes_of_N_le.
  Qed.

  Lemma blake3_word_in_range_uint32 word :
    model.blake3_word_in_range word ->
    brick_upstream.unsigned_scalar_int_word_in_range
      int_rank.Iint word.
  Proof using.
    unfold model.blake3_word_in_range, model.blake3_word_modulus,
      brick_upstream.unsigned_scalar_int_word_in_range.
    rewrite <- has_int_type.
    intro Hword.
    unfold bitsize.bound.
    change (0 <= Z.of_N word <= 4294967295)%Z.
    lia.
  Qed.

  Lemma blake3_words_in_range_uint32 words :
    List.Forall model.blake3_word_in_range words ->
    List.Forall
      (brick_upstream.unsigned_scalar_int_word_in_range
         int_rank.Iint) words.
  Proof using.
    induction 1.
    {
      constructor.
    }
    {
      constructor.
      {
        apply blake3_word_in_range_uint32.
        exact H.
      }
      exact IHForall.
    }
  Qed.

  Lemma blake3_const_key_words_to_bytes :
    forall (p : ptr) q words,
      length words = 8%nat ->
      List.Forall model.blake3_word_in_range words ->
      genv_byte_order CU = Little ->
      type_ptr (Tarray Tuint 8) p **
      p |-> blake3_impl_h_specs.Blake3ConstKeyWordsR q words
      |--
      p |-> typed_sliceR Tuint 0 8
      ** p |-> arrayLR Tuchar 0 32
        (fun byte : val => primR Tuchar (cQp.const q) byte)
        (blake3_impl_h_specs.blake3_cv_byte_values words).
  Proof using CU Sigma.
    intros p q words Hlen Hrange Hlittle.
    unfold blake3_impl_h_specs.Blake3ConstKeyWordsR.
    rewrite blake3_cv_byte_values_as_uint32_words_le.
    2: {
      exact Hlen.
    }
    2: {
      exact Hrange.
    }
    replace 8%Z with (Z.of_nat (length words)) by (rewrite Hlen; reflexivity).
    replace 32%Z with (Z.of_nat (4 * length words)) by (rewrite Hlen; reflexivity).
    replace 8%N with (N.of_nat (length words)) by (rewrite Hlen; reflexivity).
    apply brick_upstream.uint32_arrayR_to_little_endian_byte_arrayLR.
    { exact Hlittle. }
    exact (blake3_words_in_range_uint32 words Hrange).
  Qed.

  Lemma blake3_const_key_words_from_bytes :
    forall (p : ptr) q words,
      length words = 8%nat ->
      List.Forall model.blake3_word_in_range words ->
      genv_byte_order CU = Little ->
      p |-> typed_sliceR Tuint 0 8
      ** p |-> arrayLR Tuchar 0 32
        (fun byte : val => primR Tuchar (cQp.const q) byte)
        (blake3_impl_h_specs.blake3_cv_byte_values words)
      |--
      p |-> blake3_impl_h_specs.Blake3ConstKeyWordsR q words.
  Proof using CU Sigma.
    intros p q words Hlen Hrange Hlittle.
    unfold blake3_impl_h_specs.Blake3ConstKeyWordsR.
    rewrite blake3_cv_byte_values_as_uint32_words_le.
    2: {
      exact Hlen.
    }
    2: {
      exact Hrange.
    }
    replace 32%Z with (Z.of_nat (4 * length words)) by (rewrite Hlen; reflexivity).
    replace 8%Z with (Z.of_nat (length words)) by (rewrite Hlen; reflexivity).
    apply brick_upstream.little_endian_byte_arrayLR_to_const_uint32_arrayR.
    {
      exact Hlittle.
    }
    apply blake3_words_in_range_uint32.
    exact Hrange.
  Qed.

  Lemma blake3_key_words_to_bytes :
    forall (p : ptr) q words,
      length words = 8%nat ->
      List.Forall model.blake3_word_in_range words ->
      genv_byte_order CU = Little ->
      type_ptr (Tarray Tuint 8) p **
      p |-> blake3_impl_h_specs.Blake3KeyWordsR q words
      |--
      p |-> typed_sliceR Tuint 0 8
      ** p |-> arrayLR Tuchar 0 32
        (fun byte : val => primR Tuchar (cQp.mut q) byte)
        (blake3_impl_h_specs.blake3_cv_byte_values words).
  Proof using CU Sigma.
    intros p q words Hlen Hrange Hlittle.
    unfold blake3_impl_h_specs.Blake3KeyWordsR.
    rewrite blake3_cv_byte_values_as_uint32_words_le.
    2: {
      exact Hlen.
    }
    2: {
      exact Hrange.
    }
    replace 32%Z with (Z.of_nat (4 * length words)) by (rewrite Hlen; reflexivity).
    replace 8%Z with (Z.of_nat (length words)) by (rewrite Hlen; reflexivity).
    replace 8%N with (N.of_nat (length words)) by (rewrite Hlen; reflexivity).
    transitivity
      (type_ptr (Tarray Tuint (N.of_nat (length words))) p **
       p |-> arrayR Tuint
         (fun word : N => uintR (cQp.mut q) (Z.of_N word)) words).
    {
      go.
    }
    apply brick_upstream.uint32_arrayR_to_little_endian_byte_arrayLR.
    { exact Hlittle. }
    exact (blake3_words_in_range_uint32 words Hrange).
  Qed.

  Lemma blake3_key_words_from_bytes :
    forall (p : ptr) q words,
      length words = 8%nat ->
      List.Forall model.blake3_word_in_range words ->
      genv_byte_order CU = Little ->
      p |-> typed_sliceR Tuint 0 8
      ** p |-> arrayLR Tuchar 0 32
        (fun byte : val => primR Tuchar (cQp.mut q) byte)
        (blake3_impl_h_specs.blake3_cv_byte_values words)
      |--
      p |-> blake3_impl_h_specs.Blake3KeyWordsR q words.
  Proof using CU Sigma.
    intros p q words Hlen Hrange Hlittle.
    unfold blake3_impl_h_specs.Blake3KeyWordsR.
    rewrite blake3_cv_byte_values_as_uint32_words_le.
    2: {
      exact Hlen.
    }
    2: {
      exact Hrange.
    }
    replace 8%Z with (Z.of_nat (length words)) by (rewrite Hlen; reflexivity).
    replace 32%Z with (Z.of_nat (4 * length words)) by (rewrite Hlen; reflexivity).
    etransitivity.
    {
      apply brick_upstream.little_endian_byte_arrayLR_to_mut_uint32_arrayR.
      {
        exact Hlittle.
      }
      apply blake3_words_in_range_uint32.
      exact Hrange.
    }
    go.
  Qed.

  Lemma uint32_array8_uninit_to_byte_any :
    forall (p : ptr),
      type_ptr (Tarray Tuint 8) p **
      p |-> arrayLR Tuint 0 8
        (fun _ : unit => uninitR Tuint 1$m) (replicateN 8 tt)
      |--
      p |-> arrayLR Tuchar 0 32
        (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 tt).
  Proof using CU Sigma.
    intro p.
    replace 8%Z with (Z.of_N 8) by reflexivity.
    replace 32%Z with (Z.of_N (4 * 8)) by reflexivity.
    apply brick_upstream.uint32_uninit_arrayLR_to_uchar_any_arrayLR.
  Qed.

  Lemma uint32_word_arrayR_forget
      (p : ptr) (words : list N) :
    p |-> arrayR Tuint
      (fun word => uintR 1$m (Z.of_N word)) words
    |--
    p |-> arrayR Tuint
      (fun _ : unit => anyR Tuint 1$m)
      (replicateN (N.of_nat (length words)) tt).
  Proof using CU Sigma.
    revert p.
    induction words as [| word words IH]; intro p.
    {
      change (replicateN (N.of_nat 0) tt) with (@nil unit).
      rewrite !arrayR_nil.
      go.
    }
    {
      cbn [length].
      rewrite Nat2N.inj_succ.
      replace (N.succ (N.of_nat (length words)))
        with (N.of_nat (length words) + 1)%N by lia.
      rewrite replicateN_succ.
      pose (IH_F := [FWD] (IH (p .[ Tuint ! 1 ]))).
      go using _at_arrayR_cons_F, _at_arrayR_cons_B,
        IH_F, primR_anyR.
    }
  Qed.

  Definition uint32_word_arrayR_forget_F p words :=
    [FWD] (uint32_word_arrayR_forget p words).

  Lemma blake3_key_words_to_uint32_any :
    forall (p : ptr) words,
      length words = 8%nat ->
      p |-> blake3_impl_h_specs.Blake3KeyWordsR 1 words
      |--
      p |-> arrayLR Tuint 0 8
        (fun _ : unit => anyR Tuint 1$m) (replicateN 8 tt).
  Proof using CU Sigma.
    intros p words Hlen.
    unfold blake3_impl_h_specs.Blake3KeyWordsR.
    go using uint32_word_arrayR_forget_F.
    rewrite Hlen.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    change (lengthZ (replicateN 8 tt)) with 8%Z.
    go.
  Qed.

  Lemma blake3_key_word_bytes_to_uint32_any :
    forall (p : ptr) words,
      length words = 8%nat ->
      List.Forall model.blake3_word_in_range words ->
      genv_byte_order CU = Little ->
      p |-> typed_sliceR Tuint 0 8
      **
      p |-> arrayLR Tuchar 0 32
        (fun byte : val => primR Tuchar 1$m byte)
        (blake3_impl_h_specs.blake3_cv_byte_values words)
      |--
      p |-> arrayLR Tuint 0 8
        (fun _ : unit => anyR Tuint 1$m) (replicateN 8 tt).
  Proof using CU Sigma.
    intros p words Hlen Hrange Hlittle.
    rewrite (blake3_key_words_from_bytes
               p 1 words Hlen Hrange Hlittle).
    apply blake3_key_words_to_uint32_any.
    exact Hlen.
  Qed.
End with_Sigma.
