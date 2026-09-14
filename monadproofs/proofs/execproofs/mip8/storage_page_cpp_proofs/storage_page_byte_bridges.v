Set Default Goal Selector "!".

(** * Storage-page byte-layout bridges

    The generic BLAKE3 specs talk about flat [uint8_t] buffers.  Monad's
    storage-page implementation often allocates those buffers as
    [bytes32_t] or [bytes32_t[]] objects and then passes a byte pointer
    to the BLAKE3 C API.  Those layout facts are about Monad/EVMC storage, not
    about BLAKE3 itself, so they live with the storage-page proofs rather than
    under [libspecs/blake3].
*)

From Stdlib Require Import List NArith ZArith Lia.
Import ListNotations.

Require Import skylabs.prelude.arith.z_to_bytes.
Require Import skylabs.prelude.fin.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.brick_upstream.
Require Import monad.proofs.libspecs.blake3.blake3_impl_h_specs.
Require Import monad.proofs.libspecs.blake3.byte_bridges.
Require monad.proofs.libspecs.blake3.model.

Import linearity.

Transparent exec_specs.bytes32_be_values
  exec_specs.bytes32_be_values_from
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  model.N_of_bytes_be.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Definition blake3_cv_bytes32_fieldsR (words : list N) : Rep :=
    as_Rep
      (fun base =>
         base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
           o_field CU "evmc_bytes32::bytes"
           |-> arrayLR Tuchar 0 32
                 (fun byte : val => primR Tuchar 1$m byte)
                 (blake3_impl_h_specs.blake3_cv_byte_values words)
         ** base |-> structR "monad::bytes32_t"%cpp_name 1$m
         ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
           |-> structR "evmc_bytes32"%cpp_name 1$m).

  Lemma get_byte_of_N (word : N) (idx : nat) :
    Z.to_N (builtins._get_byte (Z.of_N word) idx) =
    N.land (N.shiftr word (8 * N.of_nat idx)) 255.
  Proof.
    revert word.
    induction idx as [| idx IH]; intro word.
    {
      rewrite _get_byte_0_small_id.
      rewrite Z2N.inj_mod.
      2: {
        lia.
      }
      2: {
        lia.
      }
      rewrite N2Z.id.
      rewrite N.shiftr_0_r.
      change 255%N with (N.ones 8).
      rewrite N.land_ones.
      reflexivity.
    }
    {
      rewrite builtins._get_byte_S_idx.
      rewrite Z_of_N_shiftr.
      2: {
        lia.
      }
      rewrite IH.
      rewrite N.shiftr_shiftr.
      change (Z.to_N 8) with 8%N.
      replace (8 + 8 * N.of_nat idx)%N
        with (8 * N.of_nat (S idx))%N by lia.
      reflexivity.
    }
  Qed.

  Lemma bytes32_be_values_to_Z_to_bytes (word : N) :
    exec_specs.bytes32_be_values word =
    map (fun byte => Vint (Z.of_N byte))
      (_Z_to_bytes 32 types.Big types.Unsigned (Z.of_N word)).
  Proof.
    unfold exec_specs.bytes32_be_values,
      exec_specs.bytes32_be_values_from.
    rewrite _Z_to_bytes_eq.
    unfold _Z_to_bytes_def, _Z_to_bytes_le,
      _Z_to_bytes_unsigned_le, _Z_to_bytes_unsigned_le'.
    cbn [seq map rev List.app Basics.compose].
    repeat rewrite get_byte_of_N.
    reflexivity.
  Qed.

  Lemma bytes_of_N_le_length len word :
    length (model.bytes_of_N_le len word) = len.
  Proof.
    revert word.
    induction len as [| len IH]; intro word.
    {
      reflexivity.
    }
    {
      cbn.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma concat_bytes_of_N_le_length words :
    length (concat (map (model.bytes_of_N_le 4) words)) =
    (4 * length words)%nat.
  Proof.
    induction words as [| word rest IH].
    {
      reflexivity.
    }
    {
      cbn [map concat length].
      rewrite app_length.
      rewrite bytes_of_N_le_length.
      rewrite IH.
      rewrite Nat.mul_succ_r.
      rewrite (Nat.add_comm 4 (4 * length rest)).
      reflexivity.
    }
  Qed.

  Lemma blake3_cv_bytes_length words :
    length words = 8%nat ->
    length (model.blake3_cv_bytes words) = 32%nat.
  Proof.
    intro Hlen.
    clear Hlen.
    unfold model.blake3_cv_bytes.
    rewrite concat_bytes_of_N_le_length.
    rewrite model.normalize_blake3_cv_length.
    reflexivity.
  Qed.

  Lemma fin_to_N_bytes_bound (bytes : list model.byte) :
    List.Forall (fun b : N => (b < 256)%N) (map fin.to_N bytes).
  Proof.
    induction bytes as [| b bytes IH].
    {
      constructor.
    }
    {
      constructor.
      {
        change 256%N with (model.pow2N 8).
        apply fin.to_N_lt.
      }
      exact IH.
    }
  Qed.

  Lemma bytes32_to_N_bytes32_of_be_bytes_full
      (bytes : list model.byte) :
    length bytes = 32%nat ->
    model.bytes32_to_N (model.bytes32_of_be_bytes bytes) =
    model.N_of_bytes_be bytes.
  Proof.
    intro Hlen.
    unfold model.bytes32_of_be_bytes, model.bytes32_of_N,
      model.bytes32_to_N, model.N_of_bytes_be, model.pad_bytes.
    rewrite firstn_app.
    rewrite firstn_all2.
    2: {
      lia.
    }
    replace (32 - length bytes)%nat with 0%nat by lia.
    change (firstn 0 (repeat model.zero_byte 32))
      with (@nil model.byte).
    rewrite app_nil_r.
    rewrite (fin.to_of_N' (model.pow2N_pos 256)
               (Z.to_N
                  (_Z_from_bytes types.Big types.Unsigned
                     (map fin.to_N bytes)) mod model.pow2N 256)).
    2: {
      apply N.mod_upper_bound.
      pose proof (model.pow2N_pos 256).
      lia.
    }
    rewrite N.mod_small.
    {
      reflexivity.
    }
    {
      pose proof
        (_Z_from_bytes_Unsigned_bound types.Big (map fin.to_N bytes))
        as Hbound.
      rewrite map_length in Hbound.
      rewrite Hlen in Hbound.
      change (model.pow2N 256) with (2 ^ 256)%N.
      change (2 ^ 256)%N with (Z.to_N (2 ^ 256)).
      assert
        (Hbytes_nonneg :
           (0 <=
            _Z_from_bytes types.Big types.Unsigned
              (map fin.to_N bytes))%Z)
        by lia.
      assert (Hpow_nonneg : (0 <= 2 ^ 256)%Z) by lia.
      apply
        (proj1
           (Z2N.inj_lt
              (_Z_from_bytes types.Big types.Unsigned
                 (map fin.to_N bytes))
              (2 ^ 256)%Z
              Hbytes_nonneg
              Hpow_nonneg)).
      {
        change (Z.of_N (2 ^ 256)) with (2 ^ 256)%Z.
        change (256 ^ Z.of_nat 32)%Z with (2 ^ 256)%Z in Hbound.
        lia.
      }
    }
  Qed.

  Lemma byte_values_bytes32_of_be_bytes_full
      (bytes : list model.byte) :
    length bytes = 32%nat ->
    blake3_impl_h_specs.byte_values bytes =
    exec_specs.bytes32_be_values
      (model.bytes32_to_N (model.bytes32_of_be_bytes bytes)).
  Proof.
    intro Hlen.
    rewrite bytes32_be_values_to_Z_to_bytes.
    rewrite (bytes32_to_N_bytes32_of_be_bytes_full bytes Hlen).
    unfold model.N_of_bytes_be.
    rewrite Z2N.id.
    2: {
      pose proof
        (_Z_from_bytes_Unsigned_bound types.Big (map fin.to_N bytes)).
      lia.
    }
    rewrite (_Z_to_from_bytes_roundtrip
               (map fin.to_N bytes) types.Unsigned types.Big 32).
    2: {
      apply fin_to_N_bytes_bound.
    }
    2: {
      rewrite map_length.
      exact (eq_sym Hlen).
    }
    unfold blake3_impl_h_specs.byte_values,
      blake3_impl_h_specs.byte_value.
    rewrite map_map.
    reflexivity.
  Qed.

  Lemma blake3_cv_byte_values_digest words :
    length words = 8%nat ->
    blake3_impl_h_specs.blake3_cv_byte_values words =
    exec_specs.bytes32_be_values
      (model.bytes32_to_N (model.blake3_cv_digest words)).
  Proof.
    intro Hlen.
    unfold blake3_impl_h_specs.blake3_cv_byte_values,
      model.blake3_cv_digest.
    apply byte_values_bytes32_of_be_bytes_full.
    apply blake3_cv_bytes_length.
    exact Hlen.
  Qed.

  Lemma byte_arrayR_to_arrayLR32
      (base : ptr) (q : cQp.t) bytes :
    length bytes = 32%nat ->
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar q byte) bytes
    |--
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar q byte) bytes.
  Proof using CU Sigma.
    intro Hlen.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite lengthZ_correct Hlen.
    go.
  Qed.

  Definition byte_arrayR_to_arrayLR32_F base q bytes Hlen :=
    [FWD] (byte_arrayR_to_arrayLR32 base q bytes Hlen).

  Lemma byte_arrayLR32_to_arrayR
      (base : ptr) (q : cQp.t) bytes :
    length bytes = 32%nat ->
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar q byte) bytes
    |--
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar q byte) bytes.
  Proof using CU Sigma.
    intro Hlen.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite lengthZ_correct Hlen.
    go.
  Qed.

  Definition byte_arrayLR32_to_arrayR_F base q bytes Hlen :=
    [FWD] (byte_arrayLR32_to_arrayR base q bytes Hlen).

  Section with_storage_page_module.
    Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma bytes32R_to_bytes_field
      (base : ptr) q word :
    base |-> exec_specs.bytes32R q word
    |--
    base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
      o_field CU "evmc_bytes32::bytes"
      |-> arrayLR Tuchar 0 32
            (fun byte : val => primR Tuchar q byte)
            (exec_specs.bytes32_be_values word)
    ** base |-> structR "monad::bytes32_t"%cpp_name q
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
      |-> structR "evmc_bytes32"%cpp_name q.
  Proof using CU MODd Sigma.
    rewrite /exec_specs.bytes32R /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR.
    rewrite !_at_sep.
    repeat rewrite _at_offsetR.
    rewrite !_at_sep.
    repeat rewrite _at_offsetR.
    rewrite !_at_sep.
    rewrite !_at_pureR.
    rewrite
      (byte_arrayR_to_arrayLR32
         (base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
          o_field CU "evmc_bytes32::bytes")
         q
         (exec_specs.bytes32_be_values word)
         eq_refl).
    go.
  Qed.

  Definition bytes32R_to_bytes_field_F base q word :=
    [FWD] (bytes32R_to_bytes_field base q word).

  Lemma bytes_field_to_bytes32R
      (base : ptr) q word :
    (word < 2 ^ 256)%N ->
    base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
      o_field CU "evmc_bytes32::bytes"
      |-> arrayLR Tuchar 0 32
            (fun byte : val => primR Tuchar q byte)
            (exec_specs.bytes32_be_values word)
    ** base |-> structR "monad::bytes32_t"%cpp_name q
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
      |-> structR "evmc_bytes32"%cpp_name q
    |--
    base |-> exec_specs.bytes32R q word.
  Proof using CU MODd Sigma.
    intro Hrange.
    rewrite /exec_specs.bytes32R /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR.
    rewrite (only_provable_True _ Hrange).
    rewrite
      (byte_arrayLR32_to_arrayR
         (base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
          o_field CU "evmc_bytes32::bytes")
         q
         (exec_specs.bytes32_be_values word)
         eq_refl).
    go.
  Qed.

  Definition bytes_field_to_bytes32R_B base q word Hrange :=
    [BWD] (bytes_field_to_bytes32R base q word Hrange).

  End with_storage_page_module.

  Definition evmc_bytes32_array_byte_values (outputs : list N) : list val :=
    concat (map exec_specs.bytes32_be_values outputs).

  Definition evmc_bytes32_array_bytesR
      (q : cQp.t) (outputs : list N) : Rep :=
    arrayR Tuchar
      (primR Tuchar q)
      (evmc_bytes32_array_byte_values outputs).

  Lemma bytes32_be_values_length word :
    length (exec_specs.bytes32_be_values word) = 32%nat.
  Proof.
    unfold exec_specs.bytes32_be_values.
    change (length (exec_specs.bytes32_be_values_from 32 word) = 32%nat).
    generalize 32%nat.
    intro len.
    revert word.
    induction len as [| len IH]; intro word.
    {
      reflexivity.
    }
    {
      cbn.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma evmc_bytes32_array_byte_values_length outputs :
    length (evmc_bytes32_array_byte_values outputs) =
    (32 * length outputs)%nat.
  Proof.
    unfold evmc_bytes32_array_byte_values.
    induction outputs as [| output rest IH].
    {
      reflexivity.
    }
    {
      change
        (length
           (concat
              (map exec_specs.bytes32_be_values (output :: rest))))
        with
        (length (exec_specs.bytes32_be_values output) +
         length
           (concat
              (map exec_specs.bytes32_be_values rest)))%nat.
      rewrite bytes32_be_values_length.
      rewrite IH.
      cbn [length].
      lia.
    }
  Qed.

  (** The bytes can change without ending the lifetimes of the surrounding
      objects.  Keep their non-byte resources separate, indexed only by the
      array length, so a library call can replace the contents but cannot
      create the enclosing objects. *)
  Definition evmc_bytes32_array_spineR (q : cQp.t) (len : nat) : Rep :=
    arrayR blake3_impl_h_specs.bytes32_ty
      (fun _ : unit =>
        structR "monad::bytes32_t"%cpp_name q **
        _base "monad::bytes32_t" "evmc_bytes32" |->
          (structR "evmc_bytes32"%cpp_name q **
           _field "evmc_bytes32::bytes" |-> type_ptrR (Tarray Tuchar 32)))
      (List.repeat tt len).

  #[global] Hint Opaque evmc_bytes32_array_spineR : sl_opacity.

  Record evmc_bytes32_array_byte_view
      (p : ptr) q (outputs : list N) : Prop := {
    evmc_bytes32_array_to_bytes :
      p |-> arrayR blake3_impl_h_specs.bytes32_ty
             (exec_specs.bytes32R q) outputs
      |--
      p |-> evmc_bytes32_array_spineR q (length outputs) **
      p |-> evmc_bytes32_array_bytesR q outputs;
    evmc_bytes32_array_from_bytes :
      List.Forall (fun x => (x < 2 ^ 256)%N) outputs ->
      p |-> evmc_bytes32_array_spineR q (length outputs) **
      p |-> evmc_bytes32_array_bytesR q outputs
      |--
      p |-> arrayR blake3_impl_h_specs.bytes32_ty
             (exec_specs.bytes32R q) outputs;
  }.

  (* Remaining EVMC object-representation gap: [storage_page.cpp] writes the
     [flat_out] buffer as a flat [uint8_t *] BLAKE3 output buffer and then reads
     it back as a [bytes32_t[]].  The per-object field lemmas above can expose
     or rebuild one [bytes32_t] from its [evmc_bytes32::bytes] field, but the
     array bridge also needs a generic BRiCk rule connecting an array of complete
     objects with its contiguous [unsigned char] object representation.  A flat
     [uint8_t] buffer alone does not contain the [structR] witnesses for the
     surrounding [bytes32_t] and inherited [evmc_bytes32] objects.  The spine
     therefore has to survive the BLAKE3 call and be supplied to the reverse
     rule.  The module premise fixes the actual class layouts; this is not a
     claim about arbitrary classes with these names in an arbitrary [CU]. *)
  Axiom evmc_bytes32_array_byte_view_bridge :
    forall (p : ptr) q outputs,
      storage_page_cpp.source ⊧ CU ->
      evmc_bytes32_array_byte_view p q outputs.

  Section with_storage_page_module.
    Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma blake3_output_words_to_bytes :
    forall (p : ptr) q outputs,
      p |-> blake3_impl_h_specs.Blake3OutputWordsR q outputs
      |--
      p |-> evmc_bytes32_array_spineR (cQp.mut q) (length outputs) **
      p |-> blake3_impl_h_specs.Blake3OutputBytesR q outputs.
  Proof using CU MODd Sigma.
    intros p q outputs.
    unfold blake3_impl_h_specs.Blake3OutputWordsR,
      blake3_impl_h_specs.Blake3OutputBytesR,
      blake3_impl_h_specs.output_words_byte_values,
      blake3_impl_h_specs.output_word_byte_values,
      evmc_bytes32_array_bytesR,
      evmc_bytes32_array_byte_values.
    apply evmc_bytes32_array_to_bytes.
    apply evmc_bytes32_array_byte_view_bridge.
    exact MODd.
  Qed.

  Lemma blake3_output_bytes_to_words :
    forall (p : ptr) q outputs,
      List.Forall (fun x => (x < 2 ^ 256)%N) outputs ->
      p |-> evmc_bytes32_array_spineR (cQp.mut q) (length outputs) **
      p |-> blake3_impl_h_specs.Blake3OutputBytesR q outputs
      |--
      p |-> blake3_impl_h_specs.Blake3OutputWordsR q outputs.
  Proof using CU MODd Sigma.
    intros p q outputs Hrange.
    unfold blake3_impl_h_specs.Blake3OutputWordsR,
      blake3_impl_h_specs.Blake3OutputBytesR,
      blake3_impl_h_specs.output_words_byte_values,
      blake3_impl_h_specs.output_word_byte_values,
      evmc_bytes32_array_bytesR,
      evmc_bytes32_array_byte_values.
    apply evmc_bytes32_array_from_bytes.
    {
      apply evmc_bytes32_array_byte_view_bridge.
      exact MODd.
    }
    exact Hrange.
  Qed.

  Lemma blake3_cv_bytes_field_to_bytes32R :
    forall (base : ptr) words,
      length words = 8%nat ->
      base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
        o_field CU "evmc_bytes32::bytes"
        |-> arrayLR Tuchar 0 32
              (fun byte : val => primR Tuchar 1$m byte)
              (blake3_impl_h_specs.blake3_cv_byte_values words)
      ** base |-> structR "monad::bytes32_t"%cpp_name 1$m
      ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
        |-> structR "evmc_bytes32"%cpp_name 1$m
      |--
      base |-> exec_specs.bytes32R 1
        (model.bytes32_to_N (model.blake3_cv_digest words)).
  Proof using CU MODd Sigma.
    intros base words Hlen.
    rewrite (blake3_cv_byte_values_digest words Hlen).
    apply bytes_field_to_bytes32R.
    apply model.bytes32_to_N_range.
  Qed.

  Lemma blake3_cv_bytes_field_from_bytes32R :
    forall (base : ptr) words,
      length words = 8%nat ->
      base |-> exec_specs.bytes32R 1
        (model.bytes32_to_N (model.blake3_cv_digest words))
      |--
      base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
        o_field CU "evmc_bytes32::bytes"
        |-> arrayLR Tuchar 0 32
              (fun byte : val => primR Tuchar 1$m byte)
              (blake3_impl_h_specs.blake3_cv_byte_values words)
      ** base |-> structR "monad::bytes32_t"%cpp_name 1$m
      ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
        |-> structR "evmc_bytes32"%cpp_name 1$m.
  Proof using CU MODd Sigma.
    intros base words Hlen.
    rewrite (blake3_cv_byte_values_digest words Hlen).
    apply bytes32R_to_bytes_field.
  Qed.
  End with_storage_page_module.
End with_Sigma.

(* The bridge proofs above need to unfold the concrete [bytes32R] byte layout
   and the BLAKE3 big-endian decoder.  Keep that unfolding local to this file:
   downstream C++ proofs such as [init_leaf_scratch] are large enough that
   accidentally reducing [2^256]-sized byte encodings can exhaust memory. *)
#[global] Opaque
  evmc_bytes32_array_spineR
  exec_specs.bytes32_be_values
  exec_specs.bytes32_be_values_from
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  model.N_of_bytes_be.
#[global] Hint Opaque
  exec_specs.bytes32_be_values
  exec_specs.bytes32_be_values_from
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  model.N_of_bytes_be : sl_opacity.
