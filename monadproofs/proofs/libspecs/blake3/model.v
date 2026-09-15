(** * Library-level BLAKE3 model boundary

    This file is the pure Gallina boundary for the BLAKE3 APIs that appear in
    [storage_page.cpp].  It is intentionally lower-level than the MIP-8 page
    commitment model: it talks about the public hasher API from [blake3.h] and
    the one-block/batched compression entry points from [blake3_impl.h].

    The cryptographic core is still abstract.  The important change is that the
    MIP-8 model now defines its hash functions by choosing concrete BLAKE3
    modes, keys, flags, and input lengths, instead of postulating unrelated
    symbols directly in the MIP-8 directory.
*)

Set Default Goal Selector "!".

From Stdlib Require Import List NArith ZArith Lia.
Import ListNotations.
Require Import skylabs.prelude.arith.z_to_bytes.
Require Import skylabs.prelude.fin.

Local Open Scope N_scope.

Definition pow2N (bits : N) : N :=
  2 ^ bits.

Lemma pow2N_pos bits :
  (0 < pow2N bits)%N.
Proof.
  unfold pow2N.
  pose proof (N.pow_nonzero 2 bits).
  nia.
Qed.

#[global] Opaque pow2N.

Local Close Scope N_scope.

Ltac solve_pow2N_pos := apply pow2N_pos.

(** Fixed-width byte strings used by BLAKE3 and by callers that store digests as
    machine-sized words. *)
Definition byte : Set := fin.t (pow2N 8).
Definition word32 : Set := fin.t (pow2N 32).
Definition word64 : Set := fin.t (pow2N 64).
Definition word128 : Set := fin.t (pow2N 128).
Definition word256 : Set := fin.t (pow2N 256).

Definition bytes16 : Set := word128.
Definition bytes32 : Set := word256.
Definition bytes64 : Set := (bytes32 * bytes32)%type.
Definition digest : Set := bytes32.

Definition byte_of_N (word : N) : byte :=
  @fin.of_N' (pow2N 8) ltac:(solve_pow2N_pos) (word mod pow2N 8).

Definition bytes32_of_N (word : N) : bytes32 :=
  @fin.of_N' (pow2N 256) ltac:(solve_pow2N_pos) (word mod pow2N 256).

Definition bytes32_to_N (word : bytes32) : N :=
  fin.to_N word.

Lemma bytes32_to_N_range (word : bytes32) :
  (bytes32_to_N word < pow2N 256)%N.
Proof.
  apply fin.to_N_lt.
Qed.

Definition bytes16_of_N (word : N) : bytes16 :=
  @fin.of_N' (pow2N 128) ltac:(solve_pow2N_pos) (word mod pow2N 128).

(** Little-endian and big-endian byte views.  [store_bitmap_le] in
    [storage_page.cpp] uses the little-endian view for the 128-bit bitmap.
    Digest bytes are represented in the same big-endian order used by
    [bytes32R] in [exec_specs.v]. *)
Fixpoint bytes_of_N_le (len : nat) (word : N) : list byte :=
  match len with
  | O => []
  | S len' => byte_of_N word :: bytes_of_N_le len' (N.shiftr word 8)
  end.

Fixpoint bytes_of_N_be (len : nat) (word : N) : list byte :=
  match len with
  | O => []
  | S len' =>
      byte_of_N (N.shiftr word (8 * N.of_nat len')) ::
      bytes_of_N_be len' word
  end.

Definition bytes16_le_bytes (word : bytes16) : list byte :=
  bytes_of_N_le 16 (fin.to_N word).

Definition bytes32_be_bytes (word : bytes32) : list byte :=
  bytes_of_N_be 32 (bytes32_to_N word).

Fixpoint N_of_bytes_be_from (acc : N) (bytes : list byte) : N :=
  match bytes with
  | [] => acc
  | byte :: rest =>
      N_of_bytes_be_from (256 * acc + fin.to_N byte) rest
  end.

Definition N_of_bytes_be (bytes : list byte) : N :=
  Z.to_N (_Z_from_bytes types.Big types.Unsigned (map fin.to_N bytes)).

#[global] Opaque N_of_bytes_be.

Definition zero_byte : byte := byte_of_N 0.

Definition pad_bytes (len : nat) (bytes : list byte) : list byte :=
  firstn len (bytes ++ repeat zero_byte len).

Definition bytes32_of_be_bytes (bytes : list byte) : bytes32 :=
  bytes32_of_N (N_of_bytes_be (pad_bytes 32 bytes)).

Definition bytes64_of_bytes (bytes : list byte) : bytes64 :=
  let padded := pad_bytes 64 bytes in
  (bytes32_of_be_bytes (firstn 32 padded),
   bytes32_of_be_bytes (firstn 32 (skipn 32 padded))).

(** The flags below are the semantic names from [blake3_impl.h].  Specs may
    still mention their C integer encodings, but model definitions should use
    the semantic constructors.

    [FlagChunkStart] and [FlagChunkEnd] delimit the first and last block of a
    BLAKE3 chunk.  [FlagParent] marks a parent-node compression in the ordinary
    BLAKE3 tree.  [FlagRoot] marks final output generation.  [FlagKeyedHash]
    selects the keyed-hash mode.  [FlagDeriveKeyContext] and
    [FlagDeriveKeyMaterial] are the two stages of BLAKE3's derive-key mode. *)
Inductive blake3_flag : Type :=
| FlagChunkStart
| FlagChunkEnd
| FlagParent
| FlagRoot
| FlagKeyedHash
| FlagDeriveKeyContext
| FlagDeriveKeyMaterial.

Definition blake3_flag_value (flag : blake3_flag) : Z :=
  match flag with
  | FlagChunkStart => 1
  | FlagChunkEnd => 2
  | FlagParent => 4
  | FlagRoot => 8
  | FlagKeyedHash => 16
  | FlagDeriveKeyContext => 32
  | FlagDeriveKeyMaterial => 64
  end%Z.

(** A BLAKE3 chaining value ("CV") is the eight-word state passed between
    compression calls.  The initialization vector ("IV") below is the standard
    BLAKE3 initial CV exported by the upstream C implementation as [IV]. *)
Definition blake3_cv : Set := list N.

(** A BLAKE3 chaining-value word is a [uint32_t].  The public model keeps the
    convenient [list N] representation, so this predicate records the machine
    range that the C representation enforces. *)
Definition blake3_word_modulus : N := 4294967296%N.

Definition blake3_word_in_range (word : N) : Prop :=
  (word < blake3_word_modulus)%N.

Definition normalize_blake3_word (word : N) : N :=
  word mod blake3_word_modulus.

Lemma normalize_blake3_word_range word :
  blake3_word_in_range (normalize_blake3_word word).
Proof.
  unfold blake3_word_in_range, normalize_blake3_word,
    blake3_word_modulus.
  apply N.mod_lt.
  discriminate.
Qed.

Lemma normalize_blake3_word_id word :
  blake3_word_in_range word ->
  normalize_blake3_word word = word.
Proof.
  unfold blake3_word_in_range, normalize_blake3_word.
  apply N.mod_small.
Qed.

(** The initialization vector exported by [blake3_impl.h] as [IV]. *)
Definition blake3_iv_words : blake3_cv :=
  [1779033703; 3144134277; 1013904242; 2773480762;
   1359893119; 2600822924; 528734635; 1541459225]%N.

Lemma blake3_iv_words_range :
  List.Forall blake3_word_in_range blake3_iv_words.
Proof.
  repeat constructor; vm_compute.
Qed.

(** Abstract BLAKE3 primitives.  These correspond to the library interfaces,
    not to MIP-8 security assumptions:

    - [blake3_compress_in_place_model] models the internal compression entry
      point from [blake3_impl.h];
    - [blake3_hash_one_model] models one logical lane of [blake3_hash_many].
*)
Definition normalize_blake3_cv (words : list N) : blake3_cv :=
  let prefix := firstn 8 words in
  map normalize_blake3_word
    (prefix ++ repeat 0%N (8 - length prefix)).

Lemma normalize_blake3_cv_length words :
  length (normalize_blake3_cv words) = 8%nat.
Proof.
  unfold normalize_blake3_cv.
  rewrite map_length, length_app, repeat_length.
  pose proof (firstn_le_length 8 words).
  lia.
Qed.

Lemma normalize_blake3_cv_range words :
  List.Forall blake3_word_in_range (normalize_blake3_cv words).
Proof.
  unfold normalize_blake3_cv.
  apply Forall_map.
  apply Forall_forall.
  intros word _.
  apply normalize_blake3_word_range.
Qed.

Lemma normalize_blake3_cv_id words :
  length words = 8%nat ->
  List.Forall blake3_word_in_range words ->
  normalize_blake3_cv words = words.
Proof.
  intros Hlength Hrange.
  unfold normalize_blake3_cv.
  rewrite firstn_all2.
  2: {
    lia.
  }
  replace (8 - length words)%nat with 0%nat by lia.
  rewrite app_nil_r.
  rewrite <- (map_id words) at 2.
  apply map_ext_in.
  intros word Hword.
  apply normalize_blake3_word_id.
  rewrite Forall_forall in Hrange.
  apply Hrange.
  exact Hword.
Qed.

Definition blake3_compress_in_place_model_raw
    (cv : blake3_cv) (block : bytes64) (block_len counter : N)
    (flags : list blake3_flag) : blake3_cv.
Admitted. (* TOFIXLATER: executable model of blake3_compress_in_place. *)

Definition blake3_compress_in_place_model
    (cv : blake3_cv) (block : bytes64) (block_len counter : N)
    (flags : list blake3_flag) : blake3_cv :=
  normalize_blake3_cv
    (blake3_compress_in_place_model_raw
       cv block block_len counter flags).

Lemma blake3_compress_in_place_model_length
    cv block block_len counter flags :
  length
    (blake3_compress_in_place_model
       cv block block_len counter flags) = 8%nat.
Proof.
  apply normalize_blake3_cv_length.
Qed.

Lemma blake3_compress_in_place_model_range
    cv block block_len counter flags :
  List.Forall blake3_word_in_range
    (blake3_compress_in_place_model
       cv block block_len counter flags).
Proof.
  apply normalize_blake3_cv_range.
Qed.

Record blake3_hash_many_params : Type := {
  blake3_hash_many_key : blake3_cv;
  blake3_hash_many_counter : N;
  blake3_hash_many_increment_counter : bool;
  blake3_hash_many_flags : list blake3_flag;
  blake3_hash_many_flags_start : list blake3_flag;
  blake3_hash_many_flags_end : list blake3_flag;
}.

Definition blake3_hash_one_model
    (params : blake3_hash_many_params) (input : bytes64) : digest.
Admitted. (* TOFIXLATER: executable model of one blake3_hash_many lane. *)

(** The portable and SIMD implementations advance a [uint64_t] counter
    between independent inputs when requested.  This is batch scheduling,
    not a property to assume about the abstract one-input hash. *)
Definition blake3_hash_many_next_params (params : blake3_hash_many_params)
    : blake3_hash_many_params :=
  {|
    blake3_hash_many_key := params.(blake3_hash_many_key);
    blake3_hash_many_counter :=
      ((params.(blake3_hash_many_counter) + 1) mod 18446744073709551616)%N;
    blake3_hash_many_increment_counter := params.(blake3_hash_many_increment_counter);
    blake3_hash_many_flags := params.(blake3_hash_many_flags);
    blake3_hash_many_flags_start := params.(blake3_hash_many_flags_start);
    blake3_hash_many_flags_end := params.(blake3_hash_many_flags_end);
  |}.

Fixpoint blake3_hash_many_incrementing_model
    (params : blake3_hash_many_params) (inputs : list bytes64)
    : list digest :=
  match inputs with
  | [] => []
  | input :: rest =>
      blake3_hash_one_model params input ::
      blake3_hash_many_incrementing_model
        (blake3_hash_many_next_params params) rest
  end.

Definition blake3_hash_many_model
    (params : blake3_hash_many_params) (inputs : list bytes64)
    : list digest :=
  if params.(blake3_hash_many_increment_counter)
  then blake3_hash_many_incrementing_model params inputs
  else map (blake3_hash_one_model params) inputs.

Lemma blake3_hash_many_model_length params inputs :
  length (blake3_hash_many_model params inputs) = length inputs.
Proof.
  unfold blake3_hash_many_model.
  destruct params.(blake3_hash_many_increment_counter).
  {
    revert params.
    induction inputs as [| input rest IH]; intro params.
    { reflexivity. }
    cbn [blake3_hash_many_incrementing_model length].
    rewrite IH.
    reflexivity.
  }
  { apply length_map. }
Qed.

Example blake3_hash_many_two_counters params lhs rhs :
  params.(blake3_hash_many_increment_counter) = true ->
  blake3_hash_many_model params [lhs; rhs] =
    [blake3_hash_one_model params lhs;
     blake3_hash_one_model (blake3_hash_many_next_params params) rhs].
Proof.
  intro Hincrement.
  unfold blake3_hash_many_model.
  rewrite Hincrement.
  reflexivity.
Qed.

Example blake3_hash_many_counter_wrap params :
  params.(blake3_hash_many_counter) = 18446744073709551615%N ->
  (blake3_hash_many_next_params params).(blake3_hash_many_counter) = 0%N.
Proof.
  intro Hcounter.
  change ((params.(blake3_hash_many_counter) + 1) mod
    18446744073709551616 = 0)%N.
  rewrite Hcounter.
  reflexivity.
Qed.

Definition blake3_cv_bytes (cv : blake3_cv) : list byte :=
  concat (map (bytes_of_N_le 4) (normalize_blake3_cv cv)).

Definition blake3_cv_digest (cv : blake3_cv) : digest :=
  bytes32_of_be_bytes (blake3_cv_bytes cv).
