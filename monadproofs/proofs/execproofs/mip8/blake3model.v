(** * MIP-8 view of the library-level BLAKE3 model

    The reusable BLAKE3 boundary lives in
    [monad.proofs.libspecs.blake3.model].  This file keeps the short MIP-8
    names used by the commitment development and adds the storage-page type
    aliases ([slot_word] and [pair_leaf]).

    In particular, [H64], [seal_empty], and [seal_nonempty] are no longer
    independent admitted functions here.  They are definitions obtained by
    selecting the concrete BLAKE3 modes used by [storage_page.cpp].
*)

Set Default Goal Selector "!".

From Stdlib Require Import List NArith ZArith.
Import ListNotations.
Require Import monad.proofs.libspecs.blake3.model.

Definition pow2N := model.pow2N.
Ltac solve_pow2N_pos := model.solve_pow2N_pos.

Definition byte : Set := model.byte.
Definition word32 : Set := model.word32.
Definition word64 : Set := model.word64.
Definition word128 : Set := model.word128.
Definition word256 : Set := model.word256.

Definition bytes16 : Set := model.bytes16.
Definition bytes32 : Set := model.bytes32.
Definition bytes64 : Set := model.bytes64.

Definition slot_word : Set := bytes32.
Definition digest : Set := model.digest.
Definition pair_leaf : Set := bytes64.

Definition byte_of_N := model.byte_of_N.
Definition bytes32_of_N := model.bytes32_of_N.
Definition bytes32_to_N := model.bytes32_to_N.
Definition bytes16_of_N := model.bytes16_of_N.
Definition bytes16_le_bytes := model.bytes16_le_bytes.
Definition bytes32_be_bytes := model.bytes32_be_bytes.
Definition bytes32_of_be_bytes := model.bytes32_of_be_bytes.
Definition bytes64_of_bytes := model.bytes64_of_bytes.

Lemma bytes32_to_N_range (word : bytes32) :
  (bytes32_to_N word < pow2N 256)%N.
Proof.
  apply model.bytes32_to_N_range.
Qed.

(** ["ultra_merkle_pair_leaf_domain___"] is the domain string used by the
    storage-page leaf-key derivation.  It is independent of BLAKE3's standard
    IV; the helper [get_leaf_iv] copies these exact 32 bytes into the first half
    of a zero-padded 64-byte block, then compresses that block from the standard
    IV with [DERIVE_KEY_MATERIAL]. *)
Definition mip8_leaf_domain_bytes : list byte :=
  map byte_of_N
    [117; 108; 116; 114; 97; 95; 109; 101;
     114; 107; 108; 101; 95; 112; 97; 105;
     114; 95; 108; 101; 97; 102; 95; 100;
     111; 109; 97; 105; 110; 95; 95; 95]%N.

Lemma mip8_leaf_domain_bytes_length :
  length mip8_leaf_domain_bytes = 32%nat.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition mip8_leaf_domain_word_N : N :=
  53112226453502929525972288139468611562723998211087074368781539751639348371295.

Definition mip8_leaf_domain_word : bytes32 :=
  bytes32_of_N mip8_leaf_domain_word_N.

Definition mip8_leaf_domain_block : bytes64 :=
  (mip8_leaf_domain_word, bytes32_of_N 0).

(** The page commitment uses two one-block [blake3_hash_many] call shapes.  The
    boolean tag is the MIP-8 view used by the commitment proofs: [leaf_mode]
    means "hash a 64-byte storage-pair leaf", while [merge_mode] means "hash a
    64-byte pair of already-computed child digests". *)
Definition hash_mode : Set := bool.
Definition leaf_mode : hash_mode := true.
Definition merge_mode : hash_mode := false.

(** The MIP-8 leaf key is derived exactly as [get_leaf_iv] does: start from the
    standard BLAKE3 IV, compress the domain block with block length 64, counter
    0, and [DERIVE_KEY_MATERIAL], and use the resulting eight-word chaining
    value as the key for leaf [blake3_hash_many] calls. *)
Definition mip8_leaf_iv_words : model.blake3_cv :=
  model.blake3_compress_in_place_model
    model.blake3_iv_words mip8_leaf_domain_block 64 0
    [model.FlagDeriveKeyMaterial].

Lemma mip8_leaf_iv_words_length :
  length mip8_leaf_iv_words = 8%nat.
Proof.
  apply model.blake3_compress_in_place_model_length.
Qed.

Lemma mip8_leaf_iv_words_range :
  List.Forall model.blake3_word_in_range mip8_leaf_iv_words.
Proof.
  apply model.blake3_compress_in_place_model_range.
Qed.

(** Leaf hashing uses the derived MIP-8 leaf key, counter 0, no counter
    increment, and [DERIVE_KEY_MATERIAL].  The start/end flag arguments are
    empty because the mode is selected by the main flag word in the C call. *)
Definition leaf_hash_many_params : model.blake3_hash_many_params :=
  {|
    model.blake3_hash_many_key := mip8_leaf_iv_words;
    model.blake3_hash_many_counter := 0;
    model.blake3_hash_many_increment_counter := false;
    model.blake3_hash_many_flags := [model.FlagDeriveKeyMaterial];
    model.blake3_hash_many_flags_start := [];
    model.blake3_hash_many_flags_end := [];
  |}.

(** Merge hashing uses the standard BLAKE3 IV, counter 0, no counter increment,
    no main flag word, and [CHUNK_START]/[CHUNK_END] as the start/end flags.
    This is the one-block compression mode used for internal induced-tree
    merges in [storage_page.cpp]. *)
Definition merge_hash_many_params : model.blake3_hash_many_params :=
  {|
    model.blake3_hash_many_key := model.blake3_iv_words;
    model.blake3_hash_many_counter := 0;
    model.blake3_hash_many_increment_counter := false;
    model.blake3_hash_many_flags := [];
    model.blake3_hash_many_flags_start := [model.FlagChunkStart];
    model.blake3_hash_many_flags_end := [model.FlagChunkEnd];
  |}.

Definition params_for_hash_mode (mode : hash_mode)
    : model.blake3_hash_many_params :=
  if mode then leaf_hash_many_params else merge_hash_many_params.

(** One-block BLAKE3 calls.  The C++ connection is captured by the
    [blake3_hash_many] spec in
    [monad.proofs.libspecs.blake3.blake3_impl_h_specs].  Leaf calls select the
    derived MIP-8 leaf IV and [DERIVE_KEY_MATERIAL]; merge calls select the
    standard BLAKE3 IV and [CHUNK_START | CHUNK_END]. *)
Definition H64 (mode : hash_mode) (input : bytes64) : digest :=
  model.blake3_hash_one_model (params_for_hash_mode mode) input.

Definition blake3_seal_flags : list model.blake3_flag :=
  [model.FlagChunkStart; model.FlagChunkEnd; model.FlagRoot].

Definition seal_input_bytes
    (slot_bitmap : bytes16) (root : option digest) : list byte :=
  match root with
  | None => bytes16_le_bytes slot_bitmap
  | Some root => bytes16_le_bytes slot_bitmap ++ bytes32_be_bytes root
  end.

Definition seal_input_len (root : option digest) : N :=
  match root with
  | None => 16
  | Some _ => 48
  end.

Definition seal_compress_digest
    (slot_bitmap : bytes16) (root : option digest) : digest :=
  model.blake3_cv_digest
    (model.blake3_compress_in_place_model
       model.blake3_iv_words
       (bytes64_of_bytes (seal_input_bytes slot_bitmap root))
       (seal_input_len root)
       0
       blake3_seal_flags).

(** Final page seals.  The definitions match [blake3_seal] in
    [storage_page.cpp]: build the little-endian bitmap block, optionally append
    the 32-byte merge root, run one [blake3_compress_in_place] call with
    [CHUNK_START | CHUNK_END | ROOT], and interpret the resulting chaining
    value bytes as the returned [bytes32_t]. *)
Definition seal_empty (slot_bitmap : bytes16) : digest :=
  seal_compress_digest slot_bitmap None.

Definition seal_nonempty
    (slot_bitmap : bytes16) (root : digest) : digest :=
  seal_compress_digest slot_bitmap (Some root).

Opaque H64 seal_empty seal_nonempty.
