(** * Specs for the internal [blake3_impl.h] API

    [storage_page.cpp] uses two internal BLAKE3 entry points:

    - [blake3_hash_many] for batches of independent 64-byte pair/merge blocks;
    - [blake3_compress_in_place] to derive the MIP-8 leaf IV from the domain
      string in [get_leaf_iv].

    These functions are internal to the upstream BLAKE3 C implementation.  The
    specs here expose exactly the call shapes used by the page commitment while
    delegating the cryptographic computation to [model.v].
*)

Set Default Goal Selector "!".

From Stdlib Require Import List NArith ZArith.
Import ListNotations.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.prelude.fin.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.blake3.model.

Import cQp_compat.

Local Open Scope Z_scope.

Definition all_blake3_flags : list blake3_flag :=
  [FlagChunkStart; FlagChunkEnd; FlagParent; FlagRoot;
   FlagKeyedHash; FlagDeriveKeyContext; FlagDeriveKeyMaterial].

Definition blake3_flag_is_set (flags : Z) (flag : blake3_flag) : bool :=
  negb (Z.eqb (Z.land flags (blake3_flag_value flag)) 0).

Definition blake3_flags_of_Z (flags : Z) : list blake3_flag :=
  filter (blake3_flag_is_set flags) all_blake3_flags.

Definition blake3_hash_many_call_params
    (key : blake3_cv) (counter : N) (increment_counter : bool)
    (flags flags_start flags_end : Z) : blake3_hash_many_params :=
  {|
    blake3_hash_many_key := key;
    blake3_hash_many_counter := counter;
    blake3_hash_many_increment_counter := increment_counter;
    blake3_hash_many_flags := blake3_flags_of_Z flags;
    blake3_hash_many_flags_start := blake3_flags_of_Z flags_start;
    blake3_hash_many_flags_end := blake3_flags_of_Z flags_end;
  |}.

Definition blake3_hash_many_outputs_from_params
    (params : blake3_hash_many_params) (inputs : list bytes64) : list N :=
  map bytes32_to_N (blake3_hash_many_model params inputs).

Definition blake3_compress_flags (flags : Z)
    : option (list blake3_flag) :=
  if flags =? blake3_flag_value FlagDeriveKeyMaterial
  then Some [FlagDeriveKeyMaterial]
  else
    if flags =?
       (blake3_flag_value FlagChunkStart +
        blake3_flag_value FlagChunkEnd +
        blake3_flag_value FlagRoot)
    then Some [FlagChunkStart; FlagChunkEnd; FlagRoot]
    else None.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition bytes32_ty : type := "monad::bytes32_t"%cpp_type.

  (** The original BLAKE3 API reads an array of [uint8_t const *] inputs.  The
      page commitment has two concrete call-site shapes:

      - leaf hashing stores pointers to immutable page bytes;
      - merge hashing stores pointers to mutable local [blocks] rows, then
        passes those pointers through the usual C++ qualification conversion.

      The pointee bytes are read-only in both cases.  [blake3_input_ptr_ty_for]
      records the C++ source-level pointer type, with [const = true] meaning
      [uint8_t const *] and [const = false] meaning [uint8_t *].  The
      representation predicates below use [blake3_input_ptr_store_ty_for], the
      heap type of each pointer object; BRiCk's array rules address array
      elements using erased heap types, not cv-qualified source types. *)

  Definition blake3_input_ptr_ty_for
      (const : bool) : type :=
    if const then Tptr (Qconst Tuchar) else Tptr Tuchar.

  Definition blake3_input_ptr_ty : type :=
    blake3_input_ptr_ty_for true.

  Definition blake3_input_ptr_store_ty_for
      (const : bool) : type :=
    erase_qualifiers (blake3_input_ptr_ty_for const).

  Definition blake3_input_ptr_store_ty : type :=
    blake3_input_ptr_store_ty_for true.

  Definition blake3_input_ptr_value_ty_for
      (const : bool) : type :=
    blake3_input_ptr_store_ty_for const.

  Definition blake3_input_ptr_value_ty : type :=
    blake3_input_ptr_value_ty_for true.

  Definition byte_value (byte : byte) : val :=
    Vint (Z.of_N (fin.to_N byte)).

  Definition byte_values (bytes : list byte) : list val :=
    map byte_value bytes.

  Definition bytes32_byte_values (word : bytes32) : list val :=
    bytes32_be_values (bytes32_to_N word).

  Definition bytes64_byte_values (block : bytes64) : list val :=
    bytes32_byte_values (fst block) ++
    bytes32_byte_values (snd block).

  Definition blake3_cv_byte_values (cv : blake3_cv) : list val :=
    byte_values (blake3_cv_bytes cv).

  Definition RawDigestBytesR (q : cQp.t) (digest : digest) : Rep :=
    arrayR Tuchar
      (primR Tuchar q)
      (bytes32_byte_values digest).

  Record blake3_input_block : Type := {
    blake3_input_block_ptr : ptr;
    blake3_input_block_data : bytes64;
  }.

  Definition BlockR (q : Qp) (block : bytes64) : Rep :=
    arrayR Tuchar
      (primR Tuchar (cQp.mut q))
      (bytes64_byte_values block).

  Definition Blake3BlockR := BlockR.

  Definition output_word_byte_values (word : N) : list val :=
    bytes32_be_values word.

  Definition output_words_byte_values (outputs : list N) : list val :=
    concat (map output_word_byte_values outputs).

  Fixpoint Blake3InputBlocksDataR
      (q : Qp) (inputs : list blake3_input_block) : mpred :=
    match inputs with
    | [] => emp
    | input :: inputs_rest =>
        input.(blake3_input_block_ptr)
        |-> BlockR q input.(blake3_input_block_data)
        ** Blake3InputBlocksDataR q inputs_rest
    end.

  Definition Blake3InputBlocksR
      (const : bool)
      (ptr_q block_q : Qp) (inputs : list blake3_input_block) : Rep :=
    as_Rep
      (fun base =>
         base |-> arrayLR (blake3_input_ptr_store_ty_for const)
           0 (Z.of_nat (length inputs))
           (fun input =>
              primR
                (blake3_input_ptr_value_ty_for const)
                (cQp.mut ptr_q)
                (Vptr input.(blake3_input_block_ptr)))
           inputs
         ** Blake3InputBlocksDataR block_q inputs).

  Definition Blake3OutputWordsR (q : Qp) (outputs : list N) : Rep :=
    arrayR bytes32_ty (bytes32R q) outputs.

  (** [blake3_hash_many] has C signature [uint8_t *out].  This predicate is
      the call-boundary view of its output buffer: a flat byte array containing
      the big-endian bytes of each 32-byte output word.  Callers that allocate a
      [bytes32_t[]] and pass it via [reinterpret_cast<uint8_t *>] must bridge
      between this byte view and [Blake3OutputWordsR] at the call site. *)
  Definition Blake3OutputBytesR (q : Qp) (outputs : list N) : Rep :=
    arrayR Tuchar
      (primR Tuchar (cQp.mut q))
      (output_words_byte_values outputs).

  Lemma blake3_hash_many_outputs_from_params_range params inputs :
    List.Forall (fun x => (x < 2 ^ 256)%N)
      (blake3_hash_many_outputs_from_params params inputs).
  Proof.
    unfold blake3_hash_many_outputs_from_params.
    apply List.Forall_forall.
    intros word Hword.
    apply List.in_map_iff in Hword.
    destruct Hword as [digest [<- _]].
    apply bytes32_to_N_range.
  Qed.

  Definition Blake3KeyWordsR (q : Qp) (words : list N) : Rep :=
    arrayR Tuint
      (fun word => uintR (cQp.mut q) (Z.of_N word))
      words
    ** [| length words = 8%nat |].

  Definition Blake3ConstKeyWordsR (q : Qp) (words : list N) : Rep :=
    arrayR Tuint
      (fun word => uintR (cQp.const q) (Z.of_N word))
      words.

  Lemma Blake3ConstKeyWordsR_pack (p : ptr) q words :
    length words = 8%nat ->
    p |-> arrayR Tuint
      (fun word => uintR (cQp.const q) (Z.of_N word))
      words |--
    p |-> Blake3ConstKeyWordsR q words.
  Proof.
    intro Hlength.
    unfold Blake3ConstKeyWordsR.
    go.
  Qed.

  Definition Blake3ConstKeyWordsR_pack_F p q words Hlength :=
    [FWD] (Blake3ConstKeyWordsR_pack p q words Hlength).

  Lemma Blake3ConstKeyWordsR_unpack (p : ptr) q words :
    p |-> Blake3ConstKeyWordsR q words |--
    p |-> arrayR Tuint
      (fun word => uintR (cQp.const q) (Z.of_N word))
      words.
  Proof.
    unfold Blake3ConstKeyWordsR.
    go.
  Qed.

  Definition Blake3ConstKeyWordsR_unpack_F p q words :=
    [FWD] (Blake3ConstKeyWordsR_unpack p q words).

  cpp.spec "blake3_compress_in_place"
    from storage_page_cpp.source as blake3_compress_in_place_spec
    with (
      \arg{cvp : ptr} "cv" (Vptr cvp)
      \arg{blockp : ptr} "block" (Vptr blockp)
      \arg{block_len : N} "block_len" (Vn block_len)
      \arg{counter : N} "counter" (Vn counter)
      \arg{flags : Z} "flags" (Vint flags)
      \pre{cv block flag_list}
        [| blake3_compress_flags flags = Some flag_list |]
        ** [| (block_len <= 64)%N |]
        ** cvp |-> Blake3KeyWordsR 1 cv
        ** blockp |-> Blake3BlockR 1 block
      \post
        cvp |-> Blake3KeyWordsR 1
          (blake3_compress_in_place_model
             cv block block_len counter flag_list)
        ** blockp |-> Blake3BlockR 1 block
    ).

  cpp.spec "blake3_hash_many"
    from storage_page_cpp.source as blake3_hash_many_spec
    with (
      \arg{inputs : ptr} "inputs" (Vptr inputs)
      \arg{num_inputs : N} "num_inputs" (Vn num_inputs)
      \arg{blocks : N} "blocks" (Vn blocks)
      \arg{key : ptr} "key" (Vptr key)
      \arg{counter : N} "counter" (Vn counter)
      \arg{increment_counter : bool} "increment_counter"
        (Vbool increment_counter)
      \arg{flags : Z} "flags" (Vint flags)
      \arg{flags_start : Z} "flags_start" (Vint flags_start)
      \arg{flags_end : Z} "flags_end" (Vint flags_end)
      \arg{out : ptr} "out" (Vptr out)
      \pre{(input_const : bool)
            key_q input_q key_words inputs_model old_outputs}
        [| blocks = 1%N |]
        (* The semantic flags represent bits 0..6.  The compression function
           does not discard bit 7, so calls using it are outside this spec. *)
        ** [| flags < 128 /\ flags_start < 128 /\ flags_end < 128 |]
        ** [| length inputs_model = N.to_nat num_inputs |]
        ** [| length old_outputs = length inputs_model |]
        ** [| length key_words = 8%nat |]
      \prepost
        key |-> Blake3ConstKeyWordsR key_q key_words
      \prepost
        inputs |-> Blake3InputBlocksR
          input_const 1 input_q inputs_model
      \pre
        out |-> Blake3OutputBytesR 1 old_outputs
      \post
        out |-> Blake3OutputBytesR 1
          (blake3_hash_many_outputs_from_params
             (blake3_hash_many_call_params
                key_words counter increment_counter
                flags flags_start flags_end)
             (map blake3_input_block_data inputs_model))
    ).

End with_Sigma.
