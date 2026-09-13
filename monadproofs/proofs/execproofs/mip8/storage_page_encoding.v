Set Default Goal Selector "!".

(**
  Compact RLP and the Historical Storage-Page RLE Format
  -----------------------------------------

  This file retains the compact-RLP models and the checked page-format proofs
  from before public main [1d22498c5f6a]. The current production encoder and
  decoder use [storage_page_indexed_encoding] instead. Its proofs reuse the
  compact-RLP results here; the RLE page models below are historical, not the
  contract of the updated [storage_page.cpp].

  The format is a page-local run-length encoding over the 128 storage slots:

  - zero runs are represented by a small count byte;
  - the byte [0] means "the rest of the 128-slot page is zero";
  - nonzero runs are represented by [128 + run - 1] followed by compact RLP
    encodings of the run's bytes32 slots.

  This historical decoder model enforces the canonical run and compact-RLP
  structure of the former C++ decoder. The theorem
  [decode_encode_storage_page_model] says canonical 128-slot pages round-trip
  through the public encoder and decoder.
*)

From Stdlib Require Import Bool List NArith ZArith Lia.
Import ListNotations.

Require Import monad.proofs.execproofs.mip8.commitment.
Require Import monad.proofs.libspecs.result_model.
Require Import monad.proofs.libspecs.rlp_decode_error_model.

Definition storage_encoded_byte_in_range (byte : Z) : Prop :=
  (0 <= byte <= 255)%Z.

Definition storage_encoded_bytes_in_range (bytes : list Z) : Prop :=
  Forall storage_encoded_byte_in_range bytes.

Lemma storage_encoded_bytes_in_range_nil :
  storage_encoded_bytes_in_range [].
Proof.
  constructor.
Qed.

Lemma storage_encoded_bytes_in_range_cons_head byte rest :
  storage_encoded_bytes_in_range (byte :: rest) ->
  storage_encoded_byte_in_range byte.
Proof.
  intro Hrange.
  inversion Hrange.
  assumption.
Qed.

Lemma storage_encoded_bytes_in_range_cons_tail byte rest :
  storage_encoded_bytes_in_range (byte :: rest) ->
  storage_encoded_bytes_in_range rest.
Proof.
  intro Hrange.
  inversion Hrange.
  assumption.
Qed.

(** Compact bytes32 encoding drops leading zero bytes before applying the RLP
    short-string encoding used in MIP 8.  Bytes are represented as [Z] because
    the generated C++ AST uses integer values for unsigned-char operations. *)
Definition word_byte (shift word : N) : Z :=
  Z.of_N (N.land (N.shiftr word shift) 255).

Definition be_bytes (len : nat) (word : N) : list Z :=
  map Z.of_N
    (z_to_bytes._Z_to_bytes
       len types.Big types.Unsigned (Z.of_N word)).

Fixpoint drop_leading_zeroes (bytes : list Z) : list Z :=
  match bytes with
  | 0%Z :: rest => drop_leading_zeroes rest
  | _ => bytes
  end.

Definition compact_bytes32_payload (word : N) : list Z :=
  drop_leading_zeroes (be_bytes 32 word).

Definition rlp_encode_short_string (payload : list Z) : list Z :=
  match payload with
  | [byte] =>
      if (0 <=? byte)%Z && (byte <=? 127)%Z
      then [byte]
      else [(128 + Z.of_nat (length payload))%Z; byte]
  | _ => (128 + Z.of_nat (length payload))%Z :: payload
  end.

Definition encode_slot_model (slot : N) : list Z :=
  rlp_encode_short_string (compact_bytes32_payload slot).

Definition slots_nonzero (slots : list N) : Prop :=
  Forall (fun slot => slot <> 0%N) slots.

(* Page encoding is a run-length format over slots.  Zero runs become small
   count bytes; nonzero runs become an RLP header followed by compact slot
   encodings.  This mirrors the C++ loop structure while remaining pure Coq. *)
Fixpoint count_zero_prefix (limit : nat) (page : list N) : nat :=
  match limit, page with
  | O, _ => O
  | S limit', slot :: rest =>
      if N.eq_dec slot 0
      then S (count_zero_prefix limit' rest)
      else O
  | _, [] => O
  end.

Fixpoint count_nonzero_prefix (limit : nat) (page : list N) : nat :=
  match limit, page with
  | O, _ => O
  | S limit', slot :: rest =>
      if N.eq_dec slot 0
      then O
      else S (count_nonzero_prefix limit' rest)
  | _, [] => O
  end.

Fixpoint encode_storage_page_fuel
    (fuel : nat) (page : list N) : list Z :=
  match fuel, page with
  | O, _ => []
  | _, [] => []
  | S fuel', slot :: _ =>
      if N.eq_dec slot 0
      then
        let zeros := count_zero_prefix (S fuel') page in
        if Nat.eqb zeros (length page)
        then [0%Z]
        else Z.of_nat zeros :: encode_storage_page_fuel fuel' (skipn zeros page)
      else
        let run := count_nonzero_prefix page_slot_count page in
        (128 + Z.of_nat (run - 1))%Z
          :: concat (map encode_slot_model (firstn run page))
             ++ encode_storage_page_fuel fuel' (skipn run page)
  end.

Definition encode_storage_page_model (page : list N) : list Z :=
  encode_storage_page_fuel (length page) page.

(* Decoding is written as the partial inverse shape of the encoder.  The fuel
   bounds recursive calls by the page size so malformed input cannot make the
   model diverge. *)
Fixpoint word_of_be_bytes_from (acc : N) (bytes : list Z) : N :=
  match bytes with
  | [] => acc
  | byte :: rest =>
      word_of_be_bytes_from (256 * acc + Z.to_N byte) rest
  end.

Definition word_of_compact_payload (payload : list Z) : N :=
  Z.to_N
    (z_to_bytes._Z_from_bytes
       types.Big types.Unsigned (map Z.to_N payload)).

(** [normalize_slot_model] is the value-level effect of storing only the compact
    32-byte encoding and reading it back.  For ordinary bytes32 values this is
    the identity; keeping it explicit makes the page roundtrip theorem true
    without silently assuming every [N] is already below [2^256]. *)
Definition normalize_slot_model (slot : N) : N :=
  word_of_compact_payload (compact_bytes32_payload slot).

Definition normalize_storage_page_model (page : list N) : list N :=
  map normalize_slot_model page.

Definition rlp_short_string_is_noncanonical
    (payload_length : nat) (encoded_payload : list Z) : bool :=
  Nat.eqb payload_length 1 &&
  match encoded_payload with
  | byte :: _ => (byte <? 128)%Z
  | [] => false
  end.

Definition rlp_decode_long_string_length
    (length_bytes : list Z) : option nat :=
  match length_bytes with
  | [] => None
  | first :: _ =>
      if (first =? 0)%Z
      then None
      else
        let length_N := word_of_be_bytes_from 0 length_bytes in
        (* [decode_length] returns [size_t], which is 64 bits in this build. *)
        if (N.size length_N <=? 64)%N
        then Some (N.to_nat length_N)
        else None
  end.

Fixpoint rlp_decode_string_model
    (encoded : list Z) : option (list Z * list Z) :=
  match encoded with
  | [] => None
  | header :: rest =>
      if (header <=? 127)%Z
      then Some ([header], rest)
      else if (128 <=? header)%Z && (header <=? 183)%Z
      then
        let len := Z.to_nat (header - 128)%Z in
        if rlp_short_string_is_noncanonical len rest
        then None
        else
          if Nat.leb len (length rest)
          then Some (firstn len rest, skipn len rest)
          else None
      else if (184 <=? header)%Z && (header <=? 191)%Z
      then
        let length_of_length := Z.to_nat (header - 183)%Z in
        if Nat.ltb length_of_length (length rest)
        then
          match rlp_decode_long_string_length
                  (firstn length_of_length rest) with
          | Some len =>
              if Nat.ltb len 56
              then None
              else
                let payload_and_rest := skipn length_of_length rest in
                if Nat.leb len (length payload_and_rest)
                then
                  Some
                    (firstn len payload_and_rest,
                     skipn len payload_and_rest)
                else None
          | None => None
          end
        else None
      else None
  end.

Definition compact_payload_has_leading_zero (payload : list Z) : bool :=
  match payload with
  | 0%Z :: _ => true
  | _ => false
  end.

Definition rlp_decode_bytes32_compact_model
    (encoded : list Z) : option (N * list Z) :=
  match rlp_decode_string_model encoded with
  | Some (payload, rest) =>
      if Nat.ltb 32 (length payload)
      then None
      else if compact_payload_has_leading_zero payload
      then None
      else Some (word_of_compact_payload payload, rest)
  | None => None
  end.

(** The result-valued RLP models retain the concrete [DecodeError] returned by
    the C++ implementation.  The older option-valued models remain below this
    interface because the format proofs only need success or failure. *)
Definition rlp_decode_long_string_length_result
    (length_bytes : list Z)
    : Result.t nat DecodeError.DecodeError.t :=
  match length_bytes with
  | [] => Result.Err DecodeError.DecodeError.InputTooShort
  | first :: _ =>
      if (first =? 0)%Z
      then Result.Err DecodeError.DecodeError.LeadingZero
      else
        let length_N := word_of_be_bytes_from 0 length_bytes in
        if (N.size length_N <=? 64)%N
        then Result.Ok (N.to_nat length_N)
        else Result.Err DecodeError.DecodeError.Overflow
  end.

Fixpoint rlp_decode_string_result_model
    (encoded : list Z)
    : Result.t (list Z * list Z) DecodeError.DecodeError.t :=
  match encoded with
  | [] => Result.Err DecodeError.DecodeError.InputTooShort
  | header :: rest =>
      if (header <=? 127)%Z
      then Result.Ok ([header], rest)
      else if (128 <=? header)%Z && (header <=? 183)%Z
      then
        let len := Z.to_nat (header - 128)%Z in
        if rlp_short_string_is_noncanonical len rest
        then Result.Err DecodeError.DecodeError.TypeUnexpected
        else
          if Nat.leb len (length rest)
          then Result.Ok (firstn len rest, skipn len rest)
          else Result.Err DecodeError.DecodeError.InputTooShort
      else if (184 <=? header)%Z && (header <=? 191)%Z
      then
        let length_of_length := Z.to_nat (header - 183)%Z in
        if Nat.ltb length_of_length (length rest)
        then
          match rlp_decode_long_string_length_result
                  (firstn length_of_length rest) with
          | Result.Ok len =>
              if Nat.ltb len 56
              then Result.Err DecodeError.DecodeError.TypeUnexpected
              else
                let payload_and_rest := skipn length_of_length rest in
                if Nat.leb len (length payload_and_rest)
                then
                  Result.Ok
                    (firstn len payload_and_rest,
                     skipn len payload_and_rest)
                else Result.Err DecodeError.DecodeError.InputTooShort
          | Result.Err error => Result.Err error
          end
        else Result.Err DecodeError.DecodeError.InputTooShort
      else Result.Err DecodeError.DecodeError.TypeUnexpected
  end.

Definition rlp_decode_bytes32_compact_result_model
    (encoded : list Z)
    : Result.t (N * list Z) DecodeError.DecodeError.t :=
  match rlp_decode_string_result_model encoded with
  | Result.Ok (payload, rest) =>
      if Nat.ltb 32 (length payload)
      then Result.Err DecodeError.DecodeError.InputTooLong
      else if compact_payload_has_leading_zero payload
      then Result.Err DecodeError.DecodeError.NonCanonical
      else Result.Ok (word_of_compact_payload payload, rest)
  | Result.Err error => Result.Err error
  end.

Lemma rlp_decode_long_string_length_result_to_option length_bytes :
  Result.to_option
    (rlp_decode_long_string_length_result length_bytes) =
  rlp_decode_long_string_length length_bytes.
Proof.
  destruct length_bytes as [| first rest]; [reflexivity |].
  cbn [rlp_decode_long_string_length_result
    rlp_decode_long_string_length].
  destruct (first =? 0)%Z; [reflexivity |].
  destruct (N.size (word_of_be_bytes_from 0 (first :: rest)) <=? 64)%N;
    reflexivity.
Qed.

Lemma rlp_decode_string_result_to_option encoded :
  Result.to_option (rlp_decode_string_result_model encoded) =
  rlp_decode_string_model encoded.
Proof.
  destruct encoded as [| header rest]; [reflexivity |].
  cbn [rlp_decode_string_result_model rlp_decode_string_model].
  destruct (header <=? 127)%Z; [reflexivity |].
  destruct ((128 <=? header)%Z && (header <=? 183)%Z); [|].
  - destruct
      (rlp_short_string_is_noncanonical
         (Z.to_nat (header - 128)) rest); [reflexivity |].
    destruct (Z.to_nat (header - 128) <=? length rest)%nat;
      reflexivity.
  - destruct ((184 <=? header)%Z && (header <=? 191)%Z);
      [| reflexivity].
    destruct (Z.to_nat (header - 183) <? length rest)%nat;
      [| reflexivity].
    pose proof
      (rlp_decode_long_string_length_result_to_option
         (firstn (Z.to_nat (header - 183)) rest)) as Hlength.
    destruct
      (rlp_decode_long_string_length_result
         (firstn (Z.to_nat (header - 183)) rest)) as [len | error];
      cbn [Result.to_option] in Hlength.
    + rewrite <- Hlength.
      destruct (len <? 56)%nat; [reflexivity |].
      destruct
        (len <=?
          length (skipn (Z.to_nat (header - 183)) rest))%nat;
        reflexivity.
    + rewrite <- Hlength.
      reflexivity.
Qed.

Lemma rlp_decode_bytes32_compact_result_to_option encoded :
  Result.to_option (rlp_decode_bytes32_compact_result_model encoded) =
  rlp_decode_bytes32_compact_model encoded.
Proof.
  unfold rlp_decode_bytes32_compact_result_model,
    rlp_decode_bytes32_compact_model.
  pose proof (rlp_decode_string_result_to_option encoded) as Hdecode.
  destruct (rlp_decode_string_result_model encoded)
    as [[payload rest] | error]; cbn [Result.to_option] in Hdecode.
  - rewrite <- Hdecode.
    destruct (32 <? length payload)%nat; [reflexivity |].
    destruct (compact_payload_has_leading_zero payload); reflexivity.
  - rewrite <- Hdecode.
    reflexivity.
Qed.

(** The RLP string parser advances its input view exactly when metadata parsing
    and payload extraction succeed.  A caller can still reject the extracted
    payload afterwards, without restoring the view. *)
Definition rlp_decode_string_final_view
    (encoded : list Z) : list Z :=
  match rlp_decode_string_model encoded with
  | Some (_, rest) => rest
  | None => encoded
  end.

Lemma rlp_decode_bytes32_compact_final_view_success encoded value rest :
  rlp_decode_bytes32_compact_model encoded = Some (value, rest) ->
  rlp_decode_string_final_view encoded = rest.
Proof.
  unfold rlp_decode_bytes32_compact_model,
    rlp_decode_string_final_view.
  destruct (rlp_decode_string_model encoded) as [[payload after_payload] |];
    try discriminate.
  destruct (32 <? length payload)%nat; try discriminate.
  destruct (compact_payload_has_leading_zero payload); try discriminate.
  congruence.
Qed.

Fixpoint decode_slot_run
    (count : nat) (encoded : list Z) : option (list N * list Z) :=
  match count with
  | O => Some ([], encoded)
  | S count' =>
      match rlp_decode_string_model encoded with
      | None => None
      | Some (payload, after_slot) =>
          match decode_slot_run count' after_slot with
          | None => None
          | Some (slots, rest) =>
              Some (word_of_compact_payload payload :: slots, rest)
          end
      end
  end.

Fixpoint decode_storage_page_fuel
    (fuel slots_left : nat) (encoded : list Z) : option (list N) :=
  match fuel with
  | O => None
  | S fuel' =>
      if Nat.eqb slots_left O
      then Some []
      else
        match encoded with
        | [] => None
        | header :: rest =>
            if (header =? 0)%Z
            then Some (repeat 0%N slots_left)
            else if (header <? 128)%Z
            then
              let zeros := Z.to_nat header in
              if Nat.leb zeros slots_left
              then
                match decode_storage_page_fuel
                        fuel' (slots_left - zeros) rest with
                | None => None
                | Some suffix => Some (repeat 0%N zeros ++ suffix)
                end
              else None
            else
              let run := S (Z.to_nat (header - 128)%Z) in
              if Nat.leb run slots_left
              then
                match decode_slot_run run rest with
                | None => None
                | Some (slots, after_run) =>
                    match decode_storage_page_fuel
                            fuel' (slots_left - run) after_run with
                    | None => None
                    | Some suffix => Some (slots ++ suffix)
                    end
                end
              else None
        end
  end.

Definition decode_storage_page_permissive_model
    (bytes : list Z) : option (list N) :=
  decode_storage_page_fuel
    (S page_slot_count) page_slot_count bytes.

Definition decode_storage_page_update_slot
    (offset : nat) (value : N) (page : list N) : list N :=
  firstn offset page ++ value :: skipn (S offset) page.

Fixpoint decode_storage_page_data_run
    (count offset : nat) (page : list N) (encoded : list Z)
    : option (list N * list Z) :=
  match count with
  | O => Some (page, encoded)
  | S count' =>
      match rlp_decode_bytes32_compact_model encoded with
      | None => None
      | Some (value, rest) =>
          if N.eqb value 0
          then None
          else
            decode_storage_page_data_run
              count' (S offset)
              (decode_storage_page_update_slot offset value page)
              rest
      end
  end.

Fixpoint decode_storage_page_canonical_fuel
    (fuel offset : nat) (at_start prev_is_data_run : bool)
    (page : list N) (encoded : list Z) : option (list N) :=
  match fuel with
  | O => None
  | S fuel' =>
      if Nat.ltb offset page_slot_count
      then
        match encoded with
        | [] => None
        | header :: rest =>
            if (header =? 0)%Z
            then
              if negb at_start && negb prev_is_data_run
              then None
              else
                match rest with
                | [] => Some page
                | _ :: _ => None
                end
            else if (header <? 128)%Z
            then
              if negb at_start && negb prev_is_data_run
              then None
              else
                let zeros := Z.to_nat header in
                let offset' := offset + zeros in
                if Nat.leb page_slot_count offset'
                then None
                else
                  decode_storage_page_canonical_fuel
                    fuel' offset' false false page rest
            else
              if prev_is_data_run
              then None
              else
                let run := S (Z.to_nat (header - 128)%Z) in
                if Nat.ltb page_slot_count (offset + run)
                then None
                else
                  match decode_storage_page_data_run
                          run offset page rest with
                  | None => None
                  | Some (page', rest') =>
                      decode_storage_page_canonical_fuel
                        fuel' (offset + run) false true page' rest'
                  end
        end
      else
        match encoded with
        | [] => Some page
        | _ :: _ => None
        end
  end.

Definition decode_storage_page_canonical_model
    (bytes : list Z) : option (list N) :=
  decode_storage_page_canonical_fuel
    (S page_slot_count) 0 true false
    (repeat 0%N page_slot_count) bytes.

Definition decode_storage_page_model (bytes : list Z) : option (list N) :=
  decode_storage_page_canonical_model bytes.

(** Result-valued counterparts of the two canonical page-decoder loops.  They
    preserve the exact error selected by the corresponding C++ return path. *)
Fixpoint decode_storage_page_data_run_result
    (count offset : nat) (page : list N) (encoded : list Z)
    : Result.t (list N * list Z) DecodeError.DecodeError.t :=
  match count with
  | O => Result.Ok (page, encoded)
  | S count' =>
      match rlp_decode_bytes32_compact_result_model encoded with
      | Result.Err error => Result.Err error
      | Result.Ok (value, rest) =>
          if N.eqb value 0
          then Result.Err DecodeError.DecodeError.NonCanonical
          else
            decode_storage_page_data_run_result
              count' (S offset)
              (decode_storage_page_update_slot offset value page)
              rest
      end
  end.

Fixpoint decode_storage_page_canonical_fuel_result
    (fuel offset : nat) (at_start prev_is_data_run : bool)
    (page : list N) (encoded : list Z)
    : Result.t (list N) DecodeError.DecodeError.t :=
  match fuel with
  | O => Result.Err DecodeError.DecodeError.InputTooLong
  | S fuel' =>
      if Nat.ltb offset page_slot_count
      then
        match encoded with
        | [] => Result.Err DecodeError.DecodeError.InputTooShort
        | header :: rest =>
            if (header =? 0)%Z
            then
              if negb at_start && negb prev_is_data_run
              then Result.Err DecodeError.DecodeError.NonCanonical
              else
                match rest with
                | [] => Result.Ok page
                | _ :: _ => Result.Err DecodeError.DecodeError.InputTooLong
                end
            else if (header <? 128)%Z
            then
              if negb at_start && negb prev_is_data_run
              then Result.Err DecodeError.DecodeError.NonCanonical
              else
                let zeros := Z.to_nat header in
                let offset' := offset + zeros in
                if Nat.leb page_slot_count offset'
                then Result.Err DecodeError.DecodeError.NonCanonical
                else
                  decode_storage_page_canonical_fuel_result
                    fuel' offset' false false page rest
            else
              if prev_is_data_run
              then Result.Err DecodeError.DecodeError.NonCanonical
              else
                let run := S (Z.to_nat (header - 128)%Z) in
                if Nat.ltb page_slot_count (offset + run)
                then Result.Err DecodeError.DecodeError.InputTooLong
                else
                  match decode_storage_page_data_run_result
                          run offset page rest with
                  | Result.Err error => Result.Err error
                  | Result.Ok (page', rest') =>
                      decode_storage_page_canonical_fuel_result
                        fuel' (offset + run) false true page' rest'
                  end
        end
      else
        match encoded with
        | [] => Result.Ok page
        | _ :: _ => Result.Err DecodeError.DecodeError.InputTooLong
        end
  end.

(** Public decoder result: callers see only a page or a typed Monad RLP
    error.  Boost.Outcome's erased status-code representation is not part of
    this pure format model. *)
Definition decode_storage_page_result_model
    (bytes : list Z)
    : Result.t (list N) DecodeError.DecodeError.t :=
  decode_storage_page_canonical_fuel_result
    (S page_slot_count) 0 true false
    (repeat 0%N page_slot_count) bytes.

Lemma decode_storage_page_data_run_result_to_option
    count offset page encoded :
  Result.to_option
    (decode_storage_page_data_run_result count offset page encoded) =
  decode_storage_page_data_run count offset page encoded.
Proof.
  revert offset page encoded.
  induction count as [| count IH]; intros offset page encoded;
    [reflexivity |].
  cbn [decode_storage_page_data_run_result
    decode_storage_page_data_run].
  pose proof
    (rlp_decode_bytes32_compact_result_to_option encoded) as Hdecode.
  destruct (rlp_decode_bytes32_compact_result_model encoded)
    as [[value rest] | error]; cbn [Result.to_option] in Hdecode.
  - rewrite <- Hdecode.
    destruct (N.eqb value 0); [reflexivity |].
    apply IH.
  - rewrite <- Hdecode.
    reflexivity.
Qed.

Lemma decode_storage_page_canonical_fuel_result_to_option
    fuel offset at_start prev_is_data_run page encoded :
  Result.to_option
    (decode_storage_page_canonical_fuel_result
       fuel offset at_start prev_is_data_run page encoded) =
  decode_storage_page_canonical_fuel
    fuel offset at_start prev_is_data_run page encoded.
Proof.
  revert offset at_start prev_is_data_run page encoded.
  induction fuel as [| fuel IH];
    intros offset at_start prev_is_data_run page encoded;
    [reflexivity |].
  cbn [decode_storage_page_canonical_fuel_result
    decode_storage_page_canonical_fuel].
  destruct (offset <? page_slot_count)%nat; [|].
  - destruct encoded as [| header rest]; [reflexivity |].
    destruct (header =? 0)%Z.
    + destruct (negb at_start && negb prev_is_data_run);
        [reflexivity |].
      destruct rest; reflexivity.
    + destruct (header <? 128)%Z.
      * destruct (negb at_start && negb prev_is_data_run);
          [reflexivity |].
        destruct (page_slot_count <=? offset + Z.to_nat header)%nat;
          [reflexivity |].
        apply IH.
      * destruct prev_is_data_run; [reflexivity |].
        destruct
          (page_slot_count <?
             offset + S (Z.to_nat (header - 128)))%nat;
          [reflexivity |].
        pose proof
          (decode_storage_page_data_run_result_to_option
             (S (Z.to_nat (header - 128))) offset page rest) as Hrun.
        destruct
          (decode_storage_page_data_run_result
             (S (Z.to_nat (header - 128))) offset page rest)
          as [[page' rest'] | error]; cbn [Result.to_option] in Hrun.
        -- rewrite <- Hrun.
           apply IH.
        -- rewrite <- Hrun.
           reflexivity.
  - destruct encoded; reflexivity.
Qed.

Lemma decode_storage_page_result_to_option bytes :
  Result.to_option (decode_storage_page_result_model bytes) =
  decode_storage_page_model bytes.
Proof.
  apply decode_storage_page_canonical_fuel_result_to_option.
Qed.

Definition list_Z_eq_dec :
  forall lhs rhs : list Z, {lhs = rhs} + {lhs <> rhs}.
Proof.
  decide equality.
  apply Z.eq_dec.
Defined.

Definition decode_storage_page_parse_reencode_model
    (bytes : list Z) : option (list N) :=
  match decode_storage_page_permissive_model bytes with
  | Some page =>
      if list_Z_eq_dec (encode_storage_page_model page) bytes
      then Some page
      else None
  | None => None
  end.

Lemma normalize_slot_model_zero :
  normalize_slot_model 0 = 0%N.
Proof.
  unfold normalize_slot_model, word_of_compact_payload,
    compact_bytes32_payload, be_bytes.
  rewrite z_to_bytes._Z_to_bytes_0_value.
  cbn [map drop_leading_zeroes].
  rewrite z_to_bytes._Z_from_bytes_nil.
  reflexivity.
Qed.

Lemma be_bytes_length len word :
  length (be_bytes len word) = len.
Proof.
  unfold be_bytes.
  rewrite map_length.
  apply z_to_bytes._Z_to_bytes_length.
Qed.

Lemma drop_leading_zeroes_length_le bytes :
  length (drop_leading_zeroes bytes) <= length bytes.
Proof.
  induction bytes as [| byte rest IH]; simpl; [lia |].
  destruct byte; simpl; lia.
Qed.

Lemma compact_bytes32_payload_length word :
  length (compact_bytes32_payload word) <= 32.
Proof.
  unfold compact_bytes32_payload.
  rewrite <- (be_bytes_length 32 word) at 2.
  apply drop_leading_zeroes_length_le.
Qed.

Lemma word_byte_range shift word :
  (0 <= word_byte shift word <= 255)%Z.
Proof.
  unfold word_byte.
  pose proof (N.land_le_r (N.shiftr word shift) 255) as Hbound.
  lia.
Qed.

Lemma be_bytes_range len word :
  Forall (fun byte => (0 <= byte <= 255)%Z) (be_bytes len word).
Proof.
  unfold be_bytes.
  rewrite Forall_map.
  eapply Forall_impl
    with (P := fun byte : N => (byte < 256)%N).
  {
    intros byte Hbyte.
    lia.
  }
  apply z_to_bytes._Z_to_bytes_range.
Qed.

Lemma drop_leading_zeroes_Forall (P : Z -> Prop) bytes :
  Forall P bytes ->
  Forall P (drop_leading_zeroes bytes).
Proof.
  induction bytes as [| byte rest IH]; simpl; intro Hforall; [constructor |].
  inversion Hforall as [| ? ? Hbyte Hrest]; subst.
  destruct byte; auto.
Qed.

Lemma compact_bytes32_payload_range word :
  Forall (fun byte => (0 <= byte <= 255)%Z) (compact_bytes32_payload word).
Proof.
  unfold compact_bytes32_payload.
  apply drop_leading_zeroes_Forall.
  apply be_bytes_range.
Qed.

Lemma rlp_decode_string_encode_app payload rest :
  length payload <= 32 ->
  Forall (fun byte => (0 <= byte <= 255)%Z) payload ->
  rlp_decode_string_model (rlp_encode_short_string payload ++ rest) =
  Some (payload, rest).
Proof.
  intros Hlen Hrange.
  destruct payload as [| byte [| byte2 tail]].
  { reflexivity. }
  { simpl in *.
    inversion Hrange as [| ? ? Hbyte _]; subst.
    destruct ((0 <=? byte)%Z && (byte <=? 127)%Z) eqn:Hsmall.
    { apply andb_true_iff in Hsmall as [_ Hle].
      apply Z.leb_le in Hle.
      simpl.
      replace (byte <=? 127)%Z with true by
        (symmetry; apply Z.leb_le; exact Hle).
      reflexivity. }
    change (128 + Z.of_nat 1)%Z with 129%Z.
    assert (Hlarge : (byte <? 128)%Z = false).
    { apply Z.ltb_ge.
      apply andb_false_iff in Hsmall as [Hnegative | Hlarge].
      { apply Z.leb_gt in Hnegative. lia. }
      { apply Z.leb_gt in Hlarge. lia. } }
    change
      (rlp_decode_string_model (129%Z :: byte :: rest) =
       Some ([byte], rest)).
    cbn [rlp_decode_string_model].
    unfold rlp_short_string_is_noncanonical.
    cbn.
    rewrite Hlarge.
    reflexivity. }
  simpl in *.
  replace
    (128 + Z.of_nat (S (S (length tail))) <=? 127)%Z
    with false by (symmetry; apply Z.leb_gt; lia).
  replace
    (128 <=? 128 + Z.of_nat (S (S (length tail))))%Z
    with true by (symmetry; apply Z.leb_le; lia).
  replace
    (128 + Z.of_nat (S (S (length tail))) <=? 183)%Z
    with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.to_nat (128 + Z.of_nat (S (S (length tail))) - 128)%Z)
    with (S (S (length tail))) by lia.
  replace
    (S (S (length tail)) <=? S (S (length (tail ++ rest))))
    with true by
      (symmetry; apply Nat.leb_le; rewrite app_length; lia).
  simpl.
  change (byte :: byte2 :: tail ++ rest)
    with ((byte :: byte2 :: tail) ++ rest).
  rewrite firstn_app, skipn_app.
  rewrite Nat.sub_diag.
  simpl.
  rewrite firstn_all, skipn_all2 by lia.
  rewrite app_nil_r, skipn_0.
  reflexivity.
Qed.

Lemma rlp_decode_encode_slot_app slot rest :
  rlp_decode_string_model (encode_slot_model slot ++ rest) =
  Some (compact_bytes32_payload slot, rest).
Proof.
  unfold encode_slot_model.
  apply rlp_decode_string_encode_app.
  { apply compact_bytes32_payload_length. }
  { apply compact_bytes32_payload_range. }
Qed.

Lemma drop_leading_zeroes_no_leading_zero bytes :
  compact_payload_has_leading_zero (drop_leading_zeroes bytes) = false.
Proof.
  induction bytes as [| byte rest IH]; simpl; [reflexivity |].
  destruct byte; simpl; [exact IH | reflexivity | reflexivity].
Qed.

Lemma compact_bytes32_payload_no_leading_zero word :
  compact_payload_has_leading_zero (compact_bytes32_payload word) = false.
Proof.
  unfold compact_bytes32_payload.
  apply drop_leading_zeroes_no_leading_zero.
Qed.

Lemma rlp_decode_bytes32_compact_encode_app slot rest :
  rlp_decode_bytes32_compact_model (encode_slot_model slot ++ rest) =
  Some (normalize_slot_model slot, rest).
Proof.
  unfold rlp_decode_bytes32_compact_model, normalize_slot_model.
  rewrite rlp_decode_encode_slot_app.
  replace (32 <? length (compact_bytes32_payload slot))%nat with false.
  2: {
    symmetry.
    apply Nat.ltb_ge.
    apply compact_bytes32_payload_length.
  }
  rewrite compact_bytes32_payload_no_leading_zero.
  reflexivity.
Qed.

Lemma decode_slot_run_encode_app slots rest :
  decode_slot_run (length slots)
    (concat (map encode_slot_model slots) ++ rest) =
  Some (normalize_storage_page_model slots, rest).
Proof.
  induction slots as [| slot slots IH].
  { reflexivity. }
  cbn [length map concat decode_slot_run normalize_storage_page_model].
  rewrite <- app_assoc.
  rewrite (rlp_decode_encode_slot_app
             slot (concat (map encode_slot_model slots) ++ rest)).
  rewrite IH.
  reflexivity.
Qed.

Fixpoint decode_storage_page_update_slots
    (offset : nat) (values page : list N) : list N :=
  match values with
  | [] => page
  | value :: rest =>
      decode_storage_page_update_slots
        (S offset) rest
        (decode_storage_page_update_slot offset value page)
  end.

Lemma decode_storage_page_update_slot_prefix
    prefix old suffix value :
  decode_storage_page_update_slot
    (length prefix) value (prefix ++ old :: suffix) =
  prefix ++ value :: suffix.
Proof.
  unfold decode_storage_page_update_slot.
  revert old suffix value.
  induction prefix as [| head prefix IH]; intros old suffix value.
  { reflexivity. }
  simpl.
  f_equal.
  apply IH.
Qed.

Lemma decode_storage_page_update_slots_prefix prefix values suffix :
  decode_storage_page_update_slots
    (length prefix) values
    (prefix ++ repeat 0%N (length values) ++ suffix) =
  prefix ++ values ++ suffix.
Proof.
  revert prefix suffix.
  induction values as [| value values IH]; intros prefix suffix.
  { reflexivity. }
  cbn [length repeat decode_storage_page_update_slots].
  change (prefix ++ (0%N :: repeat 0%N (length values)) ++ suffix)
    with (prefix ++ 0%N :: repeat 0%N (length values) ++ suffix).
  rewrite decode_storage_page_update_slot_prefix.
  replace (prefix ++ value :: repeat 0%N (length values) ++ suffix)
    with ((prefix ++ [value]) ++ repeat 0%N (length values) ++ suffix)
    by (rewrite <- app_assoc; reflexivity).
  replace (prefix ++ (value :: values) ++ suffix)
    with ((prefix ++ [value]) ++ values ++ suffix)
    by (rewrite <- app_assoc; reflexivity).
  rewrite <- (IH (prefix ++ [value]) suffix).
  rewrite app_length.
  simpl.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

Lemma decode_storage_page_data_run_encode_app slots offset page rest :
  slots_nonzero (normalize_storage_page_model slots) ->
  decode_storage_page_data_run (length slots) offset page
    (concat (map encode_slot_model slots) ++ rest) =
  Some
    (decode_storage_page_update_slots
       offset (normalize_storage_page_model slots) page, rest).
Proof.
  revert offset page rest.
  induction slots as [| slot slots IH]; intros offset page rest Hnonzero.
  { reflexivity. }
  cbn [length map concat normalize_storage_page_model
       decode_storage_page_data_run decode_storage_page_update_slots].
  rewrite <- app_assoc.
  rewrite rlp_decode_bytes32_compact_encode_app.
  inversion Hnonzero as [| ? ? Hslot Hrest]; subst.
  destruct (normalize_slot_model slot =? 0)%N eqn:Hzero.
  { apply N.eqb_eq in Hzero. contradiction. }
  apply IH.
  exact Hrest.
Qed.

Lemma count_zero_prefix_le limit page :
  count_zero_prefix limit page <= length page.
Proof.
  revert page.
  induction limit as [| limit IH]; intros page; simpl; [lia |].
  destruct page as [| slot rest]; simpl; [lia |].
  destruct (N.eq_dec slot 0); simpl; [specialize (IH rest); lia | lia].
Qed.

Lemma count_nonzero_prefix_le limit page :
  count_nonzero_prefix limit page <= length page.
Proof.
  revert page.
  induction limit as [| limit IH]; intros page; simpl; [lia |].
  destruct page as [| slot rest]; simpl; [lia |].
  destruct (N.eq_dec slot 0); simpl; [lia | specialize (IH rest); lia].
Qed.

Lemma count_zero_prefix_pos limit rest :
  count_zero_prefix (S limit) (0%N :: rest) > 0.
Proof.
  simpl.
  destruct (N.eq_dec 0 0); lia.
Qed.

Lemma count_nonzero_prefix_pos limit slot rest :
  slot <> 0%N ->
  count_nonzero_prefix (S limit) (slot :: rest) > 0.
Proof.
  intro Hslot.
  simpl.
  destruct (N.eq_dec slot 0); lia.
Qed.

Lemma count_zero_prefix_all_zero limit page :
  count_zero_prefix limit page = length page ->
  normalize_storage_page_model page = repeat 0%N (length page).
Proof.
  revert page.
  induction limit as [| limit IH]; intros page Hcount.
  { destruct page; simpl in *; [reflexivity | discriminate]. }
  destruct page as [| slot rest]; simpl in *; [reflexivity |].
  destruct (N.eq_dec slot 0) as [Hslot | Hslot]; [subst | discriminate].
  inversion Hcount as [Hrest].
  rewrite normalize_slot_model_zero.
  rewrite (IH rest Hrest).
  rewrite Hrest.
  reflexivity.
Qed.

Lemma normalize_storage_page_model_app lhs rhs :
  normalize_storage_page_model (lhs ++ rhs) =
  normalize_storage_page_model lhs ++ normalize_storage_page_model rhs.
Proof.
  unfold normalize_storage_page_model.
  apply map_app.
Qed.

Lemma normalize_storage_page_model_firstn_skipn n page :
  normalize_storage_page_model page =
  normalize_storage_page_model (firstn n page) ++
  normalize_storage_page_model (skipn n page).
Proof.
  rewrite <- normalize_storage_page_model_app.
  now rewrite firstn_skipn.
Qed.

Lemma count_zero_prefix_firstn_normalized limit page :
  normalize_storage_page_model
    (firstn (count_zero_prefix limit page) page) =
  repeat 0%N (count_zero_prefix limit page).
Proof.
  revert page.
  induction limit as [| limit IH]; intros page; simpl.
  { reflexivity. }
  destruct page as [| slot rest]; simpl; [reflexivity |].
  destruct (N.eq_dec slot 0) as [Hslot | Hslot].
  { subst slot.
    simpl.
    rewrite normalize_slot_model_zero.
    rewrite IH.
    reflexivity. }
  reflexivity.
Qed.

Lemma normalize_storage_page_model_zero_prefix_split limit page :
  normalize_storage_page_model page =
  repeat 0%N (count_zero_prefix limit page) ++
  normalize_storage_page_model (skipn (count_zero_prefix limit page) page).
Proof.
  rewrite normalize_storage_page_model_firstn_skipn
    with (n := count_zero_prefix limit page).
  rewrite count_zero_prefix_firstn_normalized.
  reflexivity.
Qed.

Lemma firstn_one_skipn_nth {A : Type} (xs : list A) n default :
  (n < length xs)%nat ->
  firstn 1 (skipn n xs) = [nth n xs default].
Proof.
  revert xs.
  induction n as [| n IH]; intros [| x xs] Hlt; simpl in *; try lia.
  { reflexivity. }
  apply IH.
  lia.
Qed.

Lemma nth_skipn_add {A : Type} (xs : list A) m n default :
  nth n (skipn m xs) default = nth (m + n) xs default.
Proof.
  revert xs n.
  induction m as [| m IH]; intros xs n.
  { reflexivity. }
  destruct xs as [| x xs].
  { destruct n; reflexivity. }
  simpl.
  apply IH.
Qed.

Lemma concat_map_firstn_succ {A B : Type}
    (f : A -> list B) (xs : list A) n default :
  (n < length xs)%nat ->
  concat (map f (firstn (S n) xs)) =
  concat (map f (firstn n xs)) ++ f (nth n xs default).
Proof.
  revert xs.
  induction n as [| n IH]; intros [| x xs] Hlt; simpl in *; try lia.
  { rewrite app_nil_r. reflexivity. }
  rewrite IH by lia.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma firstn_zero_prefix_succ page n :
  firstn n page = repeat 0%N n ->
  (n < length page)%nat ->
  nth n page 0%N = 0%N ->
  firstn (S n) page = repeat 0%N (S n).
Proof.
  revert page.
  induction n as [| n IH]; intros [| slot rest] Hprefix Hlt Hnth;
    simpl in *; try lia.
  { now rewrite Hnth. }
  inversion Hprefix as [[Hslot Hrest]].
  f_equal.
  rewrite Hrest.
  apply IH; [exact Hrest | lia | exact Hnth].
Qed.

Lemma firstn_nonzero_prefix_succ page n :
  slots_nonzero (firstn n page) ->
  (n < length page)%nat ->
  nth n page 0%N <> 0%N ->
  slots_nonzero (firstn (S n) page).
Proof.
  revert page.
  induction n as [| n IH]; intros [| slot rest] Hprefix Hlt Hnth;
    simpl in *; try lia.
  { constructor; [exact Hnth | constructor]. }
  inversion Hprefix as [| ? ? Hslot Hrest]; subst.
  constructor.
  { exact Hslot. }
  apply IH; [exact Hrest | lia | exact Hnth].
Qed.

Lemma count_zero_prefix_exact page n :
  (n <= length page)%nat ->
  firstn n page = repeat 0%N n ->
  (n = length page \/ nth n page 0%N <> 0%N) ->
  count_zero_prefix (length page) page = n.
Proof.
  revert n.
  induction page as [| slot rest IH]; intros n Hle Hprefix Hstop.
  { destruct n; simpl in *; [reflexivity | lia]. }
  destruct n as [| n].
  {
    simpl.
    destruct Hstop as [Hlen | Hnonzero].
    { discriminate. }
    destruct (N.eq_dec slot 0); [contradiction | reflexivity].
  }
  simpl in Hprefix.
  inversion Hprefix as [[Hslot Hrest]].
  subst slot.
  simpl.
  destruct (N.eq_dec 0 0) as [_ | Hneq]; [| contradiction].
  f_equal.
  apply IH.
  { simpl in Hle; lia. }
  { exact Hrest. }
  destruct Hstop as [Hlen | Hnonzero].
  { left. simpl in Hlen; lia. }
  right.
  exact Hnonzero.
Qed.

Lemma count_nonzero_prefix_exact limit page n :
  (n <= length page)%nat ->
  (n <= limit)%nat ->
  slots_nonzero (firstn n page) ->
  (n = length page \/ n = limit \/ nth n page 0%N = 0%N) ->
  count_nonzero_prefix limit page = n.
Proof.
  revert page n.
  induction limit as [| limit IH]; intros page n Hpage Hlimit Hprefix Hstop.
  {
    destruct n; [reflexivity | lia].
  }
  destruct page as [| slot rest].
  { destruct n; simpl in *; [reflexivity | lia]. }
  destruct n as [| n].
  {
    simpl.
    destruct Hstop as [Hlen | [Hlimit_eq | Hzero]].
    { discriminate. }
    { discriminate. }
    destruct (N.eq_dec slot 0); [reflexivity | contradiction].
  }
  simpl in Hprefix.
  inversion Hprefix as [| ? ? Hslot Hrest]; subst.
  simpl.
  destruct (N.eq_dec slot 0) as [Hzero | Hnonzero].
  { contradiction. }
  f_equal.
  apply IH.
  { simpl in Hpage. lia. }
  { simpl in Hlimit. lia. }
  { exact Hrest. }
  destruct Hstop as [Hlen | [Hlimit_eq | Hzero]].
  { left. simpl in Hlen. lia. }
  { right. left. simpl in Hlimit_eq. lia. }
  { right. right. exact Hzero. }
Qed.

Lemma count_zero_prefix_limit_irrel limit page :
  (length page <= limit)%nat ->
  count_zero_prefix limit page =
  count_zero_prefix (length page) page.
Proof.
  revert page.
  induction limit as [| limit IH]; intros page Hle.
  { destruct page; simpl in *; [reflexivity | lia]. }
  destruct page as [| slot rest]; simpl; [reflexivity |].
  destruct (N.eq_dec slot 0) as [Hslot | Hslot]; [| reflexivity].
  f_equal.
  apply IH.
  simpl in Hle.
  lia.
Qed.

Local Opaque page_slot_count.

Lemma encode_storage_page_fuel_irrel fuel fuel' page :
  (length page <= fuel)%nat ->
  (length page <= fuel')%nat ->
  encode_storage_page_fuel fuel page =
  encode_storage_page_fuel fuel' page.
Proof.
  intros Hfuel Hfuel'.
  remember (length page) as len eqn:Hlen.
  revert page fuel fuel' Hfuel Hfuel' Hlen.
  refine
    (well_founded_induction
       lt_wf
       (fun len =>
          forall page fuel fuel',
            (len <= fuel)%nat ->
            (len <= fuel')%nat ->
            len = length page ->
            encode_storage_page_fuel fuel page =
            encode_storage_page_fuel fuel' page)
       _ len).
  intros measure IH page fuel fuel' Hfuel Hfuel' Hlen.
  destruct page as [| slot rest].
  { destruct fuel, fuel'; reflexivity. }
  destruct fuel as [| fuel], fuel' as [| fuel']; simpl in *; try lia.
  destruct (N.eq_dec slot 0) as [Hslot | Hslot].
  {
    subst slot.
    rewrite (count_zero_prefix_limit_irrel fuel rest) by lia.
    rewrite (count_zero_prefix_limit_irrel fuel' rest) by lia.
    set (zeros := S (count_zero_prefix (length rest) rest)).
    destruct (Nat.eqb zeros (S (length rest))) eqn:Hall; [reflexivity |].
    f_equal.
    apply IH with (y := length (skipn zeros (0%N :: rest))); try reflexivity.
    {
      assert (Hzero_pos : (0 < zeros)%nat).
      { subst zeros; apply count_zero_prefix_pos. }
      rewrite skipn_length.
      simpl.
      lia.
    }
    all: rewrite skipn_length; simpl; lia.
  }
  set (run := count_nonzero_prefix page_slot_count (slot :: rest)).
  assert (Hrun_pos : (0 < run)%nat).
  {
    subst run.
    apply count_nonzero_prefix_pos.
    exact Hslot.
  }
  change (count_nonzero_prefix page_slot_count (slot :: rest)) with run.
  replace
    (encode_storage_page_fuel fuel (skipn run (slot :: rest)))
    with
    (encode_storage_page_fuel fuel' (skipn run (slot :: rest))).
  { reflexivity. }
  apply IH with (y := length (skipn run (slot :: rest))); try reflexivity.
  {
    rewrite skipn_length.
    simpl.
    lia.
  }
  all: rewrite skipn_length; simpl; lia.
Qed.

Local Transparent page_slot_count.

Lemma encode_storage_page_model_zero_prefix page n :
  (length page <= page_slot_count)%nat ->
  (0 < n < length page)%nat ->
  firstn n page = repeat 0%N n ->
  nth n page 0%N <> 0%N ->
  encode_storage_page_model page =
  Z.of_nat n :: encode_storage_page_model (skipn n page).
Proof.
  intros Hslots [Hpos Hlt] Hprefix Hstop.
  assert (Hcount : count_zero_prefix (length page) page = n).
  {
    apply count_zero_prefix_exact.
    { lia. }
    { exact Hprefix. }
    { right. exact Hstop. }
  }
  unfold encode_storage_page_model at 1.
  destruct page as [| slot rest].
  { simpl in Hlt. lia. }
  cbn [length encode_storage_page_fuel].
  assert (Hslot : slot = 0%N).
  {
    destruct n as [| n]; [lia |].
    simpl in Hprefix.
    injection Hprefix as Hhead _.
    exact Hhead.
  }
  subst slot.
  destruct (N.eq_dec 0 0) as [_ | Hneq]; [| contradiction].
  change (count_zero_prefix (S (length rest)) (0%N :: rest))
    with (count_zero_prefix (length (0%N :: rest)) (0%N :: rest)).
  rewrite Hcount.
  replace (n =? S (length rest)) with false by
    (symmetry; apply Nat.eqb_neq; simpl in Hlt; lia).
  f_equal.
  unfold encode_storage_page_model.
  apply encode_storage_page_fuel_irrel.
  { rewrite skipn_length. simpl. lia. }
  { rewrite skipn_length. simpl. lia. }
Qed.

Lemma encode_storage_page_model_all_zero page :
  (0 < length page)%nat ->
  firstn (length page) page = repeat 0%N (length page) ->
  encode_storage_page_model page = [0%Z].
Proof.
  intros Hnonempty Hprefix.
  assert
    (Hcount :
       count_zero_prefix (length page) page = length page).
  {
    apply count_zero_prefix_exact.
    { lia. }
    { exact Hprefix. }
    { left. reflexivity. }
  }
  unfold encode_storage_page_model.
  destruct page as [| slot rest].
  { simpl in Hnonempty. lia. }
  cbn [length encode_storage_page_fuel].
  assert (Hslot : slot = 0%N).
  {
    simpl in Hprefix.
    injection Hprefix as Hslot _.
    exact Hslot.
  }
  subst slot.
  destruct (N.eq_dec 0 0) as [_ | Hneq]; [| contradiction].
  change (count_zero_prefix (S (length rest)) (0%N :: rest))
    with (count_zero_prefix (length (0%N :: rest)) (0%N :: rest)).
  rewrite Hcount.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma encode_storage_page_model_nonzero_prefix page n :
  (length page <= page_slot_count)%nat ->
  (0 < n <= page_slot_count)%nat ->
  (n <= length page)%nat ->
  slots_nonzero (firstn n page) ->
  (n = length page \/ n = page_slot_count \/ nth n page 0%N = 0%N) ->
  encode_storage_page_model page =
  (128 + Z.of_nat (n - 1))%Z ::
    concat (map encode_slot_model (firstn n page)) ++
    encode_storage_page_model (skipn n page).
Proof.
  intros Hslots [Hpos Hnslots] Hnpage Hprefix Hstop.
  assert
    (Hcount :
       count_nonzero_prefix page_slot_count page = n).
  {
    apply count_nonzero_prefix_exact.
    { exact Hnpage. }
    { exact Hnslots. }
    { exact Hprefix. }
    { exact Hstop. }
  }
  unfold encode_storage_page_model at 1.
  destruct page as [| slot rest].
  { simpl in Hnpage. lia. }
  cbn [length encode_storage_page_fuel].
  assert (Hslot_nonzero : slot <> 0%N).
  {
    destruct n as [| n]; [lia |].
    simpl in Hprefix.
    inversion Hprefix as [| ? ? Hhead _]; subst.
    exact Hhead.
  }
  destruct (N.eq_dec slot 0) as [Hzero | Hnonzero].
  { contradiction. }
  change (count_nonzero_prefix page_slot_count (slot :: rest))
    with (count_nonzero_prefix page_slot_count (slot :: rest)).
  rewrite Hcount.
  f_equal.
  f_equal.
  unfold encode_storage_page_model.
  apply encode_storage_page_fuel_irrel.
  { rewrite skipn_length. simpl. lia. }
  { rewrite skipn_length. simpl. lia. }
Qed.

Lemma decode_encode_storage_page_fuel_normalized fuel page :
  length page <= fuel ->
  length page <= page_slot_count ->
  decode_storage_page_fuel (S fuel) (length page)
    (encode_storage_page_fuel fuel page) =
  Some (normalize_storage_page_model page).
Proof.
  revert page.
  induction fuel as [| fuel IH]; intros page Hfuel Hslots.
  { destruct page; simpl in *; [reflexivity | lia]. }
  destruct page as [| slot rest].
  { reflexivity. }
  cbn [length] in Hfuel, Hslots |- *.
  destruct (N.eq_dec slot 0) as [Hslot | Hslot].
    { subst slot.
      set (zeros := count_zero_prefix (S fuel) (0%N :: rest)).
      assert (Hzero_le : zeros <= length (0%N :: rest)).
      { subst zeros; apply count_zero_prefix_le. }
      assert (Hzero_pos : zeros > 0).
      { subst zeros; apply count_zero_prefix_pos. }
      destruct (Nat.eqb_spec zeros (length (0%N :: rest))) as [Hall | Hnot_all].
      { subst zeros.
        simpl in Hall.
        destruct (N.eq_dec 0 0); [| contradiction].
        apply Nat.succ_inj in Hall.
        simpl.
        rewrite Hall.
        rewrite Nat.eqb_refl.
        simpl.
        rewrite normalize_slot_model_zero.
        now rewrite (count_zero_prefix_all_zero fuel rest Hall). }
    subst zeros.
    simpl in Hnot_all, Hzero_le, Hzero_pos.
    simpl in Hslots, Hfuel.
    destruct (N.eq_dec 0 0); [| contradiction].
    set (tail_zeros := count_zero_prefix fuel rest) in *.
    assert (Htail_not_all : tail_zeros <> length rest).
    { intro Heq.
      apply Hnot_all.
      now f_equal. }
    simpl.
    change (count_zero_prefix fuel rest) with tail_zeros.
    replace (tail_zeros =? length rest) with false by
      (symmetry; apply Nat.eqb_neq; exact Htail_not_all).
    assert (Hzero_lt_slots : (Z.of_nat (S tail_zeros) <? 128)%Z = true).
    { apply Z.ltb_lt.
      change 128%Z with (Z.of_nat page_slot_count).
      apply Nat2Z.inj_lt.
      change page_slot_count with 128 in Hslots |- *.
      lia. }
    assert (Hzero_nonzero : (Z.of_nat (S tail_zeros) =? 0)%Z = false).
    { apply Z.eqb_neq; lia. }
    rewrite Hzero_nonzero, Hzero_lt_slots.
    replace (Z.to_nat (Z.of_nat (S tail_zeros))) with (S tail_zeros) by lia.
    replace (S tail_zeros <=? S (length rest)) with true by
      (symmetry; apply Nat.leb_le; lia).
    replace (S (length rest) - S tail_zeros)
      with (length (skipn tail_zeros rest)) by
      (rewrite length_skipn; lia).
    change
      (match
         decode_storage_page_fuel
           (S fuel) (length (skipn tail_zeros rest))
           (encode_storage_page_fuel fuel (skipn tail_zeros rest))
       with
       | Some suffix =>
           Some (repeat 0%N (S tail_zeros) ++ suffix)
       | None => None
       end =
       Some
         (normalize_slot_model 0 :: normalize_storage_page_model rest)).
    rewrite IH by (rewrite length_skipn; lia).
    cbn [repeat].
    rewrite normalize_slot_model_zero.
    unfold tail_zeros.
    rewrite (normalize_storage_page_model_zero_prefix_split fuel rest).
    reflexivity. }
  set (run := count_nonzero_prefix page_slot_count (slot :: rest)).
  assert (Hrun_le : run <= length (slot :: rest)).
  { subst run; apply count_nonzero_prefix_le. }
  assert (Hrun_pos : run > 0).
  { subst run.
    apply count_nonzero_prefix_pos.
    exact Hslot. }
  assert (Hrun_slots : run <= page_slot_count).
  { simpl in Hrun_le.
    lia. }
  cbn [encode_storage_page_fuel decode_storage_page_fuel].
  destruct (N.eq_dec slot 0) as [Hzero | Hnonzero]; [contradiction |].
  change (count_nonzero_prefix page_slot_count (slot :: rest))
    with run.
  assert (Hheader_nonzero : (128 + Z.of_nat (run - 1) =? 0)%Z = false).
  { apply Z.eqb_neq.
    lia. }
  assert (Hheader_large : (128 + Z.of_nat (run - 1) <? 128)%Z = false).
  { apply Z.ltb_ge.
    lia. }
  rewrite Hheader_nonzero, Hheader_large.
  replace (Z.to_nat (128 + Z.of_nat (run - 1) - 128)%Z)
    with (run - 1) by lia.
  replace (S (run - 1)) with run by lia.
  replace (S (length rest) =? 0) with false by reflexivity.
  replace (run <=? S (length rest)) with true by
    (symmetry; apply Nat.leb_le; simpl in Hrun_le; lia).
  assert (Hfirstn_run : length (firstn run (slot :: rest)) = run).
  { rewrite firstn_length.
    rewrite Nat.min_l; [reflexivity |].
    simpl in Hrun_le.
    exact Hrun_le. }
  rewrite <- Hfirstn_run at 1.
  rewrite decode_slot_run_encode_app.
  assert
    (Hskipn_run :
       S (length rest) - run = length (skipn run (slot :: rest))).
  { rewrite length_skipn.
    cbn [length].
    lia. }
  rewrite Hskipn_run.
  change
    (match
       decode_storage_page_fuel
         (S fuel) (length (skipn run (slot :: rest)))
         (encode_storage_page_fuel fuel (skipn run (slot :: rest)))
     with
     | Some suffix =>
         Some
           (normalize_storage_page_model (firstn run (slot :: rest)) ++
            suffix)
     | None => None
     end =
     Some (normalize_storage_page_model (slot :: rest))).
  rewrite IH by (rewrite length_skipn; cbn [length]; lia).
  rewrite <- normalize_storage_page_model_app.
  rewrite firstn_skipn.
  reflexivity.
Qed.

Theorem decode_encode_storage_page_permissive_model_normalized page :
  length page = page_slot_count ->
  decode_storage_page_permissive_model (encode_storage_page_model page) =
  Some (normalize_storage_page_model page).
Proof.
  intro Hlen.
  unfold decode_storage_page_permissive_model, encode_storage_page_model.
  rewrite <- Hlen.
  apply decode_encode_storage_page_fuel_normalized; lia.
Qed.

Definition canonical_storage_page (page : list N) : Prop :=
  normalize_storage_page_model page = page.

Definition decoder_state_ok
    (at_start prev_is_data_run : bool) (suffix : list N) : Prop :=
  match suffix with
  | [] => True
  | slot :: _ =>
      if N.eq_dec slot 0%N
      then at_start = true \/ prev_is_data_run = true
      else prev_is_data_run = false
  end.

Lemma normalize_storage_page_model_firstn n page :
  normalize_storage_page_model (firstn n page) =
  firstn n (normalize_storage_page_model page).
Proof.
  unfold normalize_storage_page_model.
  revert page.
  induction n as [| n IH]; intros [| slot rest]; simpl; auto.
  now rewrite IH.
Qed.

Lemma normalize_storage_page_model_skipn n page :
  normalize_storage_page_model (skipn n page) =
  skipn n (normalize_storage_page_model page).
Proof.
  unfold normalize_storage_page_model.
  revert page.
  induction n as [| n IH]; intros [| slot rest]; simpl; auto.
Qed.

Lemma canonical_storage_page_firstn n page :
  canonical_storage_page page ->
  canonical_storage_page (firstn n page).
Proof.
  unfold canonical_storage_page.
  intro Hcanonical.
  rewrite normalize_storage_page_model_firstn.
  now rewrite Hcanonical.
Qed.

Lemma canonical_storage_page_skipn n page :
  canonical_storage_page page ->
  canonical_storage_page (skipn n page).
Proof.
  unfold canonical_storage_page.
  intro Hcanonical.
  rewrite normalize_storage_page_model_skipn.
  now rewrite Hcanonical.
Qed.

Lemma count_nonzero_prefix_firstn_nonzero limit page :
  slots_nonzero (firstn (count_nonzero_prefix limit page) page).
Proof.
  revert page.
  induction limit as [| limit IH]; intros [| slot rest]; simpl.
  { constructor. }
  { constructor. }
  { constructor. }
  destruct (N.eq_dec slot 0%N) as [Hzero | Hnonzero].
  { constructor. }
  constructor; [exact Hnonzero | apply IH].
Qed.

Lemma count_zero_prefix_next_nonzero page :
  count_zero_prefix (length page) page < length page ->
  nth (count_zero_prefix (length page) page) page 0%N <> 0%N.
Proof.
  induction page as [| slot rest IH]; simpl; intro Hlt; [lia |].
  destruct (N.eq_dec slot 0%N) as [Hzero | Hnonzero].
  { subst slot.
    apply IH.
    lia. }
  exact Hnonzero.
Qed.

Lemma decoder_state_ok_after_zero_prefix fuel suffix :
  length suffix <= S fuel ->
  count_zero_prefix (S fuel) suffix < length suffix ->
  decoder_state_ok false false
    (skipn (count_zero_prefix (S fuel) suffix) suffix).
Proof.
  intros Hfuel Hnot_all.
  rewrite (count_zero_prefix_limit_irrel (S fuel) suffix) by lia.
  set (zeros := count_zero_prefix (length suffix) suffix) in *.
  assert (Hzeros_lt : (zeros < length suffix)%nat).
  { subst zeros.
    rewrite <- (count_zero_prefix_limit_irrel (S fuel) suffix) by lia.
    exact Hnot_all. }
  assert (Hnonempty : (0 < length (skipn zeros suffix))%nat).
  { rewrite skipn_length. lia. }
  destruct (skipn zeros suffix) as [| slot rest] eqn:Hskip.
  { simpl in Hnonempty. lia. }
  assert (Hslot : slot <> 0%N).
  {
    pose proof (count_zero_prefix_next_nonzero suffix Hzeros_lt) as Hnext.
    change slot with (nth 0 (slot :: rest) 0%N).
    rewrite <- Hskip.
    rewrite nth_skipn_add.
    replace (zeros + 0)%nat with zeros by lia.
    exact Hnext.
  }
  unfold decoder_state_ok.
  destruct (N.eq_dec slot 0%N); [contradiction | reflexivity].
Qed.

Lemma count_nonzero_prefix_next_zero limit (page : list N) :
  count_nonzero_prefix limit page < length page ->
  count_nonzero_prefix limit page < limit ->
  nth (count_nonzero_prefix limit page) page 0%N = 0%N.
Proof.
  revert page.
  induction limit as [| limit IH]; intros [| slot rest] Hpage Hlimit;
    simpl in *; try lia.
  destruct (N.eq_dec slot 0%N) as [Hzero | Hnonzero].
  { exact Hzero. }
  apply IH; lia.
Qed.

Lemma decoder_state_ok_after_nonzero_prefix
    (prefix suffix : list N) :
  length prefix + length suffix = page_slot_count ->
  let run := count_nonzero_prefix page_slot_count suffix in
  decoder_state_ok false true (skipn run suffix).
Proof.
  intros Hlen run.
  destruct (Nat.eq_dec run (length suffix)) as [Hrun_all | Hrun_not_all].
  {
    rewrite Hrun_all.
    rewrite skipn_all2 by lia.
    exact I.
  }
  assert (Hrun_lt_page : (run < length suffix)%nat).
  { subst run.
    pose proof (count_nonzero_prefix_le page_slot_count suffix).
    lia. }
  assert (Hrun_lt_limit : (run < page_slot_count)%nat).
  { lia. }
  assert (Hzero : nth run suffix 0%N = 0%N).
  {
    subst run.
    apply count_nonzero_prefix_next_zero; assumption.
  }
  assert (Hnonempty : (0 < length (skipn run suffix))%nat).
  { rewrite skipn_length. lia. }
  destruct (skipn run suffix) as [| slot rest] eqn:Hskip.
  { simpl in Hnonempty. lia. }
  assert (Hslot : slot = 0%N).
  {
    change slot with (nth 0 (slot :: rest) 0%N).
    rewrite <- Hskip.
    rewrite nth_skipn_add.
    replace (run + 0)%nat with run by lia.
    exact Hzero.
  }
  subst slot.
  unfold decoder_state_ok.
  destruct (N.eq_dec 0%N 0%N); [right; reflexivity | contradiction].
Qed.

Lemma canonical_storage_page_firstn_values n page :
  canonical_storage_page page ->
  normalize_storage_page_model (firstn n page) = firstn n page.
Proof.
  intro Hcanonical.
  unfold canonical_storage_page in Hcanonical.
  rewrite normalize_storage_page_model_firstn.
  now rewrite Hcanonical.
Qed.

Lemma canonical_storage_page_zero_prefix limit page :
  canonical_storage_page page ->
  firstn (count_zero_prefix limit page) page =
  repeat 0%N (count_zero_prefix limit page).
Proof.
  intro Hcanonical.
  pose proof (count_zero_prefix_firstn_normalized limit page) as Hzero.
  rewrite (canonical_storage_page_firstn_values
             (count_zero_prefix limit page) page Hcanonical) in Hzero.
  exact Hzero.
Qed.

Lemma repeat_app_split {A : Type} (x : A) lhs rhs :
  repeat x (lhs + rhs) = repeat x lhs ++ repeat x rhs.
Proof.
  induction lhs as [| lhs IH]; simpl; [reflexivity |].
  now rewrite IH.
Qed.

Lemma decode_storage_page_canonical_encode_cont fuel prefix suffix
    at_start prev_is_data_run :
  length suffix < fuel ->
  length prefix + length suffix = page_slot_count ->
  canonical_storage_page suffix ->
  decoder_state_ok at_start prev_is_data_run suffix ->
  decode_storage_page_canonical_fuel
    fuel (length prefix) at_start prev_is_data_run
    (prefix ++ repeat 0%N (length suffix))
    (encode_storage_page_fuel fuel suffix) =
  Some (prefix ++ suffix).
Proof.
  revert prefix suffix at_start prev_is_data_run.
  induction fuel as [| fuel IH];
    intros prefix suffix at_start prev_is_data_run
      Hfuel Hlen Hcanonical Hstate.
  {
    simpl in Hfuel.
    lia.
  }
  destruct suffix as [| slot rest].
  {
    simpl in Hlen.
    cbn [encode_storage_page_fuel decode_storage_page_canonical_fuel].
    replace (length prefix <? page_slot_count)%nat with false by
      (symmetry; apply Nat.ltb_ge; lia).
    rewrite app_nil_r.
    rewrite app_nil_r.
    reflexivity.
  }
  cbn [length] in Hfuel, Hlen.
  cbn [encode_storage_page_fuel].
  destruct (N.eq_dec slot 0%N) as [Hzero | Hnonzero].
  {
    subst slot.
    cbn [decode_storage_page_canonical_fuel].
    replace (length prefix <? page_slot_count)%nat with true by
      (symmetry; apply Nat.ltb_lt; lia).
    replace (negb at_start && negb prev_is_data_run)%bool with false.
    2: {
      destruct at_start, prev_is_data_run; simpl in Hstate |- *;
        tauto.
    }
    set (zeros := count_zero_prefix (S fuel) (0%N :: rest)).
    assert (Hzero_le : (zeros <= S (length rest))%nat).
    { subst zeros; apply count_zero_prefix_le. }
    assert (Hzero_pos : (0 < zeros)%nat).
    { subst zeros; apply count_zero_prefix_pos. }
    destruct (Nat.eqb_spec zeros (S (length rest))) as [Hall | Hnot_all].
	{
	  subst zeros.
	  rewrite Hall.
	  rewrite Nat.eqb_refl.
	  simpl.
	  assert
        (Hzero_suffix :
           0%N :: rest = repeat 0%N (S (length rest))).
      {
        pose proof
          (count_zero_prefix_all_zero
             (S fuel) (0%N :: rest)) as Hall_zero.
	    simpl in Hall_zero.
	    destruct (N.eq_dec 0%N 0%N); [| contradiction].
		    specialize (Hall_zero Hall).
		    unfold canonical_storage_page in Hcanonical.
		    simpl in Hcanonical.
		    rewrite normalize_slot_model_zero in Hcanonical.
		    injection Hcanonical as Hrest.
		    simpl in Hall_zero.
		    rewrite normalize_slot_model_zero in Hall_zero.
		    injection Hall_zero as Hzero_rest.
		    assert (Hrest_zero : rest = repeat 0%N (length rest)).
		    {
		      transitivity (normalize_storage_page_model rest).
		      { symmetry. exact Hrest. }
		      { exact Hzero_rest. }
		    }
		    change (repeat 0%N (S (length rest)))
		      with (0%N :: repeat 0%N (length rest)).
		    f_equal.
		    exact Hrest_zero.
	  }
	  rewrite Hzero_suffix.
	  reflexivity.
	}
    assert (Hzeros_lt : (zeros < S (length rest))%nat).
    { lia. }
    assert (Hheader_nonzero : (Z.of_nat zeros =? 0)%Z = false).
    { apply Z.eqb_neq; lia. }
    assert (Hheader_small : (Z.of_nat zeros <? 128)%Z = true).
    {
      apply Z.ltb_lt.
      change 128%Z with (Z.of_nat page_slot_count).
      apply Nat2Z.inj_lt.
      lia.
    }
    replace (zeros =? length (0%N :: rest))%nat with false by
      (symmetry; apply Nat.eqb_neq; exact Hnot_all).
    cbn [length].
    rewrite Hheader_nonzero.
    rewrite Hheader_small.
    replace (Z.to_nat (Z.of_nat zeros)) with zeros by lia.
    fold page_slot_count.
    replace (page_slot_count <=? length prefix + zeros)%nat with false by
      (symmetry; apply Nat.leb_gt; lia).
    replace
      (prefix ++ repeat 0%N (S (length rest)))
      with
      ((prefix ++ repeat 0%N zeros) ++
       repeat 0%N (length (skipn zeros (0%N :: rest)))).
	2: {
	  rewrite skipn_length.
	  rewrite <- app_assoc.
	  rewrite <- repeat_app_split.
	  simpl.
	  replace (zeros + (S (length rest) - zeros)) with (S (length rest))
	    by lia.
	  replace
	    (count_zero_prefix fuel rest +
	     (length rest - count_zero_prefix fuel rest))
	    with (length rest) by
	    (pose proof (count_zero_prefix_le fuel rest); lia).
	  reflexivity.
	}
    replace (length prefix + zeros)%nat
      with (length (prefix ++ repeat 0%N zeros)) by
      (rewrite app_length, repeat_length; lia).
    rewrite IH.
    2: { rewrite skipn_length. simpl. lia. }
    2: {
      rewrite app_length, repeat_length, skipn_length.
      subst zeros.
      simpl.
      pose proof (count_zero_prefix_le fuel rest).
      lia.
    }
    2: { apply canonical_storage_page_skipn. exact Hcanonical. }
    2: {
      apply decoder_state_ok_after_zero_prefix.
      { simpl. lia. }
      { exact Hzeros_lt. }
    }
    replace
      ((prefix ++ repeat 0%N zeros) ++ skipn zeros (0%N :: rest))
      with (prefix ++ 0%N :: rest).
	2: {
	  rewrite <- app_assoc.
	  f_equal.
	  subst zeros.
	  rewrite <- (firstn_skipn
	                (count_zero_prefix (S fuel) (0%N :: rest))
	                (0%N :: rest)) at 1.
	  rewrite (canonical_storage_page_zero_prefix
	             (S fuel) (0%N :: rest)) by exact Hcanonical.
	  reflexivity.
	}
    reflexivity.
  }
  cbn [decode_storage_page_canonical_fuel].
  replace (length prefix <? page_slot_count)%nat with true by
    (symmetry; apply Nat.ltb_lt; lia).
  unfold decoder_state_ok in Hstate.
  destruct (N.eq_dec slot 0%N) as [Hzero | _]; [contradiction |].
  subst prev_is_data_run.
  cbn [negb andb].
  set (run := count_nonzero_prefix page_slot_count (slot :: rest)).
  assert (Hrun_le : (run <= S (length rest))%nat).
  { subst run; apply count_nonzero_prefix_le. }
  assert (Hrun_pos : (0 < run)%nat).
  { subst run; apply count_nonzero_prefix_pos. exact Hnonzero. }
  assert (Hheader_nonzero : (128 + Z.of_nat (run - 1) =? 0)%Z = false).
  { apply Z.eqb_neq; lia. }
  assert (Hheader_large : (128 + Z.of_nat (run - 1) <? 128)%Z = false).
  { apply Z.ltb_ge; lia. }
  change (count_nonzero_prefix page_slot_count (slot :: rest)) with run.
  rewrite Hheader_nonzero, Hheader_large.
  replace (Z.to_nat (128 + Z.of_nat (run - 1) - 128)%Z)
    with (run - 1) by lia.
  replace (S (run - 1)) with run by lia.
  replace (page_slot_count <? length prefix + run)%nat with false by
    (symmetry; apply Nat.ltb_ge; lia).
  assert (Hfirstn_run : length (firstn run (slot :: rest)) = run).
  { rewrite firstn_length.
    apply Nat.min_l.
    exact Hrun_le.
  }
  rewrite <- Hfirstn_run at 1.
  rewrite decode_storage_page_data_run_encode_app.
  2: {
    rewrite canonical_storage_page_firstn_values by exact Hcanonical.
    apply count_nonzero_prefix_firstn_nonzero.
  }
  replace
    (decode_storage_page_update_slots
	       (length prefix)
	       (normalize_storage_page_model (firstn run (slot :: rest)))
	       (prefix ++ repeat 0%N (length (slot :: rest))))
    with
    ((prefix ++ firstn run (slot :: rest)) ++
     repeat 0%N (length (skipn run (slot :: rest)))).
  2: {
    rewrite canonical_storage_page_firstn_values by exact Hcanonical.
	    replace (prefix ++ repeat 0%N (length (slot :: rest)))
	      with
	      (prefix ++ repeat 0%N (length (firstn run (slot :: rest))) ++
	       repeat 0%N (length (skipn run (slot :: rest)))).
	2: {
	  rewrite Hfirstn_run.
	  rewrite skipn_length.
	  rewrite <- repeat_app_split.
	  simpl.
	  replace (run + (S (length rest) - run)) with (S (length rest))
	    by lia.
      reflexivity.
	    }
	    symmetry.
	    rewrite decode_storage_page_update_slots_prefix.
	    rewrite app_assoc.
	    reflexivity.
	  }
  replace (length prefix + run)%nat
    with (length (prefix ++ firstn run (slot :: rest))) by
    (rewrite app_length, Hfirstn_run; lia).
  rewrite IH.
  2: { rewrite skipn_length. simpl. lia. }
  2: {
    rewrite app_length, Hfirstn_run, skipn_length.
    simpl.
    lia.
  }
  2: { apply canonical_storage_page_skipn. exact Hcanonical. }
  2: { subst run.
       apply decoder_state_ok_after_nonzero_prefix with (prefix := prefix).
       exact Hlen. }
  f_equal.
  replace ((prefix ++ firstn run (slot :: rest)) ++
           skipn run (slot :: rest))
    with (prefix ++
          (firstn run (slot :: rest) ++
           skipn run (slot :: rest))).
  2: { apply app_assoc. }
  rewrite firstn_skipn.
  reflexivity.
Qed.

Corollary decode_encode_storage_page_model page :
  length page = page_slot_count ->
  canonical_storage_page page ->
  decode_storage_page_model (encode_storage_page_model page) = Some page.
Proof.
  intros Hlen Hcanonical.
  unfold decode_storage_page_model.
  unfold decode_storage_page_canonical_model, encode_storage_page_model.
  replace (repeat 0%N page_slot_count)
    with ([] ++ repeat 0%N (length page)) by
    (simpl; now rewrite Hlen).
  change 0 with (length (@nil N)).
  replace (encode_storage_page_fuel (length page) page)
    with (encode_storage_page_fuel (S page_slot_count) page).
  2: {
    apply encode_storage_page_fuel_irrel; lia.
  }
  rewrite decode_storage_page_canonical_encode_cont.
  { reflexivity. }
  { lia. }
  { simpl. exact Hlen. }
  { exact Hcanonical. }
  {
    destruct page as [| slot rest]; simpl; [exact I |].
    destruct (N.eq_dec slot 0%N); auto.
  }
Qed.

Corollary decode_encode_storage_page_result_model page :
  length page = page_slot_count ->
  canonical_storage_page page ->
  decode_storage_page_result_model (encode_storage_page_model page) =
    Result.Ok page.
Proof.
  intros Hlength Hcanonical.
  pose proof
    (decode_encode_storage_page_model page Hlength Hcanonical) as Hoption.
  pose proof
    (decode_storage_page_result_to_option
       (encode_storage_page_model page)) as Herase.
  rewrite Hoption in Herase.
  destruct
    (decode_storage_page_result_model (encode_storage_page_model page))
    as [decoded | error]; cbn [Result.to_option] in Herase;
    congruence.
Qed.

Lemma Z_from_bytes_big_leading_zeroes zero_count bytes :
  z_to_bytes._Z_from_bytes types.Big types.Unsigned
    (repeat 0%N zero_count ++ bytes) =
  z_to_bytes._Z_from_bytes types.Big types.Unsigned bytes.
Proof.
  rewrite !z_to_bytes._Z_from_bytes_eq.
  unfold z_to_bytes._Z_from_bytes_def.
  rewrite rev_app_distr, rev_repeat.
  unfold z_to_bytes._Z_from_bytes_le.
  rewrite z_to_bytes._Z_from_bytes_unsigned_le_app.
  rewrite z_to_bytes._Z_from_bytes_unsigned_le'_0s.
  rewrite Z.lor_0_r.
  reflexivity.
Qed.

Lemma encoded_bytes_to_N_range bytes :
  storage_encoded_bytes_in_range bytes ->
  Forall (fun byte : N => (byte < 256)%N) (map Z.to_N bytes).
Proof.
  intro Hrange.
  rewrite Forall_map.
  eapply Forall_impl
    with (P := storage_encoded_byte_in_range).
  {
    intros byte Hbyte.
    unfold storage_encoded_byte_in_range in Hbyte.
    lia.
  }
  exact Hrange.
Qed.

Lemma encoded_bytes_Z_N_roundtrip bytes :
  storage_encoded_bytes_in_range bytes ->
  map Z.of_N (map Z.to_N bytes) = bytes.
Proof.
  intro Hrange.
  induction Hrange as [| byte rest Hbyte Hrest IH].
  {
    reflexivity.
  }
  cbn [map].
  f_equal.
  {
    unfold storage_encoded_byte_in_range in Hbyte.
    apply Z2N.id.
    lia.
  }
  exact IH.
Qed.

Lemma be_bytes_word_of_compact_payload payload :
  length payload <= 32 ->
  storage_encoded_bytes_in_range payload ->
  be_bytes 32 (word_of_compact_payload payload) =
    repeat 0%Z (32 - length payload) ++ payload.
Proof.
  intros Hlength Hrange.
  unfold be_bytes, word_of_compact_payload.
  set (bytes := map Z.to_N payload).
  set (padding := repeat 0%N (32 - length payload)).
  assert
    (Hdecoded_nonnegative :
       (0 <=
        z_to_bytes._Z_from_bytes
          types.Big types.Unsigned bytes)%Z).
  {
    pose proof
      (z_to_bytes._Z_from_bytes_Unsigned_bound
         types.Big bytes).
    lia.
  }
  rewrite (Z2N.id _ Hdecoded_nonnegative).
  rewrite <-
    (Z_from_bytes_big_leading_zeroes
       (32 - length payload) bytes).
  assert
    (Hpadded_range :
       Forall (fun byte : N => (byte < 256)%N)
         (padding ++ bytes)).
  {
    apply Forall_app.
    split.
    {
      subst padding.
      induction (32 - length payload) as [| count IH];
        constructor; [lia | exact IH].
    }
    {
      subst bytes.
      apply encoded_bytes_to_N_range.
      exact Hrange.
    }
  }
  assert (Hpadded_length : length (padding ++ bytes) = 32).
  {
    subst padding bytes.
    rewrite app_length, repeat_length, map_length.
    lia.
  }
  fold padding.
  rewrite
    (z_to_bytes._Z_to_from_bytes_roundtrip
       (padding ++ bytes) types.Unsigned types.Big 32
       Hpadded_range (eq_sym Hpadded_length)).
  subst padding bytes.
  rewrite map_app, map_repeat.
  rewrite encoded_bytes_Z_N_roundtrip by exact Hrange.
  reflexivity.
Qed.

Lemma drop_leading_zeroes_fixed bytes :
  compact_payload_has_leading_zero bytes = false ->
  drop_leading_zeroes bytes = bytes.
Proof.
  intros Hleading.
  destruct bytes as [| byte rest]; [reflexivity |].
  destruct byte; simpl in *; try reflexivity; discriminate.
Qed.

Lemma drop_leading_zeroes_repeat_app bytes count :
  compact_payload_has_leading_zero bytes = false ->
  drop_leading_zeroes (repeat 0%Z count ++ bytes) = bytes.
Proof.
  intro Hleading.
  induction count as [| count IH]; simpl.
  {
    apply drop_leading_zeroes_fixed.
    exact Hleading.
  }
  exact IH.
Qed.

Lemma compact_payload_word_roundtrip payload :
  length payload <= 32 ->
  storage_encoded_bytes_in_range payload ->
  compact_payload_has_leading_zero payload = false ->
  compact_bytes32_payload (word_of_compact_payload payload) = payload.
Proof.
  intros Hlength Hrange Hleading.
  unfold compact_bytes32_payload.
  rewrite be_bytes_word_of_compact_payload by assumption.
  apply drop_leading_zeroes_repeat_app.
  exact Hleading.
Qed.

Lemma rlp_decode_string_short_reencode encoded payload rest :
  storage_encoded_bytes_in_range encoded ->
  rlp_decode_string_model encoded = Some (payload, rest) ->
  length payload <= 32 ->
  rlp_encode_short_string payload ++ rest = encoded.
Proof.
  intros Hrange Hdecode Hpayload_length.
  destruct encoded as [| header encoded]; [discriminate |].
  cbn [rlp_decode_string_model] in Hdecode.
  destruct (header <=? 127)%Z eqn:Hsingle.
  {
    injection Hdecode as <- <-.
    inversion Hrange as [| ? ? Hheader _]; subst.
    unfold rlp_encode_short_string.
    cbn [length].
    replace (0 <=? header)%Z with true by
      (symmetry; apply Z.leb_le; unfold storage_encoded_byte_in_range in Hheader;
       lia).
    rewrite Hsingle.
    reflexivity.
  }
  destruct ((128 <=? header)%Z && (header <=? 183)%Z)
    eqn:Hshort.
  {
    apply andb_true_iff in Hshort as [Hheader_low Hheader_high].
    apply Z.leb_le in Hheader_low.
    apply Z.leb_le in Hheader_high.
    set (payload_length := Z.to_nat (header - 128)%Z) in *.
    destruct
      (rlp_short_string_is_noncanonical payload_length encoded)
      eqn:Hcanonical; [discriminate |].
    destruct (payload_length <=? length encoded)%nat
      eqn:Hfits; [| discriminate].
    injection Hdecode as <- <-.
    apply Nat.leb_le in Hfits.
    assert (Hheader : header = (128 + Z.of_nat payload_length)%Z).
    {
      subst payload_length.
      rewrite Z2Nat.id by lia.
      lia.
    }
    destruct payload_length as [| [| payload_length]].
    {
      simpl in Hheader.
      subst header.
      reflexivity.
    }
    {
      destruct encoded as [| byte encoded]; [simpl in Hfits; lia |].
      unfold rlp_short_string_is_noncanonical in Hcanonical.
      cbn [Nat.eqb] in Hcanonical.
      apply andb_false_iff in Hcanonical as [Himpossible | Hbyte].
      {
        discriminate.
      }
      apply Z.ltb_ge in Hbyte.
      unfold rlp_encode_short_string.
      cbn [firstn length].
      replace ((0 <=? byte)%Z && (byte <=? 127)%Z) with false.
      2: {
        symmetry.
        apply andb_false_iff.
        right.
        apply Z.leb_gt.
        lia.
      }
      cbn [skipn].
      subst header.
      reflexivity.
    }
    {
      destruct encoded as [| first [| second encoded]];
        simpl in Hfits; try lia.
      unfold rlp_encode_short_string.
      cbn [firstn length].
      subst header.
      rewrite firstn_length_le by lia.
      f_equal.
      cbn [skipn].
      cbn [app].
      rewrite firstn_skipn.
      reflexivity.
    }
  }
  destruct ((184 <=? header)%Z && (header <=? 191)%Z)
    eqn:Hlong; [| discriminate].
  destruct
    (Z.to_nat (header - 183) <? length encoded)%nat
    eqn:Hlength_bytes; [| discriminate].
  destruct
    (rlp_decode_long_string_length
       (firstn (Z.to_nat (header - 183)) encoded))
    as [long_length |] eqn:Hlong_length; [| discriminate].
  destruct (long_length <? 56)%nat eqn:Hlong_short; [discriminate |].
  set
    (payload_and_rest :=
       skipn (Z.to_nat (header - 183)) encoded) in *.
  destruct (long_length <=? length payload_and_rest)%nat
    eqn:Hlong_fits; [| discriminate].
  injection Hdecode as <- <-.
  apply Nat.ltb_ge in Hlong_short.
  apply Nat.leb_le in Hlong_fits.
  rewrite firstn_length_le in Hpayload_length by exact Hlong_fits.
  lia.
Qed.

Lemma rlp_encode_short_string_payload_range payload rest :
  storage_encoded_bytes_in_range
    (rlp_encode_short_string payload ++ rest) ->
  storage_encoded_bytes_in_range payload.
Proof.
  intro Hrange.
  destruct payload as [| byte [| second tail]].
  {
    constructor.
  }
  {
    unfold rlp_encode_short_string in Hrange.
    cbn [length] in Hrange.
    destruct ((0 <=? byte)%Z && (byte <=? 127)%Z).
    {
      cbn [app] in Hrange.
      inversion Hrange as [| ? ? Hbyte _]; subst.
      constructor; [exact Hbyte | constructor].
    }
    {
      cbn [app] in Hrange.
      inversion Hrange as [| ? ? _ Htail]; subst.
      inversion Htail as [| ? ? Hbyte _]; subst.
      constructor; [exact Hbyte | constructor].
    }
  }
  unfold rlp_encode_short_string in Hrange.
  cbn [length] in Hrange.
  inversion Hrange as [| ? ? _ Hpayload_and_rest]; subst.
  change
    (Forall storage_encoded_byte_in_range
       ((byte :: second :: tail) ++ rest))
    in Hpayload_and_rest.
  apply Forall_app in Hpayload_and_rest as [Hpayload _].
  exact Hpayload.
Qed.

Lemma rlp_decode_bytes32_compact_reencode encoded value rest :
  storage_encoded_bytes_in_range encoded ->
  rlp_decode_bytes32_compact_model encoded = Some (value, rest) ->
  encode_slot_model value ++ rest = encoded /\
  normalize_slot_model value = value /\
  storage_encoded_bytes_in_range rest.
Proof.
  intros Hrange Hdecode.
  unfold rlp_decode_bytes32_compact_model in Hdecode.
  destruct (rlp_decode_string_model encoded)
    as [[payload after_payload] |] eqn:Hstring; [| discriminate].
  destruct (32 <? length payload)%nat eqn:Hlength; [discriminate |].
  destruct (compact_payload_has_leading_zero payload)
    eqn:Hleading; [discriminate |].
  injection Hdecode as <- <-.
  apply Nat.ltb_ge in Hlength.
  pose proof
    (rlp_decode_string_short_reencode
       encoded payload after_payload Hrange Hstring Hlength)
    as Hreencode.
  assert (Hpayload_range : storage_encoded_bytes_in_range payload).
  {
    apply (rlp_encode_short_string_payload_range payload after_payload).
    rewrite Hreencode.
    exact Hrange.
  }
  assert
    (Hpayload_roundtrip :
       compact_bytes32_payload (word_of_compact_payload payload) = payload).
  {
    apply compact_payload_word_roundtrip; assumption.
  }
  split.
  {
    unfold encode_slot_model.
    rewrite Hpayload_roundtrip.
    exact Hreencode.
  }
  split.
  {
    unfold normalize_slot_model.
    rewrite Hpayload_roundtrip.
    reflexivity.
  }
  rewrite <- Hreencode in Hrange.
  apply Forall_app in Hrange as [_ Hrest].
  exact Hrest.
Qed.

Lemma decode_storage_page_data_run_reencode
    count offset page encoded page' rest :
  storage_encoded_bytes_in_range encoded ->
  decode_storage_page_data_run count offset page encoded =
    Some (page', rest) ->
  exists values,
    length values = count /\
    slots_nonzero values /\
    canonical_storage_page values /\
    page' = decode_storage_page_update_slots offset values page /\
    concat (map encode_slot_model values) ++ rest = encoded /\
    storage_encoded_bytes_in_range rest.
Proof.
  revert offset page encoded page' rest.
  induction count as [| count IH];
    intros offset page encoded page' rest Hrange Hdecode.
  {
    cbn [decode_storage_page_data_run] in Hdecode.
    injection Hdecode as <- <-.
    exists [].
    split; [reflexivity |].
    split; [constructor |].
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity | exact Hrange].
  }
  cbn [decode_storage_page_data_run] in Hdecode.
  destruct (rlp_decode_bytes32_compact_model encoded)
    as [[value after_value] |] eqn:Hvalue; [| discriminate].
  destruct (value =? 0)%N eqn:Hvalue_nonzero; [discriminate |].
  pose proof
    (rlp_decode_bytes32_compact_reencode
       encoded value after_value Hrange Hvalue)
    as [Hvalue_bytes [Hvalue_canonical Hafter_range]].
  specialize
    (IH (S offset)
       (decode_storage_page_update_slot offset value page)
       after_value page' rest Hafter_range Hdecode)
    as
    (values &
     Hvalues_length &
     Hvalues_nonzero &
     Hvalues_canonical &
     Hpage' &
     Hvalues_bytes &
     Hrest_range).
  exists (value :: values).
  split.
  {
    simpl.
    now rewrite Hvalues_length.
  }
  split.
  {
    constructor.
    {
      apply N.eqb_neq.
      exact Hvalue_nonzero.
    }
    exact Hvalues_nonzero.
  }
  split.
  {
    unfold canonical_storage_page,
      normalize_storage_page_model in *.
    cbn [map].
    rewrite Hvalue_canonical.
    now rewrite Hvalues_canonical.
  }
  split.
  {
    cbn [decode_storage_page_update_slots].
    exact Hpage'.
  }
  split.
  {
    cbn [map concat].
    rewrite <- app_assoc, Hvalues_bytes.
    exact Hvalue_bytes.
  }
  exact Hrest_range.
Qed.

Lemma canonical_storage_page_app lhs rhs :
  canonical_storage_page lhs ->
  canonical_storage_page rhs ->
  canonical_storage_page (lhs ++ rhs).
Proof.
  unfold canonical_storage_page.
  intros Hlhs Hrhs.
  rewrite normalize_storage_page_model_app, Hlhs, Hrhs.
  reflexivity.
Qed.

Lemma canonical_storage_page_repeat_zero count :
  canonical_storage_page (repeat 0%N count).
Proof.
  unfold canonical_storage_page, normalize_storage_page_model.
  induction count as [| count IH]; simpl; [reflexivity |].
  rewrite normalize_slot_model_zero, IH.
  reflexivity.
Qed.

Lemma decoder_state_false_false_nonzero suffix :
  suffix <> [] ->
  decoder_state_ok false false suffix ->
  nth 0 suffix 0%N <> 0%N.
Proof.
  intros Hnonempty Hstate.
  destruct suffix as [| slot rest]; [contradiction |].
  unfold decoder_state_ok in Hstate.
  destruct (N.eq_dec slot 0%N) as [Hzero | Hnonzero].
  {
    destruct Hstate as [Hfalse | Hfalse]; discriminate.
  }
  exact Hnonzero.
Qed.

Lemma decoder_state_false_true_zero suffix :
  decoder_state_ok false true suffix ->
  suffix = [] \/ nth 0 suffix 0%N = 0%N.
Proof.
  intro Hstate.
  destruct suffix as [| slot rest].
  {
    left.
    reflexivity.
  }
  right.
  unfold decoder_state_ok in Hstate.
  destruct (N.eq_dec slot 0%N) as [Hzero | Hnonzero].
  {
    exact Hzero.
  }
  discriminate.
Qed.

Lemma decode_storage_page_update_slots_zero_suffix prefix values :
  length prefix + length values <= page_slot_count ->
  decode_storage_page_update_slots
    (length prefix) values
    (prefix ++ repeat 0%N (page_slot_count - length prefix)) =
  prefix ++ values ++
    repeat 0%N (page_slot_count - (length prefix + length values)).
Proof.
  intro Hlength.
  replace (page_slot_count - length prefix)
    with
    (length values +
     (page_slot_count - (length prefix + length values))) by lia.
  rewrite repeat_app_split.
  apply decode_storage_page_update_slots_prefix.
Qed.

Lemma decoder_state_repeat_zero
    at_start prev_is_data_run count :
  0 < count ->
  negb at_start && negb prev_is_data_run = false ->
  decoder_state_ok at_start prev_is_data_run (repeat 0%N count).
Proof.
  intros Hcount Hallowed.
  destruct count as [| count]; [lia |].
  unfold decoder_state_ok.
  cbn [repeat].
  destruct (N.eq_dec 0%N 0%N); [| contradiction].
  destruct at_start, prev_is_data_run;
    cbn in Hallowed |-; auto; discriminate.
Qed.

Lemma decoder_state_zero_prefix
    at_start prev_is_data_run count suffix :
  0 < count ->
  negb at_start && negb prev_is_data_run = false ->
  decoder_state_ok
    at_start prev_is_data_run (repeat 0%N count ++ suffix).
Proof.
  intros Hcount Hallowed.
  destruct count as [| count]; [lia |].
  cbn [repeat app].
  unfold decoder_state_ok.
  destruct (N.eq_dec 0%N 0%N); [| contradiction].
  destruct at_start, prev_is_data_run;
    cbn in Hallowed |-; auto; discriminate.
Qed.

Lemma decode_storage_page_canonical_reencode_cont
    fuel prefix at_start prev_is_data_run encoded final :
  length prefix <= page_slot_count ->
  page_slot_count < length prefix + fuel ->
  storage_encoded_bytes_in_range encoded ->
  decode_storage_page_canonical_fuel
    fuel (length prefix) at_start prev_is_data_run
    (prefix ++ repeat 0%N (page_slot_count - length prefix))
    encoded =
    Some final ->
  exists suffix,
    final = prefix ++ suffix /\
    length prefix + length suffix = page_slot_count /\
    canonical_storage_page suffix /\
    decoder_state_ok at_start prev_is_data_run suffix /\
    encode_storage_page_model suffix = encoded.
Proof.
  revert prefix at_start prev_is_data_run encoded final.
  induction fuel as [| fuel IH];
    intros prefix at_start prev_is_data_run encoded final
      Hprefix_length Hfuel Hrange Hdecode.
  {
    cbn [decode_storage_page_canonical_fuel] in Hdecode.
    discriminate.
  }
  cbn [decode_storage_page_canonical_fuel] in Hdecode.
  destruct (length prefix <? page_slot_count)%nat
    eqn:Hoffset.
  {
    apply Nat.ltb_lt in Hoffset.
    destruct encoded as [| header rest]; [discriminate |].
    pose proof
      (storage_encoded_bytes_in_range_cons_head header rest Hrange)
      as Hheader_range.
    pose proof
      (storage_encoded_bytes_in_range_cons_tail header rest Hrange)
      as Hrest_range.
    destruct (header =? 0)%Z eqn:Hterminator.
    {
      apply Z.eqb_eq in Hterminator.
      subst header.
      destruct (negb at_start && negb prev_is_data_run)
        eqn:Hallowed; [discriminate |].
      destruct rest as [| trailing rest]; [| discriminate].
      injection Hdecode as <-.
      exists (repeat 0%N (page_slot_count - length prefix)).
      split.
      {
        reflexivity.
      }
      split.
      {
        rewrite repeat_length.
        lia.
      }
      split.
      {
        apply canonical_storage_page_repeat_zero.
      }
      split.
      {
        apply decoder_state_repeat_zero; [lia | exact Hallowed].
      }
      apply encode_storage_page_model_all_zero.
      {
        rewrite repeat_length.
        lia.
      }
      replace
        (length
           (repeat 0%N (page_slot_count - length prefix)))
        with (page_slot_count - length prefix)
        by (symmetry; apply repeat_length).
      apply firstn_all2.
      rewrite repeat_length.
      lia.
    }
    destruct (header <? 128)%Z eqn:Hzero_run.
    {
      apply Z.ltb_lt in Hzero_run.
      destruct (negb at_start && negb prev_is_data_run)
        eqn:Hallowed; [discriminate |].
      assert (Hheader_positive : (0 < header)%Z).
      {
        unfold storage_encoded_byte_in_range in Hheader_range.
        apply Z.eqb_neq in Hterminator.
        lia.
      }
      set (zeros := Z.to_nat header).
      assert (Hzeros_positive : (0 < zeros)%nat).
      {
        subst zeros.
        lia.
      }
      assert (Hheader : header = Z.of_nat zeros).
      {
        subst zeros.
        rewrite Z2Nat.id by lia.
        reflexivity.
      }
      set (offset' := length prefix + zeros).
      fold zeros in Hdecode.
      fold offset' in Hdecode.
      destruct (page_slot_count <=? offset')%nat
        eqn:Hpast_end; [discriminate |].
      apply Nat.leb_gt in Hpast_end.
      assert
        (Hpage_split :
           prefix ++ repeat 0%N (page_slot_count - length prefix) =
           (prefix ++ repeat 0%N zeros) ++
           repeat 0%N
             (page_slot_count -
              length (prefix ++ repeat 0%N zeros))).
      {
        rewrite app_length, repeat_length.
        rewrite <- app_assoc.
        f_equal.
        rewrite <- repeat_app_split.
        f_equal.
        lia.
      }
      rewrite Hpage_split in Hdecode.
      assert
        (Hoffset'_length :
           offset' = length (prefix ++ repeat 0%N zeros)).
      {
        unfold offset'.
        rewrite app_length, repeat_length.
        reflexivity.
      }
      rewrite Hoffset'_length in Hdecode.
      specialize
        (IH
           (prefix ++ repeat 0%N zeros)
           false false rest final)
        as Hrec.
      assert
        (Hprefix'_length :
           length (prefix ++ repeat 0%N zeros) <= page_slot_count).
      {
        rewrite app_length, repeat_length.
        lia.
      }
      assert
        (Hfuel' :
           page_slot_count <
           length (prefix ++ repeat 0%N zeros) + fuel).
      {
        rewrite app_length, repeat_length.
        lia.
      }
      specialize
        (Hrec Hprefix'_length Hfuel' Hrest_range Hdecode)
        as
        (suffix &
         Hfinal &
         Hlength &
         Hcanonical &
         Hstate &
         Hencoded).
      exists (repeat 0%N zeros ++ suffix).
      split.
      {
        rewrite Hfinal, app_assoc.
        reflexivity.
      }
      split.
      {
        rewrite app_length, repeat_length.
        lia.
      }
      split.
      {
        apply canonical_storage_page_app.
        {
          apply canonical_storage_page_repeat_zero.
        }
        exact Hcanonical.
      }
      split.
      {
        apply decoder_state_zero_prefix; [lia | exact Hallowed].
      }
      rewrite
        (encode_storage_page_model_zero_prefix
           (repeat 0%N zeros ++ suffix) zeros).
      {
        replace
          (skipn zeros (repeat 0%N zeros ++ suffix))
        with suffix.
        2: {
          rewrite skipn_app, repeat_length, Nat.sub_diag.
          rewrite skipn_all2 by
            (rewrite repeat_length; lia).
          reflexivity.
        }
        rewrite Hheader, Hencoded.
        reflexivity.
      }
      {
        rewrite app_length, repeat_length.
        lia.
      }
      {
        rewrite app_length, repeat_length.
        assert (suffix <> []).
        {
          intro Hempty.
          subst suffix.
          simpl in Hlength.
          lia.
        }
        split; [exact Hzeros_positive | lia].
      }
      {
        rewrite firstn_app, repeat_length, Nat.sub_diag.
        rewrite firstn_all2 by
          (rewrite repeat_length; lia).
        rewrite firstn_O, app_nil_r.
        reflexivity.
      }
      {
        rewrite app_nth2 by (rewrite repeat_length; lia).
        rewrite repeat_length, Nat.sub_diag.
        apply decoder_state_false_false_nonzero.
        {
          intro Hempty.
          subst suffix.
          simpl in Hlength.
          lia.
        }
        exact Hstate.
      }
    }
    apply Z.ltb_ge in Hzero_run.
    destruct prev_is_data_run; [discriminate |].
    set (run := S (Z.to_nat (header - 128)%Z)).
    fold run in Hdecode.
    destruct (page_slot_count <? length prefix + run)%nat
      eqn:Hrun_past_end; [discriminate |].
    apply Nat.ltb_ge in Hrun_past_end.
    destruct
      (decode_storage_page_data_run
         run (length prefix)
         (prefix ++ repeat 0%N (page_slot_count - length prefix))
         rest)
      as [[page' rest'] |] eqn:Hdata_run; [| discriminate].
    pose proof
      (decode_storage_page_data_run_reencode
         run (length prefix)
         (prefix ++ repeat 0%N (page_slot_count - length prefix))
         rest page' rest' Hrest_range Hdata_run)
      as
      (values &
       Hvalues_length &
       Hvalues_nonzero &
       Hvalues_canonical &
       Hpage' &
       Hvalues_encoded &
       Hrest'_range).
    rewrite Hpage' in Hdecode.
    rewrite
      (decode_storage_page_update_slots_zero_suffix prefix values)
      in Hdecode by
      (rewrite Hvalues_length; exact Hrun_past_end).
    rewrite app_assoc in Hdecode.
    replace (length prefix + run)
      with (length (prefix ++ values)) in Hdecode by
      (rewrite app_length, Hvalues_length; reflexivity).
    replace (length prefix + length values)
      with (length (prefix ++ values)) in Hdecode by
      (rewrite app_length; reflexivity).
    specialize
      (IH (prefix ++ values) false true rest' final)
      as Hrec.
    assert
      (Hprefix'_length :
         length (prefix ++ values) <= page_slot_count).
    {
      rewrite app_length, Hvalues_length.
      exact Hrun_past_end.
    }
    assert
      (Hfuel' :
         page_slot_count < length (prefix ++ values) + fuel).
    {
      rewrite app_length, Hvalues_length.
      unfold run.
      lia.
    }
    specialize
      (Hrec Hprefix'_length Hfuel' Hrest'_range Hdecode)
      as
      (suffix &
       Hfinal &
       Hlength &
       Hcanonical &
       Hstate &
       Hencoded).
    exists (values ++ suffix).
    split.
    {
      rewrite Hfinal, app_assoc.
      reflexivity.
    }
    split.
    {
      rewrite app_length in Hlength.
      rewrite app_length.
      lia.
    }
    split.
    {
      apply canonical_storage_page_app;
        assumption.
    }
    split.
    {
      destruct values as [| value values].
      {
        simpl in Hvalues_length.
        unfold run in Hvalues_length.
        lia.
      }
      inversion Hvalues_nonzero as [| ? ? Hvalue_nonzero _]; subst.
      unfold decoder_state_ok.
      cbn [app].
      destruct (N.eq_dec value 0%N);
        [contradiction | reflexivity].
    }
    assert (Hheader : header = (128 + Z.of_nat (run - 1))%Z).
    {
      unfold run.
      replace
        (S (Z.to_nat (header - 128)%Z) - 1)
        with (Z.to_nat (header - 128)%Z) by lia.
      rewrite Z2Nat.id by lia.
      lia.
    }
    rewrite
      (encode_storage_page_model_nonzero_prefix
         (values ++ suffix) run).
    {
      rewrite Hheader.
      f_equal.
      rewrite <- Hvalues_length.
      rewrite firstn_app, firstn_all,
        Nat.sub_diag, firstn_O, app_nil_r.
      rewrite skipn_app, skipn_all,
        Nat.sub_diag, skipn_0, app_nil_l.
      rewrite Hencoded.
      exact Hvalues_encoded.
    }
    {
      rewrite app_length in Hlength.
      rewrite app_length.
      lia.
    }
    {
      unfold run.
      lia.
    }
    {
      rewrite app_length, Hvalues_length.
      lia.
    }
    {
      rewrite <- Hvalues_length.
      rewrite firstn_app, firstn_all,
        Nat.sub_diag, firstn_O, app_nil_r.
      exact Hvalues_nonzero.
    }
    {
      pose proof (decoder_state_false_true_zero suffix Hstate)
        as [Hsuffix_empty | Hsuffix_zero].
      {
        left.
        subst suffix.
        rewrite app_nil_r, Hvalues_length.
        reflexivity.
      }
      right.
      right.
      rewrite app_nth2 by
        (rewrite Hvalues_length; lia).
      rewrite Hvalues_length, Nat.sub_diag.
      exact Hsuffix_zero.
    }
  }
  apply Nat.ltb_ge in Hoffset.
  assert (Hprefix_full : length prefix = page_slot_count) by lia.
  destruct encoded as [| header rest]; [| discriminate].
  injection Hdecode as <-.
  exists [].
  split.
  {
    rewrite Hprefix_full, Nat.sub_diag.
    reflexivity.
  }
  split.
  {
    simpl.
    lia.
  }
  split.
  {
    reflexivity.
  }
  split.
  {
    exact I.
  }
  reflexivity.
Qed.

(** Every byte string accepted by the strict decoder is already the unique
    canonical encoding of the page it produces.  The byte-range premise is the
    pure-model counterpart of the C++ decoder reading [unsigned char] values. *)
Theorem decode_storage_page_model_canonical_encoding bytes page :
  storage_encoded_bytes_in_range bytes ->
  decode_storage_page_model bytes = Some page ->
  encode_storage_page_model page = bytes.
Proof.
  intros Hrange Hdecode.
  unfold decode_storage_page_model,
    decode_storage_page_canonical_model in Hdecode.
  pose proof
    (decode_storage_page_canonical_reencode_cont
       (S page_slot_count) [] true false bytes page)
    as Hcanonical.
  specialize
    (Hcanonical
       ltac:(simpl; lia)
       ltac:(simpl; lia)
       Hrange Hdecode)
    as
    (suffix &
     Hpage &
     _ &
     _ &
     _ &
     Hencoded).
  simpl in Hpage.
  subst page.
  exact Hencoded.
Qed.

Theorem decode_storage_page_result_model_canonical_encoding bytes page :
  storage_encoded_bytes_in_range bytes ->
  decode_storage_page_result_model bytes = Result.Ok page ->
  encode_storage_page_model page = bytes.
Proof.
  intros Hrange Hdecode.
  apply decode_storage_page_model_canonical_encoding; [exact Hrange |].
  rewrite <- decode_storage_page_result_to_option.
  rewrite Hdecode.
  reflexivity.
Qed.
