Set Default Goal Selector "!".

(**
  Compact RLP for Storage-Page Values
  ----------------------------------

  The indexed page codec in [storage_page_indexed_encoding] stores each
  occupied slot as an index followed by its compact-RLP value. This file
  supplies the value codec, its exact error model, round-trip and canonicality
  proofs, and the page-normalization lemmas used by that codec. The old
  run-length page format is not part of this proof suite.
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

Definition decode_storage_page_update_slot
    (offset : nat) (value : N) (page : list N) : list N :=
  firstn offset page ++ value :: skipn (S offset) page.

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

Lemma normalize_storage_page_model_app lhs rhs :
  normalize_storage_page_model (lhs ++ rhs) =
  normalize_storage_page_model lhs ++ normalize_storage_page_model rhs.
Proof.
  unfold normalize_storage_page_model.
  apply map_app.
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

Definition canonical_storage_page (page : list N) : Prop :=
  normalize_storage_page_model page = page.

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
