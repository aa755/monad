Set Default Goal Selector "!".

(** * Ordered Slot Encoding

    Public main at [1d22498c5f6a] replaces the older storage-page RLE format
    with ordered index/value pairs. Each occupied slot contributes its index
    byte and its compact RLP value; absent slots contribute nothing. An empty
    page therefore encodes as the empty byte string. The commitment algorithm
    is unaffected by this serialization change.

    [storage_page_encoding] supplies the compact-RLP machinery used here. *)

From Stdlib Require Import Bool List NArith ZArith Lia.
Require Import monad.proofs.execproofs.mip8.commitment.
Require Import monad.proofs.libspecs.result_model.
Require Import monad.proofs.libspecs.rlp_decode_error_model.
Require Import monad.proofs.execproofs.mip8.storage_page_encoding.
Import ListNotations.

Fixpoint encode_slots_from (index : nat) (page : list N) : list Z :=
  match page with
  | [] => []
  | value :: rest =>
      if N.eq_dec value 0
      then encode_slots_from (S index) rest
      else Z.of_nat index ::
        encode_slot_model value ++ encode_slots_from (S index) rest
  end.

Definition encode_storage_page_model (page : list N) : list Z :=
  encode_slots_from 0 page.

(** [next] is the first slot that a subsequent pair may name. Strict index
    ordering both rejects duplicate openings and makes the zero-filled gaps
    unambiguous. The recursive result contains slots [next..127]; the caller
    prepends the gap and value it just decoded.

    Fuel bounds the number of pairs, not the number of bytes. Range and order
    checks precede the fuel test: once all 128 positions have been consumed,
    every further index is noncanonical, exactly as in C++. *)
Fixpoint decode_slots_from (fuel next : nat) (encoded : list Z)
    : Result.t (list N) DecodeError.DecodeError.t :=
  match encoded with
  | [] => Result.Ok (repeat 0%N (page_slot_count - next))
  | index :: rest =>
      if ((index <? Z.of_nat next) ||
          (Z.of_nat page_slot_count <=? index))%Z
      then Result.Err DecodeError.DecodeError.NonCanonical
      else
        match fuel with
        | O => Result.Err DecodeError.DecodeError.NonCanonical
        | S fuel' =>
            match rlp_decode_bytes32_compact_result_model rest with
            | Result.Err error => Result.Err error
            | Result.Ok (value, suffix) =>
                if N.eq_dec value 0
                then Result.Err DecodeError.DecodeError.NonCanonical
                else
                  match decode_slots_from fuel' (S (Z.to_nat index)) suffix with
                  | Result.Err error => Result.Err error
                  | Result.Ok slots =>
                      Result.Ok
                        (repeat 0%N (Z.to_nat index - next) ++ value :: slots)
                  end
            end
        end
  end.

Definition decode_storage_page_result_model (bytes : list Z)
    : Result.t (list N) DecodeError.DecodeError.t :=
  decode_slots_from page_slot_count 0 bytes.

Definition decode_storage_page_model (bytes : list Z) : option (list N) :=
  Result.to_option (decode_storage_page_result_model bytes).

Lemma decode_storage_page_result_to_option bytes :
  Result.to_option (decode_storage_page_result_model bytes) =
  decode_storage_page_model bytes.
Proof. reflexivity. Qed.

Lemma encode_slots_from_app index lhs rhs :
  encode_slots_from index (lhs ++ rhs) =
  encode_slots_from index lhs ++ encode_slots_from (index + length lhs) rhs.
Proof.
  revert index.
  induction lhs as [| value lhs IH]; intro index.
  { simpl. now rewrite Nat.add_0_r. }
  cbn [app length encode_slots_from].
  destruct (N.eq_dec value 0); rewrite IH.
  { now rewrite Nat.add_succ_r. }
  rewrite Nat.add_succ_r, app_assoc. reflexivity.
Qed.

Lemma encode_slots_from_zeroes index count :
  encode_slots_from index (repeat 0%N count) = [].
Proof.
  revert index.
  induction count as [| count IH]; intro index; simpl; auto.
Qed.

Lemma encode_slots_from_gap index count rest :
  encode_slots_from index (repeat 0%N count ++ rest) =
  encode_slots_from (index + count) rest.
Proof.
  rewrite encode_slots_from_app, encode_slots_from_zeroes, repeat_length.
  reflexivity.
Qed.

Lemma rlp_decode_compact_result_encode_app value rest :
  rlp_decode_bytes32_compact_result_model (encode_slot_model value ++ rest) =
  Result.Ok (normalize_slot_model value, rest).
Proof.
  pose proof (rlp_decode_bytes32_compact_result_to_option
    (encode_slot_model value ++ rest)) as Hoption.
  rewrite rlp_decode_bytes32_compact_encode_app in Hoption.
  destruct (rlp_decode_bytes32_compact_result_model
    (encode_slot_model value ++ rest)); cbn in Hoption; congruence.
Qed.

(** A decoded suffix has exactly the remaining page width, and re-encoding
    it recovers every consumed byte. This rules out accepted noncanonical
    aliases, not just decoder failures on a few malformed examples. *)
Lemma decode_slots_from_reencode fuel next bytes slots :
  next <= page_slot_count ->
  storage_encoded_bytes_in_range bytes ->
  decode_slots_from fuel next bytes = Result.Ok slots ->
  length slots = page_slot_count - next /\
  canonical_storage_page slots /\
  encode_slots_from next slots = bytes.
Proof.
  revert next bytes slots.
  induction fuel as [| fuel IH]; intros next bytes slots Hnext Hrange Hdecode;
    destruct bytes as [| index rest].
  {
    cbn [decode_slots_from] in Hdecode.
    injection Hdecode as <-.
    split; [apply repeat_length |].
    split; [apply canonical_storage_page_repeat_zero |].
    apply encode_slots_from_zeroes.
  }
  {
    cbn [decode_slots_from] in Hdecode.
    destruct ((index <? Z.of_nat next) ||
      (Z.of_nat page_slot_count <=? index))%Z; discriminate.
  }
  {
    cbn [decode_slots_from] in Hdecode.
    injection Hdecode as <-.
    split; [apply repeat_length |].
    split; [apply canonical_storage_page_repeat_zero |].
    apply encode_slots_from_zeroes.
  }
  cbn [decode_slots_from] in Hdecode.
  destruct ((index <? Z.of_nat next) ||
    (Z.of_nat page_slot_count <=? index))%Z eqn:Hindex; [discriminate |].
  apply Bool.orb_false_iff in Hindex as [Hlower Hupper].
  apply Z.ltb_ge in Hlower. apply Z.leb_gt in Hupper.
  destruct (rlp_decode_bytes32_compact_result_model rest)
    as [[value suffix] | error] eqn:Hrlp; [| discriminate].
  destruct (N.eq_dec value 0) as [Hzero | Hnonzero]; [discriminate |].
  destruct (decode_slots_from fuel (S (Z.to_nat index)) suffix)
    as [decoded | error] eqn:Htail; [| discriminate].
  injection Hdecode as <-.
  pose proof (rlp_decode_bytes32_compact_result_to_option rest) as Hoption.
  rewrite Hrlp in Hoption. cbn in Hoption.
  symmetry in Hoption.
  pose proof (rlp_decode_bytes32_compact_reencode rest value suffix
    (storage_encoded_bytes_in_range_cons_tail _ _ Hrange) Hoption)
    as [Hbytes [Hvalue Hsuffix]].
  specialize (IH (S (Z.to_nat index)) suffix decoded ltac:(lia) Hsuffix Htail)
    as [Hlength [Hcanonical Hencoded]].
  split.
  { rewrite app_length, repeat_length. cbn [length]. lia. }
  split.
  {
    apply canonical_storage_page_app.
    { apply canonical_storage_page_repeat_zero. }
    unfold canonical_storage_page, normalize_storage_page_model in *.
    cbn [map]. now rewrite Hvalue, Hcanonical.
  }
  rewrite encode_slots_from_gap.
  replace (next + (Z.to_nat index - next)) with (Z.to_nat index) by lia.
  cbn [encode_slots_from].
  destruct (N.eq_dec value 0); [contradiction |].
  rewrite Hencoded, Z2Nat.id by lia.
  now rewrite Hbytes.
Qed.

Lemma decode_slots_from_encode fuel next index page :
  next <= index ->
  index + length page = page_slot_count ->
  length page <= fuel ->
  canonical_storage_page page ->
  decode_slots_from fuel next (encode_slots_from index page) =
  Result.Ok (repeat 0%N (index - next) ++ page).
Proof.
  revert fuel next index.
  induction page as [| value page IH];
    intros fuel next index Hnext Hwidth Hfuel Hcanonical.
  {
    cbn [encode_slots_from decode_slots_from length] in *.
    rewrite app_nil_r.
    replace index with page_slot_count by lia.
    destruct fuel; reflexivity.
  }
  assert (Hvalue : normalize_slot_model value = value).
  {
    unfold canonical_storage_page, normalize_storage_page_model in Hcanonical.
    cbn [map] in Hcanonical. now injection Hcanonical.
  }
  assert (Hrest : canonical_storage_page page).
  {
    unfold canonical_storage_page, normalize_storage_page_model in *.
    cbn [map] in Hcanonical. now injection Hcanonical.
  }
  cbn [encode_slots_from].
  destruct (N.eq_dec value 0) as [-> | Hnonzero].
  {
    rewrite (IH fuel next (S index)) by (cbn [length] in *; auto; lia).
    f_equal.
    replace (S index - next) with (S (index - next)) by lia.
    replace (S (index - next)) with ((index - next) + 1) by lia.
    rewrite repeat_app, <- app_assoc. reflexivity.
  }
  destruct fuel as [| fuel]; [cbn [length] in Hfuel; lia |].
  cbn [decode_slots_from].
  assert (Hlower : (Z.of_nat index <? Z.of_nat next)%Z = false)
    by (apply Z.ltb_ge; lia).
  assert (Hupper : (Z.of_nat page_slot_count <=? Z.of_nat index)%Z = false)
    by (apply Z.leb_gt; cbn [length] in Hwidth; lia).
  rewrite Hlower, Hupper.
  cbn [orb].
  rewrite rlp_decode_compact_result_encode_app, Hvalue, Nat2Z.id.
  destruct (N.eq_dec value 0); [contradiction |].
  rewrite (IH fuel (S index) (S index)) by (cbn [length] in *; auto; lia).
  rewrite Nat.sub_diag.
  reflexivity.
Qed.

(** ** Round Trip and Canonicality

    The first theorem preserves every slot value on encode/decode. The second
    rules out a different accepted byte string for the same page. Neither
    theorem assumes hash properties or C++ library specifications. *)
Theorem decode_encode_storage_page_result_model page :
  length page = page_slot_count ->
  canonical_storage_page page ->
  decode_storage_page_result_model (encode_storage_page_model page) =
  Result.Ok page.
Proof.
  intros Hlength Hcanonical.
  unfold decode_storage_page_result_model, encode_storage_page_model.
  exact (decode_slots_from_encode page_slot_count 0 0 page
    (Nat.le_refl 0) Hlength ltac:(lia) Hcanonical).
Qed.

Corollary decode_encode_storage_page_model page :
  length page = page_slot_count ->
  canonical_storage_page page ->
  decode_storage_page_model (encode_storage_page_model page) = Some page.
Proof.
  intros Hlength Hcanonical.
  unfold decode_storage_page_model.
  now rewrite decode_encode_storage_page_result_model.
Qed.

Theorem decode_storage_page_result_model_canonical_encoding bytes page :
  storage_encoded_bytes_in_range bytes ->
  decode_storage_page_result_model bytes = Result.Ok page ->
  encode_storage_page_model page = bytes.
Proof.
  intros Hrange Hdecode.
  exact (proj2 (proj2 (decode_slots_from_reencode page_slot_count 0 bytes page
    (Nat.le_0_l _) Hrange Hdecode))).
Qed.

Corollary decode_storage_page_model_canonical_encoding bytes page :
  storage_encoded_bytes_in_range bytes ->
  decode_storage_page_model bytes = Some page ->
  encode_storage_page_model page = bytes.
Proof.
  intros Hrange Hdecode.
  unfold decode_storage_page_model in Hdecode.
  destruct (decode_storage_page_result_model bytes) as [decoded | error]
    eqn:Hresult; cbn [Result.to_option] in Hdecode; [| discriminate].
  injection Hdecode as <-.
  eapply decode_storage_page_result_model_canonical_encoding; eassumption.
Qed.

(** ** Connection to the Decoder's Mutable Page

    The decoder writes each accepted pair into an initially empty page. Its
    invariant separates the completed prefix from the untouched zero suffix.
    Writing the next ordered index extends that prefix across a possibly
    empty gap; it cannot overwrite an earlier accepted pair. *)
Lemma decode_slots_from_empty fuel next :
  decode_slots_from fuel next [] =
  Result.Ok (repeat 0%N (page_slot_count - next)).
Proof. destruct fuel; reflexivity. Qed.

Lemma decode_storage_page_update_slot_gap prefix index value :
  length prefix <= index < page_slot_count ->
  decode_storage_page_update_slot index value
    (prefix ++ repeat 0%N (page_slot_count - length prefix)) =
  (prefix ++ repeat 0%N (index - length prefix) ++ [value]) ++
    repeat 0%N (page_slot_count - S index).
Proof.
  intro Hindex.
  replace (page_slot_count - length prefix) with
    ((index - length prefix) + S (page_slot_count - S index)) by lia.
  rewrite repeat_app, app_assoc.
  replace index with
    (length (prefix ++ repeat 0%N (index - length prefix))) at 1
    by (rewrite app_length, repeat_length; lia).
  cbn [repeat].
  rewrite decode_storage_page_update_slot_prefix.
  rewrite <- !app_assoc. reflexivity.
Qed.
