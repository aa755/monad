Set Default Goal Selector "!".

(** The encoder walks the set bits, whereas its public model walks the slots.
    A ghost page clears each emitted word. Its dense values are precisely the
    unread suffix of the original vector; its encoding is the output still
    owed. This file connects one bit-clearing iteration to that view. *)
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.lowest_offset.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.merge_scratch_level.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_set.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_ctor.
Require Import monad.proofs.execproofs.mip8.storage_page_encoding.
Require Import monad.proofs.execproofs.mip8.storage_page_indexed_encoding.
Import ListNotations.

Transparent lowest_offset_model countr_zero64.

Lemma lowest_offset_min_bit word index :
  (index < 128)%nat ->
  N.testbit word (N.of_nat index) = true ->
  (forall lower, (lower < index)%nat ->
    N.testbit word (N.of_nat lower) = false) ->
  lowest_offset_model word = N.of_nat index.
Proof.
  intros Hindex Hbit Hlower.
  unfold lowest_offset_model.
  rewrite N.land_ones.
  destruct (lt_dec index 64) as [Hlow | Hhigh].
  { assert (Hmasked :
        N.testbit (word mod 2 ^ 64) (N.of_nat index) = true).
    { rewrite N.mod_pow2_bits_low; [exact Hbit | lia]. }
    assert (Hnz : (word mod 2 ^ 64)%N <> 0%N).
    { intro Hz. rewrite Hz N.bits_0 in Hmasked. discriminate. }
    rewrite (proj2 (N.eqb_neq _ _) Hnz).
    unfold countr_zero64.
    apply countr_zero_fuel_min_bit; [exact Hlow | exact Hmasked |].
    intros lower Hlt.
    rewrite N.mod_pow2_bits_low; [apply Hlower; lia | lia].
  }
  assert (Hzero : (word mod 2 ^ 64)%N = 0%N).
  { apply N.bits_inj. intro bit. rewrite N.bits_0.
    destruct (N.lt_ge_cases bit 64) as [Hlt | Hge].
    { rewrite N.mod_pow2_bits_low; [|exact Hlt].
      rewrite <- (N2Nat.id bit). apply Hlower. lia. }
    apply N.mod_pow2_bits_high. exact Hge.
  }
  rewrite Hzero N.eqb_refl.
  assert (Hctz : countr_zero64 (N.shiftr word 64) = N.of_nat (index - 64)).
  { unfold countr_zero64. apply countr_zero_fuel_min_bit.
    { lia. }
    { rewrite N.shiftr_spec'.
      replace (N.of_nat (index - 64) + 64)%N with (N.of_nat index) by lia.
      exact Hbit. }
    intros lower Hlt. rewrite N.shiftr_spec'.
    replace (N.of_nat lower + 64)%N with (N.of_nat (lower + 64)) by lia.
    apply Hlower. lia.
  }
  rewrite Hctz. lia.
Qed.

Lemma dense_suffix_head (values rest : list N) dense value :
  skipn dense values = value :: rest ->
  (dense < length values)%nat /\ nth dense values 0%N = value /\
  skipn (S dense) values = rest.
Proof.
  intro Hsuffix.
  pose proof (f_equal (@length N) Hsuffix) as Hlen.
  rewrite length_skipn in Hlen. simpl in Hlen.
  split; [lia |]. split.
  { pose proof (f_equal (fun xs => nth 0 xs 0%N) Hsuffix) as Hhead.
    rewrite nth_skipn_add Nat.add_0_r in Hhead. exact Hhead. }
  pose proof (f_equal (skipn 1) Hsuffix) as Htail.
  rewrite skipn_skipn in Htail.
  replace (1 + dense)%nat with (S dense) in Htail by lia.
  exact Htail.
Qed.

Lemma indexed_bitmap_clear_cpp word :
  word <> 0%N -> (word < 2 ^ 128)%N ->
  trim 128 (Z.land (Z.of_N word) (trim 128 (Z.of_N word - 1))) =
  Z.of_N (N.land word (word - 1)).
Proof.
  intros Hnz Hbound.
  rewrite (to_unsigned_bits_id (Z.of_N word - 1) 128%N); [|lia].
  replace (Z.of_N word - 1)%Z with (Z.of_N (word - 1)) by lia.
  rewrite N2Z_land.
  apply to_unsigned_bits_id.
  pose proof (N.land_le_l word (word - 1)) as Hland. lia.
Qed.

Opaque lowest_offset_model countr_zero64 countr_zero_fuel.

Lemma split_first_nonzero (page : list N) :
  (exists index value rest,
    page = repeat 0%N index ++ value :: rest /\ value <> 0%N) \/
  page = repeat 0%N (length page).
Proof.
  induction page as [|value rest IH].
  { right. reflexivity. }
  destruct (BinNat.N.eq_dec value 0) as [-> | Hnz].
  { destruct IH as [(index & value & tail & -> & Hnz) | ->].
    { left. exists (S index), value, tail. split; [reflexivity | exact Hnz]. }
    right. simpl. now rewrite repeat_length.
  }
  left. exists 0%nat, value, rest. split; [reflexivity | exact Hnz].
Qed.

Lemma bitmap_zeroes index :
  slot_bitmap_word (repeat 0%N index) = 0%N.
Proof.
  unfold slot_bitmap_word. apply slot_bitmap_from_repeat_zero.
Qed.

Lemma first_word_bitmap index value rest :
  value <> 0%N ->
  N.testbit (slot_bitmap_word (repeat 0%N index ++ value :: rest))
    (N.of_nat index) = true /\
  (forall lower, (lower < index)%nat ->
    N.testbit (slot_bitmap_word (repeat 0%N index ++ value :: rest))
      (N.of_nat lower) = false).
Proof.
  intros Hnz. split.
  { rewrite storage_page_set_slot_bitmap_word_testbit Nat2N.id.
    rewrite app_nth2; [|rewrite repeat_length; lia].
    rewrite repeat_length Nat.sub_diag.
    unfold storage_page_slot_present. simpl.
    rewrite (proj2 (N.eqb_neq _ _) Hnz). reflexivity.
  }
  intros lower Hlt.
  rewrite storage_page_set_slot_bitmap_word_testbit Nat2N.id.
  rewrite app_nth1; [|rewrite repeat_length; lia].
  rewrite nth_repeat. reflexivity.
Qed.

Lemma clear_first_word index value rest :
  storage_page_update_slot index 0 (repeat 0%N index ++ value :: rest) =
  repeat 0%N (S index) ++ rest.
Proof.
  induction index as [|index IH].
  { reflexivity. }
  change (storage_page_update_slot (S index) 0
      (0%N :: (repeat 0%N index ++ value :: rest)) =
    repeat 0%N (S (S index)) ++ rest).
  rewrite storage_page_update_slot_cons_succ IH. reflexivity.
Qed.

Lemma dense_zero_prefix index rest :
  storage_page_dense_values (repeat 0%N index ++ rest) =
  storage_page_dense_values rest.
Proof.
  induction index as [|index IH]; [reflexivity |].
  change (storage_page_dense_values
    (0%N :: (repeat 0%N index ++ rest)) = storage_page_dense_values rest).
  unfold storage_page_dense_values in IH |- *.
  simpl. exact IH.
Qed.

Lemma indexed_encoding_bitmap_zero page :
  slot_bitmap_word page = 0%N ->
  encode_storage_page_model page = [] /\ storage_page_dense_values page = [].
Proof.
  intro Hzero.
  destruct (split_first_nonzero page) as [(index & value & rest & -> & Hnz) | Hempty].
  { pose proof (proj1 (first_word_bitmap index value rest Hnz)) as Hbit.
    rewrite Hzero N.bits_0 in Hbit. discriminate. }
  rewrite Hempty. split.
  { unfold encode_storage_page_model. apply encode_slots_from_zeroes. }
  rewrite <- (app_nil_r (repeat 0%N (length page))).
  rewrite dense_zero_prefix. reflexivity.
Qed.

Lemma indexed_encoding_step page :
  length page = page_slot_count ->
  slot_bitmap_word page <> 0%N ->
  exists (index : nat) (value : N) (remaining : list N),
    (index < page_slot_count)%nat /\ value <> 0%N /\
    length remaining = page_slot_count /\
    lowest_offset_model (slot_bitmap_word page) = N.of_nat index /\
    N.land (slot_bitmap_word page) (slot_bitmap_word page - 1) =
      slot_bitmap_word remaining /\
    storage_page_dense_values page = value :: storage_page_dense_values remaining /\
    encode_storage_page_model page =
      Z.of_nat index :: encode_slot_model value ++ encode_storage_page_model remaining.
Proof.
  intros Hlen Hnonzero.
  destruct (split_first_nonzero page) as [(index & value & rest & -> & Hnz) | Hempty].
  2: { rewrite Hempty bitmap_zeroes in Hnonzero. contradiction. }
  destruct (first_word_bitmap index value rest Hnz) as [Hbit Hlower].
  rewrite length_app repeat_length in Hlen. simpl in Hlen.
  exists index, value, (repeat 0%N (S index) ++ rest).
  split; [lia |]. split; [exact Hnz |].
  split; [rewrite length_app repeat_length; simpl; lia |].
  split.
  { apply lowest_offset_min_bit; [unfold page_slot_count in Hlen; lia | exact Hbit | exact Hlower]. }
  split.
  { rewrite (N_land_sub_one_clearbit_lowest_nat index _ Hbit Hlower).
    rewrite <- (clear_first_word index value rest).
    rewrite storage_page_set_slot_bitmap_word_update_clear; [reflexivity | |reflexivity].
    rewrite length_app repeat_length. simpl. lia.
  }
  split.
  { rewrite !dense_zero_prefix. unfold storage_page_dense_values.
    simpl. unfold storage_page_slot_present.
    rewrite (proj2 (N.eqb_neq _ _) Hnz). reflexivity.
  }
  unfold encode_storage_page_model.
  rewrite !encode_slots_from_gap.
  cbn [Nat.add encode_slots_from].
  destruct (BinNat.N.eq_dec value 0); [contradiction | reflexivity].
Qed.
