Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.

Section Pure.
  Lemma bitmap_to_N_testbit bm offset :
    (offset < length bm)%nat ->
    N.testbit (bitmap_to_N bm) (N.of_nat offset) =
    nth offset bm false.
  Proof.
    revert offset.
    induction bm as [| bit rest IH]; intros [| offset] Hoffset.
    {
      cbn in Hoffset.
      lia.
    }
    {
      cbn in Hoffset.
      lia.
    }
    {
      cbn [bitmap_to_N nth].
      change (N.of_nat 0) with 0%N.
      replace
        ((if bit then 1 else 0) + 2 * bitmap_to_N rest)%N
        with (2 * bitmap_to_N rest + N.b2n bit)%N
        by (destruct bit; cbn; lia).
      rewrite N.testbit_0_r.
      reflexivity.
    }
    {
      cbn [bitmap_to_N nth].
      replace (N.of_nat (S offset))
        with (N.succ (N.of_nat offset)) by lia.
      replace
        ((if bit then 1 else 0) + 2 * bitmap_to_N rest)%N
        with (2 * bitmap_to_N rest + N.b2n bit)%N
        by (destruct bit; cbn; lia).
      rewrite N.testbit_succ_r.
      apply IH.
      cbn in Hoffset.
      lia.
    }
  Qed.

  Lemma page_slots_model_present page :
    map slot_present (page_slots_model page) =
    map storage_page_slot_present page.
  Proof.
    induction page as [| slot rest IH]; cbn.
    {
      reflexivity.
    }
    {
      unfold page_slot_value_model, slot_present,
        storage_page_slot_present.
      destruct (N.eq_dec slot 0%N) as [Hzero | Hnonzero].
      {
        subst slot.
        cbn.
        f_equal.
        exact IH.
      }
      {
        cbn.
        destruct (slot =? 0)%N eqn:Hslot_zero.
        {
          apply N.eqb_eq in Hslot_zero.
          contradiction.
        }
        f_equal.
        exact IH.
      }
    }
  Qed.

  Lemma slot_bitmap_word_has_slot_testbit page offset :
    (offset < length page)%nat ->
    N.testbit (slot_bitmap_word page) (N.of_nat offset) =
    storage_page_has_slot page offset.
  Proof.
    intro Hoffset.
    rewrite slot_bitmap_word_page_slots_model.
    rewrite bitmap_to_N_testbit.
    2: {
      rewrite length_map.
      rewrite page_slots_model_length.
      exact Hoffset.
    }
    rewrite page_slots_model_present.
    unfold storage_page_has_slot.
    change false with (storage_page_slot_present 0%N).
    rewrite map_nth.
    reflexivity.
  Qed.

  Lemma storage_page_has_slot_machine_bit page i :
    length page = page_slot_count ->
    (0 <= i < page_slot_count)%Z ->
    asbool
      (trim 128 (Z.of_N (slot_bitmap_word page) ≫ i) `land` 1 <> 0) =
    storage_page_has_slot page (Z.to_nat i).
  Proof.
    intros Hlen Hi.
    rewrite bool_decide_land_one_odd.
    rewrite modulo.trim_pos_odd.
    2: {
      lia.
    }
    rewrite <- (Z.testbit_odd (Z.of_N (slot_bitmap_word page)) i).
    rewrite Z.testbit_of_N'.
    2: {
      lia.
    }
    replace (Z.to_N i) with (N.of_nat (Z.to_nat i)) by lia.
    apply slot_bitmap_word_has_slot_testbit.
    rewrite Hlen.
    lia.
  Qed.
End Pure.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve
    observeStoragePageLength_F : sl_opacity.

  Lemma prf_storage_page_has_bit :
    verify[source] storage_page_has_bit_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    rewrite /StoragePageR.
    go.
    eapply coq_tactics.tac_pure_intro.
    { apply _. }
    { apply _. }
    {
      apply storage_page_has_slot_machine_bit.
      {
        assumption.
      }
      {
        lia.
      }
    }
  Qed.
End with_Sigma.
