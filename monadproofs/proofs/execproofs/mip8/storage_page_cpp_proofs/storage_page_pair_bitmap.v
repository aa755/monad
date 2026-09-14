Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.

#[local] Open Scope N_scope.

Lemma pext_even_fuel_testbit fuel word bit :
  N.testbit (pext_even_fuel fuel word) bit =
  if (bit <? N.of_nat fuel)%N
  then N.testbit word (2 * bit)%N
  else false.
Proof.
  revert word bit.
  induction fuel as [| fuel IH]; intros word bit.
  {
    simpl.
    destruct (bit <? 0)%N eqn:Hlt; [| reflexivity].
    apply N.ltb_lt in Hlt.
    lia.
  }
  destruct (N.eq_dec bit 0) as [Hbit | Hbit].
  {
    subst bit.
    simpl.
    change (2 * 0)%N with 0%N.
    destruct (N.odd word) eqn:Hodd.
    {
      change (N.b2n true) with 1%N.
      replace (1 + 2 * pext_even_fuel fuel (N.shiftr word 2))%N with (2 * pext_even_fuel fuel (N.shiftr word 2) + 1)%N by lia.
      rewrite N.testbit_odd_0.
      replace (0 <? N.pos (Pos.of_succ_nat fuel))%N
        with true by (symmetry; apply N.ltb_lt; lia).
      rewrite N.bit0_odd.
      rewrite Hodd.
      reflexivity.
    }
    change (N.b2n false) with 0%N.
    change (0 + 2 * pext_even_fuel fuel (N.shiftr word 2))%N with (2 * pext_even_fuel fuel (N.shiftr word 2))%N.
    rewrite N.testbit_even_0.
    replace (0 <? N.pos (Pos.of_succ_nat fuel))%N
      with true by (symmetry; apply N.ltb_lt; lia).
    rewrite N.bit0_odd.
    rewrite Hodd.
    reflexivity.
  }
  replace bit with (N.succ (N.pred bit)) by lia.
  simpl.
  replace
    (N.b2n (N.odd word) +
     2 * pext_even_fuel fuel (N.shiftr word 2))%N
    with
    (2 * pext_even_fuel fuel (N.shiftr word 2) +
     N.b2n (N.odd word))%N by lia.
  rewrite N.testbit_succ_r.
  rewrite IH.
  rewrite N.shiftr_spec'.
  replace
    (N.pred bit <? N.of_nat fuel)%N
    with
    (bit <? N.pos (Pos.of_succ_nat fuel))%N.
  2: {
    destruct (N.pred bit <? N.of_nat fuel)%N eqn:Hlt.
    {
      apply N.ltb_lt in Hlt.
      destruct (bit <? N.pos (Pos.of_succ_nat fuel))%N eqn:Hlt';
        [reflexivity |].
      apply N.ltb_ge in Hlt'.
      replace (N.pos (Pos.of_succ_nat fuel))
        with (N.succ (N.of_nat fuel)) in Hlt' by lia.
      lia.
    }
    apply N.ltb_ge in Hlt.
    destruct (bit <? N.pos (Pos.of_succ_nat fuel))%N eqn:Hlt';
      [| reflexivity].
    apply N.ltb_lt in Hlt'.
    replace (N.pos (Pos.of_succ_nat fuel))
      with (N.succ (N.of_nat fuel)) in Hlt' by lia.
    lia.
  }
  replace (N.succ (N.pred bit)) with bit by lia.
  destruct (bit <? N.pos (Pos.of_succ_nat fuel))%N;
    [| reflexivity].
  replace (2 * N.pred bit + 2)%N
    with (2 * bit)%N by lia.
  reflexivity.
Qed.

Lemma pext_even64_testbit word bit :
  N.testbit (pext_even64 word) bit =
  if (bit <? 32)%N
  then N.testbit word (2 * bit)%N
  else false.
Proof.
  unfold pext_even64.
  rewrite pext_even_fuel_testbit.
  reflexivity.
Qed.

Lemma pair_bit_mask_testbit index bit :
  N.testbit (pair_bit_mask index) bit =
  (N.of_nat index =? bit)%N.
Proof.
  unfold pair_bit_mask.
  apply N.pow2_bits_eqb.
Qed.

Lemma N_testbit_3_high bit :
  (2 <= bit)%N ->
  N.testbit 3 bit = false.
Proof.
  intro Hbit.
  apply N.bits_above_log2.
  change (N.log2 3) with 1%N.
  lia.
Qed.

Lemma pair_slot_mask_testbit_true_low index :
  N.testbit
    (pair_slot_mask index)
    (2 * N.of_nat index)%N = true.
Proof.
  unfold pair_slot_mask.
  replace (2 * N.of_nat index)%N
    with (0 + 2 * N.of_nat index)%N by lia.
  rewrite N.mul_pow2_bits_add.
  reflexivity.
Qed.

Lemma pair_slot_mask_testbit_true_high index :
  N.testbit
    (pair_slot_mask index)
    (2 * N.of_nat index + 1)%N = true.
Proof.
  unfold pair_slot_mask.
  replace (2 * N.of_nat index + 1)%N
    with (1 + 2 * N.of_nat index)%N by lia.
  rewrite N.mul_pow2_bits_add.
  reflexivity.
Qed.

Lemma pair_slot_mask_testbit_other index bit :
  bit <> (2 * N.of_nat index)%N ->
  bit <> (2 * N.of_nat index + 1)%N ->
  N.testbit (pair_slot_mask index) bit = false.
Proof.
  intros Hlow Hhigh.
  unfold pair_slot_mask.
  destruct (bit <? 2 * N.of_nat index)%N eqn:Hlt.
  {
    apply N.ltb_lt in Hlt.
    now rewrite N.mul_pow2_bits_low.
  }
  apply N.ltb_ge in Hlt.
  rewrite N.mul_pow2_bits_high.
  2: {
    exact Hlt.
  }
  apply N_testbit_3_high.
  lia.
Qed.

Lemma pair_slot_mask_occupied_bit word index :
  negb
    (N.eqb
       (N.land word (pair_slot_mask index))
       0) =
  (N.testbit word (2 * N.of_nat index)%N ||
   N.testbit word (2 * N.of_nat index + 1)%N).
Proof.
  destruct (N.testbit word (2 * N.of_nat index)%N) eqn:Hlow;
    destruct (N.testbit word (2 * N.of_nat index + 1)%N) eqn:Hhigh;
    simpl.
  all: unfold pair_slot_mask at 1.
  all: fold (pair_slot_mask index).
  all: destruct
    (N.eqb (N.land word (pair_slot_mask index)) 0) eqn:Hland;
    try reflexivity.
  all: try
    (apply N.eqb_eq in Hland;
     pose proof
       (f_equal
          (fun value =>
             N.testbit value (2 * N.of_nat index)%N)
          Hland) as Htest;
     rewrite N.land_spec in Htest;
     rewrite pair_slot_mask_testbit_true_low in Htest;
     rewrite Bool.andb_true_r in Htest;
     rewrite Hlow in Htest;
     discriminate).
  all: try
    (apply N.eqb_eq in Hland;
     pose proof
       (f_equal
          (fun value =>
             N.testbit value (2 * N.of_nat index + 1)%N)
          Hland) as Htest;
     rewrite N.land_spec in Htest;
     rewrite pair_slot_mask_testbit_true_high in Htest;
     rewrite Bool.andb_true_r in Htest;
     rewrite Hhigh in Htest;
     discriminate).
  assert (Hzero : N.land word (pair_slot_mask index) = 0%N).
  {
    apply N.bits_inj_0.
    intro bit.
    rewrite N.land_spec.
    destruct (N.eq_dec bit (2 * N.of_nat index)%N) as [Heq | Hneq].
    { subst bit. now rewrite Hlow. }
    destruct (N.eq_dec bit (2 * N.of_nat index + 1)%N) as [Heq | Hneq'].
    { subst bit. now rewrite Hhigh. }
    rewrite pair_slot_mask_testbit_other.
    2: {
      exact Hneq.
    }
    2: {
      exact Hneq'.
    }
    now rewrite Bool.andb_false_r.
  }
  rewrite Hzero in Hland.
  rewrite N.eqb_refl in Hland.
  discriminate.
Qed.

Lemma pair_bitmap_prefix_testbit fuel slot_bitmap bit :
  N.testbit (pair_bitmap_prefix fuel slot_bitmap) bit =
  if (bit <? N.of_nat fuel)%N
  then
    negb
      (N.eqb
         (N.land slot_bitmap
            (pair_slot_mask (N.to_nat bit)))
         0)
  else false.
Proof.
  revert bit.
  induction fuel as [| fuel IH]; intro bit.
  {
    simpl.
    destruct (bit <? 0)%N eqn:Hlt; [| reflexivity].
    apply N.ltb_lt in Hlt.
    lia.
  }
  simpl.
  destruct
    (N.eqb
       (N.land slot_bitmap (pair_slot_mask fuel))
       0) eqn:Hoccupied.
  {
    rewrite IH.
    destruct (bit <? N.of_nat fuel)%N eqn:Hlt_fuel.
    {
      apply N.ltb_lt in Hlt_fuel.
      replace (bit <? N.pos (Pos.of_succ_nat fuel))%N
        with true.
      2: {
        symmetry.
        apply N.ltb_lt.
        replace (N.pos (Pos.of_succ_nat fuel))
          with (N.succ (N.of_nat fuel)) by lia.
        lia.
      }
      reflexivity.
    }
    apply N.ltb_ge in Hlt_fuel.
    destruct (N.eq_dec bit (N.of_nat fuel)) as [Heq | Hneq].
    {
      subst bit.
      rewrite Nat2N.id.
      rewrite Hoccupied.
      replace (N.of_nat fuel <? N.pos (Pos.of_succ_nat fuel))%N
        with true.
      2: {
        symmetry.
        apply N.ltb_lt.
        replace (N.pos (Pos.of_succ_nat fuel))
          with (N.succ (N.of_nat fuel)) by lia.
        lia.
      }
      reflexivity.
    }
    replace (bit <? N.pos (Pos.of_succ_nat fuel))%N
      with false.
    2: {
      symmetry.
      apply N.ltb_ge.
      replace (N.pos (Pos.of_succ_nat fuel))
        with (N.succ (N.of_nat fuel)) by lia.
      lia.
    }
    reflexivity.
  }
  rewrite N.lor_spec.
  rewrite IH.
  rewrite pair_bit_mask_testbit.
  destruct (bit <? N.of_nat fuel)%N eqn:Hlt_fuel.
  {
    apply N.ltb_lt in Hlt_fuel.
    replace (N.of_nat fuel =? bit)%N with false
      by (symmetry; apply N.eqb_neq; lia).
    rewrite Bool.orb_false_r.
    replace (bit <? N.pos (Pos.of_succ_nat fuel))%N
      with true.
    2: {
      symmetry.
      apply N.ltb_lt.
      replace (N.pos (Pos.of_succ_nat fuel))
        with (N.succ (N.of_nat fuel)) by lia.
      lia.
    }
    reflexivity.
  }
  apply N.ltb_ge in Hlt_fuel.
  destruct (N.eq_dec bit (N.of_nat fuel)) as [Heq | Hneq].
  {
    subst bit.
    rewrite N.eqb_refl.
    rewrite Bool.orb_true_r.
    rewrite Nat2N.id.
    rewrite Hoccupied.
    replace (N.of_nat fuel <? N.pos (Pos.of_succ_nat fuel))%N
      with true.
    2: {
      symmetry.
      apply N.ltb_lt.
      replace (N.pos (Pos.of_succ_nat fuel))
        with (N.succ (N.of_nat fuel)) by lia.
      lia.
    }
    reflexivity.
  }
  replace (N.of_nat fuel =? bit)%N with false
    by (symmetry; apply N.eqb_neq; lia).
  rewrite Bool.orb_false_r.
  replace (bit <? N.pos (Pos.of_succ_nat fuel))%N
    with false.
  2: {
    symmetry.
    apply N.ltb_ge.
    replace (N.pos (Pos.of_succ_nat fuel))
      with (N.succ (N.of_nat fuel)) by lia.
    lia.
  }
  reflexivity.
Qed.

Definition storage_pair_bitmap_pext_word (slot_bitmap : N) : N :=
  let lo := (slot_bitmap mod (2 ^ 64))%N in
  let hi := N.shiftr slot_bitmap 64 in
  N.lor
    (pext_even64 (N.lor lo (N.shiftr lo 1)))
    (N.shiftl (pext_even64 (N.lor hi (N.shiftr hi 1))) 32).

Lemma storage_pair_bitmap_pext_word_correct slot_bitmap :
  storage_pair_bitmap_pext_word slot_bitmap =
  pair_bitmap_word slot_bitmap.
Proof.
  apply N.bits_inj.
  intro bit.
  unfold storage_pair_bitmap_pext_word, pair_bitmap_word.
  rewrite pair_bitmap_prefix_testbit.
  rewrite N.lor_spec.
  rewrite pext_even64_testbit.
  destruct (bit <? 32)%N eqn:Hbit32.
  {
    apply N.ltb_lt in Hbit32.
    rewrite N.shiftl_spec_low.
    2: {
      lia.
    }
    rewrite Bool.orb_false_r.
    rewrite N.lor_spec.
    rewrite N.mod_pow2_bits_low.
    2: {
      lia.
    }
    rewrite N.shiftr_spec'.
    rewrite N.mod_pow2_bits_low.
    2: {
      lia.
    }
    rewrite pair_slot_mask_occupied_bit.
    rewrite !N2Nat.id.
    replace (bit <? N.of_nat page_pair_count)%N with true.
    2: {
      symmetry.
      apply N.ltb_lt.
      unfold page_pair_count.
      lia.
    }
    reflexivity.
  }
  apply N.ltb_ge in Hbit32.
  rewrite N.shiftl_spec_high'.
  2: {
    lia.
  }
  rewrite pext_even64_testbit.
  destruct (bit <? 64)%N eqn:Hbit64.
  {
    apply N.ltb_lt in Hbit64.
    replace (bit - 32 <? 32)%N with true.
    2: {
      symmetry.
      apply N.ltb_lt.
      lia.
    }
    rewrite N.lor_spec.
    rewrite N.shiftr_spec'.
    rewrite N.shiftr_spec'.
    rewrite N.shiftr_spec'.
    rewrite pair_slot_mask_occupied_bit.
    replace (bit <? N.of_nat page_pair_count)%N with true.
    2: {
      symmetry.
      apply N.ltb_lt.
      unfold page_pair_count.
      lia.
    }
    rewrite !N2Nat.id.
    replace (2 * (bit - 32) + 64)%N
      with (2 * bit)%N by lia.
    replace (2 * (bit - 32) + 1 + 64)%N
      with (2 * bit + 1)%N by lia.
    reflexivity.
  }
  apply N.ltb_ge in Hbit64.
  replace (bit - 32 <? 32)%N with false.
  2: {
    symmetry.
    apply N.ltb_ge.
    lia.
  }
  rewrite Bool.orb_false_r.
  replace (bit <? N.of_nat page_pair_count)%N with false.
  2: {
    symmetry.
    apply N.ltb_ge.
    unfold page_pair_count.
    exact Hbit64.
  }
  reflexivity.
Qed.

Lemma trim64_of_N word :
  trim 64 (Z.of_N word) =
  Z.of_N (word mod 2 ^ 64).
Proof.
  unfold trim.
  rewrite N2Z.inj_mod; lia.
Qed.

Lemma shiftr1_lt_2_64 word :
  (word < 2 ^ 64)%N ->
  (word ≫ 1 < 2 ^ 64)%N.
Proof.
  intros Hword.
  destruct word as [| word].
  {
    rewrite N.shiftr_0_l.
    lia.
  }
  apply N.lt_le_trans with (N.pos word).
  2: {
    lia.
  }
  rewrite N.shiftr_div_pow2.
  change (2 ^ 1)%N with 2%N.
  apply N.div_lt; lia.
Qed.

Lemma trim64_shiftr1_of_N word :
  trim 64 (trim 64 (Z.of_N word) ≫ 1) =
  Z.of_N ((word mod 2 ^ 64) ≫ 1).
Proof.
  rewrite trim64_of_N.
  rewrite <- N2Z_shiftr.
  unfold trim.
  rewrite Z.mod_small.
  {
    reflexivity.
  }
  split.
  {
    apply Z.shiftr_nonneg.
    lia.
  }
  pose proof
    (shiftr1_lt_2_64
       (word mod 2 ^ 64)
       ltac:(apply N.mod_upper_bound; lia)).
  change 1%Z with (Z.of_N 1%N).
  rewrite N2Z_shiftr.
  change (2 ^ 64%N)%Z with (Z.of_N (2 ^ 64)).
  now apply (proj1 (N2Z.inj_lt _ _)).
Qed.

Lemma trim64_shiftr1_small word :
  (word < 2 ^ 64)%N ->
  trim 64 (Z.of_N word ≫ 1) =
  Z.of_N (word ≫ 1).
Proof.
  intro Hword.
  rewrite <- N2Z_shiftr.
  unfold trim.
  rewrite Z.mod_small.
  {
    reflexivity.
  }
  split.
  {
    apply Z.shiftr_nonneg.
    lia.
  }
  change 1%Z with (Z.of_N 1%N).
  rewrite N2Z_shiftr.
  change (2 ^ 64%N)%Z with (Z.of_N (2 ^ 64)).
  apply (proj1 (N2Z.inj_lt _ _)).
  now apply shiftr1_lt_2_64.
Qed.

Lemma pext_low_input_cpp_Z word :
  (trim 64 (Z.of_N word)
   `lor` trim 64 (trim 64 (Z.of_N word) ≫ 1))%Z =
  Z.of_N
    (word mod 2 ^ 64 `lor` (word mod 2 ^ 64) ≫ 1).
Proof.
  rewrite trim64_shiftr1_of_N.
  rewrite trim64_of_N.
  rewrite N2Z_lor.
  reflexivity.
Qed.

Lemma pext_low_input_cpp word :
  Z.to_N
    (trim 64 (Z.of_N word)
     `lor` trim 64 (trim 64 (Z.of_N word) ≫ 1)) =
  (word mod 2 ^ 64 `lor` (word mod 2 ^ 64) ≫ 1)%N.
Proof.
  rewrite pext_low_input_cpp_Z.
  rewrite N2Z.id.
  reflexivity.
Qed.

Lemma shiftr64_lt_2_64 word :
  (word < 2 ^ 128)%N ->
  (word ≫ 64 < 2 ^ 64)%N.
Proof.
  intro Hword.
  rewrite N.shiftr_div_pow2.
  apply N.div_lt_upper_bound; lia.
Qed.

Lemma trim64_shiftr64_of_N word :
  (word < 2 ^ 128)%N ->
  trim 64 (Z.of_N word ≫ 64) =
  Z.of_N (word ≫ 64).
Proof.
  intro Hword.
  rewrite Z_of_N_shiftr.
  2: {
    lia.
  }
  unfold trim.
  rewrite Z.mod_small.
  {
    reflexivity.
  }
  split.
  {
    lia.
  }
  change (2 ^ 64%N)%Z with (Z.of_N (2 ^ 64)).
  apply (proj1 (N2Z.inj_lt _ _)).
  now apply shiftr64_lt_2_64.
Qed.

Lemma pext_high_input_cpp_Z word :
  (word < 2 ^ 128)%N ->
  (trim 64 (Z.of_N word ≫ 64)
   `lor`
   trim 64 (trim 64 (Z.of_N word ≫ 64) ≫ 1))%Z =
  Z.of_N (word ≫ 64 `lor` (word ≫ 64) ≫ 1).
Proof.
  intro Hword.
  rewrite (trim64_shiftr64_of_N word Hword).
  rewrite
    (trim64_shiftr1_small
       (word ≫ 64)
       (shiftr64_lt_2_64 word Hword)).
  rewrite N2Z_lor.
  reflexivity.
Qed.

Lemma pext_high_input_cpp word :
  (word < 2 ^ 128)%N ->
  Z.to_N
    (trim 64 (Z.of_N word ≫ 64)
     `lor`
     trim 64 (trim 64 (Z.of_N word ≫ 64) ≫ 1)) =
  (word ≫ 64 `lor` (word ≫ 64) ≫ 1)%N.
Proof.
  intro Hword.
  rewrite (pext_high_input_cpp_Z word Hword).
  rewrite N2Z.id.
  reflexivity.
Qed.

Lemma pext_even64_bound32 word :
  pext_even64 word < 2 ^ 32.
Proof.
  unfold pext_even64.
  pose proof (pext_even_fuel_bound 32 word) as Hbound.
  change (N.of_nat 32) with 32%N in Hbound.
  exact Hbound.
Qed.

Lemma trim64_shiftl32_of_N word :
  (word < 2 ^ 32)%N ->
  trim 64 (Z.of_N word ≪ 32) =
  Z.of_N (word ≪ 32).
Proof.
  intro Hword.
  rewrite <- N2Z_shiftl.
  unfold trim.
  rewrite Z.mod_small.
  {
    reflexivity.
  }
  split.
  {
    apply Z.shiftl_nonneg.
    lia.
  }
  change 32%Z with (Z.of_N 32%N).
  rewrite N2Z_shiftl.
  change (2 ^ 64%N)%Z with (Z.of_N (2 ^ 64)).
  apply (proj1 (N2Z.inj_lt _ _)).
  rewrite N.shiftl_mul_pow2.
  nia.
Qed.

Lemma pair_bitmap_return_cpp_Z lo hi :
  (hi < 2 ^ 32)%N ->
  (Z.of_N lo `lor` trim 64 (Z.of_N hi ≪ 32))%Z =
  Z.of_N (lo `lor` hi ≪ 32).
Proof.
  intro Hhi.
  rewrite (trim64_shiftl32_of_N hi Hhi).
  rewrite N2Z_lor.
  reflexivity.
Qed.

Lemma pair_bitmap_return_cpp_Z_coe (lo hi : N) :
  (hi < 2 ^ 32)%N ->
  (lo `lor` trim 64 (hi ≪ 32))%Z =
  Z.of_N (lo `lor` hi ≪ 32).
Proof.
  apply pair_bitmap_return_cpp_Z.
Qed.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve
    UNSAFE_read_prim_cancel : sl_opacity.
  #[local] Hint Opaque
    pair_bitmap_word pair_bitmap_prefix
    pext_fuel pext64 pext_even_mask_fuel pext_even_fuel pext_even64
    : sl_opacity.
  Opaque
    pair_bitmap_word pair_bitmap_prefix
    pext_fuel pext64 pext_even_mask_fuel pext_even_fuel pext_even64.

  Lemma prf_storage_page_pair_bitmap :
    verify[source] storage_page_pair_bitmap_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    pose proof
      (storage_pair_bitmap_pext_word_correct
         (slot_bitmap_word page)) as Hpext.
    unfold storage_pair_bitmap_pext_word in Hpext.
    rewrite /StoragePageR.
    do 44 run1 using pext_u64_spec.
    rewrite pext_low_input_cpp.
    rewrite pext64_even_mask.
    repeat match goal with
    | H : context[pext64 _ _] |- _ => clear H
    end.
    match goal with
    | Hlen : length page = page_slot_count |- _ =>
        pose proof (slot_bitmap_word_lt_128 page Hlen)
          as Hslot_bitmap_lt
    end.
    change (slot_bitmap_word page < 2 ^ 128)%N
      in Hslot_bitmap_lt.
    rewrite
      (pext_high_input_cpp_Z
         (slot_bitmap_word page)
         Hslot_bitmap_lt).
    run1 using pext_u64_spec.
    rewrite pext64_even_mask.
    repeat match goal with
    | H : context[pext64 _ _] |- _ => clear H
    end.
    do 8 run1.
    rewrite
      (pair_bitmap_return_cpp_Z_coe
         (pext_even64
            (slot_bitmap_word page mod 2 ^ 64
             `lor` (slot_bitmap_word page mod 2 ^ 64) ≫ 1))
         (pext_even64
            (slot_bitmap_word page ≫ 64
             `lor` (slot_bitmap_word page ≫ 64) ≫ 1))
         (pext_even64_bound32 _)).
    rewrite Hpext.
    go.
  Qed.
End with_Sigma.
