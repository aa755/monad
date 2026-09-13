Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_has_bit.

Lemma dense_index_popcount_fuel_le fuel word :
  popcount_fuel fuel word <= N.of_nat fuel.
Proof.
  revert word.
  induction fuel as [| fuel IH]; intro word; simpl.
  {
    lia.
  }
  destruct (N.odd word);
    specialize (IH (N.shiftr word 1)); simpl; lia.
Qed.

Lemma dense_index_popcount64_int_bound word :
  bitsize.bound (int_rank.bitsize int_rank.Iint) Signed
    (Z.of_N (popcount64 word)).
Proof.
  pose proof (dense_index_popcount_fuel_le 64 word).
  unfold popcount64 in *.
  change (bitsize.bound (int_rank.bitsize int_rank.Iint)
            Signed (Z.of_N (popcount_fuel 64 word)))
    with (-2147483648 <= Z.of_N (popcount_fuel 64 word)
          <= 2147483647)%Z.
  lia.
Qed.

Definition count_true (bm : list bool) : nat :=
  length (List.filter (fun bit => bit) bm).

Lemma popcount_fuel_zero fuel :
  popcount_fuel fuel 0 = 0%N.
Proof.
  induction fuel as [| fuel IH].
  {
    reflexivity.
  }
  {
    cbn.
    rewrite N.shiftr_0_l.
    exact IH.
  }
Qed.

Lemma bitmap_to_N_cons_odd (bit : bool) (rest : list bool) :
  N.odd ((if bit then 1 else 0) + 2 * bitmap_to_N rest)%N = bit.
Proof.
  destruct bit.
  {
    replace (1 + 2 * bitmap_to_N rest)%N
      with (2 * bitmap_to_N rest + 1)%N by lia.
    apply N.odd_odd.
  }
  {
    change ((0 + 2 * bitmap_to_N rest)%N)
      with (2 * bitmap_to_N rest)%N.
    apply N.odd_even.
  }
Qed.

Lemma bitmap_to_N_cons_shiftr (bit : bool) (rest : list bool) :
  (((if bit then 1 else 0) + 2 * bitmap_to_N rest) ≫ 1 =
   bitmap_to_N rest)%N.
Proof.
  change 1%N with (N.succ 0%N).
  rewrite N.shiftr_succ_r.
  rewrite N.shiftr_0_r.
  destruct bit.
  {
    replace (N.succ 0 + 2 * bitmap_to_N rest)%N
      with (2 * bitmap_to_N rest + 1)%N by lia.
    apply N.div2_odd'.
  }
  {
    change ((0 + 2 * bitmap_to_N rest)%N)
      with (2 * bitmap_to_N rest)%N.
    apply N.div2_even.
  }
Qed.

Lemma popcount_fuel_bitmap_to_N fuel bm :
  (length bm <= fuel)%nat ->
  popcount_fuel fuel (bitmap_to_N bm) =
  N.of_nat (count_true bm).
Proof.
  revert fuel.
  induction bm as [| bit rest IH]; intros [| fuel] Hfuel.
  {
    reflexivity.
  }
  {
    rewrite popcount_fuel_zero.
    reflexivity.
  }
  {
    cbn in Hfuel.
    lia.
  }
  {
    unfold count_true in *.
    cbn [bitmap_to_N popcount_fuel List.filter length].
    rewrite bitmap_to_N_cons_odd.
    rewrite bitmap_to_N_cons_shiftr.
    assert (Hrest : (length rest <= fuel)%nat) by (cbn in Hfuel; lia).
    rewrite (IH fuel Hrest).
    destruct bit; cbn; lia.
  }
Qed.

Lemma popcount64_bitmap_to_N bm :
  (length bm <= 64)%nat ->
  popcount64 (bitmap_to_N bm) =
  N.of_nat (count_true bm).
Proof.
  intro Hlen.
  unfold popcount64.
  apply popcount_fuel_bitmap_to_N.
  exact Hlen.
Qed.

Lemma bitmap_to_N_app lhs rhs :
  bitmap_to_N (lhs ++ rhs) =
  (bitmap_to_N lhs +
   2 ^ N.of_nat (length lhs) * bitmap_to_N rhs)%N.
Proof.
  induction lhs as [| bit lhs IH].
  {
    rewrite app_nil_l.
    cbn [bitmap_to_N length].
    nia.
  }
  {
    change ((bit :: lhs) ++ rhs) with (bit :: lhs ++ rhs).
    cbn [bitmap_to_N length].
    rewrite IH.
    rewrite Nat2N.inj_succ.
    rewrite N.pow_succ_r'.
    nia.
  }
Qed.

Lemma bitmap_to_N_land_ones_firstn bm n :
  (Z.of_N (bitmap_to_N bm) `land` Z.ones (Z.of_nat n))%Z =
  Z.of_N (bitmap_to_N (firstn n bm)).
Proof.
  destruct (Nat.leb_spec n (length bm)) as [Hn | Hn].
  2: {
    rewrite firstn_all2.
    2: {
      lia.
    }
    rewrite Z.land_ones.
    2: {
      lia.
    }
    rewrite Z.mod_small.
    {
      reflexivity.
    }
    {
      pose proof (bitmap_to_N_lt_length bm).
      pose proof (proj1 (N2Z.inj_lt _ _) H) as HZ.
      split.
      {
        lia.
      }
      {
        eapply Z.lt_le_trans.
        {
          exact HZ.
        }
        change
          (Z.of_N (2 ^ N.of_nat (length bm)) <=
           2 ^ Z.of_nat n)%Z.
        rewrite N2Z.inj_pow.
        change (Z.of_N 2) with 2%Z.
        apply Z.pow_le_mono_r; lia.
      }
    }
  }
  rewrite <- (firstn_skipn n bm) at 1.
  rewrite bitmap_to_N_app.
  rewrite Z.land_ones.
  2: {
    lia.
  }
  rewrite N2Z.inj_add.
  rewrite N2Z.inj_mul.
  rewrite N2Z.inj_pow.
  change (Z.of_N 2) with 2%Z.
  rewrite nat_N_Z.
  rewrite firstn_length_le.
  2: {
    exact Hn.
  }
  replace
    (2 ^ Z.of_nat n * Z.of_N (bitmap_to_N (skipn n bm)))%Z
    with
    (Z.of_N (bitmap_to_N (skipn n bm)) * 2 ^ Z.of_nat n)%Z
    by lia.
  rewrite
    (Z_mod_plus_full
       (Z.of_N (bitmap_to_N (firstn n bm)))
       (Z.of_N (bitmap_to_N (skipn n bm)))
       (2 ^ Z.of_nat n)).
  rewrite Z.mod_small.
  {
    reflexivity.
  }
  {
    pose proof (bitmap_to_N_lt_length (firstn n bm)).
    pose proof (proj1 (N2Z.inj_lt _ _) H) as HZ.
    rewrite firstn_length_le in HZ.
    2: {
      exact Hn.
    }
    lia.
  }
Qed.

Lemma dense_index_mask_ones i :
  (0 <= i < page_slot_count)%Z ->
  trim 128 (1 ≪ i - 1) = Z.ones i.
Proof.
  intro Hi.
  rewrite Z.shiftl_1_l.
  rewrite Z_ones_pow2.
  apply to_unsigned_bits_id.
  change (2 ^ 128%N) with (2 ^ 128)%Z.
  split.
  {
    pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) ltac:(lia)).
    lia.
  }
  {
    change (Z.of_nat page_slot_count) with 128%Z in Hi.
    assert (Hpow : (2 ^ i < 2 ^ 128%Z)%Z).
    {
      apply Z.pow_lt_mono_r; lia.
    }
    lia.
  }
Qed.

Lemma bitmap_to_N_low64 bm :
  Z.to_N (trim 64 (Z.of_N (bitmap_to_N bm))) =
  bitmap_to_N (firstn 64 bm).
Proof.
  rewrite modulo.trim_as_bitwise_and.
  rewrite Z.land_comm.
  rewrite (bitmap_to_N_land_ones_firstn bm 64%nat).
  apply N2Z.id.
Qed.

Lemma bitmap_to_N_high64 bm :
  (length bm <= 128)%nat ->
  Z.to_N (trim 64 (Z.of_N (bitmap_to_N bm) ≫ 64)) =
  bitmap_to_N (skipn 64 bm).
Proof.
  intro Hlen.
  destruct (Nat.leb_spec 64 (length bm)) as [H64 | H64].
  2: {
    rewrite skipn_all2.
    2: {
      lia.
    }
    cbn [bitmap_to_N].
    rewrite Z.shiftr_div_pow2.
    2: {
      lia.
    }
    rewrite Z.div_small.
    2: {
      pose proof (bitmap_to_N_lt_length bm).
      pose proof (proj1 (N2Z.inj_lt _ _) H) as HZ.
      split.
      {
        lia.
      }
      {
        eapply Z.lt_le_trans.
        {
          exact HZ.
        }
        change
          (Z.of_N (2 ^ N.of_nat (length bm)) <=
           Z.of_N (2 ^ 64%N))%Z.
        rewrite !N2Z.inj_pow.
        change (Z.of_N 2) with 2%Z.
        rewrite nat_N_Z.
        apply Z.pow_le_mono_r; lia.
      }
    }
    rewrite trim_0_r.
    reflexivity.
  }
  rewrite <- (firstn_skipn 64 bm) at 1.
  rewrite bitmap_to_N_app.
  rewrite firstn_length_le.
  2: {
    exact H64.
  }
  rewrite N2Z.inj_add.
  rewrite N2Z.inj_mul.
  rewrite N2Z.inj_pow.
  change (Z.of_N 2) with 2%Z.
  rewrite nat_N_Z.
  rewrite Z.shiftr_div_pow2.
  2: {
    lia.
  }
  replace
    (bitmap_to_N (firstn 64 bm) +
     2 ^ 64%nat * bitmap_to_N (skipn 64 bm))%Z
    with
    (bitmap_to_N (skipn 64 bm) * 2 ^ 64%nat +
     bitmap_to_N (firstn 64 bm))%Z
    by lia.
  rewrite Z.div_add_l.
  2: {
    vm_compute.
    discriminate.
  }
  rewrite Z.div_small.
  2: {
    pose proof (bitmap_to_N_lt_length (firstn 64 bm)).
    pose proof (proj1 (N2Z.inj_lt _ _) H) as HZ.
    rewrite firstn_length_le in HZ.
    2: {
      exact H64.
    }
    lia.
  }
  rewrite Z.add_0_r.
  rewrite to_unsigned_bits_id.
  {
    apply N2Z.id.
  }
  {
    pose proof (bitmap_to_N_lt_length (skipn 64 bm)).
    rewrite skipn_length in H.
    assert (length bm - 64 <= 64)%nat by lia.
    split.
    {
      lia.
    }
    {
      eapply Z.lt_le_trans.
      {
        exact (proj1 (N2Z.inj_lt _ _) H).
      }
      change
        (Z.of_N (2 ^ N.of_nat (length bm - 64)) <=
         Z.of_N (2 ^ 64%N))%Z.
      rewrite !N2Z.inj_pow.
      change (Z.of_N 2) with 2%Z.
      rewrite nat_N_Z.
      apply Z.pow_le_mono_r; lia.
    }
  }
Qed.

Lemma popcount128_bitmap_to_N bm :
  (length bm <= 128)%nat ->
  (popcount64 (Z.to_N (trim 64 (Z.of_N (bitmap_to_N bm)))) +
   popcount64 (Z.to_N (trim 64 (Z.of_N (bitmap_to_N bm) ≫ 64))) =
   N.of_nat (count_true bm))%N.
Proof.
  intro Hlen.
  rewrite bitmap_to_N_low64.
  rewrite bitmap_to_N_high64.
  2: {
    exact Hlen.
  }
  rewrite !popcount64_bitmap_to_N.
  2: {
    rewrite skipn_length; lia.
  }
  2: {
    rewrite firstn_length; lia.
  }
  unfold count_true.
  rewrite <- Nat2N.inj_add.
  apply f_equal.
  rewrite <- app_length.
  rewrite <- List.filter_app.
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma dense_index_popcount_machine page i :
  length page = page_slot_count ->
  (0 <= i < page_slot_count)%Z ->
  (popcount64
     (Z.to_N
        (trim 64
           (slot_bitmap_word page `land` trim 128 (1 ≪ i - 1)))) +
   popcount64
     (Z.to_N
        (trim 64
           ((slot_bitmap_word page `land` trim 128 (1 ≪ i - 1)) ≫ 64))) =
   N.of_nat (storage_page_dense_index page (Z.to_nat i)))%N.
Proof.
  intros Hlen Hi.
  rewrite dense_index_mask_ones.
  2: {
    exact Hi.
  }
  rewrite slot_bitmap_word_page_slots_model.
  rewrite page_slots_model_present.
  replace (Z.ones i) with (Z.ones (Z.of_nat (Z.to_nat i))).
  2: {
    f_equal.
    lia.
  }
  rewrite
    (bitmap_to_N_land_ones_firstn
       (map storage_page_slot_present page) (Z.to_nat i)).
  rewrite popcount128_bitmap_to_N.
  2: {
    change page_slot_count with 128%nat in Hlen.
    change (Z.of_nat page_slot_count) with 128%Z in Hi.
    rewrite firstn_length_le.
    {
      lia.
    }
    rewrite length_map.
    lia.
  }
  unfold storage_page_dense_index, count_true.
  rewrite firstn_map.
  unfold storage_page_has_slot, storage_page_slot_present.
  induction (firstn (Z.to_nat i) page) as [| slot rest IH].
  {
    reflexivity.
  }
  {
    cbn.
    destruct (slot =? 0)%N; cbn; lia.
  }
Qed.

#[local] Hint Resolve
  dense_index_popcount64_int_bound
  dense_index_popcount_machine : typeclass_instances pure.
#[local] Hint Opaque
  popcount64 popcount_fuel : typeclass_instances sl_opacity.
Opaque popcount64 popcount_fuel.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Definition primR_anyR_F ty q v :=
    [FWD] (primR_anyR ty q v).

  Lemma primR_wp_destroy_val_num
      (tu : translation_unit) sz sgn (p : ptr) cv v Q :
    p |-> primR (Tnum sz sgn) (cQp.mk (q_const cv) 1) v
    ** Q
    |-- wp_destroy_val tu cv (Tnum sz sgn) p Q.
  Proof using.
    rewrite primR_anyR.
    apply destroy.wp_destroy_val_num.
  Qed.

  Definition primR_wp_destroy_val_num_B tu sz sgn p cv v Q :=
    [BWD] (primR_wp_destroy_val_num tu sz sgn p cv v Q).

  Lemma sep_add_wand_refl (P C : mpred) :
    P |-- P ** (C -* C).
  Proof using.
    rewrite <- (bi.sep_emp P) at 1.
    apply bi.sep_mono_r.
    apply Forget.bi_wand_refl.
  Qed.

  Lemma envs_entails_weaken
      (E : environments.envs mpredI) (P Q : mpred) :
    P |-- Q ->
    environments.envs_entails E P ->
    environments.envs_entails E Q.
  Proof using.
    intros HP HE.
    rewrite /environments.envs_entails
      environments.pre_envs_entails_unseal
      /environments.pre_envs_entails_def.
    rewrite /environments.envs_entails
      environments.pre_envs_entails_unseal
      /environments.pre_envs_entails_def in HE.
    transitivity P.
    {
      exact HE.
    }
    {
      exact HP.
    }
  Qed.

  Lemma ucharR_make_mutable
      (tu : translation_unit) (p : ptr) i Q :
    p |-> ucharR 1$c i
    ** (p |-> ucharR 1$m i -* Q)
    |-- wp_make_mutable tu p Tuchar Q.
  Proof using.
    rewrite <-
      (primR_wp_const_val
         tu 1$c 1$m p Tuchar Q
         ltac:(vm_compute; reflexivity)).
    cbn.
    rewrite <- (bi.exist_intro (Vint i)).
    go.
  Qed.

  Definition ucharR_make_mutable_B tu p i Q :=
    [BWD] (ucharR_make_mutable tu p i Q).

  Lemma StoragePageR_dense_index_unpack (p : ptr) q page :
    p |-> StoragePageR q page
    |--
    p ,, storage_page_bitmap_field
      |-> primR Tuint128_t q$m (Vn (slot_bitmap_word page))
    ** p ,, storage_page_values_vector_field
      |-> boost_small_vector.SmallVectorR
        storage_page_values_ty storage_page_values_vector_ty
        storage_page_values_holder_ty bytes32_ty
        bytes32R q (storage_page_dense_values page)
    ** p |-> structR "monad::storage_page_t" q$m
    ** [| length page = page_slot_count |]
    ** [| List.Forall (fun word => (word < 2 ^ 256)%N) page |].
  Proof using.
    unfold StoragePageR.
    go.
  Qed.

  Definition StoragePageR_dense_index_unpack_F p q page :=
    [FWD] (StoragePageR_dense_index_unpack p q page).

  Lemma StoragePageR_dense_index_pack (p : ptr) q page :
    p ,, storage_page_bitmap_field
      |-> primR Tuint128_t q$m (Vn (slot_bitmap_word page))
    ** p ,, storage_page_values_vector_field
      |-> boost_small_vector.SmallVectorR
        storage_page_values_ty storage_page_values_vector_ty
        storage_page_values_holder_ty bytes32_ty
        bytes32R q (storage_page_dense_values page)
    ** p |-> structR "monad::storage_page_t" q$m
    ** [| length page = page_slot_count |]
    ** [| List.Forall (fun word => (word < 2 ^ 256)%N) page |]
    |-- p |-> StoragePageR q page.
  Proof using.
    unfold StoragePageR.
    go.
  Qed.

  Definition StoragePageR_dense_index_pack_B p q page :=
    [BWD] (StoragePageR_dense_index_pack p q page).

  Lemma dense_index_return_cleanup
      (Post : ptr -> mpred)
      (this i_addr below_addr retp : ptr) q page i :
    length page = page_slot_count ->
    List.Forall (fun word => (word < 2 ^ 256)%N) page ->
    (0 <= i < page_slot_count)%Z ->
    (this |-> StoragePageR q page -*
      Forall x : ptr,
        i_addr |-> anyR Tuchar 1$m **
        x |-> tptsto_fuzzyR Tulong 1$m
          (Vn (N.of_nat (storage_page_dense_index page (Z.to_nat i)))) -*
        Post x)
    ** this ,, storage_page_values_vector_field
      |-> boost_small_vector.SmallVectorR
        storage_page_values_ty storage_page_values_vector_ty
        storage_page_values_holder_ty bytes32_ty
        bytes32R q (storage_page_dense_values page)
    ** this |-> structR "monad::storage_page_t" q$m
    ** this ,, storage_page_bitmap_field
      |-> primR Tuint128_t q$m (Vn (slot_bitmap_word page))
    ** i_addr |-> ucharR 1$c i
    ** below_addr |-> primR Tuint128_t 1$c
      (slot_bitmap_word page `land` trim 128 (1 ≪ i - 1))
    ** retp |-> ulongR 1$m
      (popcount64
         (Z.to_N
            (trim 64
               (slot_bitmap_word page `land` trim 128 (1 ≪ i - 1)))) +
       popcount64
         (Z.to_N
            (trim 64
               ((slot_bitmap_word page `land` trim 128 (1 ≪ i - 1))
                ≫ 64))))%N
    |--
    below_addr |-> primR Tuint128_t 1$c
      (slot_bitmap_word page `land` trim 128 (1 ≪ i - 1))
    ** i_addr |-> ucharR 1$c i
    ** (i_addr |-> ucharR 1$m i -* ▷ Post retp).
  Proof using.
    intros Hlen Hwords Hi.
    rewrite (dense_index_popcount_machine page i Hlen Hi).
    go using StoragePageR_dense_index_pack_B, primR_anyR_F.
  Qed.

  #[local] Hint Resolve
    observeStoragePageLength_F
    StoragePageR_dense_index_unpack_F
    StoragePageR_dense_index_pack_B
    primR_wp_destroy_val_num_B
    ucharR_make_mutable_B : sl_opacity.

  Lemma prf_storage_page_dense_index :
    verify[source] storage_page_dense_index_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    do 44 run1.
    match goal with
    | |- context[below_addr |-> primR Tuint128_t 1$c ?below] =>
        match goal with
        | |- context[wp_destroy_val source QC Tuint128_t below_addr ?Q] =>
            wapply
              (primR_wp_destroy_val_num
                 source int_rank.I128 Unsigned below_addr QC below Q)
        end
    end.
    rewrite HiddenPostCondition.unlock.
    eapply environments.envs_entails_mono.
    {
      reflexivity.
    }
    {
      apply sep_add_wand_refl.
    }
    match goal with
    | |- environments.envs_entails ?E
           (?A ** wp_make_mutable source i_addr Tuchar ?K) =>
        eapply
          (envs_entails_weaken E
             (A ** (i_addr |-> ucharR 1$c i
                   ** (i_addr |-> ucharR 1$m i -* K)))
             (A ** wp_make_mutable source i_addr Tuchar K))
    end.
    {
      apply bi.sep_mono_r.
      apply ucharR_make_mutable.
    }
    eapply envs_entails_weaken.
    {
      match goal with
      | Post : ptr -> mpred,
        Hwords : List.Forall (fun word => (word < 2 ^ 256)%N) page |- _ =>
          eapply
            (dense_index_return_cleanup
               Post this i_addr below_addr p q page i H Hwords (conj a b))
      end.
    }
    go.
  Qed.
End with_Sigma.
