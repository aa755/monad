Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

#[local] Open Scope N_scope.

Section Pure.
  Lemma storage_page_set_bit_model_bound bitmap offset :
    (bitmap < 2 ^ 128)%N ->
    (offset < page_slot_count)%nat ->
    (storage_page_set_bit_model bitmap offset < 2 ^ 128)%N.
  Proof.
    intros Hbitmap Hoffset.
    unfold storage_page_set_bit_model.
    rewrite N.setbit_spec'.
    assert (Hlor_pos : (0 < bitmap `lor` 2 ^ N.of_nat offset)%N).
    {
      apply N.neq_0_lt_0.
      intros Hzero.
      apply N.lor_eq_0_iff in Hzero as [_ Hpow].
      apply N.pow_nonzero in Hpow; lia.
    }
    apply (proj2 (N.log2_lt_pow2 _ _ Hlor_pos)).
    rewrite N.log2_lor.
    apply N.max_lub_lt.
    {
      destruct (N.eq_dec bitmap 0) as [-> | Hnonzero].
      { reflexivity. }
      assert (Hbitmap_pos : (0 < bitmap)%N).
      { apply N.neq_0_lt_0; exact Hnonzero. }
      apply (proj1 (N.log2_lt_pow2 _ _ Hbitmap_pos)) in Hbitmap.
      { exact Hbitmap. }
    }
    rewrite N.log2_pow2.
    2: { lia. }
    unfold page_slot_count in Hoffset.
    lia.
  Qed.

  Lemma storage_page_clear_bit_model_bound bitmap offset :
    (bitmap < 2 ^ 128)%N ->
    (storage_page_clear_bit_model bitmap offset < 2 ^ 128)%N.
  Proof.
    intros Hbitmap.
    unfold storage_page_clear_bit_model.
    eapply N.le_lt_trans.
    { apply N.ldiff_le_l. }
    exact Hbitmap.
  Qed.

  Lemma storage_page_set_bit_expr bitmap i :
    (0 <= i < Z.of_nat page_slot_count)%Z ->
    (bitmap < 2 ^ 128)%N ->
    (Z.of_N bitmap `lor` trim 128 (1 ≪ i))%Z =
    Z.of_N (storage_page_set_bit_model bitmap (Z.to_nat i)).
  Proof.
    intros Hi _.
    unfold storage_page_set_bit_model.
    rewrite N.setbit_spec'.
    assert (Hshift : trim 128 (1 ≪ i) = (2 ^ i)%Z).
    {
      rewrite Z.shiftl_1_l.
      apply to_unsigned_bits_id.
      change (2 ^ 128%N) with (2 ^ 128)%Z.
      split.
      {
        apply Z.pow_nonneg.
        lia.
      }
      {
        change (Z.of_nat page_slot_count) with 128%Z in Hi.
        apply Z.pow_lt_mono_r; lia.
      }
    }
    rewrite Hshift.
    replace (2 ^ i)%Z
      with (Z.of_N (2 ^ N.of_nat (Z.to_nat i)))%Z.
    2: {
      rewrite N2Z.inj_pow.
      rewrite Z_nat_N.
      rewrite Z2N.id.
      2: { lia. }
      reflexivity.
    }
    rewrite <- N2Z.inj_lor.
    reflexivity.
  Qed.

  Lemma storage_page_clear_bit_expr bitmap i :
    (0 <= i < Z.of_nat page_slot_count)%Z ->
    (bitmap < 2 ^ 128)%N ->
    (Z.of_N bitmap `land`
       trim 128 (Z.lnot (trim 128 (1 ≪ i))))%Z =
    Z.of_N (storage_page_clear_bit_model bitmap (Z.to_nat i)).
  Proof.
    intros Hi Hbitmap.
    unfold storage_page_clear_bit_model.
    assert (Hshift : trim 128 (1 ≪ i) = (2 ^ i)%Z).
    {
      rewrite Z.shiftl_1_l.
      apply to_unsigned_bits_id.
      change (2 ^ 128%N) with (2 ^ 128)%Z.
      split.
      {
        apply Z.pow_nonneg.
        lia.
      }
      {
        change (Z.of_nat page_slot_count) with 128%Z in Hi.
        apply Z.pow_lt_mono_r; lia.
      }
    }
    rewrite Hshift.
    assert
      (Hmask :
        (Z.of_N bitmap `land` trim 128 (Z.lnot (2 ^ i)))%Z =
        (Z.of_N bitmap `land` Z.lnot (2 ^ i))%Z).
    {
      rewrite modulo.trim_as_bitwise_and.
      rewrite Z.land_assoc.
      assert (Hbitmap_ones :
        (Z.of_N bitmap `land` Z.ones 128)%Z = Z.of_N bitmap).
      {
        rewrite Z.land_ones.
        {
          rewrite Z.mod_small.
          { reflexivity. }
          lia.
        }
        lia.
      }
      rewrite Hbitmap_ones.
      reflexivity.
    }
    rewrite Hmask.
    rewrite <- Z.ldiff_land.
    rewrite N.clearbit_spec'.
    replace (2 ^ i)%Z
      with (Z.of_N (2 ^ N.of_nat (Z.to_nat i)))%Z.
    2: {
      rewrite N2Z.inj_pow.
      rewrite Z_nat_N.
      rewrite Z2N.id.
      2: { lia. }
      reflexivity.
    }
    rewrite <- N2Z.inj_ldiff.
    reflexivity.
  Qed.
End Pure.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve
    storage_page_set_bit_model_bound
    storage_page_clear_bit_model_bound
    storage_page_set_bit_expr
    storage_page_clear_bit_expr : pure.

  Lemma prf_storage_page_set_bit :
    verify[source] storage_page_set_bit_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    unfold StoragePageBitmapR.
    go.
  Qed.

  Lemma prf_storage_page_clear_bit :
    verify[source] storage_page_clear_bit_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    unfold StoragePageBitmapR.
    go.
  Qed.
End with_Sigma.
