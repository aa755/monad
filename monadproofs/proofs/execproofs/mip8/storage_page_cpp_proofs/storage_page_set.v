Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_index_const.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Section Pure.
  Lemma storage_page_set_slot_present_eqb_true value :
    (value =? 0)%N = true ->
    storage_page_slot_present value = false.
  Proof.
    unfold storage_page_slot_present.
    intro Hvalue.
    rewrite Hvalue.
    reflexivity.
  Qed.

  Lemma storage_page_set_slot_present_eqb_false value :
    (value =? 0)%N = false ->
    storage_page_slot_present value = true.
  Proof.
    unfold storage_page_slot_present.
    intro Hvalue.
    rewrite Hvalue.
    reflexivity.
  Qed.

  Lemma storage_page_set_has_slot_eqb_true page offset :
    (nth offset page 0%N =? 0)%N = true ->
    storage_page_has_slot page offset = false.
  Proof.
    unfold storage_page_has_slot, storage_page_slot_present.
    intro Hslot.
    rewrite Hslot.
    reflexivity.
  Qed.

  Lemma storage_page_set_has_slot_eqb_false page offset :
    (nth offset page 0%N =? 0)%N = false ->
    storage_page_has_slot page offset = true.
  Proof.
    unfold storage_page_has_slot, storage_page_slot_present.
    intro Hslot.
    rewrite Hslot.
    reflexivity.
  Qed.

  Lemma storage_page_set_slot_present_nth_eqb_true page offset :
    (nth offset page 0%N =? 0)%N = true ->
    storage_page_slot_present (nth offset page 0%N) = false.
  Proof.
    unfold storage_page_slot_present.
    intro Hslot.
    rewrite Hslot.
    reflexivity.
  Qed.

  Lemma storage_page_set_slot_present_nth_eqb_false page offset :
    (nth offset page 0%N =? 0)%N = false ->
    storage_page_slot_present (nth offset page 0%N) = true.
  Proof.
    unfold storage_page_slot_present.
    intro Hslot.
    rewrite Hslot.
    reflexivity.
  Qed.

  Lemma storage_page_set_dense_index_lt_from_eqb_false page offset :
    (nth offset page 0%N =? 0)%N = false ->
    (storage_page_dense_index page offset <
     length (storage_page_dense_values page))%nat.
  Proof.
    intro Hslot.
    apply storage_page_dense_index_lt.
    apply storage_page_set_has_slot_eqb_false.
    exact Hslot.
  Qed.

  Lemma storage_page_set_dense_index_lt_N_from_eqb_false page offset :
    (nth offset page 0%N =? 0)%N = false ->
    (N.of_nat (storage_page_dense_index page offset) <
     N.of_nat (length (storage_page_dense_values page)))%N.
  Proof.
    intro Hslot.
    pose proof
      (storage_page_set_dense_index_lt_from_eqb_false
         page offset Hslot).
    lia.
  Qed.

  Lemma storage_page_set_dense_index_lt_Z_from_eqb_false page offset :
    (nth offset page 0%N =? 0)%N = false ->
    (Z.of_N (N.of_nat (storage_page_dense_index page offset)) <
     Z.of_nat (length (storage_page_dense_values page)))%Z.
  Proof.
    intro Hslot.
    pose proof
      (storage_page_set_dense_index_lt_from_eqb_false
         page offset Hslot).
      lia.
    Qed.

  Lemma storage_page_set_dense_index_le_N page offset :
    (N.of_nat (storage_page_dense_index page offset) <=
     N.of_nat (length (storage_page_dense_values page)))%N.
  Proof.
    unfold storage_page_dense_index, storage_page_dense_values.
    revert offset.
    induction page as [| slot rest IH]; intro offset.
    { destruct offset; simpl; lia. }
    destruct offset as [| offset].
    {
      simpl.
      destruct (storage_page_slot_present slot); simpl; lia.
    }
    simpl.
    destruct (storage_page_slot_present slot); simpl.
    {
      specialize (IH offset).
      lia.
    }
    exact (IH offset).
  Qed.

  Lemma storage_page_set_dense_index_le_insert_bound page offset :
    N.of_nat (storage_page_dense_index page offset) <=
    length (storage_page_dense_values page).
  Proof.
    pose proof (storage_page_set_dense_index_le_N page offset).
    lia.
  Qed.

  Lemma storage_page_set_dense_index_to_signed_W64 page offset :
    length page = page_slot_count ->
    (0 <= offset < Z.of_nat page_slot_count)%Z ->
    to_signed bitsize.W64
      (N.of_nat (storage_page_dense_index page (Z.to_nat offset))) =
    Z.of_N
      (N.of_nat (storage_page_dense_index page (Z.to_nat offset))).
  Proof.
    intros Hlen Hoffset.
    apply to_signed_id.
    split.
    {
      lia.
    }
    {
      unfold storage_page_dense_index.
      pose proof
        (filter_length storage_page_slot_present
           (firstn (Z.to_nat offset) page)).
      rewrite firstn_length in H.
      unfold page_slot_count in *.
      change (2 ^ (bitsize.bitsZ bitsize.W64 - 1))%Z
        with 9223372036854775808%Z.
      lia.
    }
  Qed.

  Lemma storage_page_set_update_slot_nth idx offset value page :
    (offset < length page)%nat ->
    nth idx (storage_page_update_slot offset value page) 0%N =
    if Nat.eqb idx offset then value else nth idx page 0%N.
  Proof.
    revert offset idx.
    induction page as [| slot rest IH]; intros offset idx Hoffset.
    { simpl in Hoffset; lia. }
    destruct offset as [| offset].
    {
      destruct idx;
        unfold storage_page_update_slot; simpl; reflexivity.
    }
    destruct idx as [| idx].
    {
      unfold storage_page_update_slot; simpl; reflexivity.
    }
    rewrite storage_page_update_slot_cons_succ.
    simpl.
    apply IH.
    simpl in Hoffset.
    lia.
  Qed.

  Lemma storage_page_set_bitmap_to_N_testbit_nat bm index :
    N.testbit (bitmap_to_N bm) (N.of_nat index) =
    nth index bm false.
  Proof.
    revert index.
    induction bm as [| bit rest IH]; intro index.
    { destruct index; reflexivity. }
    destruct index as [| index].
    {
      simpl.
      destruct bit.
      {
        replace (1 + 2 * bitmap_to_N rest)%N
          with (2 * bitmap_to_N rest + 1)%N by lia.
        apply N.testbit_odd_0.
      }
      rewrite N.add_0_l.
      apply N.testbit_even_0.
    }
    simpl.
    replace (N.pos (Pos.of_succ_nat index))
      with (N.succ (N.of_nat index))
      by lia.
    replace
      ((if bit then 1 else 0) + 2 * bitmap_to_N rest)%N
      with (2 * bitmap_to_N rest + N.b2n bit)%N
      by (destruct bit; simpl; lia).
    rewrite N.testbit_succ_r.
    apply IH.
  Qed.

  Lemma storage_page_set_page_slots_model_present page :
    map slot_present (page_slots_model page) =
    map storage_page_slot_present page.
  Proof.
    induction page as [| slot rest IH]; cbn.
    { reflexivity. }
    unfold page_slot_value_model, slot_present,
      storage_page_slot_present.
    destruct (N.eq_dec slot 0%N) as [Hzero | Hnonzero].
    {
      subst slot.
      cbn.
      f_equal.
      exact IH.
    }
    cbn.
    destruct (slot =? 0)%N eqn:Hslot_zero.
    {
      apply N.eqb_eq in Hslot_zero.
      contradiction.
    }
    f_equal.
    exact IH.
  Qed.

  Lemma storage_page_set_slot_bitmap_word_testbit page bit :
    N.testbit (slot_bitmap_word page) bit =
    storage_page_slot_present (nth (N.to_nat bit) page 0%N).
  Proof.
    rewrite slot_bitmap_word_page_slots_model.
    rewrite <- (N2Nat.id bit) at 1.
    rewrite storage_page_set_bitmap_to_N_testbit_nat.
    rewrite storage_page_set_page_slots_model_present.
    change false with (storage_page_slot_present 0%N).
    rewrite map_nth.
    reflexivity.
  Qed.

  Lemma storage_page_set_nat_eqb_N_eqb bit offset :
    Nat.eqb (N.to_nat bit) offset = N.eqb bit (N.of_nat offset).
  Proof.
    destruct (Nat.eq_dec (N.to_nat bit) offset) as [Heq | Hneq].
    {
      subst offset.
      rewrite Nat.eqb_refl.
      symmetry.
      apply N.eqb_eq.
      symmetry.
      apply N2Nat.id.
    }
    {
      replace ((N.to_nat bit =? offset)%nat) with false.
      2: {
        symmetry.
        apply Nat.eqb_neq.
        exact Hneq.
      }
      symmetry.
      apply N.eqb_neq.
      intro Hbit.
      apply Hneq.
      rewrite Hbit.
      rewrite Nat2N.id.
      reflexivity.
    }
  Qed.

  Lemma storage_page_set_slot_bitmap_word_update_clear
      page offset value :
    (offset < length page)%nat ->
    storage_page_slot_present value = false ->
    slot_bitmap_word (storage_page_update_slot offset value page) =
    storage_page_clear_bit_model (slot_bitmap_word page) offset.
  Proof.
    intros Hoffset Hvalue.
    apply N.bits_inj.
    intro bit.
    unfold storage_page_clear_bit_model.
    rewrite N.clearbit_eqb.
    rewrite !storage_page_set_slot_bitmap_word_testbit.
    rewrite storage_page_set_update_slot_nth.
    2: { exact Hoffset. }
    rewrite storage_page_set_nat_eqb_N_eqb.
    rewrite (N.eqb_sym (N.of_nat offset) bit).
    destruct (N.eqb bit (N.of_nat offset)); simpl.
    {
      rewrite Bool.andb_false_r.
      exact Hvalue.
    }
    rewrite Bool.andb_true_r.
    reflexivity.
  Qed.

  Lemma storage_page_set_slot_bitmap_word_update_set
      page offset value :
    (offset < length page)%nat ->
    storage_page_slot_present value = true ->
    slot_bitmap_word (storage_page_update_slot offset value page) =
    storage_page_set_bit_model (slot_bitmap_word page) offset.
  Proof.
    intros Hoffset Hvalue.
    apply N.bits_inj.
    intro bit.
    unfold storage_page_set_bit_model.
    rewrite N.setbit_eqb.
    rewrite !storage_page_set_slot_bitmap_word_testbit.
    rewrite storage_page_set_update_slot_nth.
    2: { exact Hoffset. }
    rewrite storage_page_set_nat_eqb_N_eqb.
    rewrite (N.eqb_sym (N.of_nat offset) bit).
    destruct (N.eqb bit (N.of_nat offset)); simpl.
    {
      exact Hvalue.
    }
    reflexivity.
  Qed.

  Lemma storage_page_set_slot_bitmap_word_update_same
      page offset value :
    (offset < length page)%nat ->
    storage_page_slot_present value =
    storage_page_slot_present (nth offset page 0%N) ->
    slot_bitmap_word (storage_page_update_slot offset value page) =
    slot_bitmap_word page.
  Proof.
    intros Hoffset Hsame.
    apply N.bits_inj.
    intro bit.
    rewrite !storage_page_set_slot_bitmap_word_testbit.
    rewrite storage_page_set_update_slot_nth.
    2: { exact Hoffset. }
    destruct (Nat.eqb (N.to_nat bit) offset) eqn:Heq.
    {
      apply Nat.eqb_eq in Heq.
      rewrite Heq.
      exact Hsame.
    }
    reflexivity.
  Qed.

  Lemma storage_page_set_small_vector_erase_at {A : Type}
      offset (values : list A) :
    boost_small_vector.small_vector_erase_at offset values =
    list_erase_at offset values.
  Proof.
    reflexivity.
  Qed.

  Lemma storage_page_set_small_vector_insert_at {A : Type}
      offset (value : A) (values : list A) :
    boost_small_vector.small_vector_insert_at offset value values =
    list_insert_at offset value values.
  Proof.
    reflexivity.
  Qed.

  Lemma storage_page_set_small_vector_replace_at {A : Type}
      offset (value : A) (values : list A) :
    boost_small_vector.small_vector_replace_at offset value values =
    list_replace_at offset value values.
  Proof.
    reflexivity.
  Qed.

  Lemma storage_page_set_Z_to_nat_N_of_nat index :
    Z.to_nat (Z.of_N (N.of_nat index)) = index.
  Proof.
    lia.
  Qed.

  Lemma storage_page_set_update_slot_length_page_count
      page offset value :
    length page = page_slot_count ->
    (0 <= offset < Z.of_nat page_slot_count)%Z ->
    length
      (storage_page_update_slot (Z.to_nat offset) value page) =
    page_slot_count.
  Proof.
    intros Hlen Hoffset.
    rewrite storage_page_update_slot_length.
    { exact Hlen. }
    rewrite Hlen.
    lia.
  Qed.

  Lemma storage_page_set_update_slot_Forall_range
      page offset value :
    length page = page_slot_count ->
    (0 <= offset < Z.of_nat page_slot_count)%Z ->
    (value < 2 ^ 256)%N ->
    List.Forall (fun word => (word < 2 ^ 256)%N) page ->
    List.Forall
      (fun word => (word < 2 ^ 256)%N)
      (storage_page_update_slot (Z.to_nat offset) value page).
  Proof.
    intros Hlen Hoffset Hvalue Hpage.
    apply storage_page_update_slot_Forall_range.
    {
      rewrite Hlen.
      lia.
    }
    { exact Hvalue. }
    exact Hpage.
  Qed.
End Pure.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma storage_page_dense_index_valid_long page offset :
    length page = page_slot_count ->
    (0 <= offset < Z.of_nat page_slot_count)%Z ->
    valid<Tlong>
      (Vn
         (N.of_nat
            (storage_page_dense_index page (Z.to_nat offset)))).
  Proof using.
    intros Hlen Hoffset.
    apply type.has_int_type_LR.
    unfold bitsize.bound.
    split.
    {
      cbn.
      lia.
    }
    {
      unfold storage_page_dense_index.
      pose proof
        (filter_length storage_page_slot_present
           (firstn (Z.to_nat offset) page)).
      rewrite firstn_length in H.
      unfold page_slot_count in *.
      change
        (bitsize.max_val
           (int_rank.bitsize int_rank.Ilong) Signed)
        with (2 ^ (64 - 1) - 1)%Z.
      change (2 ^ (64 - 1) - 1)%Z
        with 9223372036854775807%Z.
      lia.
    }
  Qed.

  #[local] Hint Resolve
    storage_page_dense_index_valid_long
    storage_page_set_dense_index_lt_N_from_eqb_false
    storage_page_set_dense_index_lt_Z_from_eqb_false
    storage_page_set_dense_index_le_N
    storage_page_set_update_slot_length_page_count
    storage_page_set_update_slot_Forall_range : pure.

  Lemma storage_page_set_use_index_mut_post
      (retp vectorp base : ptr) capacity index values value :
    (∀ t : N,
      retp |-> bytes32R 1 t -*
      vectorp |-> boost_small_vector.SmallVectorCapR
        storage_page_values_ty storage_page_values_vector_ty
        storage_page_values_holder_ty bytes32_ty bytes32R 1
        {|
          boost_small_vector.small_vector_base := base;
          boost_small_vector.small_vector_capacity := capacity;
        |}
        (boost_small_vector.small_vector_replace_at index t values))
    ** retp |-> bytes32R 1 value
    |--
    vectorp |-> boost_small_vector.SmallVectorCapR
      storage_page_values_ty storage_page_values_vector_ty
      storage_page_values_holder_ty bytes32_ty bytes32R 1
      {|
        boost_small_vector.small_vector_base := base;
        boost_small_vector.small_vector_capacity := capacity;
      |}
      (boost_small_vector.small_vector_replace_at index value values).
  Proof using.
    rewrite (bi.forall_elim value).
    apply bi.wand_elim_l.
  Qed.

  Definition storage_page_set_use_index_mut_post_F
      (retp vectorp base : ptr) capacity index values value :=
    [FWD]
      (storage_page_set_use_index_mut_post
         retp vectorp base capacity index values value).

  Lemma storage_page_set_add_dense_index_bound
      page offset (P : mpred) :
    P |--
    [| N.of_nat (storage_page_dense_index page offset) <=
       length (storage_page_dense_values page) |]
    ** P.
  Proof using.
    pose proof
      (storage_page_set_dense_index_le_insert_bound page offset).
    go.
  Qed.

  Lemma storage_page_set_dense_index_valid_ptr
      (vectorp base : ptr) capacity page (offset : nat) :
    vectorp |-> boost_small_vector.SmallVectorCapR
      storage_page_values_ty storage_page_values_vector_ty
      storage_page_values_holder_ty bytes32_ty bytes32R 1
      {|
        boost_small_vector.small_vector_base := base;
        boost_small_vector.small_vector_capacity := capacity;
      |}
      (storage_page_dense_values page)
    |--
    valid_ptr
      (base .[ bytes32_ty !
        N.of_nat (storage_page_dense_index page offset) ])
    ** vectorp |-> boost_small_vector.SmallVectorCapR
      storage_page_values_ty storage_page_values_vector_ty
      storage_page_values_holder_ty bytes32_ty bytes32R 1
      {|
        boost_small_vector.small_vector_base := base;
        boost_small_vector.small_vector_capacity := capacity;
      |}
      (storage_page_dense_values page).
  Proof using.
    unfold boost_small_vector.SmallVectorCapR,
      boost_small_vector.SmallVectorPayloadR.
    pose proof
      (storage_page_set_dense_index_le_insert_bound page offset).
    go.
  Qed.

  Lemma prf_storage_page_set :
    verify[source] storage_page_set_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    go using
      type_ptr_valid,
      observeStoragePageTypePtr_index_F,
      type_ptr_reference_to_B_local.
    rewrite <- (bi.exist_intro (A := Qp) 1%Qp).
    go using
      type_ptr_valid,
      observeStoragePageTypePtr_index_F,
      type_ptr_reference_to_B_local.
    rewrite <- (bi.exist_intro page).
    go using
      type_ptr_valid,
      observeStoragePageTypePtr_index_F,
      type_ptr_reference_to_B_local.
    go using StoragePageR_index_unpack_F.
    unfold boost_small_vector.SmallVectorR.
    unfold storage_page_values_vector_field,
      storage_page_values_field,
      storage_page_values_name,
      storage_page_values_small_vector_base_name,
      storage_page_values_vector_name.
    rewrite !offset_ptr_dot.
    unfold storage_page_values_iterator_plus_spec,
      storage_page_values_const_iterator_ctor_spec,
      storage_page_values_const_iterator_dtor_spec,
      storage_page_values_iterator_dtor_spec,
      storage_page_values_erase_spec,
      storage_page_values_insert_spec,
      storage_page_values_index_mut_spec,
      boost_small_vector.iterator_plus_spec,
      boost_small_vector.const_iterator_from_iterator_ctor_spec,
      boost_small_vector.iterator_dtor_spec,
      boost_small_vector.erase_spec,
      boost_small_vector.insert_spec,
      boost_small_vector.index_mut_spec.
    go.
    rewrite
      (storage_page_set_dense_index_valid_ptr
         (this ,, storage_page_values_field ,,
          o_base CU storage_page_values_name
            storage_page_values_small_vector_base_name ,,
          o_base CU storage_page_values_small_vector_base_name
            storage_page_values_vector_name)
         base capacity page (Z.to_nat offset)).
    rewrite <- (bi.exist_intro (A := Qp) 1%Qp).
    rewrite <- (bi.exist_intro page).
    go using
      StoragePageR_index_pack_vector_path_B,
      boost_small_vector.SmallVectorCapR_at_pack_F.
    go using StoragePageR_index_unpack_F.
    unfold boost_small_vector.SmallVectorR,
      storage_page_values_vector_field,
      storage_page_values_field,
      storage_page_values_name,
      storage_page_values_small_vector_base_name,
      storage_page_values_vector_name.
    rewrite !offset_ptr_dot.
    go.
    rewrite
      (storage_page_set_dense_index_valid_ptr
         (this ,, storage_page_values_field ,,
          o_base CU storage_page_values_name
            storage_page_values_small_vector_base_name ,,
          o_base CU storage_page_values_small_vector_base_name
            storage_page_values_vector_name)
         base capacity page (Z.to_nat offset)).
    rewrite (storage_page_set_dense_index_to_signed_W64 page offset _H_2).
    2: { lia. }
    rewrite N2Z.id.
    go.
    wp_if.
    {
      intro His_zero.
      go.
      wp_if.
      {
        intro Hwas_absent.
        unfold storage_page_set_model.
        rewrite <-
          (storage_page_dense_values_update_absent_zero
             page (Z.to_nat offset) value).
        2: { rewrite _H_2; lia. }
        2: {
          apply storage_page_set_slot_present_nth_eqb_true.
          exact Hwas_absent.
        }
        2: {
          apply storage_page_set_slot_present_eqb_true.
          exact His_zero.
        }
        rewrite <-
          (storage_page_set_slot_bitmap_word_update_same
             page (Z.to_nat offset) value).
        2: { rewrite _H_2; lia. }
        2: {
          rewrite
            (storage_page_set_slot_present_eqb_true
               value His_zero).
          rewrite
            (storage_page_set_slot_present_nth_eqb_true
               page (Z.to_nat offset) Hwas_absent).
          reflexivity.
        }
        unfold storage_page_values_field.
        go using
          boost_small_vector.SmallVectorCapR_at_pack_F,
          StoragePageR_index_pack_vector_path_B,
          storage_page_update_slot_length,
          storage_page_update_slot_Forall_range.
      }
      {
        intro Hwas_present.
        go.
        rewrite <- (bi.exist_intro (slot_bitmap_word page)).
        unfold StoragePageBitmapR.
        go using slot_bitmap_word_lt_128.
        unfold storage_page_set_model.
        rewrite storage_page_set_small_vector_erase_at.
        rewrite storage_page_set_Z_to_nat_N_of_nat.
        rewrite <-
          (storage_page_dense_values_update_present_zero
             page (Z.to_nat offset) value).
        2: { rewrite _H_2; lia. }
        2: {
          apply storage_page_set_slot_present_nth_eqb_false.
          exact Hwas_present.
        }
        2: {
          apply storage_page_set_slot_present_eqb_true.
          exact His_zero.
        }
        rewrite <-
          (storage_page_set_slot_bitmap_word_update_clear
             page (Z.to_nat offset) value).
        2: { rewrite _H_2; lia. }
        2: {
          apply storage_page_set_slot_present_eqb_true.
          exact His_zero.
        }
        go using
          boost_small_vector.SmallVectorCapR_at_pack_F,
          StoragePageR_index_pack_vector_path_B,
          storage_page_update_slot_length,
          storage_page_update_slot_Forall_range.
      }
    }
    {
      intro His_nonzero.
      go.
      wp_if.
      {
        intro Hwas_present.
        go.
        go using storage_page_set_use_index_mut_post_F.
        unfold storage_page_set_model.
        rewrite storage_page_set_small_vector_replace_at.
        rewrite Nat2N.id.
        rewrite <-
          (storage_page_dense_values_update_present_nonzero
             page (Z.to_nat offset) value).
        2: { rewrite _H_2; lia. }
        2: {
          apply storage_page_set_slot_present_nth_eqb_false.
          exact Hwas_present.
        }
        2: {
          apply storage_page_set_slot_present_eqb_false.
          exact His_nonzero.
        }
        rewrite <-
          (storage_page_set_slot_bitmap_word_update_same
             page (Z.to_nat offset) value).
        2: { rewrite _H_2; lia. }
        2: {
          rewrite
            (storage_page_set_slot_present_eqb_false
               value His_nonzero).
          rewrite
            (storage_page_set_slot_present_nth_eqb_false
               page (Z.to_nat offset) Hwas_present).
          reflexivity.
        }
        unfold storage_page_values_field.
        go using
          boost_small_vector.SmallVectorCapR_at_pack_F,
          StoragePageR_index_pack_vector_path_B,
          storage_page_update_slot_length,
          storage_page_update_slot_Forall_range.
      }
      {
        intro Hwas_absent.
        go.
        go.
        rewrite <-
          (storage_page_set_add_dense_index_bound
             page (Z.to_nat offset)).
        go.
        rewrite <- (bi.exist_intro (slot_bitmap_word page)).
        unfold StoragePageBitmapR.
        go using slot_bitmap_word_lt_128.
        unfold storage_page_set_model.
        rewrite storage_page_set_small_vector_insert_at.
        rewrite storage_page_set_Z_to_nat_N_of_nat.
        rewrite <-
          (storage_page_dense_values_update_absent_nonzero
             page (Z.to_nat offset) value).
        2: { rewrite _H_2; lia. }
        2: {
          apply storage_page_set_slot_present_nth_eqb_true.
          exact Hwas_absent.
        }
        2: {
          apply storage_page_set_slot_present_eqb_false.
          exact His_nonzero.
        }
        rewrite <-
          (storage_page_set_slot_bitmap_word_update_set
             page (Z.to_nat offset) value).
        2: { rewrite _H_2; lia. }
        2: {
          apply storage_page_set_slot_present_eqb_false.
          exact His_nonzero.
        }
        go using
          boost_small_vector.SmallVectorCapR_at_pack_F,
          StoragePageR_index_pack_vector_path_B,
          storage_page_update_slot_length,
          storage_page_update_slot_Forall_range.
      }
    }
  Qed.
End with_Sigma.
