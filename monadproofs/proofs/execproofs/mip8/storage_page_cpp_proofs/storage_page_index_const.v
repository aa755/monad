Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.

Lemma storage_page_nth_error_offset page offset :
  length page = page_slot_count ->
  (0 <= offset < page_slot_count)%Z ->
  nth_error page (N.to_nat (Z.to_N offset)) =
    Some (nth (Z.to_nat offset) page 0%N).
Proof.
  intros Hlen Hoffset.
  replace (N.to_nat (Z.to_N offset)) with (Z.to_nat offset) by lia.
  destruct (nth_error page (Z.to_nat offset)) as [value |] eqn:Hnth.
  {
    f_equal.
    symmetry.
    assert (Hlt : (Z.to_nat offset < length page)%nat) by lia.
    rewrite (@nth_indep N page (Z.to_nat offset) 0%N value Hlt).
    exact (nth_error_nth page (Z.to_nat offset) value Hnth).
  }
  {
    apply nth_error_None in Hnth.
    lia.
  }
Qed.

Lemma storage_page_has_slot_false page offset :
  storage_page_has_slot page offset = false ->
  nth offset page 0%N = 0%N.
Proof.
  unfold storage_page_has_slot, storage_page_slot_present.
  rewrite negb_false_iff.
  rewrite N.eqb_eq.
  intros H.
  exact H.
Qed.

Lemma storage_page_dense_index_lt page offset :
  storage_page_has_slot page offset = true ->
  (storage_page_dense_index page offset <
   length (storage_page_dense_values page))%nat.
Proof.
  revert offset.
  induction page as [| slot rest IH]; intros [| offset] Hpresent.
  {
    discriminate.
  }
  {
    discriminate.
  }
  {
    unfold storage_page_has_slot in Hpresent.
    cbn [nth] in Hpresent.
    unfold storage_page_dense_index, storage_page_dense_values.
    cbn [firstn List.filter length].
    rewrite Hpresent.
    cbn.
    lia.
  }
  {
    unfold storage_page_has_slot in Hpresent.
    cbn [nth] in Hpresent.
    unfold storage_page_dense_index, storage_page_dense_values.
    cbn [firstn List.filter length].
    destruct (storage_page_slot_present slot); cbn.
    {
      specialize (IH offset Hpresent).
      unfold storage_page_dense_index, storage_page_dense_values in IH.
      lia.
    }
    {
      specialize (IH offset Hpresent).
      unfold storage_page_dense_index, storage_page_dense_values in IH.
      lia.
    }
  }
Qed.

Lemma storage_page_dense_values_nth_present page offset :
  storage_page_has_slot page offset = true ->
  nth (storage_page_dense_index page offset)
    (storage_page_dense_values page) 0%N =
  nth offset page 0%N.
Proof.
  revert offset.
  induction page as [| slot rest IH]; intros [| offset] Hpresent.
  {
    discriminate.
  }
  {
    discriminate.
  }
  {
    unfold storage_page_has_slot in Hpresent.
    cbn [nth] in Hpresent.
    unfold storage_page_dense_index, storage_page_dense_values.
    cbn [firstn List.filter nth].
    rewrite Hpresent.
    cbn.
    reflexivity.
  }
  {
    unfold storage_page_has_slot in Hpresent.
    cbn [nth] in Hpresent.
    unfold storage_page_dense_index, storage_page_dense_values.
    cbn [firstn List.filter nth].
    destruct (storage_page_slot_present slot); cbn.
    {
      apply IH.
      exact Hpresent.
    }
    {
      apply IH.
      exact Hpresent.
    }
  }
Qed.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma StoragePageR_index_unpack (p : ptr) q page :
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

  Definition StoragePageR_index_unpack_F p q page :=
    [FWD] (StoragePageR_index_unpack p q page).

  Lemma StoragePageR_index_pack (p : ptr) q page :
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

  Definition StoragePageR_index_pack_B p q page :=
    [BWD] (StoragePageR_index_pack p q page).

  Lemma StoragePageR_index_pack_vector_path (p : ptr) q page :
    p ,, storage_page_bitmap_field
      |-> primR Tuint128_t q$m (Vn (slot_bitmap_word page))
    ** p ,, storage_page_values_field ,,
      o_base CU storage_page_values_name
        storage_page_values_small_vector_base_name ,,
      o_base CU storage_page_values_small_vector_base_name
        storage_page_values_vector_name
      |-> boost_small_vector.SmallVectorR
        storage_page_values_ty storage_page_values_vector_ty
        storage_page_values_holder_ty bytes32_ty
        bytes32R q (storage_page_dense_values page)
    ** p |-> structR "monad::storage_page_t" q$m
    ** [| length page = page_slot_count |]
    ** [| List.Forall (fun word => (word < 2 ^ 256)%N) page |]
    |-- p |-> StoragePageR q page.
  Proof using.
    unfold StoragePageR, storage_page_values_vector_field.
    replace
      (p ,, storage_page_values_field ,,
       o_base CU storage_page_values_name
         storage_page_values_small_vector_base_name ,,
       o_base CU storage_page_values_small_vector_base_name
         storage_page_values_vector_name)
      with
      (p ,, (storage_page_values_field ,,
       o_base CU storage_page_values_name
         storage_page_values_small_vector_base_name) ,,
       o_base CU storage_page_values_small_vector_base_name
         storage_page_values_vector_name)
      by (rewrite offset_ptr_dot; reflexivity).
    go.
  Qed.

  Definition StoragePageR_index_pack_vector_path_B p q page :=
    [BWD] (StoragePageR_index_pack_vector_path p q page).

  Lemma observeStoragePageTypePtr_index (p : ptr) q page :
    Observe (type_ptr storage_page_ty p) (p |-> StoragePageR q page).
  Proof using MODd.
    apply observe_intro.
    { exact _. }
    unfold StoragePageR.
    rewrite !_at_sep.
    go.
  Qed.

  Definition observeStoragePageTypePtr_index_F p q page :=
    @observe_fwd _ _ _ (observeStoragePageTypePtr_index p q page).

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).

  #[local] Hint Resolve
    observeStoragePageLength_F
    observeStoragePageTypePtr_index_F
    type_ptr_reference_to_B_local : sl_opacity.

  Lemma prf_storage_page_index_const :
    verify[source] storage_page_index_const_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    go using type_ptr_valid.
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro page).
    go.
    wp_if.
    {
      intro Habsent.
      go.
    }
    intro Hpresent.
    go.
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro page).
    go.
    go using
      StoragePageR_index_unpack_F,
      StoragePageR_index_pack_B.
    assert
      (Hslot_present :
        storage_page_has_slot page (Z.to_nat offset) = true).
    {
      unfold storage_page_has_slot, storage_page_slot_present.
      rewrite Hpresent.
      reflexivity.
    }
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro (storage_page_dense_values page)).
    assert
      (Hidx_lt :
        (N.of_nat (storage_page_dense_index page (Z.to_nat offset)) <
         N.of_nat (length (storage_page_dense_values page)))%N).
    {
      pose proof
        (storage_page_dense_index_lt page
           (Z.to_nat offset) Hslot_present) as Hlt_nat.
      lia.
    }
    assert
      (Hdense_nth :
        nth
          (N.to_nat
             (N.of_nat
                (storage_page_dense_index page (Z.to_nat offset))))
          (storage_page_dense_values page) 0%N =
        nth (Z.to_nat offset) page 0%N).
    {
      rewrite Nat2N.id.
      apply storage_page_dense_values_nth_present.
      exact Hslot_present.
    }
    rewrite Hdense_nth.
    unfold storage_page_values_vector_field,
      storage_page_values_field,
      storage_page_values_name,
      storage_page_values_small_vector_base_name,
      storage_page_values_vector_name.
    rewrite !offset_ptr_dot.
    go using StoragePageR_index_pack_vector_path_B.
  Qed.
End with_Sigma.
