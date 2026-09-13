Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_index_const.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma storage_page_ctor_model_length :
    length storage_page_empty_model = page_slot_count.
  Proof using.
    unfold storage_page_empty_model.
    rewrite repeat_length.
    reflexivity.
  Qed.

  Lemma storage_page_ctor_model_range :
    List.Forall
      (fun word => (word < 2 ^ 256)%N)
      storage_page_empty_model.
  Proof using.
    unfold storage_page_empty_model.
    generalize page_slot_count as slot_count.
    induction slot_count as [| slot_count IH]; simpl.
    { constructor. }
    {
      constructor.
      { change (0 < 2 ^ 256)%N. reflexivity. }
      exact IH.
    }
  Qed.

  Lemma storage_page_ctor_model_dense_values :
    storage_page_dense_values storage_page_empty_model = [].
  Proof using.
    unfold storage_page_empty_model.
    generalize page_slot_count as slot_count.
    induction slot_count as [| slot_count IH]; simpl.
    { reflexivity. }
    exact IH.
  Qed.

  Lemma slot_bitmap_from_repeat_zero index slot_count :
    slot_bitmap_from index (repeat 0%N slot_count) = 0%N.
  Proof using.
    revert index.
    induction slot_count as [| slot_count IH]; intros index; simpl.
    { reflexivity. }
    rewrite IH.
    reflexivity.
  Qed.

  Lemma storage_page_ctor_model_bitmap :
    slot_bitmap_word storage_page_empty_model = 0%N.
  Proof using.
    unfold storage_page_empty_model.
    apply slot_bitmap_from_repeat_zero.
  Qed.

  #[local] Hint Resolve
    storage_page_ctor_model_length
    storage_page_ctor_model_range : pure.

  #[local] Hint Rewrite
    storage_page_ctor_model_bitmap
    storage_page_ctor_model_dense_values : storage_page_ctor_model.

  Lemma prf_storage_page_ctor :
    verify[source] storage_page_ctor_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    unfold boost_small_vector.SmallVectorObjectR,
      boost_small_vector.small_vector_base_offset.
    unfold storage_page_values_vector_field.
    go.
    unfold boost_small_vector.SmallVectorObjectR,
      boost_small_vector.small_vector_base_offset.
    rewrite !_at_offsetR.
    unfold storage_page_values_field,
      storage_page_values_name,
      storage_page_values_small_vector_base_name,
      storage_page_values_vector_name.
    rewrite !offset_ptr_dot.
    autorewrite with storage_page_ctor_model.
    go using StoragePageR_index_pack_vector_path_B.
  Qed.
End with_Sigma.
