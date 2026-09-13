Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_index_const.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma prf_storage_page_dtor :
    verify[source] storage_page_dtor_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    go using StoragePageMoveResidualR_unpack_F.
    rewrite <- (bi.exist_intro values).
    unfold boost_small_vector.SmallVectorObjectR,
      boost_small_vector.small_vector_base_offset.
    rewrite !_at_offsetR.
    unfold storage_page_values_vector_field,
      storage_page_values_field,
      storage_page_values_name,
      storage_page_values_small_vector_base_name,
      storage_page_values_vector_name.
    rewrite !offset_ptr_dot.
    go.
  Qed.
End with_Sigma.
