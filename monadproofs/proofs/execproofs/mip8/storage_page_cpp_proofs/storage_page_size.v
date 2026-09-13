Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_index_const.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma prf_storage_page_size :
    verify[source] storage_page_size_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    unfold storage_page_size.
    go using StoragePageR_index_unpack_F.
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro (storage_page_dense_values page)).
    unfold storage_page_values_vector_field,
      storage_page_values_field,
      storage_page_values_name,
      storage_page_values_small_vector_base_name,
      storage_page_values_vector_name.
    rewrite !offset_ptr_dot.
    go using StoragePageR_index_pack_vector_path_B.
  Qed.
End with_Sigma.
