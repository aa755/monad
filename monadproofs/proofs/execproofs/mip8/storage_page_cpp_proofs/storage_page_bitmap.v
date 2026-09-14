Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve
    observeStoragePageLength_F : sl_opacity.

  Lemma prf_storage_page_bitmap :
    verify[source] storage_page_bitmap_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    rewrite /StoragePageR.
    go.
  Qed.
End with_Sigma.
