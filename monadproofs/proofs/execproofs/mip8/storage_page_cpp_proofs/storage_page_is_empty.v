Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve
    observeStoragePageLength_F : sl_opacity.

  Lemma prf_storage_page_is_empty :
    verify[source] storage_page_is_empty_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    rewrite /StoragePageR.
    go.
    eapply coq_tactics.tac_pure_intro.
    { apply _. }
    { apply _. }
    {
      case_bool_decide as Hzero.
      {
        pose proof
          (proj1 (slot_bitmap_word_Z_zero_storage_page_empty page) Hzero)
          as Hempty.
        rewrite Hempty.
        reflexivity.
      }
      {
        destruct (storage_page_empty page) eqn:Hempty.
        {
          pose proof
            (proj2 (slot_bitmap_word_Z_zero_storage_page_empty page) Hempty)
            as Hzero'.
          contradiction.
        }
        {
          reflexivity.
        }
      }
    }
  Qed.
End with_Sigma.
