Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Require Import skylabs.auto.invariants.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import monad.asts.reserve_balance_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.ranges_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.fiber_specs.
Require Import monad.proofs.libspecs.vector_upstream.
Require Import stdpp.gmap.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import monad.proofs.execproofs.reservebal.non_sender_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_low_balance_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_sufficient_balance_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_history_lemmas.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Import linearity.
Import optional_specs.
Import fiber_specs.
Import environments.
Import exec_specs.

Set Warnings "+sl-impossible-patterns".
Open Scope Z_scope.
Set Printing Coercions.
Set Default Goal Selector "!".
Set Printing Depth 99999999.
Unset SsrIdents.
Remove Hints MonadChainContextR_B : sl_opacity.
Opaque MonadChainContextR.
Opaque Zdigits.binary_value Zdigits.Z_to_binary.
Local Transparent
  sender_in_recent_historyb delundel_in_recent_historyb
  sender_in_current_prefixb delundel_in_current_prefixb.
Local Transparent tx_seen_within_k delundel_seen_within_k.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context {MODd : reserve_balance_cpp.source ⊧ CU}.

  Disable Notation "::wpS".
  Disable Notation "::wpL".
  Hint Rewrite map_fst_update_assum_exactness_map : syntactic.
  Hint Rewrite
    current_balance_pessimistic_model_stack_cons
    original_balance_pessimistic_model_map_check_min_original_balance_update
    original_balance_pessimistic_model_map_update_assum_exactness_at
    preTxAccountOf_map_update_assum_exactness_at
    using eauto : syntactic.
  Hint Resolve
    stateCodeMapInvariants_update_assum_exactness_state_insert
    validModel_update_assum_exactness_state_insert
    gdom_insert_subset_takeN_succ
    allFinalBalSufficient_takeN_succ
    updates_stricter_insert
    validPres
    : pure.
  #[local] Instance learn_sender_auth_set :
    LearnEq2 SenderAuthoritiesSetR :=
    ltac:(solve_learnable).
  #[local] Instance learn_sender_vec_spine :
    LearnEq3
      (std.vector.spineR "monad::Address" (std.allocator.T "monad::Address")) :=
    ltac:(solve_learnable).
  #[local] Instance learn_auth_vec_spine :
    LearnEq3
      (std.vector.spineR
         (std.vector.T
            "std::optional<monad::Address>"
            (std.allocator.T "std::optional<monad::Address>"))
         (std.allocator.T
            (std.vector.T
               "std::optional<monad::Address>"
               (std.allocator.T "std::optional<monad::Address>")))) :=
    ltac:(solve_learnable).
  Open Scope N_scope.

  #[local] Existing Instance exec_specs.SpecFor_address_set_contains.
  #[local] Existing Instance ranges_specs.SpecFor_std_ranges_contains.
  #[local] Existing Instance exec_specs.SpecFor_ranges_contains_optional_address.
  #[local] Existing Instance ranges_specs.SpecFor_identity_ctor.
  #[local] Existing Instance ranges_specs.SpecFor_identity_dtor.

  Definition wp_init_implicit_B_local := [BWD] wp_init_implicit.
  #[local] Hint Resolve wp_init_implicit_B_local : sl_opacity.
  #[local] Hint Resolve wp.wp_init_initlist_struct_B : sl_opacity.
  #[local] Hint Resolve wp_operand_initlist_default_B : sl_opacity.
  #[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
  Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
    : db_bluerock_syntactic.
  Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
    : pick_frac.
  Remove Hints _at_split_specific_cfrac_C _at_split_specific_frac_C
    : db_bluerock_syntactic.
  Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
    : db_skylabs_syntactic.
  Remove Hints _at_split_specific_cfrac_C _at_split_specific_frac_C
    : db_skylabs_syntactic.
  Remove Hints pick_cfrac_and_split_C pick_frac_and_split_C
    primR_aggressive_frac_C primR_split_C ownhalf_splitC
    : sl_opacity.
  Remove Hints pick_cfrac_and_split_C pick_frac_and_split_C
    primR_aggressive_frac_C
    : pick_frac.
  Remove Hints split_specific_cfrac_C split_specific_frac_C
    : sl_opacity.

  Lemma cblock_eq_currentBlock_local (ctx : MonadChainContext) :
    cblock ctx = currentBlock (blocks ctx).
  Proof.
    reflexivity.
  Qed.

  #[local] Hint Rewrite cblock_eq_currentBlock_local : syntactic.

  Lemma lookupZ_of_lookupN_local {A : Type} (xs : list A) (j : N) (x : A) :
    xs !! N.to_nat j = Some x ->
    xs !! Z.of_N j = Some x.
  Proof.
    intros HlookupN.
    apply (proj2 (lookupZ_Some_to_nat xs (Z.of_N j) x)).
    split.
    { lia. }
    { replace (Z.to_nat (Z.of_N j)) with (N.to_nat j) by lia.
      exact HlookupN.
    }
  Qed.

  #[local] Hint Resolve lookupZ_of_lookupN_local : pure.

  Lemma lookupZ_of_lookupN_local_entails {A : Type}
      (xs : list A) (j : N) (x : A) :
    ([| xs !! N.to_nat j = Some x |] : mpred) |--
    [| xs !! Z.of_N j = Some x |].
  Proof.
    go.
  Qed.

  Lemma lookupN_of_lookupZ_local {A : Type} (xs : list A) (j : N) (x : A) :
    xs !! Z.of_N j = Some x ->
    xs !! N.to_nat j = Some x.
  Proof.
    intros HlookupZ.
    destruct (proj1 (lookupZ_Some_to_nat xs (Z.of_N j) x) HlookupZ)
      as [_ HlookupN].
    replace (Z.to_nat (Z.of_N j)) with (N.to_nat j) in HlookupN by lia.
    exact HlookupN.
  Qed.

  Lemma nth_error_of_lookupZ_local {A : Type} (xs : list A) (j : N) (x : A) :
    xs !! Z.of_N j = Some x ->
    nth_error xs (N.to_nat j) = Some x.
  Proof.
    intros HlookupZ.
    rewrite nth_error_lookup.
    exact (lookupN_of_lookupZ_local xs j x HlookupZ).
  Qed.

  Lemma lengthN_sub0_normalize_local {A : Type} (xs : list A) (size : Z) :
    lengthN xs = Z.to_N (size - 0) ->
    lengthN xs = Z.to_N size.
  Proof.
    intro Hlen.
    replace (Z.to_N size) with (Z.to_N (size - 0)) by lia.
    exact Hlen.
  Qed.

  Lemma nth_lookup_of_lt_lengthZ_local {A : Type}
      (xs : list A) (k : N) (d : A) :
    (Z.of_N k < lengthZ xs)%Z ->
    xs !! N.to_nat k = Some (nth (N.to_nat k) xs d).
  Proof.
    intro Hlt.
    change (Z.of_N k < Z.of_N (lengthN xs))%Z in Hlt.
    pose proof ((proj2 (N2Z.inj_lt k (lengthN xs))) Hlt) as Hklt.
    destruct (nth_error_SomeN xs k Hklt) as [x Hlookup].
    rewrite (nth_error_nth xs (N.to_nat k) d Hlookup).
    rewrite nth_error_lookup in Hlookup.
    exact Hlookup.
  Qed.

  Lemma arrayLR_extract_middle_lookup_local {A : Type}
      (ty : type) (p : ptr) (i j k : Z) (f : A -> Rep) (xs : list A)
      (Hijk : SolveArith (i <= j /\ j < k)%Z) :
    p |-> arrayLR ty i k f xs |--
    type_ptr ty (p .[ ty ! (j)%Z ]) **
    Exists x : A,
      p .[ ty ! (j)%Z ] |-> f x **
      p |-> arrayLR ty i j f (sliceZ i i j xs) **
      p |-> arrayLR ty (j + 1)%Z k f (sliceZ i (j + 1)%Z k xs) **
      [| lengthN xs = Z.to_N (k - i) |] **
      [| xs !! (j - i)%Z = Some x |].
  Proof.
    pose proof
      (@instances.list_split_middle_forall_var_sliceZ
         A i j k xs _ (j + 1)%Z eq_refl (j - i)%Z eq_refl)
      as Hsplit.
    pose proof
      (@classes.extract _ _ _ _ _ _
         (@array.array_sliceR_extractable_middle _ _ _ _ A ty p i j (j + 1)%Z
            k f xs Hijk _ _ _ _ _ Hsplit eq_refl))
      as Hextract.
    rewrite Hextract.
    go.
  Qed.

  Lemma arrayLR_combine_middle_lookup_local {A : Type}
      (ty : type) (p : ptr) (i j k : Z) (f : A -> Rep) (xs : list A)
      (Hijk : SolveArith (i <= j /\ j < k)%Z) :
    type_ptr ty (p .[ ty ! (j)%Z ]) **
    (Exists x : A,
      p .[ ty ! (j)%Z ] |-> f x **
      p |-> arrayLR ty i j f (sliceZ i i j xs) **
      p |-> arrayLR ty (j + 1)%Z k f (sliceZ i (j + 1)%Z k xs) **
      [| lengthN xs = Z.to_N (k - i) |] **
      [| xs !! (j - i)%Z = Some x |]) |--
    p |-> arrayLR ty i k f xs.
  Proof.
    pose proof
      (@instances.list_split_middle_forall_var_sliceZ
         A i j k xs _ (j + 1)%Z eq_refl (j - i)%Z eq_refl)
      as Hsplit.
    pose proof
      (@classes.extract _ _ _ _ _ _
         (@array.array_sliceR_extractable_middle _ _ _ _ A ty p i j (j + 1)%Z
            k f xs Hijk _ _ _ _ _ Hsplit eq_refl))
      as Hextract.
    rewrite Hextract.
    go.
  Qed.

  Lemma arrayLR_extract_middle_lookup_equiv_local {A : Type}
      (ty : type) (p : ptr) (i j k : Z) (f : A -> Rep) (xs : list A)
      (Hijk : SolveArith (i <= j /\ j < k)%Z) :
    p |-> arrayLR ty i k f xs -|-
    type_ptr ty (p .[ ty ! (j)%Z ]) **
    Exists x : A,
      p .[ ty ! (j)%Z ] |-> f x **
      p |-> arrayLR ty i j f (sliceZ i i j xs) **
      p |-> arrayLR ty (j + 1)%Z k f (sliceZ i (j + 1)%Z k xs) **
      [| lengthN xs = Z.to_N (k - i) |] **
      [| xs !! (j - i)%Z = Some x |].
  Proof.
    split'.
    { exact (arrayLR_extract_middle_lookup_local ty p i j k f xs Hijk). }
    { exact (arrayLR_combine_middle_lookup_local ty p i j k f xs Hijk). }
  Qed.

  Lemma arrayLR_extract_middle_known_equiv_local {A : Type}
      (ty : type) (p : ptr) (i j k : Z) (f : A -> Rep) (xs : list A)
      (Hijk : SolveArith (i <= j /\ j < k)%Z) (x : A)
      (Hlookup : xs !! (j - i)%Z = Some x) :
    p |-> arrayLR ty i k f xs -|-
    type_ptr ty (p .[ ty ! (j)%Z ]) **
    p .[ ty ! (j)%Z ] |-> f x **
    p |-> arrayLR ty i j f (sliceZ i i j xs) **
    p |-> arrayLR ty (j + 1)%Z k f (sliceZ i (j + 1)%Z k xs) **
    [| lengthN xs = Z.to_N (k - i) |].
  Proof.
    rewrite (arrayLR_extract_middle_lookup_equiv_local ty p i j k f xs Hijk).
    split'.
    { go. }
    { go. }
  Qed.

  Definition optional_address_ty_local : type :=
    "std::optional<monad::Address>"%cpp_type.

  Definition optional_address_vector_ty_local : type :=
    std.vector.T optional_address_ty_local
      (std.allocator.T optional_address_ty_local).

  Definition optional_address_vectorR_local
      (q : Qp) (l : list (option EvmAddr)) : Rep :=
    (∃ (size0 : Z) (st0 : std.vector.InternalState),
      std.vector.spineR
        optional_address_ty_local
        (std.allocator.T optional_address_ty_local)
        (cQp.m q) size0 st0 ∗
      pureR
        (std.vector.base_pointer st0
         |-> arrayLR optional_address_ty_local 0 size0
               (optional_specs.optionR "monad::Address"
                 (concepts.objR "monad::Address") (cQp.m q)) l))%I.

  Lemma sender_seen_in_current_prefix_sender_lookup_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) (j : N) :
    (Z.of_N j < Z.of_nat i)%Z ->
    map sender (txsWithHdr (cblock ctx)) !! N.to_nat j = Some (sender tx) ->
    sender_seen_in_current_prefix ctx i tx.
  Proof.
    intros Hlt Hlookup.
    exists (N.to_nat j).
    split.
    { rewrite N_nat_Z. lia. }
    left.
    split.
    { rewrite N_nat_Z. lia. }
    rewrite nth_error_lookup.
    exact Hlookup.
  Qed.

  Lemma sender_seen_in_current_prefix_sender_lookupZ_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) (j : N) :
    (Z.of_N j < Z.of_nat i)%Z ->
    map sender (txsWithHdr (cblock ctx)) !! Z.of_N j = Some (sender tx) ->
    true = true ->
    sender_seen_in_current_prefix ctx i tx.
  Proof.
    intros Hlt Hlookup _.
    eapply sender_seen_in_current_prefix_sender_lookup_local; [exact Hlt |].
    exact (lookupN_of_lookupZ_local _ _ _ Hlookup).
  Qed.

  Lemma sender_not_seen_from_last_authority_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr)
      (t : N) (auths_t : list (option EvmAddr))
      (b : forall k : N,
          (k < t)%N ->
          ((k < N.of_nat i)%N ->
             map sender (txsWithHdr (cblock ctx)) !! N.to_nat k <> Some (sender tx)) /\
          forall auths0 : list (option EvmAddr),
            map txAuthoritiesDelFrom (transactions (cblock ctx)) !! N.to_nat k = Some auths0 ->
            Some (sender tx) ∉ auths0) :
    t = N.of_nat i ->
    map txAuthoritiesDelFrom (transactions (cblock ctx)) !! N.to_nat t = Some auths_t ->
    Some (sender tx) ∉ auths_t ->
    ~ sender_seen_in_current_prefix ctx i tx.
  Proof.
    intros HteqN Hlookup_t Hnmem [j [Hle Hseen]].
    destruct Hseen as [Hseen | Hseen].
    { destruct Hseen as [Hjlt Hsenderj].
      assert (HjNlt : (N.of_nat j < t)%N) by
        (apply N2Z.inj_lt;
         zify;
         nia).
      destruct (b (N.of_nat j) HjNlt) as [Hsenderk _].
      assert (HjNlt_i : (N.of_nat j < N.of_nat i)%N) by
        (apply N2Z.inj_lt;
         zify;
         nia).
      specialize (Hsenderk HjNlt_i).
      rewrite nth_error_lookup in Hsenderj.
      rewrite Nat2N.id in Hsenderk.
      exact (Hsenderk Hsenderj).
    }
    destruct Hseen as [auths0 [Hauthj Hinauth]].
    destruct (Nat.lt_ge_cases j i) as [Hjlt | Hjge].
    {
      assert (HjNlt : (N.of_nat j < t)%N) by
        (apply N2Z.inj_lt;
         zify;
         nia).
      destruct (b (N.of_nat j) HjNlt) as [_ Hauthk].
      specialize (Hauthk auths0).
      rewrite nth_error_lookup in Hauthj.
      rewrite Nat2N.id in Hauthk.
      specialize (Hauthk Hauthj).
      exact (Hauthk Hinauth).
    }
    assert (Hjeq : j = i) by lia.
    subst j.
    assert (Ht_nat : N.to_nat t = i) by
      (rewrite HteqN; apply Nat2N.id).
    rewrite nth_error_lookup in Hauthj.
    rewrite <- Ht_nat in Hauthj.
    rewrite Hlookup_t in Hauthj.
    inversion Hauthj; subst auths0.
    exact (Hnmem Hinauth).
  Qed.

  Lemma sender_not_seen_from_last_authority_nth_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr)
      (t : N) (auths_t : list (option EvmAddr))
      (b : forall k : N,
          (k < t)%N ->
          ((k < N.of_nat i)%N ->
             nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <>
             Some (sender tx)) /\
          forall auths0 : list (option EvmAddr),
            nth_error
              (map txAuthoritiesDelFrom (transactions (cblock ctx)))
              (N.to_nat k) = Some auths0 ->
            Some (sender tx) ∉ auths0) :
    t = N.of_nat i ->
    map txAuthoritiesDelFrom (transactions (cblock ctx)) !! N.to_nat t =
      Some auths_t ->
    Some (sender tx) ∉ auths_t ->
    ~ sender_seen_in_current_prefix ctx i tx.
  Proof.
    intros HteqN Hlookup_t Hnmem.
    eapply sender_not_seen_from_last_authority_local.
    { intros k Hk.
      destruct (b k Hk) as [Hsenderk Hauthk].
      split.
      { intros Hki Hlookup.
        apply (Hsenderk Hki).
        rewrite nth_error_lookup.
        exact Hlookup.
      }
      intros auths0 Hlookup.
      apply (Hauthk auths0).
      rewrite nth_error_lookup.
      exact Hlookup.
    }
    { exact HteqN. }
    { exact Hlookup_t. }
    { exact Hnmem. }
  Qed.

  Lemma trim64_nat_succ_le_local (i : nat) :
    (Z.to_N (trim 64 (Z.of_N (N.of_nat i) + 1)) <=
     N.succ (N.of_nat i))%N.
  Proof.
    apply N2Z.inj_le.
    rewrite Z2N.id.
    { rewrite N2Z.inj_succ.
      rewrite nat_N_Z.
      unfold trim.
      apply Z.mod_le.
      { lia. }
      { apply Z.pow_pos_nonneg; lia. } }
    unfold trim.
    apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
  Qed.

  Lemma sender_authority_history_empty_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) :
    forall k : N,
      (k < 0)%N ->
      ((k < N.of_nat i)%N ->
       nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <>
       Some (sender tx)) /\
      forall auths : list (option EvmAddr),
        nth_error
          (map txAuthoritiesDelFrom (transactions (cblock ctx)))
          (N.to_nat k) =
        Some auths ->
        Some (sender tx) ∉ auths.
  Proof.
    intros k Hlt.
    exact (False_rect _ ((N.nlt_0_r k) Hlt)).
  Qed.

  #[local] Hint Resolve sender_authority_history_empty_local : pure.

  Lemma sender_authority_history_step_lookupZ_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr)
      (t : N) (bv : EvmAddr) (auths_t : list (option EvmAddr))
      (b : forall k : N,
          (k < t)%N ->
          ((k < N.of_nat i)%N ->
             nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <>
             Some (sender tx)) /\
          forall auths0 : list (option EvmAddr),
            nth_error
              (map txAuthoritiesDelFrom (transactions (cblock ctx)))
              (N.to_nat k) = Some auths0 ->
            Some (sender tx) ∉ auths0) :
    map sender (txsWithHdr (cblock ctx)) !! Z.of_N t = Some bv ->
    sender tx <> bv ->
    map txAuthoritiesDelFrom (transactions (cblock ctx)) !! Z.of_N t =
      Some auths_t ->
    Some (sender tx) ∉ auths_t ->
    forall k : N,
      (k < Z.to_N (Z.of_N t + 1))%N ->
      ((k < N.of_nat i)%N ->
       nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <>
       Some (sender tx)) /\
      forall auths0 : list (option EvmAddr),
        nth_error
          (map txAuthoritiesDelFrom (transactions (cblock ctx)))
          (N.to_nat k) = Some auths0 ->
        Some (sender tx) ∉ auths0.
  Proof.
    intros Hsender Hneq Hauth Hnmem k Hk.
    assert (Hsucc : Z.to_N (Z.of_N t + 1) = N.succ t).
    {
      apply N2Z.inj.
      rewrite Z2N.id.
      2:{ lia. }
      rewrite N2Z.inj_succ.
      lia.
    }
    rewrite Hsucc in Hk.
    apply N.lt_succ_r in Hk.
    apply N.lt_eq_cases in Hk.
    destruct Hk as [Hk | ->].
    { exact (b k Hk). }
    split.
    {
      intros _ Hnth.
      rewrite nth_error_lookup in Hnth.
      pose proof (lookupN_of_lookupZ_local _ _ _ Hsender) as HsenderN.
      rewrite HsenderN in Hnth.
      inversion Hnth; subst.
      congruence.
    }
    intros auths0 Hnth.
    rewrite nth_error_lookup in Hnth.
    pose proof (lookupN_of_lookupZ_local _ _ _ Hauth) as HauthN.
    rewrite HauthN in Hnth.
    inversion Hnth; subst auths0.
    exact Hnmem.
  Qed.

  Lemma sender_authority_history_step_current_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr)
      (t : N) (auths_t : list (option EvmAddr))
      (b : forall k : N,
          (k < t)%N ->
          ((k < N.of_nat i)%N ->
             nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <>
             Some (sender tx)) /\
          forall auths0 : list (option EvmAddr),
            nth_error
              (map txAuthoritiesDelFrom (transactions (cblock ctx)))
              (N.to_nat k) = Some auths0 ->
            Some (sender tx) ∉ auths0) :
    t = N.of_nat i ->
    map txAuthoritiesDelFrom (transactions (cblock ctx)) !! N.to_nat t =
      Some auths_t ->
    Some (sender tx) ∉ auths_t ->
    forall k : N,
      (k < N.succ t)%N ->
      ((k < N.of_nat i)%N ->
       nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <>
       Some (sender tx)) /\
      forall auths0 : list (option EvmAddr),
        nth_error
          (map txAuthoritiesDelFrom (transactions (cblock ctx)))
          (N.to_nat k) = Some auths0 ->
        Some (sender tx) ∉ auths0.
  Proof.
    intros HteqN Hauth Hnmem k Hk.
    destruct (N.lt_ge_cases k t) as [Hklt | Hkge].
    { exact (b k Hklt). }
    assert (Hkeq : k = t) by lia.
    subst k.
    split.
    { rewrite HteqN. intros Hlt_i _. lia. }
    intros auths0 Hlookup0.
    rewrite nth_error_lookup in Hlookup0.
    rewrite Hauth in Hlookup0.
    inversion Hlookup0; subst auths0.
    exact Hnmem.
  Qed.

  Lemma sender_authority_history_step_current_trim_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr)
      (t : N) (auths_t : list (option EvmAddr))
      (b : forall k : N,
          (k < t)%N ->
          ((k < N.of_nat i)%N ->
             nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <>
             Some (sender tx)) /\
          forall auths0 : list (option EvmAddr),
            nth_error
              (map txAuthoritiesDelFrom (transactions (cblock ctx)))
              (N.to_nat k) = Some auths0 ->
            Some (sender tx) ∉ auths0) :
    t = N.of_nat i ->
    map txAuthoritiesDelFrom (transactions (cblock ctx)) !! N.to_nat t =
      Some auths_t ->
    Some (sender tx) ∉ auths_t ->
    forall k : N,
      (k < Z.to_N (trim 64 (Z.of_N t + 1)))%N ->
      ((k < N.of_nat i)%N ->
       nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <>
       Some (sender tx)) /\
      forall auths0 : list (option EvmAddr),
        nth_error
          (map txAuthoritiesDelFrom (transactions (cblock ctx)))
          (N.to_nat k) = Some auths0 ->
        Some (sender tx) ∉ auths0.
  Proof.
    intros HteqN Hauth Hnmem k Hk.
    eapply (sender_authority_history_step_current_local
              ctx i tx t auths_t b);
      [ exact HteqN | exact Hauth | exact Hnmem | ].
    eapply N.lt_le_trans; [exact Hk |].
    rewrite HteqN.
    apply trim64_nat_succ_le_local.
  Qed.

  #[local] Hint Extern 1 =>
    lazymatch goal with
    | |- forall k : N, (k < Z.to_N (Z.of_N ?t + 1))%N -> _ =>
      eapply sender_authority_history_step_lookupZ_local
    end
    : pure.

  #[local] Hint Extern 1 =>
    lazymatch goal with
    | |- forall k : N, (k < Z.to_N (trim 64 (Z.of_N ?t + 1)))%N -> _ =>
      eapply sender_authority_history_step_current_trim_local
    end
    : pure.

  Lemma sender_not_seen_from_loop_exit_local
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) (t : N)
      (b : forall k : N,
          (k < t)%N ->
          ((k < N.of_nat i)%N ->
             nth_error
               (map sender
                  (map (fun t0 : Transaction => (t0, header (cblock ctx)))
                     (transactions (cblock ctx))))
               (N.to_nat k) <> Some (sender tx)) /\
          forall auths0 : list (option EvmAddr),
            nth_error
              (map txAuthoritiesDelFrom (transactions (cblock ctx)))
              (N.to_nat k) = Some auths0 ->
            Some (sender tx) ∉ auths0) :
    t = N.succ (N.of_nat i) ->
    ~ sender_seen_in_current_prefix ctx i tx.
  Proof.
    intros Ht_succ [j [Hle Hseen]].
    destruct Hseen as [[Hjlt Hsenderj] | [auths0 [Hauthj Hinauth]]].
    { assert (Hj_bound : (N.of_nat j < t)%N) by
        (rewrite Ht_succ; apply N2Z.inj_lt; zify; lia).
      destruct (b (N.of_nat j) Hj_bound) as [Hsenderk _].
      assert (Hj_lt_i : (N.of_nat j < N.of_nat i)%N) by
        (apply N2Z.inj_lt; zify; lia).
      specialize (Hsenderk Hj_lt_i).
      rewrite Nat2N.id in Hsenderk.
      exact (Hsenderk Hsenderj). }
    assert (Hj_bound : (N.of_nat j < t)%N) by
      (rewrite Ht_succ; apply N2Z.inj_lt; zify; lia).
    destruct (b (N.of_nat j) Hj_bound) as [_ Hauthk].
    specialize (Hauthk auths0).
    rewrite Nat2N.id in Hauthk.
    exact (Hauthk Hauthj Hinauth).
  Qed.

  Lemma senders_size_from_size_local
      (ctx : MonadChainContext) (size : Z) :
    (0 <= size)%Z ->
    lengthN (map sender (txsWithHdr (cblock ctx))) = Z.to_N size ->
    size = lengthZ (transactions (cblock ctx)).
  Proof.
    intros Hsize_nonneg Hlen.
    pose proof
      ((proj1
          (sizeLen (map sender (txsWithHdr (cblock ctx))) size Hsize_nonneg))
         ltac:(replace (Z.to_N (size - 0)) with (Z.to_N size) by lia; exact Hlen))
      as Hsize_senders.
    replace
      (lengthZ (map sender (txsWithHdr (cblock ctx))))
      with (lengthZ (txsWithHdr (cblock ctx))) in Hsize_senders.
    2:{
      unfold lengthZ.
      autorewrite with syntactic.
      reflexivity.
    }
    rewrite lengthZ_txsWithHdr in Hsize_senders.
    exact Hsize_senders.
  Qed.

  Lemma senders_size_from_size_sub0_local
      (ctx : MonadChainContext) (size : Z) :
    (0 <= size)%Z ->
    lengthN (map sender (txsWithHdr (cblock ctx))) = Z.to_N (size - 0) ->
    size = lengthZ (transactions (cblock ctx)).
  Proof.
    intros Hsize_nonneg Hlen.
    eapply senders_size_from_size_local; [exact Hsize_nonneg |].
    exact (lengthN_sub0_normalize_local _ _ Hlen).
  Qed.

  Lemma authorities_size_from_size_local
      (ctx : MonadChainContext) (size : Z) :
    (0 <= size)%Z ->
    lengthN (map txAuthoritiesDelFrom (transactions (cblock ctx))) = Z.to_N size ->
    size = lengthZ (transactions (cblock ctx)).
  Proof.
    intros Hsize_nonneg Hlen.
    pose proof
      ((proj1
          (sizeLen
             (map txAuthoritiesDelFrom (transactions (cblock ctx)))
             size Hsize_nonneg))
         ltac:(replace (Z.to_N (size - 0)) with (Z.to_N size) by lia; exact Hlen))
      as Hsize_auths.
    replace
      (lengthZ (map txAuthoritiesDelFrom (transactions (cblock ctx))))
      with (lengthZ (transactions (cblock ctx))) in Hsize_auths.
    2:{
      unfold lengthZ.
      autorewrite with syntactic.
      reflexivity.
    }
    exact Hsize_auths.
  Qed.

  Lemma authorities_size_from_size_sub0_local
      (ctx : MonadChainContext) (size : Z) :
    (0 <= size)%Z ->
    lengthN (map txAuthoritiesDelFrom (transactions (cblock ctx))) = Z.to_N (size - 0) ->
    size = lengthZ (transactions (cblock ctx)).
  Proof.
    intros Hsize_nonneg Hlen.
    eapply authorities_size_from_size_local; [exact Hsize_nonneg |].
    exact (lengthN_sub0_normalize_local _ _ Hlen).
  Qed.


(* The production prefix loop is now inside can_sender_dip_into_reserve.
   Its C++ proof is in cansenderdip.v; the lemmas above retain the original
   loop invariant and its connection to transaction history. *)

End with_Sigma.
