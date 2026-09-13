Require Import monad.proofs.misc.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.dippedlam_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import stdpp.gmap.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import monad.proofs.execproofs.reservebal.non_sender_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_rewrite_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_low_balance_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_sufficient_balance_lemmas.
Import exec_specs.
Import linearity.
Import cQp_compat.
Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".
Open Scope N_scope.

  Lemma binary_value_lt_two_power_nat_local n (bv : vec bool n) :
    (EVMOpSem.Zdigits.binary_value n bv < two_power_nat n)%Z.
  Proof using.
    induction bv; simpl.
    - change (two_power_nat 0) with 1%Z.
      lia.
    - rewrite two_power_nat_S.
      pose proof (EVMOpSem.Zdigits.binary_value_pos n bv) as Hpos.
      assert (Hpowpos : (0 < two_power_nat n)%Z).
      {
        clear -n.
        induction n.
        - change (two_power_nat 0) with 1%Z.
          lia.
        - rewrite two_power_nat_S.
          lia.
      }
      pose proof IHbv as IH.
      destruct h; simpl.
      + assert (Hgap :
            (EVMOpSem.Zdigits.binary_value n bv <= two_power_nat n - 1)%Z).
        { lia. }
        change
          (1 + 2 * EVMOpSem.Zdigits.binary_value n bv <
             2 * two_power_nat n)%Z.
        lia.
      + change
          (2 * EVMOpSem.Zdigits.binary_value n bv <
             2 * two_power_nat n)%Z.
        lia.
  Qed.

  Lemma w256_to_N_lt_2pow256_local (w : EVMOpSem.keccak.w256) :
    (w256_to_N w < 2 ^ 256)%N.
  Proof using.
    unfold w256_to_N, w256_to_Z.
    apply N2Z.inj_lt.
    rewrite Z2N.id.
    2:{
      pose proof (EVMOpSem.Zdigits.binary_value_pos 256 w) as Hpos.
      lia.
    }
    change (Z.of_N (2 ^ 256)) with (two_power_nat 256).
    exact (binary_value_lt_two_power_nat_local 256 w).
  Qed.

  Lemma original_balance_gt_diff_as_value_pos (bal value : N) :
    (value <= bal)%N ->
    (bal < 2 ^ 256)%N ->
    asbool (Z.of_N (Z.to_N ((Z.of_N bal - Z.of_N value) `mod` 2 ^ 256)) < Z.of_N bal)%Z =
    asbool (0 < value)%N.
  Proof using.
    intros Hle Hlt.
    assert (Hsmall :
      Z.to_N ((Z.of_N bal - Z.of_N value) `mod` 2 ^ 256)%Z = bal - value).
    { apply u256_sub_mod_small; assumption. }
    rewrite Hsmall.
    assert (Hsub : (Z.of_N (bal - value) = Z.of_N bal - Z.of_N value)%Z).
    { apply N2Z.inj_sub. exact Hle. }
    rewrite Hsub.
    apply bool_decide_ext.
    lia.
  Qed.

  Lemma original_balance_minus_diff_eq_value (bal value : N) :
    (value <= bal)%N ->
    (bal < 2 ^ 256)%N ->
    Z.to_N
      ((Z.of_N bal -
        Z.of_N (Z.to_N ((Z.of_N bal - Z.of_N value) `mod` 2 ^ 256))) `mod`
       2 ^ 256) = value.
  Proof using.
    intros Hle Hlt.
    rewrite (u256_sub_mod_small bal value Hle Hlt).
    assert (Hle' : (bal - value <= bal)%N).
    { lia. }
    rewrite (u256_sub_mod_small bal (bal - value) Hle' Hlt).
    apply N2Z.inj.
    erewrite N2Z.inj_sub; [|exact Hle'].
    erewrite N2Z.inj_sub; [|exact Hle].
    lia.
  Qed.

(** Very important: otherwise, proofs can become very slow *)
Opaque w256_to_Z.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.
  Ltac loadLocalSpec foo :=
    iAssert (□ foo)%I as "#?"%string;
      [ first [iAssumption | go] | ].

  (*
  Lemma u256R_keep_type_ptr (p : ptr) q v :
    p |-> u256R q v |-- p |-> u256R q v ** type_ptr u256t p.
  Proof using.
    go.
  Qed.
  (* FIXME:  this instance is not enough for `go.` . need to convert it to to a forward instance. read sepproofs.v *)
  #[local] Instance u256_type_ptrR_observe q v : Observe (type_ptrR u256t) (u256R q v).
  Proof.
    apply observe_intro; [exact _ |].
    apply /Rep_entails_at => p.
    rewrite _at_sep _at_type_ptrR.
    exact (u256R_keep_type_ptr p q v).
  Qed.
 *)

  Set Printing Coercions.
  Set Printing Depth 99999999.

  Lemma u256R_keep_type_ptr (p : ptr) q v :
    p |-> u256R q v |-- p |-> u256R q v ** type_ptr u256t p.
  Proof using.
    go.
  Qed.

  #[local] Instance u256_type_ptrR_observe q v :
    Observe (type_ptrR u256t) (u256R q v).
  Proof.
    apply observe_intro; [exact _ |].
    apply /Rep_entails_at => p.
    rewrite _at_sep _at_type_ptrR.
    exact (u256R_keep_type_ptr p q v).
  Qed.

      (*
        Lemma sdg st t addr : state_is_delegated_model (update_assum_exactness_state st t) addr =
                           state_is_delegated_model st addr.
        Proof using. Admitted.
       *)
      (*
        Lemma force_destroy x Q:
          wp_destroy_named source "std::pair<monad::Address, monad::VersionStack<monad::AccountState>>" x Q
          = Q.
        
        Proof using. Admitted.
        *)
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
  Open Scope N_scope.

Unset SsrIdents.
Remove Hints MonadChainContextR_B : sl_opacity.
  
  #[local] Open Scope free_scope.
  Local Transparent AccountStateRcore.
  Lemma use_wand_local (P Q : mpred) : (P -∗ Q) ** P |-- Q.
  Proof.
    rewrite bi.sep_comm.
    exact (bi.wand_elim_r P Q).
  Qed.

  Lemma use_wand_local_r (P Q : mpred) : P ** (P -∗ Q) |-- Q.
  Proof.
    exact (bi.wand_elim_r P Q).
  Qed.

  Definition use_wand_local_r_C P Q :=
    [CANCEL] (use_wand_local_r P Q).
  #[local] Hint Resolve use_wand_local_r_C : sl_opacity.

  Lemma optionR_account_wand
      (p : ptr) (acct : option evmmisc.AccountM) (Q : mpred) :
    p |-> optional_specs.optionR "monad::Account"%cpp_type
           AccountR 1 acct
    ** (p |-> optional_specs.optionR "monad::Account"%cpp_type
            AccountR 1 acct -∗ Q)
    |-- Q.
  Proof.
    exact (bi.wand_elim_r _ _).
  Qed.

  Definition optionR_account_wand_C p acct Q :=
    [CANCEL] (optionR_account_wand p acct Q).
  #[local] Hint Resolve optionR_account_wand_C : sl_opacity.

  Create HintDb wand.
  Definition use_wand_local_F := [FWD] use_wand_local.
  Definition use_wand_local_r_F := [FWD] use_wand_local_r.
  Ltac specialize_wands_local :=
    sep with wand* using use_wand_local_F, use_wand_local_r_F.

  Lemma use_wand_chain_local (P Q R : mpred) :
    (P ** (P -∗ Q)) ** (Q -∗ R) |-- R.
  Proof.
    etrans.
    - apply bi.sep_mono_l.
      exact (bi.wand_elim_r P Q).
    - exact (bi.wand_elim_r Q R).
  Qed.

  Definition unfoldAccountR :=
    [FWD] (fun p q ac =>
      @AutoUnlocking.unfold_eq _ _ _ 
        (@AutoUnlocking.Unfoldable_at _ _ _ _ _ p
           (AccountR_unfoldable _ _ _ _ q ac))).
  Definition foldAccountR :=
    [FWD] (fun p q ac =>
      @AutoUnlocking.unfold_eq _ _ _
        (@AutoUnlocking.Unfoldable_at _ _ _ _ _ p
           (AccountR_unfoldable _ _ _ _ q ac))).
  Transparent AccountR.
  #[local] Hint Opaque AccountR : sl_opacity.
  #[local] Instance learnac : LearnEq2 AccountR := ltac:(solve_learnable).
  #[local] Instance learnorig : LearnEq2 OriginalAccountStateR := ltac:(solve_learnable).
  #[local] Instance learn_optional_spine : LearnEq3 optional_specs.spineR :=
    ltac:(solve_learnable).
  #[local] Hint Resolve optional_specs.trivial_optional_some_split_F
    : sl_opacity.
  #[local] Instance learn_block_state_rfrag :
    AtLearnEq3 BlockState.Rfrag :=
    ltac:(solve_learnable).
  Definition wp_init_condition_B := [BWD] wp_init_condition.

  
  Lemma observeAccountRef (p : ptr) q acct :
    Observe (reference_to "monad::Account" p) (p |-> AccountR q acct).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _|].
    unfold AccountR.
    simpl.
    go.
  Qed.

  Lemma u256R_keep_reference_to_local (p : ptr) q v :
    p |-> u256R q v |-- p |-> u256R q v ** reference_to u256t p.
  Proof using.
    iIntros "Hu"%string.
    iPoseProof (u256R_keep_type_ptr p q v with "Hu"%string) as "[Hu Htp]"%string.
    iSplitL "Hu"%string.
    { iExact "Hu"%string. }
    iApply (type_ptr_reference_to with "Htp"%string).
  Qed.

  Lemma observeU256Ref (p : ptr) q v :
    Observe (reference_to u256t p) (p |-> u256R q v).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _|].
    exact (u256R_keep_reference_to_local p q v).
  Qed.

  Lemma AccountR_separated_fold (p : ptr) (q : Qp) acct :
    balance acct = w256_to_N (block.block_account_balance (coreAc acct)) ->
    p ,, o_field CU "monad::Account::balance"
      |-> u256R q (w256_to_N (block.block_account_balance (coreAc acct)))
    ** p ,, o_field CU "monad::Account::code_hash"
         |-> bytes32R q (code_hash_of_program (block.block_account_code (coreAc acct)))
    ** p ,, o_field CU "monad::Account::nonce"
         |-> ulongR (cQp.mut q) (w256_to_Z (block.block_account_nonce (coreAc acct)))
    ** p ,, o_field CU "monad::Account::incarnation"
         |-> IncarnationR q (incarnation acct)
    ** p |-> structR "monad::Account"%cpp_name (cQp.mut q)
    |-- p |-> AccountR q acct.
  Proof using CU MODd Sigma.
    intro Hbal_eq.
    unfold AccountR.
    rewrite Hbal_eq.
    go.
  Qed.

  Definition AccountR_separated_fold_B p q acct :=
    [BWD] (AccountR_separated_fold p q acct).

  Lemma AccountStateRcore_separated_fold
      (p : ptr) (q : Qp) acct_opt transient_map :
    p ,, o_field CU "monad::AccountState::account_"
      |-> optional_specs.optionR "monad::Account"%cpp_type AccountR q acct_opt
    ** p ,, o_field CU "monad::AccountState::storage_"
         |-> StorageMapR q (storageMapOf acct_opt)
    ** p ,, o_field CU "monad::AccountState::transient_storage_"
         |-> StorageMapR q transient_map
    ** p |-> structR "monad::AccountState"%cpp_name (cQp.mut q)
    |-- p |-> AccountStateRcore q acct_opt.
  Proof using CU MODd Sigma.
    unfold AccountStateRcore.
    go.
    iExists transient_map.
    go.
  Qed.

  Definition AccountStateRcore_separated_fold_B p q acct_opt transient_map :=
    [BWD] (AccountStateRcore_separated_fold p q acct_opt transient_map).

  Lemma AccountStateRcore_none_separated_unfold
      (p : ptr) q :
    p |-> AccountStateRcore q None
    |-- p ,, o_field CU "monad::AccountState::account_"
          |-> optional_specs.optionR "monad::Account"%cpp_type
                AccountR q None
        ** p ,, o_field CU "monad::AccountState::storage_"
             |-> StorageMapR q (storageMapOf None)
        ** (Exists transient_map,
              p ,, o_field CU "monad::AccountState::transient_storage_"
                |-> StorageMapR q transient_map)
        ** p |-> structR "monad::AccountState"%cpp_name (cQp.mut q).
  Proof using CU MODd Sigma.
    unfold AccountStateRcore.
    iIntrosDestructs.
    go.
    iExists transient_map.
    go.
  Qed.

  Lemma OriginalAccountStateR_separated_fold
      (p : ptr) q os transient_map :
    p |-> structR "monad::OriginalAccountState"%cpp_name (cQp.mut q)
    ** p ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
         |-> boolR (cQp.mut q) (~~ bool_decide (is_Some (min_balance (assumExactness os))))
    ** p ,, o_field CU "monad::OriginalAccountState::min_balance_"
         |-> match min_balance (assumExactness os) with
             | Some n => u256R q n
             | None => Exists (nb : N), u256R q nb
             end
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::account_"
         |-> optional_specs.optionR "monad::Account"%cpp_type
               AccountR q (preTxState os)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::storage_"
         |-> StorageMapR q (preTxStorage os)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::transient_storage_"
         |-> StorageMapR q transient_map
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         |-> structR "monad::AccountState"%cpp_name (cQp.mut q)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         |-> o_base CU "monad::AccountState" "monad::AccountSubstate"
              |-> AccountSubstateR q unusedAccountSubstate
    |-- p |-> OriginalAccountStateR q os.
  Proof using CU MODd Sigma.
    unfold OriginalAccountStateR, AccountStateRcore.
    go.
    iExists transient_map.
    go.
  Qed.

  Definition OriginalAccountStateR_separated_fold_B p q os transient_map :=
    [BWD] (OriginalAccountStateR_separated_fold p q os transient_map).

  Lemma observeOptionalAccountRef (p : ptr) q acct :
    Observe (reference_to "std::optional<monad::Account>" p)
      (p |-> optional_specs.optionR "monad::Account"%cpp_type AccountR q acct).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _|].
    go.
  Qed.

  Lemma observeAccountBalanceRef (p : ptr) q acct :
    Observe (reference_to "monad::uint256_t" (p ,, o_field CU "monad::Account::balance"))
      (p |-> AccountR q acct).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _|].
    unfold AccountR.
    go.
  Qed.

  Lemma observeAccountBalanceModelEq (p : ptr) q acct :
    Observe [| acct.(balance) =
               w256_to_N (block.block_account_balance (coreAc acct)) |]
      (p |-> AccountR q acct).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _|].
    unfold AccountR.
    go.
  Qed.

  Definition observeAccountRef_F p q acct :=
    @observe_fwd _ _ _ (observeAccountRef p q acct).
  Definition observeOptionalAccountRef_F p q acct :=
    @observe_fwd _ _ _ (observeOptionalAccountRef p q acct).
  Definition observeAccountBalanceRef_F p q acct :=
    @observe_fwd _ _ _ (observeAccountBalanceRef p q acct).
  Definition observeAccountBalanceModelEq_F p q acct :=
    @observe_fwd _ _ _ (observeAccountBalanceModelEq p q acct).
  #[local] Hint Resolve
    observeAccountRef_F
    observeOptionalAccountRef_F
    observeAccountBalanceRef_F
    observeAccountBalanceModelEq_F : sl_opacity.

  Definition observeAccountRefF p q acct :=
    @observe_fwd _ _ _ (observeAccountRef p q acct).
  Definition observeOptionalAccountRefF p q acct :=
    @observe_fwd _ _ _ (observeOptionalAccountRef p q acct).

  Definition observeAccountBalanceRefF p q acct :=
    @observe_fwd _ _ _ (observeAccountBalanceRef p q acct).



  Definition set_min_balance_update_assumed
      (orig_state : AssumedPreTxAccountState)
      (value : N) : AssumedPreTxAccountState :=
    update_assum_exactness_assumed
      (fun ex =>
         match min_balance ex with
         | Some old =>
             {| min_balance := Some (N.max old value);
                nonce_exact := nonce_exact ex |}
         | None => ex
         end) orig_state.

  Lemma min_balance_update_zero_zero_zero
      (ex : AssumptionExactness) :
    min_balance_update ex 0 0 0 = ex.
  Proof using.
    unfold min_balance_update, check_min_balance_ok.
    destruct ex as [mb ne].
    simpl.
    destruct (bool_decide (0 <= 0)%N) eqn:Hok; simpl.
    - destruct mb as [m|]; simpl; [reflexivity..].
    - apply bool_decide_eq_false_1 in Hok.
      exfalso.
      apply Hok.
      reflexivity.
  Qed.

  Lemma min_balance_update_same_zero
      (ex : AssumptionExactness) (bal : N) :
    min_balance_update ex bal bal 0 = ex.
  Proof using.
    unfold min_balance_update, check_min_balance_ok.
    destruct ex as [mb ne].
    simpl.
    destruct (bool_decide (0 <= bal)%N) eqn:Hok; simpl.
    - destruct mb as [m|]; simpl; [|reflexivity].
      + rewrite N.sub_0_r.
        destruct (N.ltb bal bal) eqn:Hltb; [|reflexivity].
        apply N.ltb_lt in Hltb.
        lia.
    - apply bool_decide_eq_false_1 in Hok.
      exfalso.
      apply Hok.
      apply N.le_0_l.
  Qed.

  Lemma min_balance_update_same_pos
      (ex : AssumptionExactness) (bal value : N) :
    (0 < value <= bal)%N ->
    min_balance_update ex bal bal value =
    match min_balance ex with
    | Some old =>
        {| min_balance := Some (N.max old value);
           nonce_exact := nonce_exact ex |}
    | None => ex
    end.
  Proof using.
    intros [Hpos Hle].
    unfold min_balance_update, check_min_balance_ok.
    destruct ex as [mb ne].
    simpl.
    destruct (bool_decide (value <= bal)%N) eqn:Hok; simpl.
    - destruct mb as [old|]; simpl; [|reflexivity].
      + set (diff := N.sub bal value).
        assert (Hltb : N.ltb diff bal = true).
        {
          apply N.ltb_lt.
          apply N2Z.inj_lt.
          subst diff.
          erewrite N2Z.inj_sub; [|exact Hle].
          lia.
        }
        assert (Hdiff_le : (diff <= bal)%N).
        {
          apply N.lt_le_incl.
          apply N.ltb_lt.
          exact Hltb.
        }
        rewrite Hltb.
        assert (Hdiff : (bal - diff = value)%N).
        {
          apply N2Z.inj_iff.
          subst diff.
          erewrite N2Z.inj_sub; [|exact Hdiff_le].
          erewrite N2Z.inj_sub; [|exact Hle].
          lia.
        }
        rewrite Hdiff.
        reflexivity.
    - apply bool_decide_eq_false_1 in Hok.
      exfalso.
      apply Hok.
      exact Hle.
  Qed.

  Lemma min_balance_update_same_overdraw
      (ex : AssumptionExactness) (bal value : N) :
    (bal < value)%N ->
    min_balance_update ex bal bal value = exact_balance_update ex.
  Proof using.
    intro Hlt.
    unfold min_balance_update, check_min_balance_ok, exact_balance_update.
    destruct ex as [mb ne].
    simpl.
    destruct (bool_decide (value <= bal)%N) eqn:Hok; simpl.
    - apply bool_decide_eq_true_1 in Hok.
      exfalso.
      lia.
    - reflexivity.
  Qed.

  Lemma original_balance_pessimistic_model_map_lookup_some_account
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (acct : evmmisc.AccountM) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    preTxState orig_state = Some acct ->
    original_balance_pessimistic_model_map orig addr = acct.(balance).
  Proof using.
    intros Hlookup Hacct.
    unfold original_balance_pessimistic_model_map, preTxAccountOf_map, balanceOfAccount.
    rewrite Hlookup.
    cbn.
    rewrite Hacct.
    cbn.
    reflexivity.
  Qed.

  Lemma check_min_original_balance_update_some_zero
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (acct : evmmisc.AccountM) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    preTxState orig_state = Some acct ->
    check_min_original_balance_update orig addr 0 = orig.
  Proof using.
    intros Hlookup Hacct.
    unfold check_min_original_balance_update.
    rewrite (original_balance_pessimistic_model_map_lookup_some_account
               orig addr loc orig_state acct Hlookup Hacct).
    unfold update_assum_exactness_at.
    rewrite <- List.map_id.
    apply map_ext.
    intros [addr' [loc' aps]].
    simpl.
    destruct (bool_decide (addr' = addr)) eqn:Hcase.
    - destruct aps as [acct' ex].
      simpl.
      repeat f_equal.
      apply min_balance_update_same_zero.
    - reflexivity.
  Qed.

  Lemma check_min_original_balance_update_some_pos
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (acct : evmmisc.AccountM)
      (value : N) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    preTxState orig_state = Some acct ->
    (0 < value <= acct.(balance))%N ->
    check_min_original_balance_update orig addr value =
    update_assum_exactness_at addr
      (fun ex =>
         match min_balance ex with
         | Some old =>
             {| min_balance := Some (N.max old value);
                nonce_exact := nonce_exact ex |}
         | None => ex
         end) orig.
  Proof using.
    intros Hlookup Hacct Hrange.
    unfold check_min_original_balance_update.
    rewrite (original_balance_pessimistic_model_map_lookup_some_account
               orig addr loc orig_state acct Hlookup Hacct).
    unfold update_assum_exactness_at.
    apply map_ext.
    intros [addr' [loc' aps]].
    simpl.
    destruct (bool_decide (addr' = addr)) eqn:Hcase.
    - destruct aps as [acct' ex].
      simpl.
      repeat f_equal.
      apply min_balance_update_same_pos.
      exact Hrange.
    - reflexivity.
  Qed.

  Lemma check_min_original_balance_update_some_overdraw
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (acct : evmmisc.AccountM)
      (value : N) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    preTxState orig_state = Some acct ->
    (acct.(balance) < value)%N ->
    check_min_original_balance_update orig addr value =
    update_assum_exactness_at addr exact_balance_update orig.
  Proof using.
    intros Hlookup Hacct Hlt.
    unfold check_min_original_balance_update.
    rewrite (original_balance_pessimistic_model_map_lookup_some_account
               orig addr loc orig_state acct Hlookup Hacct).
    unfold update_assum_exactness_at.
    apply map_ext.
    intros [addr' [loc' aps]].
    simpl.
    destruct (bool_decide (addr' = addr)) eqn:Hcase.
    - destruct aps as [acct' ex].
      simpl.
      repeat f_equal.
      apply min_balance_update_same_overdraw.
      exact Hlt.
    - reflexivity.
  Qed.

  Lemma check_min_original_balance_update_none_zero
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    preTxState orig_state = None ->
    check_min_original_balance_update orig addr 0 = orig.
  Proof using.
    intros Hlookup Hacct.
    unfold check_min_original_balance_update,
      original_balance_pessimistic_model_map, preTxAccountOf_map.
    rewrite Hlookup.
    simpl.
    rewrite Hacct.
    simpl.
    unfold update_assum_exactness_at.
    rewrite <- List.map_id.
    apply map_ext.
    intros [addr' [loc' aps]].
    simpl.
    destruct (bool_decide (addr' = addr)) eqn:Hcase.
    - apply bool_decide_eq_true_1 in Hcase.
      subst addr'.
      destruct aps as [acct ex].
      simpl.
      repeat f_equal.
      apply min_balance_update_zero_zero_zero.
    - reflexivity.
  Qed.

  Lemma check_min_original_balance_update_none_pos
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (p : positive) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    preTxState orig_state = None ->
    check_min_original_balance_update orig addr (N.pos p) =
    update_assum_exactness_at addr exact_balance_update orig.
  Proof using.
    intros Hlookup Hacct.
    unfold check_min_original_balance_update,
      original_balance_pessimistic_model_map, preTxAccountOf_map.
    rewrite Hlookup.
    simpl.
    rewrite Hacct.
    simpl.
    unfold update_assum_exactness_at.
    apply map_ext.
    intros [addr' [loc' aps]].
    simpl.
    destruct (bool_decide (addr' = addr)) eqn:Hcase.
    - apply bool_decide_eq_true_1 in Hcase.
      subst addr'.
      destruct aps as [acct ex].
      simpl.
      repeat f_equal.
    - reflexivity.
  Qed.

  Lemma removeKey_update_assum_exactness_at_same
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (f : AssumptionExactness -> AssumptionExactness) :
    removeKey (update_assum_exactness_at addr f orig) addr = removeKey orig addr.
  Proof using.
    induction orig as [| a tl IH]; simpl.
    - reflexivity.
    - destruct a as [addr' [loc aps]].
      simpl.
      destruct (decide (addr' = addr)) as [->|Hneq].
      + assert (Heq : asbool (addr = addr) = true).
        { apply bool_decide_eq_true_2. reflexivity. }
        rewrite Heq.
        simpl.
        assert (Hneqfalse : asbool (addr ≠ addr) = false).
        { apply bool_decide_eq_false_2. intros Hneq'. exact (Hneq' eq_refl). }
        rewrite Hneqfalse.
        exact IH.
      + assert (Heqfalse : asbool (addr' = addr) = false).
        { apply bool_decide_eq_false_2. exact Hneq. }
        rewrite Heqfalse.
        simpl.
        assert (Hneqtrue : asbool (addr' ≠ addr) = true).
        { apply bool_decide_eq_true_2. exact Hneq. }
        rewrite Hneqtrue.
        f_equal.
        exact IH.
  Qed.

  Definition account_option_layout (p : ptr) (acct : evmmisc.AccountM) : mpred :=
    p |-> optional_specs.spineR "monad::Account" 1$m
      (Some (p ,, optional_specs.value_offset "monad::Account"))
      ** p ,, optional_specs.value_offset "monad::Account"%cpp_type
           |-> AccountR 1 acct.

  Lemma optionR_account_some_separated_unfold
      (p : ptr) (acct : evmmisc.AccountM) :
    p |-> optional_specs.optionR "monad::Account"%cpp_type
          AccountR 1 (Some acct)
    |-- account_option_layout p acct.
  Proof using CU MODd Sigma.
    unfold account_option_layout.
    exact (optional_specs.trivial_optional_some_split
      "monad::Account" AccountR 1 acct p).
  Qed.

  Lemma optionR_account_some_separated_fold
      (p : ptr) (acct : evmmisc.AccountM) :
    account_option_layout p acct
    |-- p |-> optional_specs.optionR "monad::Account"%cpp_type
          AccountR 1 (Some acct).
  Proof using CU MODd Sigma.
    unfold account_option_layout.
    go.
  Qed.

  Definition optionR_account_some_separated_fold_B p acct :=
    [BWD] (optionR_account_some_separated_fold p acct).

  Local Ltac unpack_some_account_option acct :=
    iDestruct
      select
        (_ |-> optional_specs.optionR "monad::Account"%cpp_type
             AccountR 1 (Some acct))%I
      as "Hopt0"%string;
    iPoseProof
      (optionR_account_some_separated_unfold _ acct with "Hopt0"%string)
      as "Hlayout"%string;
    iSplitL "Hlayout"%string;
    [ iExact "Hlayout"%string | ];
    iIntros "Hopt"%string;
    go;
    iPoseProof
      (optionR_account_some_separated_unfold _ acct with "Hopt"%string)
      as "Hlayout2"%string;
    iSplitL "Hlayout2"%string;
    [ iExact "Hlayout2"%string | ];
    iIntros "(Hopt & Href_acct & Href_balance)"%string;
    go;
    iPoseProof
      (optionR_account_some_separated_unfold _ acct with "Hopt"%string)
      as "(Hopt_struct & Hopt_engaged & HacctR)"%string;
    iEval (cbv delta [AccountR]) in "HacctR"%string;
    iDestruct "HacctR"%string as "(Hbal & Hcode & Hnonce & Hinc & HacctS)"%string.

  #[local] Hint Opaque optional_account_has_value_spec : sl_opacity.
  #[local] Hint Opaque optional_account_arrow_spec : sl_opacity.
  #[local] Hint Opaque optional_account_bool_spec : sl_opacity.
  #[local] Hint Opaque optional_account_arrow_const_spec : sl_opacity.
  #[local] Hint Opaque optional_specs.optionR : sl_opacity.
  #[local] Hint Opaque uint256_int_ctor_spec : sl_opacity.
  #[local] Hint Opaque accountstate_set_validate_exact_balance_spec : sl_opacity.
  #[local] Hint Opaque accountstate_set_min_balance_spec : sl_opacity.
  #[local] Hint Opaque u256R : sl_opacity.
  #[local] Hint Resolve observeU256F : sl_opacity.
  #[local] Hint Resolve observeAccountRefF observeOptionalAccountRefF observeAccountBalanceRefF : sl_opacity.
  Local Transparent AccountR.
  #[local] Hint Opaque
    StorageMapR
    uint256_int_ctor_spec
    state_original_account_state_spec
    optional_account_bool_spec
    optional_account_arrow_const_spec
    accountstate_set_validate_exact_balance_spec
    accountstate_set_min_balance_spec
    uint256dtor
    uint256_copy_ctor_spec
    u256_minus_spec
    u256_gt_spec
    u256_ge_spec : sl_opacity.
  #[local] Hint Opaque u256_ge_spec : sl_opacity.

  #[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
  Local Ltac unborrowAnkerPayloadAt idx :=
    lazymatch goal with
    | H : nth_error ?m (N.to_nat idx) = Some ?entry |- _ =>
        lazymatch entry with
        | (?key, (?loc, ?orig_state)) =>
            lazymatch goal with
            | |- context [ ?p |-> AnkerMapPayloadsR
                                "monad::Address" "monad::OriginalAccountState"
                                addressR OriginalAccountStateR 1 m ] =>
                unshelve (wapplyRev
                  (@borrowIndex_at _ _ _ _ 1
                    evmopsem.evm.address AssumedPreTxAccountState _
                    "monad::Address" "monad::OriginalAccountState"
                    addressR OriginalAccountStateR
                    m idx (key, (loc, orig_state)) key p));
                [ exact H | reflexivity | .. ]
            end
        end
    end;
    try eagerUnifyC;
    eauto.

  Lemma update_assum_exactness_assumed_id
      (orig_state : AssumedPreTxAccountState) :
    update_assum_exactness_assumed (fun ex => ex) orig_state = orig_state.
  Proof using.
    destruct orig_state as [acct ex].
    reflexivity.
  Qed.

  Lemma update_assum_exactness_at_id
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address) :
    update_assum_exactness_at addr (fun ex => ex) orig = orig.
  Proof using.
    unfold update_assum_exactness_at.
    rewrite -> map_ext with (g := fun x => x); [apply map_id|].
    intros [addr' [loc [acct ex]]].
    simpl.
    destruct (bool_decide (addr' = addr)); reflexivity.
  Qed.

  Lemma reinsert_updated_original_account_payload
      (map_ptr : ptr)
      (origp : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (f : AssumptionExactness -> AssumptionExactness) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" ->
    map_ptr |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
      addressToN addressR 1 (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
    ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    ** loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** origp |-> OriginalAccountStateR 1
         (update_assum_exactness_assumed f orig_state)
    |-- map_ptr |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
          addressToN addressR 1 (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
        ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
             addressR OriginalAccountStateR 1 (update_assum_exactness_at addr f orig).
  Proof using CU MODd Sigma.
    intros Hlookup ->.
    assert (Hmem : (addr, (loc, orig_state)) ∈ orig).
    { eapply elem_of_list_to_map_2. exact Hlookup. }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_upd :
      nth_error (update_assum_exactness_at addr f orig) (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, update_assum_exactness_assumed f orig_state))).
    {
      rewrite Nat2N.id.
      unfold update_assum_exactness_at.
      rewrite nth_error_map.
      rewrite Hnth.
      simpl.
      rewrite (bool_decide_eq_true_2 (addr = addr)).
      2: reflexivity.
      reflexivity.
    }
    rewrite <- (removeKey_update_assum_exactness_at_same orig addr f).
    unshelve (wapplyRev
      (@borrowIndex_at _ _ _ _ 1
        evmopsem.evm.address AssumedPreTxAccountState _
        "monad::Address" "monad::OriginalAccountState"
        addressR OriginalAccountStateR
        (update_assum_exactness_at addr f orig) (N.of_nat i)
        (addr, (loc, update_assum_exactness_assumed f orig_state))
        addr map_ptr));
      [ exact Hnth_upd | reflexivity | try eagerUnifyC; eauto ].
    cbv delta [pairR OriginalAccountStateR AccountStateRcore] in *.
    repeat first [ progress go | progress provePure ].
    iExists transient_map.
    repeat first [ progress go | progress provePure ].
  Qed.

  Lemma reinsert_original_account_payload
      (map_ptr : ptr)
      (origp : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" ->
    map_ptr |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
      addressToN addressR 1 (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
    ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    ** loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** origp |-> OriginalAccountStateR 1 orig_state
    |-- map_ptr |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
          addressToN addressR 1 (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
        ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
             addressR OriginalAccountStateR 1 orig.
  Proof using CU MODd Sigma.
    intros Hlookup ->.
    assert (Hmem : (addr, (loc, orig_state)) ∈ orig).
    { eapply elem_of_list_to_map_2. exact Hlookup. }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_id :
      nth_error orig (N.to_nat (N.of_nat i)) = Some (addr, (loc, orig_state))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    unshelve (wapplyRev
      (@borrowIndex_at _ _ _ _ 1
        evmopsem.evm.address AssumedPreTxAccountState _
        "monad::Address" "monad::OriginalAccountState"
        addressR OriginalAccountStateR
        orig (N.of_nat i)
        (addr, (loc, orig_state))
        addr map_ptr));
      [ exact Hnth_id | reflexivity | try eagerUnifyC; eauto ].
    cbv delta [pairR OriginalAccountStateR AccountStateRcore] in *.
    repeat first [ progress go | progress provePure ].
    iExists transient_map.
    repeat first [ progress go | progress provePure ].
  Qed.

  Lemma reinsert_updated_original_account_payload_only
      (map_ptr : ptr)
      (origp : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (f : AssumptionExactness -> AssumptionExactness) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" ->
    map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    ** loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** origp |-> OriginalAccountStateR 1
         (update_assum_exactness_assumed f orig_state)
    |-- map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
          addressR OriginalAccountStateR 1 (update_assum_exactness_at addr f orig).
  Proof using CU MODd Sigma.
    intros Hlookup ->.
    assert (Hmem : (addr, (loc, orig_state)) ∈ orig).
    { eapply elem_of_list_to_map_2. exact Hlookup. }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_upd :
      nth_error (update_assum_exactness_at addr f orig) (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, update_assum_exactness_assumed f orig_state))).
    {
      rewrite Nat2N.id.
      unfold update_assum_exactness_at.
      rewrite nth_error_map.
      rewrite Hnth.
      simpl.
      rewrite (bool_decide_eq_true_2 (addr = addr)).
      2: reflexivity.
      reflexivity.
    }
    rewrite <- (removeKey_update_assum_exactness_at_same orig addr f).
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address AssumedPreTxAccountState _
      "monad::Address" "monad::OriginalAccountState"
      addressR OriginalAccountStateR
      (update_assum_exactness_at addr f orig) (N.of_nat i)
      (addr, (loc, update_assum_exactness_assumed f orig_state))
      addr map_ptr);
      [| exact Hnth_upd | reflexivity].
    work using use_wand_local_r_F.
  Qed.

  Lemma reinsert_updated_original_account_payload_only_with_bool
      (map_ptr : ptr)
      (origp : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (f : AssumptionExactness -> AssumptionExactness)
      (p : ptr)
      (b : bool) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" ->
    map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    ** loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** origp |-> OriginalAccountStateR 1
         (update_assum_exactness_assumed f orig_state)
    ** p |-> boolR 1$m b
    |-- p |-> boolR 1$m b
          ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
               addressR OriginalAccountStateR 1 (update_assum_exactness_at addr f orig).
  Proof using CU MODd Sigma.
    intros Hlookup ->.
    pose proof
      (reinsert_updated_original_account_payload_only
         map_ptr
         (loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
         orig addr loc orig_state f
         Hlookup eq_refl) as Hreinsert.
    wapply Hreinsert.
    work using use_wand_local_r_F.
  Qed.

  Lemma reinsert_updated_original_account_payload_only_separated
      (map_ptr : ptr)
      (origp : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (f : AssumptionExactness -> AssumptionExactness)
      (transient_map : list (N * N)) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" ->
    map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    ** loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** origp |-> structR "monad::OriginalAccountState"%cpp_name 1$m
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::account_"
         |-> optional_specs.optionR "monad::Account"%cpp_type
              AccountR 1 (preTxState orig_state)
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::storage_"
         |-> StorageMapR 1 (preTxStorage orig_state)
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::transient_storage_"
         |-> StorageMapR 1 transient_map
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         |-> structR "monad::AccountState"%cpp_name 1$m
    ** origp ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
         |-> boolR 1$m
              (~~ bool_decide
                    (is_Some
                       (min_balance
                          (assumExactness
                             (update_assum_exactness_assumed f orig_state)))))
    ** origp ,, o_field CU "monad::OriginalAccountState::min_balance_"
         |-> match
              min_balance
                (assumExactness
                   (update_assum_exactness_assumed f orig_state))
            with
            | Some n => u256R 1 n
            | None => Exists (nb : N), u256R 1 nb
            end
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         |-> o_base CU "monad::AccountState" "monad::AccountSubstate"
              |-> AccountSubstateR 1 unusedAccountSubstate
    |-- map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
          addressR OriginalAccountStateR 1 (update_assum_exactness_at addr f orig).
  Proof using CU MODd Sigma.
    intros Hlookup ->.
    pose proof
      (OriginalAccountStateR_separated_fold
         (loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
         1 (update_assum_exactness_assumed f orig_state)
         transient_map) as Hfold_orig_state.
    cbn in Hfold_orig_state.
    pose proof
      (reinsert_updated_original_account_payload_only
         map_ptr
         (loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
         orig addr loc orig_state f Hlookup eq_refl) as Hreinsert.
    wapply Hreinsert.
    wapply Hfold_orig_state.
    go.
  Qed.

  Lemma reinsert_updated_original_account_payload_only_separated_with_bool
      (map_ptr : ptr)
      (origp : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (f : AssumptionExactness -> AssumptionExactness)
      (transient_map : list (N * N))
      (p : ptr)
      (b : bool) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" ->
    map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    ** loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** origp |-> structR "monad::OriginalAccountState"%cpp_name 1$m
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::account_"
         |-> optional_specs.optionR "monad::Account"%cpp_type
              AccountR 1 (preTxState orig_state)
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::storage_"
         |-> StorageMapR 1 (preTxStorage orig_state)
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         ,, o_field CU "monad::AccountState::transient_storage_"
         |-> StorageMapR 1 transient_map
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         |-> structR "monad::AccountState"%cpp_name 1$m
    ** origp ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
         |-> boolR 1$m
              (~~ bool_decide
                    (is_Some
                       (min_balance
                          (assumExactness
                             (update_assum_exactness_assumed f orig_state)))))
    ** origp ,, o_field CU "monad::OriginalAccountState::min_balance_"
         |-> match
              min_balance
                (assumExactness
                   (update_assum_exactness_assumed f orig_state))
            with
            | Some n => u256R 1 n
            | None => Exists (nb : N), u256R 1 nb
            end
    ** origp ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
         |-> o_base CU "monad::AccountState" "monad::AccountSubstate"
              |-> AccountSubstateR 1 unusedAccountSubstate
    ** p |-> boolR 1$m b
    |-- p |-> boolR 1$m b
          ** map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
               addressR OriginalAccountStateR 1 (update_assum_exactness_at addr f orig).
  Proof using CU MODd Sigma.
    intros Hlookup ->.
    pose proof
      (reinsert_updated_original_account_payload_only_separated
         map_ptr
         (loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState")
         orig addr loc orig_state f transient_map
         Hlookup eq_refl) as Hreinsert.
    wapply Hreinsert.
    go.
  Qed.

  Lemma reinsert_original_account_payload_only
      (map_ptr : ptr)
      (origp : ptr)
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" ->
    map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
         addressR OriginalAccountStateR 1 (removeKey orig addr)
    ** loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
         |-> addressR (1 / 2) addr
    ** origp |-> OriginalAccountStateR 1 orig_state
    |-- map_ptr |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
          addressR OriginalAccountStateR 1 orig.
  Proof using CU MODd Sigma.
    intros Hlookup ->.
    assert (Hmem : (addr, (loc, orig_state)) ∈ orig).
    { eapply elem_of_list_to_map_2. exact Hlookup. }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address AssumedPreTxAccountState _
      "monad::Address" "monad::OriginalAccountState"
      addressR OriginalAccountStateR
      orig (N.of_nat i)
      (addr, (loc, orig_state))
      addr map_ptr);
      [| rewrite Nat2N.id; exact Hnth | reflexivity].
    work using use_wand_local_r_F.
  Qed.

  (* The former check_account_min_balance body is now checked inline by
     prf_state_record_balance_constraint_for_debit in check_min_balance_proof.v.
     check_min_original_balance has no production target. The checked layout
     and map-restoration lemmas above remain shared with set_storage_proof. *)
End with_Sigma.
