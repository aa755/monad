Require Import monad.proofs.misc.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.execproofs.reservebal.dippedlam_lemmas.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import stdpp.gmap.

Import exec_specs.
Import linearity.

Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".
Open Scope N_scope.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Lemma w256_to_N_Z_to_w256_small (n : N) :
  (n < 2 ^ 256)%N ->
  w256_to_N (Z_to_w256 (Z.of_N n)) = n.
Proof using.
  intro Hlt.
  unfold w256_to_N, w256_to_Z, Z_to_w256.
  rewrite EVMOpSem.Zdigits.Z_to_binary_to_Z.
  - apply N2Z.id.
  - lia.
  - change (Z.of_N (2 ^ 256)) with (two_power_nat 256).
    pose proof (proj1 (N2Z.inj_lt n (2 ^ 256)) Hlt) as HltZ.
    change (Z.of_N (2 ^ 256)) with (two_power_nat 256) in HltZ.
    exact HltZ.
Qed.

Opaque Zdigits.binary_value Zdigits.Z_to_binary.
Opaque w256_to_Z.

Lemma state_current_account_state_post_recent_some
    (st st_final : StateM) (addr : evmopsem.evm.address)
    (retp : ptr) (upd : UpdatedAccountState) (ac : AccountM) :
  state_current_account_state_post st addr st_final retp upd ->
  recentAccountOf st addr = Some ac ->
  postTxState upd = Some ac.
Proof using.
  unfold state_current_account_state_post, recentAccountOf, preTxAccountOf.
  destruct (mapModelLookup (newStates st) addr)
    as [[cur_loc updates] |] eqn:Hcur.
  {
    destruct updates as [| [upd_loc upd0] tl]; simpl; [tauto |].
    intros [Hst [Hret Hupd]] Hrecent.
    inversion Hrecent; subst.
    subst.
    reflexivity.
  }
  intros [orig_loc [orig_final [orig_state [cur_loc [Horig [Hupd Hst]]]]]]
    Hrecent.
  destruct (mapModelLookup (preTxAssumedState st) addr)
    as [[old_loc old_state] |] eqn:Horig_lookup; simpl in Hrecent;
    [| discriminate].
  destruct (preTxState old_state) as [old_ac |] eqn:Hpre; inversion Hrecent;
    subst old_ac.
  unfold state_original_account_state_post in Horig.
  rewrite Horig_lookup in Horig.
  destruct Horig as [_ [_ Hstate]].
  subst orig_state upd.
  simpl.
  exact Hpre.
Qed.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  Definition add_to_balance_final_update (delta : N)
      (upd : UpdatedAccountState) : UpdatedAccountState :=
    match postTxState upd with
    | Some ac => updated_account_add_to_balance_model upd ac delta
    | None => upd
    end.

  #[local] Hint Opaque
    optional_account_has_value_spec
    optional_account_value_spec
    account_dtor_spec
    incarnation_dtor_spec
    uint256_max_spec
    account_substate_touch_spec
    state_current_account_state_update_spec
    u256R
    optional_specs.optionR
    StateR
    AccountStateRcore
    AccountSubstateR
    StorageMapR : sl_opacity.

  Local Transparent AccountR UpdatedAccountStateR AccountStateRcore.

  Lemma AccountR_account_set_balance_fold
      (p : ptr) (ac : AccountM) (bal : N) :
    (bal < 2 ^ 256)%N ->
    p ,, o_field CU "monad::Account::balance" |-> u256R 1 bal
    ** p ,, o_field CU "monad::Account::code_hash" |-> bytes32R 1
         (code_hash_of_program (block.block_account_code (coreAc ac)))
    ** p ,, o_field CU "monad::Account::nonce" |-> primR "unsigned long" 1$m
         (w256_to_Z (block.block_account_nonce (coreAc ac)))
    ** p ,, o_field CU "monad::Account::incarnation" |-> IncarnationR 1
         (incarnation ac)
    ** p |-> structR "monad::Account"%cpp_name 1$m
    |-- p |-> AccountR 1 (account_set_balance ac bal).
  Proof using CU MODd Sigma.
    intro Hbal.
    destruct ac as [core inc keys bal0].
    destruct core.
    unfold AccountR, account_set_balance.
    simpl in *.
    rewrite (w256_to_N_Z_to_w256_small bal Hbal).
    go.
  Qed.

  Definition AccountR_account_set_balance_fold_B p ac bal Hbal :=
    [BWD] (AccountR_account_set_balance_fold p ac bal Hbal).

  Lemma use_wand_local_r (P Q : mpred) : P ** (P -* Q) |-- Q.
  Proof using.
    exact (bi.wand_elim_r P Q).
  Qed.

  Definition use_wand_local_r_F P Q :=
    [FWD] (use_wand_local_r P Q).

  Lemma use_current_update_forall_wand
      (this p : ptr) (st_current : StateM)
      (addr : evmopsem.evm.address)
      (upd : UpdatedAccountState)
      (upd_final : UpdatedAccountState) :
    p |-> UpdatedAccountStateR 1 upd_final
    ** (Forall G : UpdatedAccountState -> UpdatedAccountState,
        p |-> UpdatedAccountStateR 1 (G upd) -*
        this |-> StateR (state_update_current_account st_current addr (G upd)))
    |-- this |-> StateR (state_update_current_account st_current addr upd_final).
  Proof using CU MODd Sigma.
    change upd_final with ((fun _ => upd_final) upd).
    go using use_wand_local_r_F.
  Qed.

  Definition use_current_update_forall_wand_F
      this p st_current addr upd upd_final :=
    [FWD] (use_current_update_forall_wand
      this p st_current addr upd upd_final).

  Lemma StorageMapR_account_set_balance (p : ptr) q ac bal :
    p |-> StorageMapR q (storageMapOf (Some ac))
    |-- p |-> StorageMapR q
          (storageMapOf (Some (account_set_balance ac bal))).
  Proof using CU MODd Sigma.
    rewrite storageMapOf_account_set_balance.
    go.
  Qed.

  Definition StorageMapR_account_set_balance_F p q ac bal :=
    [FWD] (StorageMapR_account_set_balance p q ac bal).

  Lemma AccountStateRcore_separated_fold
      (p : ptr) q acct_opt transient_map :
    p ,, o_field CU "monad::AccountState::account_"
      |-> optional_specs.optionR "monad::Account"%cpp_type
            AccountR (cQp.mut q) acct_opt
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

  Lemma UpdatedAccountStateR_separated_fold
      (p : ptr) q upd :
    p |-> AccountStateRcore q (postTxState upd)
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR q (substateModel upd)
    |-- p |-> UpdatedAccountStateR q upd.
  Proof using CU MODd Sigma.
    go.
  Qed.

  Lemma UpdatedAccountStateR_add_to_balance_fold
      (p : ptr) (upd : UpdatedAccountState) (ac : AccountM) (delta : N) :
    postTxState upd = Some ac ->
    p |-> AccountStateRcore 1
          (Some (account_set_balance ac (balance ac + delta)))
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1
              (account_substate_touch_model (substateModel upd))
    |--
    p |-> UpdatedAccountStateR 1
          (updated_account_add_to_balance_model upd ac delta).
  Proof using CU MODd Sigma.
    intro Hpost.
    unfold UpdatedAccountStateR, updated_account_add_to_balance_model,
      account_add_to_balance_model.
    go.
  Qed.

  Definition UpdatedAccountStateR_add_to_balance_fold_B p upd ac delta Hpost :=
    [BWD] (UpdatedAccountStateR_add_to_balance_fold p upd ac delta Hpost).

  Lemma use_add_to_balance_update_wand
      (this p : ptr) (st_current : StateM)
      (addr : evmopsem.evm.address)
      (upd : UpdatedAccountState) (ac : AccountM) (delta : N) :
    postTxState upd = Some ac ->
    p |-> AccountStateRcore 1
          (Some (account_set_balance ac (balance ac + delta)))
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1
              (account_substate_touch_model (substateModel upd))
    ** (Forall F : UpdatedAccountState -> UpdatedAccountState,
        p |-> UpdatedAccountStateR 1 (F upd) -*
        this |-> StateR (state_update_current_account st_current addr (F upd)))
    |-- this |-> StateR
          (state_update_current_account st_current addr
             (updated_account_add_to_balance_model upd ac delta)).
  Proof using CU MODd Sigma.
    intro Hpost.
    transitivity
      (p |-> UpdatedAccountStateR 1
            (updated_account_add_to_balance_model upd ac delta)
       ** (Forall F : UpdatedAccountState -> UpdatedAccountState,
           p |-> UpdatedAccountStateR 1 (F upd) -*
           this |-> StateR
             (state_update_current_account st_current addr (F upd))))%I.
    {
      go using UpdatedAccountStateR_add_to_balance_fold_B.
    }
    exact (use_current_update_forall_wand this p st_current addr upd
      (updated_account_add_to_balance_model upd ac delta)).
  Qed.

  Definition use_add_to_balance_update_wand_F
      this p st_current addr upd ac delta Hpost :=
    [FWD] (use_add_to_balance_update_wand
      this p st_current addr upd ac delta Hpost).

  Lemma state_add_to_balance_post_update_current_account
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (delta : N) (retp : ptr) (upd : UpdatedAccountState) (ac : AccountM) :
    state_current_account_state_post st addr st_current retp upd ->
    postTxState upd = Some ac ->
    state_add_to_balance_post st addr delta
      (state_update_current_account st_current addr
         (updated_account_add_to_balance_model upd ac delta)).
  Proof using.
    intros Hpost Hpost_tx.
    unfold state_add_to_balance_post.
    exists st_current, retp, upd, ac.
    repeat split; eauto; reflexivity.
  Qed.

  Lemma prf_state_add_to_balance :
    verify[state_cpp.source] state_add_to_balance_spec.
  Proof using MODd.
    verify_spec.
    match goal with
    | H : exists ac, _ |- _ =>
        destruct H as [ac [Hrecent Hoverflow]]
    end.
    go.
    iExists preBlockState, bs, qb.
    go.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd |- _ =>
        pose proof
          (state_current_account_state_post_recent_some
             st st_current addr retp upd ac Hpost Hrecent)
          as Hacct
    end.
    unfold add_to_balance_final_update in *.
    rewrite Hacct.
    cbv delta [AccountStateRcore].
    cbn [updated_account_add_to_balance_model].
    go.
    iExists ac.
    go.
    iExists (substateModel t).
    go.
    assert (Hadd_lt : (balance ac + delta < 2 ^ 256)%N) by lia.
    assert (Hadd_mod :
      ((balance ac + delta) mod 2 ^ 256 = balance ac + delta)%N).
    { apply N.mod_small. exact Hadd_lt. }
    match goal with
    | Hbal : balance ac =
        w256_to_N (block.block_account_balance (coreAc ac)) |- _ =>
        rewrite <- Hbal
    end.
    rewrite Hadd_mod.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd |- _ =>
        iExists
          (state_update_current_account st_current addr
             (updated_account_add_to_balance_model upd ac delta))
    end.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd |- _ =>
        let storagep :=
          constr:(retp ,, o_field CU "monad::AccountState::storage_") in
        pose proof
          (StorageMapR_account_set_balance
             storagep 1
             ac
             (balance ac + delta))
          as Hstorage_model
    end.
    wapply Hstorage_model.
    go using use_wand_local_r_F.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd |- _ =>
        pose proof
          (AccountStateRcore_separated_fold
             retp 1
             (Some
                (account_set_balance ac
                   (balance ac + delta)))
             transient_map) as Hfold_core_ent;
        wapply Hfold_core_ent
    end.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd |- _ =>
        let accountp :=
          constr:(retp ,, o_field CU "monad::AccountState::account_"
                    ,, optional_specs.value_offset
                         "monad::Account"%cpp_type) in
        pose proof
          (AccountR_account_set_balance_fold
             accountp ac (balance ac + delta) Hadd_lt)
          as Hfold_account_ent;
        wapply Hfold_account_ent
    end.
    go using
      use_add_to_balance_update_wand_F,
      state_add_to_balance_post_update_current_account.
  Qed.
End with_Sigma.
