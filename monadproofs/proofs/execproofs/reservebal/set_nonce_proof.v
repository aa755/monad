Require Import monad.proofs.misc.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.execproofs.reservebal.reservebal_specs.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.

Import exec_specs.
Import linearity.

Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".
Open Scope Z_scope.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Lemma w256_to_Z_Z_to_w256_small (z : Z) :
  (0 <= z < 2 ^ 256)%Z ->
  w256_to_Z (Z_to_w256 z) = z.
Proof using.
  intro Hrange.
  unfold w256_to_Z, Z_to_w256.
  rewrite EVMOpSem.Zdigits.Z_to_binary_to_Z.
  - reflexivity.
  - lia.
  - change (two_power_nat 256) with (2 ^ 256)%Z.
    lia.
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

  Definition set_nonce_option_update
      (nonce : Z) (acct_opt : option AccountM) : option AccountM :=
    match acct_opt with
    | Some ac => Some (account_set_nonce_model ac nonce)
    | None => None
    end.

  #[local] Hint Opaque
    optional_account_has_value_spec
    optional_account_value_spec
    account_dtor_spec
    incarnation_dtor_spec
    uint256_int_ctor_spec
    state_current_account_option_spec
    optional_specs.optionR
    StateR
    AccountR : sl_opacity.

  Local Transparent AccountR.

  #[local] Instance learn_optional_spine : LearnEq3 optional_specs.spineR :=
    ltac:(solve_learnable).
  #[local] Instance learn_account_value : LearnEq2 AccountR :=
    ltac:(solve_learnable).

  Definition account_option_layout (p : ptr) (acct : AccountM) : mpred :=
    p |-> optional_specs.spineR "monad::Account" 1$m
      (Some (p ,, optional_specs.value_offset "monad::Account"))
    ** p ,, optional_specs.value_offset "monad::Account"%cpp_type
         |-> AccountR 1 acct.

  Lemma optionR_account_some_separated_fold
      (p : ptr) (acct : AccountM) :
    account_option_layout p acct
    |-- p |-> optional_specs.optionR "monad::Account"%cpp_type
          AccountR 1 (Some acct).
  Proof using CU MODd Sigma.
    unfold account_option_layout.
    go.
  Qed.

  Definition optionR_account_some_separated_fold_B p acct :=
    [BWD] (optionR_account_some_separated_fold p acct).

  Lemma use_option_account_some_wand
      (p : ptr) (acct : AccountM) (Q : mpred) :
    account_option_layout p acct
    ** (p |-> optional_specs.optionR "monad::Account"%cpp_type
          AccountR 1 (Some acct) -* Q)
    |-- Q.
  Proof using CU MODd Sigma.
    etrans.
    - apply bi.sep_mono_l.
      exact (optionR_account_some_separated_fold p acct).
    - exact (bi.wand_elim_r _ _).
  Qed.

  Definition use_option_account_some_wand_F p acct Q :=
    [FWD] (use_option_account_some_wand p acct Q).

  Lemma AccountR_account_set_nonce_fold
      (p : ptr) (ac : AccountM) (nonce : Z) :
    balance ac = w256_to_N (block.block_account_balance (coreAc ac)) ->
    (0 <= nonce < 2 ^ 64)%Z ->
    p ,, o_field CU "monad::Account::balance" |->
      u256R 1 (w256_to_N (block.block_account_balance (coreAc ac)))
    ** p ,, o_field CU "monad::Account::code_hash" |-> bytes32R 1
         (code_hash_of_program (block.block_account_code (coreAc ac)))
    ** p ,, o_field CU "monad::Account::nonce" |->
         primR "unsigned long" 1$m nonce
    ** p ,, o_field CU "monad::Account::incarnation" |-> IncarnationR 1
         (incarnation ac)
    ** p |-> structR "monad::Account"%cpp_name 1$m
    |-- p |-> AccountR 1 (account_set_nonce_model ac nonce).
  Proof using CU MODd Sigma.
    intros Hbal_eq Hnonce.
    destruct ac as [core inc keys bal].
    destruct core.
    unfold AccountR, account_set_nonce_model in *.
    simpl in *.
    rewrite Hbal_eq.
    rewrite (w256_to_Z_Z_to_w256_small nonce).
    - go.
    - lia.
  Qed.

  Definition AccountR_account_set_nonce_fold_B p ac nonce Hbal_eq Hnonce :=
    [BWD] (AccountR_account_set_nonce_fold p ac nonce Hbal_eq Hnonce).

  Opaque account_set_nonce_model.

  Lemma use_wand_local_r (P Q : mpred) : P ** (P -* Q) |-- Q.
  Proof using.
    exact (bi.wand_elim_r P Q).
  Qed.

  Definition use_wand_local_r_F P Q :=
    [FWD] (use_wand_local_r P Q).

  Lemma state_set_nonce_post_update_current_account
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (nonce : Z) (retp : ptr) (upd : UpdatedAccountState) (ac : AccountM) :
    state_current_account_state_post st addr st_current retp upd ->
    postTxState upd = Some ac ->
    state_set_nonce_post st addr nonce
      (state_update_current_account st_current addr
         (updated_account_set_nonce_model upd ac nonce)).
  Proof using.
    intros Hpost Hpost_tx.
    unfold state_set_nonce_post.
    exists st_current, retp, upd, ac.
    repeat split; eauto; reflexivity.
  Qed.

  Lemma finish_set_nonce_optional_update
      (this statep : ptr) (st st_current : StateM)
      (addr : evmopsem.evm.address) (nonce : Z)
      (upd : UpdatedAccountState) (ac : AccountM) :
    state_current_account_state_post st addr st_current statep upd ->
    postTxState upd = Some ac ->
    let optp := statep ,, o_field CU "monad::AccountState::account_" in
    account_option_layout optp (account_set_nonce_model ac nonce)
    ** (optp |-> optional_specs.optionR "monad::Account"%cpp_type
          AccountR 1
          (Some (account_set_nonce_model ac nonce)) -*
        this |-> StateR
          (state_update_current_account st_current addr
             {| postTxState := Some (account_set_nonce_model ac nonce);
                substateModel := substateModel upd |}))
    |-- Exists st_final,
          this |-> StateR st_final
          ** [| state_set_nonce_post st addr nonce st_final |].
  Proof using CU MODd Sigma.
    intros Hpost Hpost_tx.
    simpl.
    etrans.
    - apply bi.sep_mono_l.
      apply optionR_account_some_separated_fold.
    - etrans.
      + exact (bi.wand_elim_r _ _).
      + go using state_set_nonce_post_update_current_account.
  Qed.

  Lemma prf_state_set_nonce :
    verify[state_cpp.source] state_set_nonce_spec.
  Proof using MODd.
    verify_spec.
    match goal with
    | H : exists ac, _ |- _ =>
        destruct H as [ac Hrecent]
    end.
    go.
    iExists (set_nonce_option_update nonce), preBlockState, bs, qb.
    go.
    match goal with
    | Hpost : state_current_account_state_post ?st0 ?addr0 ?st_current ?retp ?upd |- _ =>
        pose proof
          (state_current_account_state_post_recent_some
             st st_current addr retp upd ac Hpost Hrecent)
          as Hacct
    end.
    unfold set_nonce_option_update in *.
    rewrite Hacct.
    go using optional_specs.trivial_optional_some_split_F.
    match goal with
    | Hbal : balance ac =
        w256_to_N (block.block_account_balance (coreAc ac)) |- _ =>
        pose proof Hbal as Hbal_eq
    end.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?statep ?upd |- _ =>
        let accountp :=
          constr:(statep ,, o_field CU "monad::AccountState::account_"
                    ,, optional_specs.value_offset
                         "monad::Account"%cpp_type) in
        pose proof
          (AccountR_account_set_nonce_fold
             accountp ac nonce Hbal_eq (conj a b))
          as Hfold_account_ent;
        wapply Hfold_account_ent
    end.
    go using use_wand_local_r_F.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?statep ?upd |- _ =>
        pose proof
          (finish_set_nonce_optional_update
             this statep st st_current addr nonce upd ac Hpost Hacct)
          as Hfinish_ent;
        wapply Hfinish_ent
    end.
    unfold account_option_layout.
    go.
  Qed.
End with_Sigma.
