Require Import monad.proofs.misc.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.dippedlam_lemmas.
Require monad.proofs.execproofs.reservebal.current_account_state_proof.
Require monad.proofs.execproofs.reservebal.check_min_balance_proof.
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

  Remove Hints LearnEq1_StateCodeMapR : typeclass_instances.

  #[local] Existing Instance state_current_account_state_update_spec_spec_instance.
  #[local] Existing Instance state_check_min_balance_slice_spec_spec_instance.

  Definition subtract_from_balance_final_update (delta : N)
      (upd : UpdatedAccountState) : UpdatedAccountState :=
    match postTxState upd with
    | Some ac => updated_account_subtract_from_balance_model upd ac delta
    | None => upd
    end.

  Definition subtract_from_balance_final_state
      (st_current : StateM) (addr : evmopsem.evm.address)
      (delta : N) (upd : UpdatedAccountState) (ac : AccountM) : StateM :=
    state_update_current_account
      (update_assum_exactness_state_at st_current addr
         (fun ex =>
            min_balance_update ex
              (original_balance_pessimistic_model_map
                 (preTxAssumedState st_current) addr)
              (balance ac)
              delta))
      addr
      (updated_account_subtract_from_balance_model upd ac delta).

  #[local] Hint Opaque
    optional_account_has_value_spec
    optional_account_value_spec
    account_dtor_spec
    incarnation_dtor_spec
    uint256_max_spec
    account_substate_touch_spec
    state_current_account_state_update_spec
    state_check_min_balance_slice_spec
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
      (upd : UpdatedAccountState) :
    p |-> UpdatedAccountStateR 1 upd
    ** (Forall F : UpdatedAccountState -> UpdatedAccountState,
        p |-> UpdatedAccountStateR 1 (F upd) -*
        this |-> StateR (state_update_current_account st_current addr (F upd)))
    |-- this |-> StateR (state_update_current_account st_current addr upd).
  Proof using CU MODd Sigma.
    go using use_wand_local_r_F.
  Qed.

  Definition use_current_update_forall_wand_F this p st_current addr upd :=
    [FWD] (use_current_update_forall_wand this p st_current addr upd).

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
    unfold UpdatedAccountStateR.
    go.
  Qed.

  Definition UpdatedAccountStateR_separated_fold_B p q upd :=
    [BWD] (UpdatedAccountStateR_separated_fold p q upd).

  Lemma optionR_account_some_separated_fold
      (p : ptr) (acct : AccountM) :
    p ,, optional_specs.value_offset "monad::Account"%cpp_type
      |-> AccountR 1 acct
    ** p |-> optional_specs.spineR "monad::Account" 1$m
         (Some (p ,, optional_specs.value_offset "monad::Account"))
    |-- p |-> optional_specs.optionR "monad::Account"%cpp_type
          AccountR 1$m (Some acct).
  Proof using CU MODd Sigma.
    go.
  Qed.

  Definition optionR_account_some_separated_fold_B p acct :=
    [BWD] (optionR_account_some_separated_fold p acct).

  Lemma use_updated_account_state_wand_some
      (p : ptr) (upd : UpdatedAccountState) (ac : AccountM)
      (transient_map : list (N * N)) (Q : mpred) :
    postTxState upd = Some ac ->
    p ,, o_field CU "monad::AccountState::account_" ,,
      optional_specs.value_offset "monad::Account"%cpp_type
        |-> AccountR 1 ac
    ** p ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.spineR "monad::Account" 1$m
          (Some (p ,, o_field CU "monad::AccountState::account_" ,,
            optional_specs.value_offset "monad::Account"))
    ** p ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR 1 (storageMapOf (Some ac))
    ** p ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR 1 transient_map
    ** p |-> structR "monad::AccountState"%cpp_name 1$m
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 (substateModel upd)
    ** (p |-> UpdatedAccountStateR 1 upd -* Q)
    |-- Q.
  Proof using CU MODd Sigma.
    intro Hpost.
    etrans.
    2: exact (bi.wand_elim_r (p |-> UpdatedAccountStateR 1 upd) Q).
    unfold UpdatedAccountStateR, AccountStateRcore.
    rewrite Hpost.
    go using optionR_account_some_separated_fold_B.
    iExists transient_map.
    go using optionR_account_some_separated_fold_B.
  Qed.

  Lemma UpdatedAccountStateR_some_fold
      (p : ptr) (upd : UpdatedAccountState) (ac : AccountM)
      (transient_map : list (N * N)) :
    postTxState upd = Some ac ->
    p ,, o_field CU "monad::AccountState::account_" ,,
      optional_specs.value_offset "monad::Account"%cpp_type
        |-> AccountR 1 ac
    ** p ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.spineR "monad::Account" 1$m
          (Some (p ,, o_field CU "monad::AccountState::account_" ,,
            optional_specs.value_offset "monad::Account"))
    ** p ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR 1 (storageMapOf (Some ac))
    ** p ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR 1 transient_map
    ** p |-> structR "monad::AccountState"%cpp_name 1$m
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 (substateModel upd)
    |-- p |-> UpdatedAccountStateR 1 upd.
  Proof using CU MODd Sigma.
    intro Hpost.
    unfold UpdatedAccountStateR, AccountStateRcore.
    rewrite Hpost.
    go using optionR_account_some_separated_fold_B.
    iExists transient_map.
    go using optionR_account_some_separated_fold_B.
  Qed.

  Definition UpdatedAccountStateR_some_fold_F p upd ac transient_map Hpost :=
    [FWD] (UpdatedAccountStateR_some_fold
      p upd ac transient_map Hpost).

  Lemma state_update_current_account_post_self
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (retp : ptr) (upd : UpdatedAccountState) :
    state_current_account_state_post st addr st_current retp upd ->
    state_update_current_account st_current addr upd = st_current.
  Proof using.
  Admitted.

  Lemma use_updated_account_state_update_wand_some
      (this p : ptr) (st_current : StateM)
      (addr : evmopsem.evm.address)
      (upd : UpdatedAccountState) (ac : AccountM)
      (transient_map : list (N * N)) :
    postTxState upd = Some ac ->
    state_update_current_account st_current addr upd = st_current ->
    p ,, o_field CU "monad::AccountState::account_" ,,
      optional_specs.value_offset "monad::Account"%cpp_type
        |-> AccountR 1 ac
    ** p ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.spineR "monad::Account" 1$m
          (Some (p ,, o_field CU "monad::AccountState::account_" ,,
            optional_specs.value_offset "monad::Account"))
    ** p ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR 1 (storageMapOf (Some ac))
    ** p ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR 1 transient_map
    ** p |-> structR "monad::AccountState"%cpp_name 1$m
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 (substateModel upd)
    ** (Forall F : UpdatedAccountState -> UpdatedAccountState,
        p |-> UpdatedAccountStateR 1 (F upd) -*
        this |-> StateR (state_update_current_account st_current addr (F upd)))
    |-- this |-> StateR st_current.
  Proof using CU MODd Sigma.
    intros Hpost Hself.
    replace (this |-> StateR st_current) with
      (this |-> StateR (state_update_current_account st_current addr upd)).
    2:{
      rewrite Hself.
      reflexivity.
    }
    go using
      UpdatedAccountStateR_some_fold_F,
      use_current_update_forall_wand_F.
  Qed.

  Lemma state_current_account_state_post_current_lookup
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (retp : ptr) (upd : UpdatedAccountState) :
    state_current_account_state_post st addr st_current retp upd ->
    exists cur_loc tl,
      mapModelLookup (newStates st_current) addr =
      Some (cur_loc, (retp, upd) :: tl).
  Proof using.
    unfold state_current_account_state_post.
    destruct (mapModelLookup (newStates st) addr)
      as [[cur_loc updates] |] eqn:Hlookup.
    {
      destruct updates as [| [upd_loc upd0] tl]; simpl; [tauto |].
      intros [-> [-> ->]].
      exists cur_loc, tl.
      exact Hlookup.
    }
    {
      intros [orig_loc [orig_final [orig_state [cur_loc [Horig [-> ->]]]]]].
      exists cur_loc, [].
      unfold mapModelLookup.
      simpl.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_ | Hcontra].
      2:{ contradiction Hcontra; reflexivity. }
      reflexivity.
    }
  Qed.

  Lemma state_current_account_state_post_blockStatePtr
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (retp : ptr) (upd : UpdatedAccountState) :
    state_current_account_state_post st addr st_current retp upd ->
    blockStatePtr st_current = blockStatePtr st.
  Proof using.
    unfold state_current_account_state_post.
    destruct (mapModelLookup (newStates st) addr)
      as [[cur_loc updates] |] eqn:Hlookup.
    {
      destruct updates as [| [upd_loc upd0] tl]; simpl; [tauto |].
      intros [-> [-> ->]].
      reflexivity.
    }
    {
      intros [orig_loc [orig_final [orig_state [cur_loc [Horig [-> ->]]]]]].
      reflexivity.
    }
  Qed.

  Lemma validModel_original_lookup_of_current_lookup
      (st : StateM) (addr : evmopsem.evm.address)
      (loc : ptr) (updates : list (ptr * UpdatedAccountState)) :
    validModel st ->
    mapModelLookup (newStates st) addr = Some (loc, updates) ->
    is_Some (mapModelLookup (preTxAssumedState st) addr).
  Proof using.
    intros [Hsub _] Hlookup.
    apply mapModelLookup_is_Some_of_mem.
    apply Hsub.
    apply mapModelLookup_is_Some_implies_mem.
    eexists.
    exact Hlookup.
  Qed.

  Lemma borrow_current_head_slice_payload
      (map_ptr : ptr)
      (qcur : Qp)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState))
      (idx : nat) :
    nth_error (map (fun '(a1, (b0, _)) => (a1, b0)) cur) idx =
      Some (addr, loc) ->
    map_ptr |-> AnkerMapSliceR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR
          (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          qcur addr ((upd_loc, upd) :: tl)
          (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
    |--
    map_ptr |-> ankerl_specs.AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR qcur
          (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
        |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** upd_loc |-> UpdatedAccountStateR 1 upd
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0).
  Proof using CU MODd Sigma.
    intro Hnth.
    unfold AnkerMapSliceR, VersionStackR.
    go.
    match goal with
    | Hnodup : NoDup _ |- _ =>
        rename Hnodup into Hnodup_spine
    end.
    match goal with
    | |- context [nth_error ?xs (N.to_nat ?j)] =>
        destruct (nth_error xs (N.to_nat j)) as [[k loc0] |] eqn:Hj
    end.
    {
      go.
      pose proof
        (nodup_map_fst_nth_error_eq_nat
           (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
           idx (N.to_nat i) k loc loc0 Hnodup_spine Hnth Hj)
        as Hidx.
      rewrite <- Hidx in Hj.
      rewrite Hnth in Hj.
      inversion Hj; subst loc0.
      go.
    }
    {
      go.
    }
  Qed.

  Definition borrow_current_head_slice_payload_F
      map_ptr qcur cur addr loc upd_loc upd tl i Hnth :=
    [FWD] (borrow_current_head_slice_payload
             map_ptr qcur cur addr loc upd_loc upd tl i Hnth).

  Lemma state_original_account_state_post_noop_of_is_some
      (orig orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr) (orig_state : AssumedPreTxAccountState) :
    is_Some (mapModelLookup orig addr) ->
    state_original_account_state_post orig addr orig_final loc orig_state ->
    orig_final = orig.
  Proof using.
    unfold state_original_account_state_post.
    destruct (mapModelLookup orig addr) as [[old_loc old_state] |].
    {
      intros _ [-> _].
      reflexivity.
    }
    {
      intros [[x Hlookup]] _.
      discriminate.
    }
  Qed.

  Lemma current_spine_map_replace_current_account_update_direct
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    map (fun '(a, (b, _)) => (a, b))
      (replace_current_account_update addr upd_final cur) =
    map (fun '(a, (b, _)) => (a, b)) cur.
  Proof using.
    unfold replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    {
      destruct (asbool (a = addr)); simpl; rewrite IH; reflexivity.
    }
  Qed.

  Lemma map_fst_replace_current_account_update_direct
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    map fst (replace_current_account_update addr upd_final cur) =
    map fst cur.
  Proof using.
    unfold replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    {
      destruct (bool_decide (a = addr)); simpl; rewrite IH; reflexivity.
    }
  Qed.

  Lemma replace_current_account_update_notin
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    addr ∉ map fst cur ->
    replace_current_account_update addr upd_final cur = cur.
  Proof using.
    unfold replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    intros Hnotin.
    apply not_elem_of_cons in Hnotin as [Ha Hnotin].
    rewrite bool_decide_false.
    2:{ intro Heq; apply Ha; symmetry; exact Heq. }
    simpl.
    rewrite IH; [reflexivity | exact Hnotin].
  Qed.

  Lemma removeKey_replace_current_account_update_direct
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    removeKey (replace_current_account_update addr upd_final cur) addr =
    removeKey cur addr.
  Proof using.
    unfold removeKey, replace_current_account_update.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    destruct (decide (a = addr)) as [-> | Ha].
    {
      rewrite (bool_decide_eq_true_2 (addr = addr)); [| reflexivity].
      rewrite (bool_decide_eq_false_2 (addr <> addr)); [| tauto].
      exact IH.
    }
    {
      rewrite (bool_decide_eq_false_2 (a = addr)); [| exact Ha].
      rewrite (bool_decide_eq_true_2 (a <> addr)); [| exact Ha].
      simpl.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma nth_error_replace_current_account_update_direct
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (upd_final : UpdatedAccountState)
      (i : nat) (loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    nth_error cur i = Some (addr, (loc, (upd_loc, upd) :: tl)) ->
    nth_error (replace_current_account_update addr upd_final cur) i =
      Some (addr, (loc, (upd_loc, upd_final) :: tl)).
  Proof using.
    revert i.
    induction cur as [| [a [loc0 updates0]] cur IH]; intros [| i] Hnth;
      simpl in *; try discriminate.
    {
      destruct (bool_decide (a = addr)) eqn:Ha.
      {
        apply bool_decide_eq_true in Ha.
        subst a.
        destruct updates0 as [| [upd_loc0 upd0] tl0]; simpl in *;
          inversion Hnth; subst.
        reflexivity.
      }
      {
        apply bool_decide_eq_false in Ha.
        inversion Hnth; subst.
        contradiction.
      }
    }
    {
      exact (IH i Hnth).
    }
  Qed.

  Lemma mapModelLookup_replace_current_account_update_head_direct
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd upd_final : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    NoDup (map fst cur) ->
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    mapModelLookup (replace_current_account_update addr upd_final cur) addr =
      Some (loc, (upd_loc, upd_final) :: tl).
  Proof using.
    induction cur as [| [a [loc0 updates0]] cur IH]; intros Hnodup Hlookup;
      simpl in *.
    {
      unfold mapModelLookup in Hlookup.
      rewrite lookup_empty in Hlookup.
      discriminate.
    }
    inversion Hnodup as [| ? ? Hnotin Hnodup_tl]; subst.
    unfold mapModelLookup in Hlookup |- *.
    simpl in Hlookup |- *.
    destruct (decide (a = addr)) as [-> | Ha].
    {
      rewrite lookup_insert in Hlookup.
      inversion Hlookup; subst loc0 updates0; clear Hlookup.
      rewrite bool_decide_true; [| reflexivity].
      simpl.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_ | Hcontra].
      2:{ contradiction Hcontra; reflexivity. }
      reflexivity.
    }
    {
      rewrite lookup_insert_ne in Hlookup.
      2:{ exact Ha. }
      rewrite bool_decide_false; [| exact Ha].
      simpl.
      rewrite lookup_insert_ne.
      2:{ exact Ha. }
      exact (IH Hnodup_tl Hlookup).
    }
  Qed.

  Lemma mapModelLookup_replace_current_account_update_ne
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr a : evmopsem.evm.address)
      (upd_final : UpdatedAccountState) :
    a <> addr ->
    mapModelLookup (replace_current_account_update addr upd_final cur) a =
    mapModelLookup cur a.
  Proof using.
    intro Hneq.
    unfold replace_current_account_update, mapModelLookup.
    induction cur as [| [k [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    destruct (decide (k = a)) as [-> | Hka].
    {
      rewrite bool_decide_false; [| exact Hneq].
      simpl.
      repeat rewrite lookup_insert.
      cbn.
      destruct (decide (a = a)) as [_ | Hcontra].
      2:{ contradiction Hcontra; reflexivity. }
      reflexivity.
    }
    destruct (decide (k = addr)) as [-> | Hkaddr].
    {
      rewrite bool_decide_eq_true_2; [| reflexivity].
      simpl.
      repeat (rewrite lookup_insert_ne; [| exact Hka]).
      rewrite IH.
      reflexivity.
    }
    {
      rewrite bool_decide_eq_false_2; [| exact Hkaddr].
      simpl.
      repeat (rewrite lookup_insert_ne; [| exact Hka]).
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma state_original_account_state_post_lookup_of_is_some
      (orig orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (loc : ptr) (orig_state : AssumedPreTxAccountState) :
    is_Some (mapModelLookup orig addr) ->
    state_original_account_state_post orig addr orig_final loc orig_state ->
    mapModelLookup orig addr = Some (loc, orig_state).
  Proof using.
    unfold state_original_account_state_post.
    destruct (mapModelLookup orig addr) as [[old_loc old_state] |] eqn:Hlookup.
    {
      intros _ [_ [-> ->]].
      reflexivity.
    }
    {
      intros [[x Hnone]] _.
      discriminate.
    }
  Qed.

  Lemma validModel_state_update_current_account_some
      (st : StateM) (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd upd_final : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    NoDup (map fst (newStates st)) ->
    validModel st ->
    mapModelLookup (newStates st) addr = Some (loc, (upd_loc, upd) :: tl) ->
    is_Some (postTxState upd_final) ->
    validModel (state_update_current_account st addr upd_final).
  Proof using.
    intros Hnodup [Hsub [Hstate Hpost]] Hlookup Hsome.
    unfold validModel.
    split.
    {
      rewrite map_fst_replace_current_account_update_direct.
      exact Hsub.
    }
    split.
    {
      intro a.
      unfold validStateM in Hstate.
      unfold assumptionAndUpdateOfAddr, state_update_current_account,
        state_with_preTxAssumedState_and_newStates.
      simpl.
      specialize (Hstate a).
      unfold assumptionAndUpdateOfAddr in Hstate.
      destruct (preTxAssumedState st !! a) as [[loc0 aps] |];
        simpl in *; exact Hstate.
    }
    {
      intros a loc0 tl0 orig_loc aps Hnew Hpre.
      unfold state_update_current_account,
        state_with_preTxAssumedState_and_newStates in Hnew, Hpre.
      simpl in Hnew, Hpre.
      destruct (decide (a = addr)) as [-> | Hneq].
      {
        rewrite (mapModelLookup_replace_current_account_update_head_direct
          (newStates st) addr loc upd_loc upd upd_final tl Hnodup Hlookup)
          in Hnew.
        inversion Hnew; subst loc0 tl0; clear Hnew.
        destruct Hsome as [ac_final Hfinal].
        rewrite Hfinal.
        discriminate.
      }
      {
        rewrite mapModelLookup_replace_current_account_update_ne in Hnew;
          [| exact Hneq].
        exact (Hpost a loc0 tl0 orig_loc aps Hnew Hpre).
      }
    }
  Qed.

  Lemma validModel_subtract_from_balance_final_state
      (st st_current : StateM)
      (addr : evmopsem.evm.address) (delta : N)
      (cur_loc retp : ptr) (upd : UpdatedAccountState)
      (cur_tl : list (ptr * UpdatedAccountState))
      (ac : AccountM) (orig_loc : ptr)
      (orig_state : AssumedPreTxAccountState) :
    NoDup (map fst (newStates st_current)) ->
    validModel st_current ->
    mapModelLookup (newStates st_current) addr =
      Some (cur_loc, (retp, upd) :: cur_tl) ->
    state_original_account_state_post
      (preTxAssumedState st_current) addr
      (preTxAssumedState st_current) orig_loc orig_state ->
    is_Some (mapModelLookup (preTxAssumedState st_current) addr) ->
    postTxState upd = Some ac ->
    validModel (subtract_from_balance_final_state st_current addr delta upd ac).
  Proof using.
    intros Hnodup Hvalid Hcur Horig Horig_some Hacct.
    pose proof
      (state_original_account_state_post_lookup_of_is_some
         (preTxAssumedState st_current) (preTxAssumedState st_current)
         addr orig_loc orig_state Horig_some Horig) as Horig_lookup.
    unfold subtract_from_balance_final_state.
    rewrite <- check_min_balance_proof.original_balance_pessimistic_model_eq_map.
    eapply validModel_state_update_current_account_some.
    {
      exact Hnodup.
    }
    {
      eapply check_min_balance_proof.validModel_update_assum_exactness_state_at_min_balance;
        eauto.
    }
    {
      simpl.
      exact Hcur.
    }
    {
      eexists.
      reflexivity.
    }
  Qed.

  Lemma account_code_account_set_balance (ac : AccountM) (bal : N) :
    account_code (account_set_balance ac bal) = account_code ac.
  Proof using.
    destruct ac as [core inc keys old_bal].
    destruct core.
    reflexivity.
  Qed.

  Lemma code_entry_of_updates_subtract_from_balance
      (upd : UpdatedAccountState) (ac : AccountM) (delta : N)
      (retp : ptr) (tl : list (ptr * UpdatedAccountState)) :
    postTxState upd = Some ac ->
    code_entry_of_updates
      ((retp, updated_account_subtract_from_balance_model upd ac delta) :: tl) =
    code_entry_of_updates ((retp, upd) :: tl).
  Proof using.
    intro Hacct.
    unfold code_entry_of_updates, updated_account_subtract_from_balance_model,
      account_subtract_from_balance_model.
    simpl.
    rewrite Hacct.
    rewrite account_code_account_set_balance.
    reflexivity.
  Qed.

  Lemma code_entries_of_state_replace_current_account_update_subtract
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc retp : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState))
      (ac : AccountM) (delta : N) :
    NoDup (map fst cur) ->
    mapModelLookup cur addr = Some (loc, (retp, upd) :: tl) ->
    postTxState upd = Some ac ->
    code_entries_of_state
      (replace_current_account_update addr
         (updated_account_subtract_from_balance_model upd ac delta) cur) =
    code_entries_of_state cur.
  Proof using.
    induction cur as [| [a [loc0 updates0]] cur IH];
      intros Hnodup Hlookup Hacct; simpl in *.
    {
      unfold mapModelLookup in Hlookup.
      rewrite lookup_empty in Hlookup.
      discriminate.
    }
    inversion Hnodup as [| ? ? Hnotin Hnodup_tl]; subst.
    unfold mapModelLookup in Hlookup.
    simpl in Hlookup.
    destruct (decide (a = addr)) as [-> | Ha].
    {
      rewrite lookup_insert in Hlookup.
      inversion Hlookup; subst loc0 updates0; clear Hlookup.
      rewrite bool_decide_true; [| reflexivity].
      simpl.
      rewrite Hacct.
      unfold account_subtract_from_balance_model.
      rewrite account_code_account_set_balance.
      rewrite replace_current_account_update_notin; [reflexivity | exact Hnotin].
    }
    {
      rewrite lookup_insert_ne in Hlookup.
      2:{ exact Ha. }
      rewrite bool_decide_false; [| exact Ha].
      simpl.
      rewrite IH; eauto.
    }
  Qed.

  Lemma codeMapOfPreTxAssumedAccounts_subtract_from_balance_final_state
      (st_current : StateM)
      (addr : evmopsem.evm.address) (delta : N)
      (upd : UpdatedAccountState) (ac : AccountM) :
    codeMapOfPreTxAssumedAccounts
      (subtract_from_balance_final_state st_current addr delta upd ac) =
    codeMapOfPreTxAssumedAccounts st_current.
  Proof using.
    unfold subtract_from_balance_final_state, state_update_current_account,
      update_assum_exactness_state_at, codeMapOfPreTxAssumedAccounts,
      state_with_preTxAssumedState_and_newStates.
    simpl.
    rewrite check_min_balance_proof.code_entries_of_preTxAssumed_update_assum_exactness_at.
    reflexivity.
  Qed.

  Lemma codeMapOfNewStates_subtract_from_balance_final_state
      (st_current : StateM)
      (addr : evmopsem.evm.address) (delta : N)
      (cur_loc retp : ptr) (upd : UpdatedAccountState)
      (cur_tl : list (ptr * UpdatedAccountState))
      (ac : AccountM) :
    NoDup (map fst (newStates st_current)) ->
    mapModelLookup (newStates st_current) addr =
      Some (cur_loc, (retp, upd) :: cur_tl) ->
    postTxState upd = Some ac ->
    codeMapOfNewStates
      (subtract_from_balance_final_state st_current addr delta upd ac) =
    codeMapOfNewStates st_current.
  Proof using.
    intros Hnodup Hcur Hacct.
    unfold subtract_from_balance_final_state, state_update_current_account,
      update_assum_exactness_state_at, codeMapOfNewStates,
      state_with_preTxAssumedState_and_newStates.
    simpl.
    rewrite (code_entries_of_state_replace_current_account_update_subtract
      (newStates st_current) addr cur_loc retp upd cur_tl ac delta
      Hnodup Hcur Hacct).
    reflexivity.
  Qed.

  Lemma all_code_entries_subtract_from_balance_final_state
      (st_current : StateM)
      (addr : evmopsem.evm.address) (delta : N)
      (cur_loc retp : ptr) (upd : UpdatedAccountState)
      (cur_tl : list (ptr * UpdatedAccountState))
      (ac : AccountM) :
    NoDup (map fst (newStates st_current)) ->
    mapModelLookup (newStates st_current) addr =
      Some (cur_loc, (retp, upd) :: cur_tl) ->
    postTxState upd = Some ac ->
    all_code_entries
      (subtract_from_balance_final_state st_current addr delta upd ac) =
    all_code_entries st_current.
  Proof using.
    intros Hnodup Hcur Hacct.
    unfold all_code_entries.
    rewrite (codeMapOfPreTxAssumedAccounts_subtract_from_balance_final_state
      st_current addr delta upd ac).
    unfold subtract_from_balance_final_state, state_update_current_account,
      update_assum_exactness_state_at, state_with_preTxAssumedState_and_newStates.
    simpl.
    rewrite (code_entries_of_state_replace_current_account_update_subtract
      (newStates st_current) addr cur_loc retp upd cur_tl ac delta
      Hnodup Hcur Hacct).
    reflexivity.
  Qed.

  Lemma stateCodeMapInvariants_subtract_from_balance_final_state
      (st st_current : StateM)
      (addr : evmopsem.evm.address) (delta : N)
      (cur_loc retp : ptr) (upd : UpdatedAccountState)
      (cur_tl : list (ptr * UpdatedAccountState))
      (ac : AccountM) :
    NoDup (map fst (newStates st_current)) ->
    stateCodeMapInvariants st_current ->
    mapModelLookup (newStates st_current) addr =
      Some (cur_loc, (retp, upd) :: cur_tl) ->
    postTxState upd = Some ac ->
    stateCodeMapInvariants
      (subtract_from_balance_final_state st_current addr delta upd ac).
  Proof using.
    intros Hnodup Hcode Hcur Hacct.
    unfold stateCodeMapInvariants in *.
    rewrite (codeMapOfNewStates_subtract_from_balance_final_state
      st_current addr delta cur_loc retp upd cur_tl ac Hnodup Hcur Hacct).
    rewrite (codeMapOfPreTxAssumedAccounts_subtract_from_balance_final_state
      st_current addr delta upd ac).
    repeat rewrite (all_code_entries_subtract_from_balance_final_state
      st_current addr delta cur_loc retp upd cur_tl ac Hnodup Hcur Hacct).
    exact Hcode.
  Qed.

  Lemma map_fst_current_spine_map
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    map fst (map (fun '(a, (b, _)) => (a, b)) cur) = map fst cur.
  Proof using.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      reflexivity.
    }
    {
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma NoDup_current_spine_map_to_newStates
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState))) :
    NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) cur)) ->
    NoDup (map fst cur).
  Proof using.
    intro Hnodup.
    rewrite map_fst_current_spine_map in Hnodup.
    exact Hnodup.
  Qed.

  #[local] Hint Resolve
    NoDup_current_spine_map_to_newStates
    validModel_subtract_from_balance_final_state
    stateCodeMapInvariants_subtract_from_balance_final_state : pure.

  Lemma StateCodeMapR_subtract_from_balance_final_state
      (p : ptr) (st_current : StateM)
      (addr : evmopsem.evm.address) (delta : N)
      (upd : UpdatedAccountState) (ac : AccountM) :
    stateCodeMapInvariants
      (subtract_from_balance_final_state st_current addr delta upd ac) ->
    p |-> StateCodeMapR st_current
    |-- p |-> StateCodeMapR
          (subtract_from_balance_final_state st_current addr delta upd ac).
  Proof using CU MODd Sigma.
    intro Hcode_final.
    unfold StateCodeMapR, subtract_from_balance_final_state,
      state_update_current_account, update_assum_exactness_state_at,
      state_with_preTxAssumedState_and_newStates.
    simpl.
    go.
  Qed.

  Definition StateCodeMapR_subtract_from_balance_final_state_F
      p st_current addr delta upd ac Hcode_final :=
    [FWD] (StateCodeMapR_subtract_from_balance_final_state
             p st_current addr delta upd ac Hcode_final).

  Lemma reinsert_updated_current_head_payload_direct
      (map_ptr : ptr)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (loc upd_loc : ptr)
      (upd upd_final : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** upd_loc |-> UpdatedAccountStateR 1 upd_final
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (removeKey cur addr)
    |--
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (replace_current_account_update addr upd_final cur).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, (upd_loc, upd) :: tl)) ∈ cur).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_final :
      nth_error (replace_current_account_update addr upd_final cur)
        (N.to_nat (N.of_nat i)) =
      Some (addr, (loc, (upd_loc, upd_final) :: tl))).
    {
      rewrite Nat2N.id.
      eapply nth_error_replace_current_account_update_direct.
      exact Hnth.
    }
    erewrite (@borrowIndex_at _ _ _ _ 1
      evmopsem.evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
      (replace_current_account_update addr upd_final cur) (N.of_nat i)
      (addr, (loc, (upd_loc, upd_final) :: tl)) addr map_ptr
      Hnth_final eq_refl).
    rewrite removeKey_replace_current_account_update_direct.
    unfold pairR, VersionStackR.
    simpl.
    go.
  Qed.

  Definition reinsert_updated_current_head_payload_direct_B
      map_ptr cur addr loc upd_loc upd upd_final tl Hlookup :=
    [BWD] (reinsert_updated_current_head_payload_direct
             map_ptr cur addr loc upd_loc upd upd_final tl Hlookup).

  Lemma state_subtract_from_balance_post_update_current_account
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (delta : N) (retp : ptr) (upd : UpdatedAccountState) (ac : AccountM) :
    state_current_account_state_post st addr st_current retp upd ->
    postTxState upd = Some ac ->
    state_subtract_from_balance_post st addr delta
      (state_update_current_account
         (update_assum_exactness_state_at st_current addr
            (fun ex =>
               min_balance_update ex
                 (original_balance_pessimistic_model st_current addr)
                 (current_balance_pessimistic_model st_current addr)
                 delta))
         addr
         (updated_account_subtract_from_balance_model upd ac delta)).
  Proof using.
    intros Hpost Hpost_tx.
    unfold state_subtract_from_balance_post.
    exists st_current, retp, upd, ac.
    repeat split; eauto; reflexivity.
  Qed.

  Lemma state_subtract_from_balance_post_final_state
      (st st_current : StateM) (addr : evmopsem.evm.address)
      (delta : N) (cur_loc retp : ptr) (upd : UpdatedAccountState)
      (cur_tl : list (ptr * UpdatedAccountState)) (ac : AccountM) :
    mapModelLookup (newStates st_current) addr =
      Some (cur_loc, (retp, upd) :: cur_tl) ->
    state_current_account_state_post st addr st_current retp upd ->
    postTxState upd = Some ac ->
    state_subtract_from_balance_post st addr delta
      (subtract_from_balance_final_state st_current addr delta upd ac).
  Proof using.
    intros Hcur Hpost Hpost_tx.
    unfold state_subtract_from_balance_post,
      subtract_from_balance_final_state.
    exists st_current, retp, upd, ac.
    repeat split; eauto.
    rewrite check_min_balance_proof.original_balance_pessimistic_model_eq_map.
    rewrite (check_min_balance_proof.current_balance_pessimistic_model_current_lookup
      st_current addr cur_loc retp upd cur_tl Hcur).
    rewrite Hpost_tx.
    reflexivity.
  Qed.

  #[local] Hint Resolve
    state_subtract_from_balance_post_update_current_account
    state_subtract_from_balance_post_final_state : pure.

  Lemma StateR_subtract_from_balance_post_reassemble
      (this : ptr) (st st_current : StateM)
      (addr : evmopsem.evm.address) (delta : N)
      (cur_loc retp : ptr) (upd : UpdatedAccountState)
      (cur_tl : list (ptr * UpdatedAccountState))
      (ac : AccountM)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (orig_loc : ptr) (orig_state : AssumedPreTxAccountState)
      (transient_map : list (N * N)) :
    validModel st_current ->
    stateCodeMapInvariants st_current ->
    mapModelLookup (newStates st_current) addr =
      Some (cur_loc, (retp, upd) :: cur_tl) ->
    state_current_account_state_post st addr st_current retp upd ->
    postTxState upd = Some ac ->
    state_original_account_state_post
      (preTxAssumedState st_current) addr orig_final orig_loc orig_state ->
    is_Some (mapModelLookup (preTxAssumedState st_current) addr) ->
    blockStatePtr st_current = blockStatePtr st ->
    (balance ac - delta < 2 ^ 256)%N ->
    this |-> StateCodeMapR st_current
    ** this ,, o_field CU "monad::State::incarnation_"
        |-> IncarnationR 1 (indices st_current)
    ** this ,, o_field CU "monad::State::relaxed_validation_"
        |-> boolR 1$m (relaxedValidation st_current)
    ** this ,, o_field CU "monad::State::current_"
        |-> AnkerMapPayloadsR
              "monad::Address" "monad::VersionStack<monad::AccountState>"
              addressR
              (VersionStackR "monad::AccountState" UpdatedAccountStateR)
              1 (removeKey (newStates st_current) addr)
    ** cur_loc ,, pairFstOffset
                    "monad::Address" "monad::VersionStack<monad::AccountState>"
        |-> addressR (1 / 2) addr
    ** this ,, o_field CU "monad::State::original_"
        |-> AnkerMapPayloadsR
              "monad::Address" "monad::OriginalAccountState"
              addressR OriginalAccountStateR 1
              (check_min_balance_update_model
                 orig_final addr
                 (check_min_balance_recent_account_model
                    (newStates st_current) addr orig_state)
                 delta)
    ** this ,, o_field CU "monad::State::original_"
        |-> ankerl_specs.AnkerMapSpineR
              "monad::Address" "monad::OriginalAccountState"
              addressToN addressR 1
              (map (fun '(a1, (b0, _)) => (a1, b0))
                 (check_min_balance_update_model
                    orig_final addr
                 (check_min_balance_recent_account_model
                    (newStates st_current) addr orig_state)
                 delta))
    ** this ,, o_field CU "monad::State::block_state_"
        |-> refR<"monad::BlockState"> 1$m (blockStatePtr st)
    ** this ,, o_field CU "monad::State::current_"
        |-> ankerl_specs.AnkerMapSpineR
              "monad::Address" "monad::VersionStack<monad::AccountState>"
              addressToN addressR 1
              (map (fun '(a1, (b0, _)) => (a1, b0)) (newStates st_current))
    ** cur_loc ,, pairSndOffset
                    "monad::Address" "monad::VersionStack<monad::AccountState>"
        |-> VersionStackSpineR "monad::AccountState" 1
              (retp :: map fst cur_tl)
    ** ([∗ list] p ∈ cur_tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** retp |-> structR "monad::AccountState" 1$m
    ** retp ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR 1 (storageMapOf (Some ac))
    ** retp ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR 1 transient_map
    ** retp ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.spineR "monad::Account" 1$m
          (Some (retp ,, o_field CU "monad::AccountState::account_" ,,
            optional_specs.value_offset "monad::Account"))
    ** retp ,, o_field CU "monad::AccountState::account_" ,,
         optional_specs.value_offset "monad::Account"
        |-> structR "monad::Account" 1$m
    ** retp ,, o_field CU "monad::AccountState::account_" ,,
         optional_specs.value_offset "monad::Account" ,,
         o_field CU "monad::Account::incarnation"
        |-> IncarnationR 1 (incarnation ac)
    ** retp ,, o_field CU "monad::AccountState::account_" ,,
         optional_specs.value_offset "monad::Account" ,,
         o_field CU "monad::Account::nonce"
        |-> primR "unsigned long" 1$m
             (w256_to_Z (block.block_account_nonce (coreAc ac)))
    ** retp ,, o_field CU "monad::AccountState::account_" ,,
         optional_specs.value_offset "monad::Account" ,,
         o_field CU "monad::Account::code_hash"
        |-> bytes32R 1
             (code_hash_of_program (block.block_account_code (coreAc ac)))
    ** retp ,, o_field CU "monad::AccountState::account_" ,,
         optional_specs.value_offset "monad::Account" ,,
         o_field CU "monad::Account::balance"
        |-> u256R 1 (balance ac - delta)
    ** retp ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1
              (account_substate_touch_model (substateModel upd))
    |--
    (this ,, o_field CU "monad::State::current_"
       |-> ankerl_specs.AnkerMapSpineR
             "monad::Address" "monad::VersionStack<monad::AccountState>"
             addressToN addressR 1
             (map (fun '(a, (b, _)) => (a, b))
                (newStates
                   (subtract_from_balance_final_state
                      st_current addr delta upd ac)))
     ** this ,, o_field CU "monad::State::current_"
       |-> AnkerMapPayloadsR
             "monad::Address" "monad::VersionStack<monad::AccountState>"
             addressR
             (VersionStackR "monad::AccountState" UpdatedAccountStateR)
             1 (newStates
                  (subtract_from_balance_final_state
                     st_current addr delta upd ac)))
    ** (this ,, o_field CU "monad::State::original_"
       |-> ankerl_specs.AnkerMapSpineR
             "monad::Address" "monad::OriginalAccountState"
             addressToN addressR 1
             (map (fun '(a, (b, _)) => (a, b))
                (preTxAssumedState
                   (subtract_from_balance_final_state
                      st_current addr delta upd ac)))
     ** this ,, o_field CU "monad::State::original_"
       |-> AnkerMapPayloadsR
             "monad::Address" "monad::OriginalAccountState"
             addressR OriginalAccountStateR 1
             (preTxAssumedState
                (subtract_from_balance_final_state
                   st_current addr delta upd ac)))
    ** this ,, o_field CU "monad::State::block_state_"
        |-> refR<"monad::BlockState"> 1$m
             (blockStatePtr
                (subtract_from_balance_final_state
                   st_current addr delta upd ac))
    ** this ,, o_field CU "monad::State::incarnation_"
        |-> IncarnationR 1
             (indices
                (subtract_from_balance_final_state
                   st_current addr delta upd ac))
    ** this ,, o_field CU "monad::State::relaxed_validation_"
        |-> boolR 1$m
             (relaxedValidation
                (subtract_from_balance_final_state
                   st_current addr delta upd ac))
    ** [| validModel
            (subtract_from_balance_final_state
               st_current addr delta upd ac) |]
    ** this |-> StateCodeMapR
         (subtract_from_balance_final_state st_current addr delta upd ac)
    ** [| state_subtract_from_balance_post st addr delta
            (subtract_from_balance_final_state
               st_current addr delta upd ac) |].
  Proof using CU MODd Sigma.
    intros Hvalid Hcode Hcur Hpost Hacct Horig Horig_some Hblock Hbal.
    pose proof
      (state_original_account_state_post_noop_of_is_some
         (preTxAssumedState st_current) orig_final addr orig_loc orig_state
         Horig_some Horig) as Horig_final.
    subst orig_final.
    unfold subtract_from_balance_final_state.
    simpl.
    rewrite Hblock.
    unfold check_min_balance_recent_account_model.
    rewrite Hcur.
    cbn [balanceOfAccount recentAccountOf_stack].
    rewrite Hacct.
    unfold check_min_balance_update_model.
    rewrite current_spine_map_replace_current_account_update_direct.
    pose proof
      (StorageMapR_account_set_balance
         (retp ,, o_field CU "monad::AccountState::storage_")
         1 ac (balance ac - delta))
      as Hstorage_model.
    wapply Hstorage_model.
    go using
      AccountR_account_set_balance_fold_B,
      optionR_account_some_separated_fold_B,
      AccountStateRcore_separated_fold_B,
      UpdatedAccountStateR_separated_fold_B,
      reinsert_updated_current_head_payload_direct_B.
    go using StateCodeMapR_subtract_from_balance_final_state_F.
  Qed.

  Lemma prf_state_subtract_from_balance :
    verify[state_cpp.source] state_subtract_from_balance_spec.
  Proof using MODd.
    verify_spec.
    match goal with
    | H : exists ac, _ |- _ =>
        destruct H as [ac [Hrecent [Hunderflow Hbal_lt]]]
    end.
    go.
    iExists preBlockState, bs, qb.
    go.
    match goal with
    | Hpost : state_current_account_state_post ?st0 ?addr0 ?st_current ?retp ?upd |- _ =>
        pose proof
          (state_current_account_state_post_recent_some
             st st_current addr retp upd ac Hpost Hrecent)
          as Hacct;
        pose (st_current0 := st_current);
        pose (retp0 := retp);
        pose (upd0 := upd)
    end.
    unfold subtract_from_balance_final_update in *.
    rewrite Hacct.
    cbv delta [AccountStateRcore].
    cbn [updated_account_subtract_from_balance_model].
    go.
    pose proof
      (state_update_current_account_post_self
         st st_current0 addr retp0 upd0 H)
      as Hcurrent_self.
    pose proof
      (use_updated_account_state_update_wand_some
         this retp0 st_current0 addr upd0 ac transient_map
         Hacct Hcurrent_self)
      as Huse_current_state_ent.
    wapply Huse_current_state_ent.
    go.
    match goal with
    | Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd,
      Hvalid : validModel ?st_current |- _ =>
        destruct
          (state_current_account_state_post_current_lookup
             st st_current addr retp upd Hpost)
          as [cur_loc [cur_tl Hcur_lookup]];
        pose proof
          (validModel_original_lookup_of_current_lookup
             st_current addr cur_loc ((retp, upd) :: cur_tl)
             Hvalid Hcur_lookup)
          as Horig_some;
        pose proof
          (state_current_account_state_post_blockStatePtr
             st st_current addr retp upd Hpost)
          as Hblock_ptr
    end.
    assert (Hcur_mem :
      (addr, (cur_loc, (retp0, upd0) :: cur_tl)) ∈
      newStates st_current0).
    {
      eapply elem_of_list_to_map_2.
      exact Hcur_lookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hcur_mem)
      as [cur_i Hcur_nth].
    rewrite lookup_nth_error in Hcur_nth.
    pose proof
      (nth_error_map_key_ptr
         (newStates st_current0) cur_i addr cur_loc
         ((retp0, upd0) :: cur_tl) Hcur_nth)
      as Hcur_spine_nth.
    rewrite Hblock_ptr.
    iExists (preTxAssumedState st_current0), preBlockState, bs, qb,
      1%Qp, (newStates st_current0).
    unfold StateCurrentLookupR.
    rewrite Hcur_lookup.
    go using current_account_state_proof.borrow_current_payload_F.
    iExists (N.of_nat cur_i).
    rewrite Nat2N.id.
    rewrite Hcur_spine_nth.
    go using current_account_state_proof.borrow_current_payload_F.
    assert (Hsub_lt : (balance ac - delta < 2 ^ 256)%N) by lia.
    cbv delta [current_balance_pessimistic_model_stack recentAccountOf_stack
      balanceOfAccount].
    cbn beta iota zeta.
    rewrite Hacct.
    unfold check_min_balance_ok.
    rewrite bool_decide_true.
    2: exact Hunderflow.
    go.
    pose proof
      (borrow_current_head_slice_payload
         (this ,, o_field CU "monad::State::current_")
         1 (newStates st_current0) addr cur_loc retp0 upd0 cur_tl
         cur_i Hcur_spine_nth)
      as Hborrow_current_head_payload.
    wapply Hborrow_current_head_payload.
    unfold AnkerMapSliceR.
    go.
    iExists i.
    go.
    rewrite Hacct.
    cbv delta [AccountStateRcore].
    go using use_wand_local_r_F.
    cbv delta [AccountR].
    go.
    match goal with
    | Hbal : balance ac = w256_to_N ?bal |- _ =>
        rewrite <- Hbal
    end.
    iExists ac.
    go using optionR_account_some_separated_fold_B.
    match goal with
    | Hbal : balance ac = w256_to_N ?bal |- _ =>
        rewrite <- Hbal
    end.
    rewrite (u256_sub_mod_small (balance ac) delta Hunderflow Hbal_lt).
    match goal with
    | Hvalid : validModel ?st_current,
      Hcode : stateCodeMapInvariants ?st_current,
      Hcur : mapModelLookup (newStates ?st_current) addr =
               Some (?cur_loc0, (?retp, ?upd) :: ?cur_tl0),
      Hpost : state_current_account_state_post st addr ?st_current ?retp ?upd,
      Hacct0 : postTxState ?upd = Some ac,
      Horig : state_original_account_state_post
                (preTxAssumedState ?st_current) addr ?orig_final ?orig_loc
                ?orig_state,
      Horig_some0 : is_Some
                      (mapModelLookup (preTxAssumedState ?st_current) addr),
      Hblock : blockStatePtr ?st_current = blockStatePtr st
      |- _ =>
        pose proof
          (StateR_subtract_from_balance_post_reassemble
             this st st_current addr delta cur_loc0 retp upd cur_tl0 ac
             orig_final orig_loc orig_state transient_map
             Hvalid Hcode Hcur Hpost Hacct0 Horig Horig_some0 Hblock Hsub_lt)
          as Hfinish_ent
    end.
    iExists (substateModel upd0).
    go.
    iExists (subtract_from_balance_final_state st_current0 addr delta upd0 ac).
    wapply Hfinish_ent.
    go.
  Qed.
End with_Sigma.
