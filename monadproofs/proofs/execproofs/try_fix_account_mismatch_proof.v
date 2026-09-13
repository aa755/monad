Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.initialize.
Require Import skylabs.auto.cpp.hints.inline_invoke.
Require Import skylabs.auto.cpp.hints.invoke.
Require Import skylabs.auto.cpp.hints.ptrs.valid.
Require Import skylabs.auto.cpp.tactics4.
Require Import stdpp.gmap.

Import exec_specs.
Import linearity.
Import cQp_compat.

Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".
Set Warnings "-non-reference-hint-using".
Open Scope N_scope.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Definition uint256_modulus : N := (2 ^ 256)%N.

Lemma Z_of_N_uint256_modulus :
  Z.of_N uint256_modulus = two_power_nat 256.
Proof using.
  unfold uint256_modulus.
  change (Z.of_N (2 ^ 256)) with (two_power_nat 256).
  reflexivity.
Qed.

Lemma uint256_modulus_pos : (0 < uint256_modulus)%N.
Proof using.
  unfold uint256_modulus.
  lia.
Qed.

Lemma uint256_word_modulus_eq :
  uint256_word_modulus = uint256_modulus.
Proof using.
  unfold uint256_word_modulus, uint256_modulus.
  reflexivity.
Qed.

Lemma lt_uint256_modulus_of_pow (n : N) :
  (n < 2 ^ 256)%N ->
  (n < uint256_modulus)%N.
Proof using.
  unfold uint256_modulus.
  exact id.
Qed.

Opaque uint256_modulus.

Lemma w256_to_N_Z_to_w256_small (n : N) :
  (n < uint256_modulus)%N ->
  w256_to_N (Z_to_w256 (Z.of_N n)) = n.
Proof using.
  intro Hlt.
  unfold w256_to_N, w256_to_Z, Z_to_w256.
  rewrite EVMOpSem.Zdigits.Z_to_binary_to_Z.
  - apply N2Z.id.
  - lia.
  - pose proof (proj1 (N2Z.inj_lt n uint256_modulus) Hlt) as HltZ.
    rewrite Z_of_N_uint256_modulus in HltZ.
    exact HltZ.
Qed.

Opaque Zdigits.binary_value Zdigits.Z_to_binary.
Opaque w256_to_Z.

Lemma balance_set_core_storage (ac : AccountM) (st : evm.storage) :
  balance ((_coreAc .@ _block_account_storage .= st) ac) =
  balance ac.
Proof using.
  change (balance ((_coreAc .@ _block_account_storage .= st) ac)) with
    (balance (ac &: _coreAc .@ _block_account_storage .= st)).
  apply balance_update_storage.
Qed.

Lemma balance_set_balance (ac : AccountM) (bal : N) :
  balance ((_balance .= bal) ac) = bal.
Proof using.
  change (balance ((_balance .= bal) ac)) with
    (balance (ac &: _balance .= bal)).
  apply balance_update_balance.
Qed.

Lemma balance_set_nonce (ac : AccountM) (nonce : Z) :
  balance ((_nonce .= nonce) ac) = balance ac.
Proof using.
  change (balance ((_nonce .= nonce) ac)) with
    (balance (ac &: _nonce .= nonce)).
  apply balance_update_nonce.
Qed.

Lemma balance_account_set_balance (ac : AccountM) (bal : N) :
  balance (account_set_balance ac bal) = bal.
Proof using.
  unfold account_set_balance.
  rewrite balance_set_balance.
  reflexivity.
Qed.

Create HintDb try_fix_account_balance.
#[local] Hint Rewrite balance_set_core_storage balance_set_balance
  balance_set_nonce balance_account_set_balance : try_fix_account_balance.

Definition try_fix_account_balance_update
    (actual : option AccountM) (orig_state : AssumedPreTxAccountState)
  : AssumedPreTxAccountState :=
  {| preTxState :=
       match preTxState orig_state, actual with
       | Some original, Some actual_ac =>
           Some (account_set_balance original (balance actual_ac))
       | _, _ => preTxState orig_state
       end;
     preTxStorage := preTxStorage orig_state;
     assumExactness := assumExactness orig_state |}.

Lemma try_fix_account_balance_update_some
    (actual_ac original_ac : AccountM)
    (orig_state : AssumedPreTxAccountState) :
  preTxState orig_state = Some original_ac ->
  {| preTxState := Some (account_set_balance original_ac (balance actual_ac));
     preTxStorage := preTxStorage orig_state;
     assumExactness := assumExactness orig_state |} =
  try_fix_account_balance_update (Some actual_ac) orig_state.
Proof using.
  intro Hpre.
  unfold try_fix_account_balance_update.
  rewrite Hpre.
  reflexivity.
Qed.

Definition try_fix_account_original_update
    (actual : option AccountM) (orig_state : AssumedPreTxAccountState)
  : AssumedPreTxAccountState :=
  update_assum_exactness_assumed exact_balance_update
    (try_fix_account_balance_update actual orig_state).

Lemma try_fix_account_original_update_some
    (actual_ac original_ac : AccountM)
    (orig_state : AssumedPreTxAccountState) :
  preTxState orig_state = Some original_ac ->
  update_assum_exactness_assumed exact_balance_update
    {| preTxState := Some (account_set_balance original_ac (balance actual_ac));
       preTxStorage := preTxStorage orig_state;
       assumExactness := assumExactness orig_state |} =
  try_fix_account_original_update (Some actual_ac) orig_state.
Proof using.
  intro Hpre.
  unfold try_fix_account_original_update, try_fix_account_balance_update.
  rewrite Hpre.
  reflexivity.
Qed.

Definition try_fix_account_current_update
    (actual original : AccountM) (upd : UpdatedAccountState)
  : UpdatedAccountState :=
  match postTxState upd with
  | Some recent =>
      let new_balance :=
        if bool_decide (balance original < balance actual)%N then
          N.modulo (balance recent + (balance actual - balance original))%N
            uint256_word_modulus
        else
          Z.to_N
            ((Z.of_N (balance recent) -
              Z.of_N (balance original - balance actual)) mod
             Z.of_N uint256_modulus)%Z in
      {| postTxState := Some (account_set_balance recent new_balance);
         substateModel := substateModel upd |}
  | None => upd
  end.

Definition try_fix_account_updated_orig_map
    (addr : evm.address) (actual : option AccountM)
    (orig : MapModel evm.address AssumedPreTxAccountState)
  : MapModel evm.address AssumedPreTxAccountState :=
  map (fun '(a, (loc, orig_state)) =>
         if bool_decide (a = addr) then
           (a, (loc, try_fix_account_original_update actual orig_state))
         else (a, (loc, orig_state))) orig.

Definition try_fix_account_updated_cur_map
    (addr : evm.address) (actual original : AccountM)
    (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
  : MapModel evm.address (list (ptr * UpdatedAccountState)) :=
  map (fun '(a, (loc, updates)) =>
         if bool_decide (a = addr) then
           (a, (loc,
             match updates with
             | [] => []
             | (upd_loc, upd) :: tl =>
                 (upd_loc, try_fix_account_current_update actual original upd) :: tl
             end))
         else (a, (loc, updates))) cur.

Definition try_fix_account_final_cur_map
    (addr : evm.address) (actual original : AccountM)
    (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
  : MapModel evm.address (list (ptr * UpdatedAccountState)) :=
  match mapModelLookup cur addr with
  | Some _ => try_fix_account_updated_cur_map addr actual original cur
  | None => cur
  end.

Definition try_fix_account_tx_slice
    (orig_loc : ptr) (orig_state : AssumedPreTxAccountState)
    (cur_entry : option (ModelWithPtr (list (ptr * UpdatedAccountState))))
  : TxAssumptionsAndUpdates :=
  {| preAssumption := orig_state;
     originalLoc := orig_loc;
     txUpdates :=
       match cur_entry with
       | Some (cur_loc, [(upd_loc, upd)]) =>
           Some (cur_loc, (upd_loc, upd))
       | _ => None
       end |}.

Definition try_fix_account_final_balance
    (relaxed : bool) (tx : TxAssumptionsAndUpdates)
    (actual : option AccountM) : option N :=
  option_map (fun ac => balance ac mod uint256_word_modulus)
    (accountFinalVal relaxed tx actual).

Definition try_fix_account_mismatch_ret_prop
    (addr : evm.address) (actual : option AccountM)
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
    (relaxed : bool) (orig_loc : ptr)
    (orig_state : AssumedPreTxAccountState) (retb : bool)
    (orig_final : MapModel evm.address AssumedPreTxAccountState)
    (cur_final : MapModel evm.address (list (ptr * UpdatedAccountState)))
  : Prop :=
  if retb then
    match preTxState orig_state, actual with
    | Some original_ac, Some actual_ac =>
        orig_final =
          try_fix_account_updated_orig_map addr (Some actual_ac) orig /\
        cur_final =
          try_fix_account_final_cur_map addr actual_ac original_ac cur /\
        satAccountNonStorageAssumptions relaxed (Some orig_state) actual /\
        try_fix_account_final_balance false
          (try_fix_account_tx_slice orig_loc
             (try_fix_account_original_update (Some actual_ac) orig_state)
             (mapModelLookup cur_final addr))
          actual =
        try_fix_account_final_balance relaxed
          (try_fix_account_tx_slice orig_loc orig_state
             (mapModelLookup cur addr))
          actual
    | _, _ => False
    end
  else
    orig_final = orig /\ cur_final = cur.

Lemma try_fix_account_mismatch_ret_prop_false
    (addr : evm.address) (actual : option AccountM)
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
    (relaxed : bool) (orig_loc : ptr)
    (orig_state : AssumedPreTxAccountState) :
  try_fix_account_mismatch_ret_prop
    addr actual orig cur relaxed orig_loc orig_state false orig cur.
Proof using.
  unfold try_fix_account_mismatch_ret_prop.
  split; reflexivity.
Qed.

#[local] Hint Resolve try_fix_account_mismatch_ret_prop_false : pure.

Definition try_fix_account_balance_mismatch
    (orig_state : AssumedPreTxAccountState) (actual : option AccountM)
  : Prop :=
  match preTxState orig_state, actual with
  | Some original, Some actual_ac =>
      balance original <> balance actual_ac
  | _, _ => True
  end.

Definition try_fix_account_current_top_level
    (cur_entry : option (ModelWithPtr (list (ptr * UpdatedAccountState))))
  : Prop :=
  match cur_entry with
  | Some (_, updates) => length updates = 1%nat
  | None => True
  end.

Definition try_fix_account_balance_invariant
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (cur : MapModel evm.address (list (ptr * UpdatedAccountState))) : Prop :=
  forall addr orig_loc orig_state cur_loc upd_loc upd tl,
    mapModelLookup orig addr = Some (orig_loc, orig_state) ->
    mapModelLookup cur addr = Some (cur_loc, (upd_loc, upd) :: tl) ->
    sliceInvariants
      {| preAssumption := orig_state;
         originalLoc := orig_loc;
         txUpdates := Some (cur_loc, (upd_loc, upd)) |}.

Lemma try_fix_account_balance_mismatch_neq
    (orig_state : AssumedPreTxAccountState)
    (actual_ac original_ac : AccountM) :
  preTxState orig_state = Some original_ac ->
  try_fix_account_balance_mismatch orig_state (Some actual_ac) ->
  balance original_ac <> balance actual_ac.
Proof.
  intros Hpre Hmismatch.
  unfold try_fix_account_balance_mismatch in Hmismatch.
  rewrite Hpre in Hmismatch.
  exact Hmismatch.
Qed.

Lemma try_fix_account_balance_bound_of_invariant
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
    (addr : evm.address)
    (orig_loc cur_loc upd_loc : ptr)
    (orig_state : AssumedPreTxAccountState)
    (original_ac recent_ac : AccountM)
    (upd : UpdatedAccountState)
    (min_balance_bound : N) :
  try_fix_account_balance_invariant orig cur ->
  mapModelLookup orig addr = Some (orig_loc, orig_state) ->
  mapModelLookup cur addr = Some (cur_loc, [(upd_loc, upd)]) ->
  preTxState orig_state = Some original_ac ->
  min_balance (assumExactness orig_state) = Some min_balance_bound ->
  postTxState upd = Some recent_ac ->
  (balance original_ac - balance recent_ac <= min_balance_bound)%N.
Proof.
  intros Hinv Horig Hcur Hpre Hmin Hpost.
  specialize (Hinv addr orig_loc orig_state cur_loc upd_loc upd [] Horig Hcur).
  unfold sliceInvariants in Hinv.
  simpl in Hinv.
  rewrite Hmin in Hinv.
  rewrite Hpre in Hinv.
  rewrite Hpost in Hinv.
  exact Hinv.
Qed.

Lemma try_fix_account_recent_balance_covers_delta_of_invariant
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
    (addr : evm.address)
    (orig_loc cur_loc upd_loc : ptr)
    (orig_state : AssumedPreTxAccountState)
    (actual_ac original_ac recent_ac : AccountM)
    (upd : UpdatedAccountState)
    (min_balance_bound actual_raw : N) :
  try_fix_account_balance_invariant orig cur ->
  mapModelLookup orig addr = Some (orig_loc, orig_state) ->
  mapModelLookup cur addr = Some (cur_loc, [(upd_loc, upd)]) ->
  preTxState orig_state = Some original_ac ->
  min_balance (assumExactness orig_state) = Some min_balance_bound ->
  postTxState upd = Some recent_ac ->
  balance actual_ac = actual_raw ->
  (min_balance_bound <= actual_raw)%N ->
  (balance original_ac - balance actual_ac <= balance recent_ac)%N.
Proof.
  intros Hinv Horig Hcur Hpre Hmin Hpost Hactual_balance Hmin_le.
  pose proof
    (try_fix_account_balance_bound_of_invariant
      orig cur addr orig_loc cur_loc upd_loc orig_state
      original_ac recent_ac upd min_balance_bound
      Hinv Horig Hcur Hpre Hmin Hpost)
    as Horig_recent_le_min.
  rewrite Hactual_balance.
  lia.
Qed.

#[local] Hint Extern 4
  (balance _ - balance _ <= balance _)%N =>
  eapply try_fix_account_recent_balance_covers_delta_of_invariant; eauto
  : pure.

Lemma account_balance_bound_from_core (acct : AccountM) :
  balance acct =
    w256_to_N (block.block_account_balance (coreAc acct)) ->
  (w256_to_N (block.block_account_balance (coreAc acct)) <
   uint256_modulus)%N ->
  (balance acct < uint256_modulus)%N.
Proof using.
  intros Hbalance Hbound.
  rewrite Hbalance.
  exact Hbound.
Qed.

Lemma u256_sub_mod_small (x y : N) :
  (y <= x)%N ->
  (x < uint256_modulus)%N ->
  Z.to_N ((Z.of_N x - Z.of_N y) mod
          Z.of_N uint256_modulus)%Z = (x - y)%N.
Proof using.
  intros Hle Hlt.
  assert (Hinjsub :
    (Z.of_N (x - y) = Z.of_N x - Z.of_N y)%Z).
  {
    apply N2Z.inj_sub.
    exact Hle.
  }
  rewrite <- Hinjsub.
  rewrite Z.mod_small.
  2: {
    assert (Hsub_lt : (x - y < uint256_modulus)%N) by lia.
    pose proof (proj1 (N2Z.inj_lt (x - y) uint256_modulus)
      Hsub_lt).
    lia.
  }
  rewrite N2Z.id.
  reflexivity.
Qed.

Lemma u256_sub_mod_small_twopower (x y : N) :
  (y <= x)%N ->
  (x < uint256_modulus)%N ->
  Z.to_N ((Z.of_N x - Z.of_N y) mod
          two_power_nat 256)%Z = (x - y)%N.
Proof using.
  intros Hle Hbound.
  rewrite <- Z_of_N_uint256_modulus.
  apply u256_sub_mod_small; assumption.
Qed.

Lemma uint256_mod_bound (n : N) :
  (n mod uint256_word_modulus < uint256_modulus)%N.
Proof using.
  rewrite uint256_word_modulus_eq.
  apply N.mod_upper_bound.
  pose proof uint256_modulus_pos.
  lia.
Qed.

Lemma uint256_zmod_bound (z : Z) :
  (Z.to_N (z mod Z.of_N uint256_modulus) < uint256_modulus)%N.
Proof using.
  pose proof uint256_modulus_pos as Hmod_pos_N.
  pose proof (proj1 (N2Z.inj_lt 0 uint256_modulus) Hmod_pos_N)
    as Hmod_pos_Z.
  pose proof (Z.mod_pos_bound z (Z.of_N uint256_modulus)
    Hmod_pos_Z) as [Hz_nonneg Hz_lt].
  apply (proj2 (N2Z.inj_lt _ _)).
  rewrite Z2N.id; lia.
Qed.

Lemma add_delta_mod_of_u256_sub (recent actual original : N) :
  (original < actual)%N ->
  (actual < uint256_modulus)%N ->
  ((recent +
    Z.to_N ((Z.of_N actual - Z.of_N original) mod
            Z.of_N uint256_modulus)%Z) mod
   uint256_word_modulus =
   (recent + (actual - original)) mod uint256_word_modulus)%N.
Proof using.
  intros Hlt Hbound.
  rewrite (u256_sub_mod_small actual original
    (N.lt_le_incl _ _ Hlt) Hbound).
  reflexivity.
Qed.

Lemma add_delta_mod_of_u256_sub_twopower (recent actual original : N) :
  (original < actual)%N ->
  (actual < uint256_modulus)%N ->
  ((recent +
    Z.to_N ((Z.of_N actual - Z.of_N original) mod
            two_power_nat 256)%Z) mod
   uint256_word_modulus =
   (recent + (actual - original)) mod uint256_word_modulus)%N.
Proof using.
  intros Hlt Hbound.
  rewrite <- Z_of_N_uint256_modulus.
  apply add_delta_mod_of_u256_sub;
    assumption.
Qed.

Lemma sub_assign_delta_of_u256_sub_twopower
    (recent original actual : N) :
  (actual < original)%N ->
  (original < uint256_modulus)%N ->
  Z.to_N
    ((Z.of_N recent -
      Z.to_N
        ((Z.of_N original - Z.of_N actual) mod
         two_power_nat 256)%Z) mod
     two_power_nat 256)%Z =
  Z.to_N
    ((Z.of_N recent - Z.of_N (original - actual)) mod
     Z.of_N uint256_modulus)%Z.
Proof using.
  intros Hlt Hbound.
  rewrite (u256_sub_mod_small_twopower original actual
    (N.lt_le_incl _ _ Hlt) Hbound).
  rewrite <- Z_of_N_uint256_modulus.
  reflexivity.
Qed.

Lemma try_fix_account_add_balance_mod (recent actual original : N) :
  (original < actual)%N ->
  (((recent + (actual - original)) mod uint256_word_modulus) mod
   uint256_word_modulus =
   Z.to_N
     (Z.of_N actual + (Z.of_N recent - Z.of_N original)) mod
   uint256_word_modulus)%N.
Proof using.
  intro Hlt.
  rewrite N.mod_mod.
  2: {
    rewrite uint256_word_modulus_eq.
    pose proof uint256_modulus_pos.
    lia.
  }
  replace
    (Z.to_N
       (Z.of_N actual + (Z.of_N recent - Z.of_N original)))
    with (recent + (actual - original))%N.
  {
    reflexivity.
  }
  {
    apply N2Z.inj.
    rewrite Z2N.id.
    {
      rewrite N2Z.inj_add.
      rewrite N2Z.inj_sub.
      {
        lia.
      }
      {
        lia.
      }
    }
    {
      lia.
    }
  }
Qed.

Lemma try_fix_account_sub_balance_mod
    (recent original actual : N) :
  (actual < original)%N ->
  (original - actual <= recent)%N ->
  (recent < uint256_modulus)%N ->
  (Z.to_N
     ((Z.of_N recent - Z.of_N (original - actual)) mod
      Z.of_N uint256_modulus)%Z mod uint256_word_modulus =
   Z.to_N
     (Z.of_N actual + (Z.of_N recent - Z.of_N original)) mod
   uint256_word_modulus)%N.
Proof using.
  intros Hlt Hle Hrecent_bound.
  rewrite (u256_sub_mod_small recent (original - actual)
    Hle Hrecent_bound).
  replace
    (Z.to_N
       (Z.of_N actual + (Z.of_N recent - Z.of_N original)))
    with (recent - (original - actual))%N.
  {
    reflexivity.
  }
  {
    apply N2Z.inj.
    rewrite Z2N.id.
    {
      rewrite N2Z.inj_sub.
      2: {
        exact Hle.
      }
      rewrite N2Z.inj_sub.
      2: {
        lia.
      }
      lia.
    }
    {
      lia.
    }
  }
Qed.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  Lemma ignore_valid_bool_return_local (b : bool) (Q : mpred) :
    Q |-- (validP<"bool"> (Vbool b) -∗ Q).
  Proof using.
    go.
  Qed.

  Lemma wp_destroy_incarnation_named_fupd_local
      (tu : translation_unit) (p : ptr) (inc : Indices) (Q : epred) :
    □ incarnation_dtor_spec ** p |-> IncarnationR 1 inc ** Q
    |-- |={⊤}=> wp_destroy_named tu "monad::Incarnation" p Q.
  Proof using CU MODd Sigma.
    rewrite -fupd_intro.
    go using
      wp_destroy_val_named_C,
      incarnation_dtor_spec.
    iExists inc.
    go.
  Qed.

  Definition wp_destroy_incarnation_named_fupd_B
      tu p inc Q :=
    [BWD] (wp_destroy_incarnation_named_fupd_local tu p inc Q).

  Lemma wp_destroy_incarnation_value_local
      (tu : translation_unit) (p : ptr) (inc : Indices) (Q : epred) :
    □ incarnation_dtor_spec ** p |-> IncarnationR 1 inc ** Q
    |-- wp_destroy_val tu QM "monad::Incarnation" p Q.
  Proof using CU MODd Sigma.
    go using
      destroy.wp_destroy_val_named_B,
      wp_destroy_val_named_C,
      incarnation_dtor_spec.
    iExists inc.
    go.
  Qed.

  Definition wp_destroy_incarnation_value_B
      tu p inc Q :=
    [BWD] (wp_destroy_incarnation_value_local tu p inc Q).

  #[local] Instance learn_anker_payloads {K V} :
    LearnEq6 (@AnkerMapPayloadsR _ _ Sigma K V) :=
    ltac:(solve_learnable).
  #[local] Instance learn_original_account_state :
    LearnEq2 OriginalAccountStateR :=
    ltac:(solve_learnable).
  #[local] Instance learn_updated_account_state :
    LearnEq2 UpdatedAccountStateR :=
    ltac:(solve_learnable).
  #[local] Instance learn_storage_map :
    LearnEq2 StorageMapR :=
    ltac:(solve_learnable).

  Definition StateTryFixAccountMismatchR
      (this : ptr)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (relaxed : bool) : mpred :=
    this ,, o_field CU "monad::State::original_"
      |-> AnkerMapR "monad::Address" "monad::OriginalAccountState"
            addressToN addressR OriginalAccountStateR 1 orig
    ** this ,, o_field CU "monad::State::current_"
      |-> AnkerMapR "monad::Address" "monad::VersionStack<monad::AccountState>"
            addressToN addressR
            (VersionStackR "monad::AccountState" UpdatedAccountStateR) 1 cur
    ** this ,, o_field CU "monad::State::relaxed_validation_"
      |-> boolR 1$m relaxed
    ** this |-> structR "monad::State"%cpp_name 1$m.

  Arguments pair_name/.
  Arguments pair_ty/.
  Arguments pairFstOffset/.
  Arguments pairSndOffset/.
  Arguments pairOffsets/.
  Arguments anker_pair_name/.
  Arguments anker_pair_ty/.
  Arguments anker_allocator_name/.
  Arguments anker_hash_name/.
  Arguments anker_equal_to_name/.
  Arguments anker_table_name/.
  Arguments anker_segvec_name/.
  Arguments anker_iter_name/.
  Arguments anker_iter_ty/.

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).

  Definition account_option_layout (p : ptr) (acct : AccountM) : mpred :=
    p |-> optional_specs.spineR "monad::Account" 1$m
      (Some (p ,, optional_specs.value_offset "monad::Account"))
    ** p ,, optional_specs.value_offset "monad::Account"%cpp_type
         |-> AccountR 1 acct.

  #[local] Instance learn_account_option_layout :
    LearnEq2 account_option_layout :=
    ltac:(solve_learnable).
  #[local] Instance learn_accountR :
    LearnEq2 AccountR :=
    ltac:(solve_learnable).

  Lemma account_option_layout_unfold (p : ptr) (acct : AccountM) :
    account_option_layout p acct
    |--
    p |-> optional_specs.spineR "monad::Account" 1$m
      (Some (p ,, optional_specs.value_offset "monad::Account"))
    ** p ,, optional_specs.value_offset "monad::Account"%cpp_type
         |-> AccountR 1 acct.
  Proof using.
    unfold account_option_layout.
    go.
  Qed.

  Definition account_option_layout_unfold_F p acct :=
    [FWD] (account_option_layout_unfold p acct).

  Lemma account_option_layout_fold (p : ptr) (acct : AccountM) :
    p |-> optional_specs.spineR "monad::Account" 1$m
      (Some (p ,, optional_specs.value_offset "monad::Account"))
    ** p ,, optional_specs.value_offset "monad::Account"%cpp_type
         |-> AccountR 1 acct
    |-- account_option_layout p acct.
  Proof using.
    unfold account_option_layout.
    go.
  Qed.

  Definition account_option_layout_fold_B p acct :=
    [BWD] (account_option_layout_fold p acct).

  Lemma optionR_account_some_separated_unfold
      (p : ptr) (acct : AccountM) :
    p |-> optional_specs.optionR "monad::Account"%cpp_type
          AccountR 1 (Some acct)
    |-- account_option_layout p acct.
  Proof using CU MODd Sigma.
    unfold account_option_layout.
    exact (optional_specs.trivial_optional_some_split
      "monad::Account" AccountR 1 acct p).
  Qed.

  Definition optionR_account_some_separated_unfold_F p acct :=
    [FWD] (optionR_account_some_separated_unfold p acct).

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

  Lemma AccountR_separated_unfold (p : ptr) (q : Qp) acct :
    p |-> AccountR q acct
    |--
    [| balance acct =
         w256_to_N (block.block_account_balance (coreAc acct)) |]
    ** p ,, o_field CU "monad::Account::balance"
         |-> u256R q (w256_to_N (block.block_account_balance (coreAc acct)))
    ** p ,, o_field CU "monad::Account::code_hash"
         |-> bytes32R q
              (code_hash_of_program
                 (block.block_account_code (coreAc acct)))
    ** p ,, o_field CU "monad::Account::nonce"
         |-> primR "unsigned long" (cQp.mut q)
              (w256_to_Z (block.block_account_nonce (coreAc acct)))
    ** p ,, o_field CU "monad::Account::incarnation"
         |-> IncarnationR q (incarnation acct)
    ** p |-> structR "monad::Account"%cpp_name (cQp.mut q).
  Proof using CU MODd Sigma.
    unfold AccountR.
    go.
  Qed.

  Definition AccountR_separated_unfold_F p q acct :=
    [FWD] (AccountR_separated_unfold p q acct).

  Lemma AccountR_separated_fold (p : ptr) (q : Qp) acct :
    balance acct =
      w256_to_N (block.block_account_balance (coreAc acct)) ->
    p ,, o_field CU "monad::Account::balance"
      |-> u256R q (w256_to_N (block.block_account_balance (coreAc acct)))
    ** p ,, o_field CU "monad::Account::code_hash"
         |-> bytes32R q
              (code_hash_of_program
                 (block.block_account_code (coreAc acct)))
    ** p ,, o_field CU "monad::Account::nonce"
         |-> primR "unsigned long" (cQp.mut q)
              (w256_to_Z (block.block_account_nonce (coreAc acct)))
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

  Lemma AccountR_account_set_balance_fold
      (p : ptr) (ac : AccountM) (bal : N) :
    (bal < uint256_modulus)%N ->
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

  Definition AccountR_account_set_balance_mod_fold_B p ac bal :=
    [BWD] (AccountR_account_set_balance_fold
             p ac (bal mod uint256_word_modulus)
             (uint256_mod_bound bal)).

  Definition AccountR_account_set_balance_zmod_fold_B p ac z :=
    [BWD] (AccountR_account_set_balance_fold
             p ac
             (Z.to_N (z mod Z.of_N uint256_modulus)%Z)
             (uint256_zmod_bound z)).

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

  Lemma observe_u256_reference (p : ptr) q v :
    Observe (reference_to u256t p) (p |-> u256R q v).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _|].
    go using observeU256F, type_ptr_reference_to_B_local.
  Qed.

  Lemma observe_bytes32_reference (p : ptr) q v :
    Observe (reference_to "monad::bytes32_t" p) (p |-> bytes32R q v).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _|].
    go using observeBytes32F, type_ptr_reference_to_B_local.
  Qed.

  Lemma observe_ulong_reference (p : ptr) q v :
    Observe (reference_to "unsigned long" p) (p |-> ulongR q v).
  Proof using CU MODd Sigma.
    apply observe_intro; [exact _|].
    go using type_ptr_reference_to_B_local.
  Qed.

  Definition observe_u256_reference_F p q v :=
    @observe_fwd _ _ _ (observe_u256_reference p q v).
  Definition observe_bytes32_reference_F p q v :=
    @observe_fwd _ _ _ (observe_bytes32_reference p q v).
  Definition observe_ulong_reference_F p q v :=
    @observe_fwd _ _ _ (observe_ulong_reference p q v).

  #[local] Hint Resolve
    observe_u256_reference_F
    observe_bytes32_reference_F : sl_opacity.

  Lemma map_model_spine_snd {K V : Type} (m : MapModel K V) :
    map snd (map (fun '(k, (p, _)) => (k, p)) m) =
    map (fun x => x.2.1) m.
  Proof using.
    induction m as [| [k [p v]] m IH]; simpl; [reflexivity |].
    now f_equal.
  Qed.

  Lemma map_model_spine_fst {K V : Type} (m : MapModel K V) :
    map fst (map (fun '(k, (p, _)) => (k, p)) m) =
    map fst m.
  Proof using.
    induction m as [| [k [p v]] m IH]; simpl; [reflexivity |].
    now f_equal.
  Qed.

  Lemma map_model_spine_lengthN {K V : Type} (m : MapModel K V) :
    lengthN (map (fun '(k, (p, _)) => (k, p)) m) = lengthN m.
  Proof using.
    rewrite lengthN_map.
    reflexivity.
  Qed.

  Lemma map_model_spine_lengthN_sym {K V : Type} (m : MapModel K V) :
    lengthN m = lengthN (map (fun '(k, (p, _)) => (k, p)) m).
  Proof using.
    symmetry.
    apply map_model_spine_lengthN.
  Qed.

  Lemma map_model_iterR_snd_map_at {K V : Type}
      (kty vty : type) (p : ptr) (i : N) (m : MapModel K V) :
    p |-> AnkerMapIterR kty vty false 1$m i
        (map snd (map (fun '(k, (p0, _)) => (k, p0)) m))
    |--
    p |-> AnkerMapIterR kty vty false 1$m i (map (fun x => x.2.1) m).
  Proof using.
    rewrite map_model_spine_snd.
    go.
  Qed.

  Lemma map_model_iterR_snd_map_rev_at {K V : Type}
      (kty vty : type) (p : ptr) (i : N) (m : MapModel K V) :
    p |-> AnkerMapIterR kty vty false 1$m i (map (fun x => x.2.1) m)
    |--
    p |-> AnkerMapIterR kty vty false 1$m i
        (map snd (map (fun '(k, (p0, _)) => (k, p0)) m)).
  Proof using.
    rewrite map_model_spine_snd.
    go.
  Qed.

  Lemma map_model_iterR_end_map_rev_at {K V : Type}
      (kty vty : type) (p : ptr) (m : MapModel K V) :
    p |-> AnkerMapIterR kty vty false 1$m (lengthN m) (map (fun x => x.2.1) m)
    |--
    p |-> AnkerMapIterR kty vty false 1$m
        (lengthN (map (fun '(k, (p0, _)) => (k, p0)) m))
        (map snd (map (fun '(k, (p0, _)) => (k, p0)) m)).
  Proof using.
    rewrite map_model_spine_snd.
    rewrite map_model_spine_lengthN.
    go.
  Qed.

  Lemma map_model_find_index_not_end {K V : Type}
      (m : MapModel K V) (k : K) (i : N) :
    option_map fst
      (nth_error (map (fun '(k0, (p, _)) => (k0, p)) m)
        (N.to_nat i)) = Some k ->
    i <> lengthN (map (fun '(k0, (p, _)) => (k0, p)) m).
  Proof using.
    intros Hnth Heq.
    destruct (nth_error (map (fun '(k0, (p, _)) => (k0, p)) m)
      (N.to_nat i)) as [[k' p]|] eqn:Hnth_lookup.
    2: discriminate.
    simpl in Hnth.
    subst i.
    unfold lengthN in Hnth_lookup.
    rewrite Nat2N.id in Hnth_lookup.
    pose proof
      (proj2
        (nth_error_None
          (map (fun '(k0, (p0, _)) => (k0, p0)) m)
          (length (map (fun '(k0, (p0, _)) => (k0, p0)) m)))
        (Nat.le_refl _)) as Hnone.
    rewrite Hnone in Hnth_lookup.
    discriminate.
  Qed.

  Lemma map_model_spine_lookup_ploc_exists {K V : Type}
      (m : MapModel K V) (k : K) (i : N) :
    option_map fst
      (nth_error (map (fun '(k0, (p, _)) => (k0, p)) m)
        (N.to_nat i)) = Some k ->
    exists ploc,
      nth_error (map (fun x => x.2.1) m) (N.to_nat i) = Some ploc.
  Proof using.
    intros Hnth_key.
    destruct (nth_error (map (fun '(k0, (p, _)) => (k0, p)) m)
      (N.to_nat i)) as [[k' ploc]|] eqn:Hnth_spine.
    2: discriminate.
    exists ploc.
    rewrite <- map_model_spine_snd.
    rewrite nth_error_map.
    rewrite Hnth_spine.
    reflexivity.
  Qed.

  Lemma map_model_lookup_of_spine_lookup
      {K V : Type} `{Countable K}
      (m : MapModel K V) (k : K) (i : N) (ploc : ptr) :
    NoDup (map fst (map (fun '(k0, (p, _)) => (k0, p)) m)) ->
    option_map fst
      (nth_error (map (fun '(k0, (p, _)) => (k0, p)) m)
        (N.to_nat i)) = Some k ->
    nth_error (map (fun x => x.2.1) m) (N.to_nat i) = Some ploc ->
    exists v, mapModelLookup m k = Some (ploc, v).
  Proof using.
    intros Hnodup Hnth_key Hnth_ploc.
    destruct (nth_error m (N.to_nat i)) as [[k' [loc' v]]|] eqn:Hnth_m.
    {
      rewrite nth_error_map Hnth_m in Hnth_key.
      simpl in Hnth_key.
      injection Hnth_key as Hk.
      rewrite nth_error_map Hnth_m in Hnth_ploc.
      simpl in Hnth_ploc.
      injection Hnth_ploc as Hloc.
      subst k' loc'.
      exists v.
      unfold mapModelLookup.
      apply elem_of_list_to_map_1.
      {
        rewrite <- map_model_spine_fst.
        exact Hnodup.
      }
      eapply list_elem_of_lookup_2 with (i := N.to_nat i).
      rewrite lookup_nth_error.
      exact Hnth_m.
    }
    {
      rewrite nth_error_map Hnth_m in Hnth_key.
      discriminate.
    }
  Qed.

  Lemma map_model_lookup_none_of_not_elem
      {K V : Type} `{Countable K}
      (m : MapModel K V) (k : K) :
    k ∉ map fst m ->
    mapModelLookup m k = None.
  Proof using.
    intros Hnot_elem.
    unfold mapModelLookup.
    induction m as [| [k0 [loc v]] m IH]; simpl in *.
    {
      rewrite lookup_empty.
      reflexivity.
    }
    {
      rewrite lookup_insert_ne.
      {
        apply IH.
        intros Hin.
        apply Hnot_elem.
        right.
        exact Hin.
      }
      intros Heq.
      subst k0.
      apply Hnot_elem.
      left.
    }
  Qed.

  Lemma map_model_lookup_some_not_spine_absurd
      {K V : Type} `{Countable K}
      (m : MapModel K V) (k : K) (loc : ptr) (v : V) :
    mapModelLookup m k = Some (loc, v) ->
    k ∉ map fst (map (fun '(k0, (p, _)) => (k0, p)) m) ->
    False.
  Proof using.
    intros Hlookup Hnot.
    rewrite map_model_spine_fst in Hnot.
    pose proof (map_model_lookup_none_of_not_elem m k Hnot) as Hnone.
    congruence.
  Qed.

  Lemma mapModelLookup_try_fix_account_updated_cur_map_head
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address)
      (loc upd_loc : ptr)
      (actual original : AccountM)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    mapModelLookup (try_fix_account_updated_cur_map addr actual original cur)
      addr =
    Some
      (loc, (upd_loc, try_fix_account_current_update actual original upd)
            :: tl).
  Proof using.
    unfold mapModelLookup, try_fix_account_updated_cur_map.
    induction cur as [| [a [loc0 updates0]] cur IH]; simpl.
    {
      rewrite lookup_empty.
      discriminate.
    }
    destruct (bool_decide (a = addr)) eqn:Ha.
    {
      apply bool_decide_eq_true in Ha.
      subst a.
      intro Hlookup.
      rewrite lookup_insert in Hlookup.
      destruct (decide (addr = addr)) as [_|Hcontra] in Hlookup;
        [|contradiction Hcontra; reflexivity].
      inversion Hlookup; subst; clear Hlookup.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_|Hcontra];
        [|contradiction Hcontra; reflexivity].
      reflexivity.
    }
    {
      apply bool_decide_eq_false in Ha.
      intro Hlookup.
      rewrite lookup_insert_ne in Hlookup; [| exact Ha].
      rewrite lookup_insert_ne; [| exact Ha].
      exact (IH Hlookup).
    }
  Qed.

  Lemma mapModelLookup_try_fix_account_updated_orig_map_same
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (actual : option AccountM) :
    mapModelLookup (try_fix_account_updated_orig_map addr actual orig) addr =
    option_map
      (fun '(loc, orig_state) =>
         (loc, try_fix_account_original_update actual orig_state))
      (mapModelLookup orig addr).
  Proof using.
    unfold mapModelLookup, try_fix_account_updated_orig_map.
    induction orig as [| [a [loc orig_state]] orig IH]; simpl.
    {
      rewrite lookup_empty.
      reflexivity.
    }
    destruct (bool_decide (a = addr)) eqn:Ha.
    {
      apply bool_decide_eq_true in Ha.
      subst a.
      rewrite lookup_insert.
      rewrite lookup_insert.
      cbn.
      destruct (decide (addr = addr)) as [_|Hcontra];
        [|contradiction Hcontra; reflexivity].
      reflexivity.
    }
    {
      apply bool_decide_eq_false in Ha.
      rewrite lookup_insert_ne; [| exact Ha].
      rewrite lookup_insert_ne; [| exact Ha].
      exact IH.
    }
  Qed.

  Lemma mapModelLookup_try_fix_account_updated_orig_map_ne
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr other : evm.address) (actual : option AccountM) :
    other <> addr ->
    mapModelLookup (try_fix_account_updated_orig_map addr actual orig) other =
    mapModelLookup orig other.
  Proof using.
    intro Hne.
    unfold mapModelLookup, try_fix_account_updated_orig_map.
    induction orig as [| [a [loc orig_state]] orig IH]; simpl.
    {
      rewrite lookup_empty.
      reflexivity.
    }
    destruct (bool_decide (a = addr)) eqn:Ha.
    {
      apply bool_decide_eq_true in Ha.
      subst a.
      rewrite lookup_insert_ne; [| intro Heq; apply Hne; symmetry; exact Heq].
      rewrite lookup_insert_ne; [| intro Heq; apply Hne; symmetry; exact Heq].
      exact IH.
    }
    {
      destruct (decide (a = other)) as [-> | Hother].
      {
        rewrite lookup_insert.
        rewrite lookup_insert.
        cbn.
        destruct (decide (other = other)) as [_ | Hcontra].
        2: { contradiction Hcontra; reflexivity. }
        reflexivity.
      }
      {
        rewrite lookup_insert_ne; [| exact Hother].
        rewrite lookup_insert_ne; [| exact Hother].
        exact IH.
      }
    }
  Qed.

  Lemma mapModelLookup_try_fix_account_updated_cur_map_ne
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr other : evm.address) (actual original : AccountM) :
    other <> addr ->
    mapModelLookup (try_fix_account_updated_cur_map addr actual original cur)
      other =
    mapModelLookup cur other.
  Proof using.
    intro Hne.
    unfold mapModelLookup, try_fix_account_updated_cur_map.
    induction cur as [| [a [loc updates]] cur IH]; simpl.
    {
      rewrite lookup_empty.
      reflexivity.
    }
    destruct (bool_decide (a = addr)) eqn:Ha.
    {
      apply bool_decide_eq_true in Ha.
      subst a.
      rewrite lookup_insert_ne; [| intro Heq; apply Hne; symmetry; exact Heq].
      rewrite lookup_insert_ne; [| intro Heq; apply Hne; symmetry; exact Heq].
      exact IH.
    }
    {
      destruct (decide (a = other)) as [-> | Hother].
      {
        rewrite lookup_insert.
        rewrite lookup_insert.
        cbn.
        destruct (decide (other = other)) as [_ | Hcontra].
        2: { contradiction Hcontra; reflexivity. }
        reflexivity.
      }
      {
        rewrite lookup_insert_ne; [| exact Hother].
        rewrite lookup_insert_ne; [| exact Hother].
        exact IH.
      }
    }
  Qed.

  Lemma try_fix_account_balance_invariant_update_orig
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address) (actual : option AccountM)
      (orig_loc : ptr) (orig_state : AssumedPreTxAccountState) :
    try_fix_account_balance_invariant orig cur ->
    mapModelLookup orig addr = Some (orig_loc, orig_state) ->
    try_fix_account_balance_invariant
      (try_fix_account_updated_orig_map addr actual orig) cur.
  Proof using.
    intros Hinv Horig other other_orig_loc other_orig_state
      cur_loc upd_loc upd tl Horig_other Hcur_other.
    destruct (decide (other = addr)) as [-> | Hne].
    {
      rewrite mapModelLookup_try_fix_account_updated_orig_map_same in Horig_other.
      rewrite Horig in Horig_other.
      simpl in Horig_other.
      inversion Horig_other; subst other_orig_loc other_orig_state.
      unfold sliceInvariants.
      simpl.
      unfold try_fix_account_original_update,
        update_assum_exactness_assumed, exact_balance_update.
      simpl.
      exact I.
    }
    {
      rewrite mapModelLookup_try_fix_account_updated_orig_map_ne in Horig_other;
        [| exact Hne].
      eapply Hinv; eauto.
    }
  Qed.

  Lemma try_fix_account_balance_invariant_update_both
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address) (actual original : AccountM)
      (orig_loc : ptr) (orig_state : AssumedPreTxAccountState) :
    try_fix_account_balance_invariant orig cur ->
    mapModelLookup orig addr = Some (orig_loc, orig_state) ->
    try_fix_account_balance_invariant
      (try_fix_account_updated_orig_map addr (Some actual) orig)
      (try_fix_account_updated_cur_map addr actual original cur).
  Proof using.
    intros Hinv Horig other other_orig_loc other_orig_state
      cur_loc upd_loc upd tl Horig_other Hcur_other.
    destruct (decide (other = addr)) as [-> | Hne].
    {
      rewrite mapModelLookup_try_fix_account_updated_orig_map_same in Horig_other.
      rewrite Horig in Horig_other.
      simpl in Horig_other.
      inversion Horig_other; subst other_orig_loc other_orig_state.
      unfold sliceInvariants.
      simpl.
      unfold try_fix_account_original_update,
        update_assum_exactness_assumed, exact_balance_update.
      simpl.
      exact I.
    }
    {
      rewrite mapModelLookup_try_fix_account_updated_orig_map_ne in Horig_other;
        [| exact Hne].
      rewrite mapModelLookup_try_fix_account_updated_cur_map_ne in Hcur_other;
        [| exact Hne].
      eapply Hinv; eauto.
    }
  Qed.

  #[local] Hint Resolve
    try_fix_account_balance_invariant_update_orig
    try_fix_account_balance_invariant_update_both : pure.

  Lemma try_fix_account_sat_non_storage_true
      (actual_ac original_ac : AccountM)
      (orig_state : AssumedPreTxAccountState)
      (min_balance_bound actual_raw : N) :
    preTxState orig_state = Some original_ac ->
    min_balance (assumExactness orig_state) = Some min_balance_bound ->
    balance actual_ac = actual_raw ->
    (min_balance_bound <= actual_raw)%N ->
    w256_to_Z (block.block_account_nonce (coreAc original_ac)) =
      w256_to_Z (block.block_account_nonce (coreAc actual_ac)) ->
    satAccountNonStorageAssumptions true (Some orig_state)
      (Some actual_ac).
  Proof using.
    intros Hpre Hmin Hactual_balance Hmin_le Hnonce.
    unfold satAccountNonStorageAssumptions.
    rewrite Hpre.
    rewrite Hmin.
    simpl.
    split.
    {
      change
        (match actual_ac with
         | {| balance := balance |} => balance
         end)
        with (balance actual_ac).
      rewrite Hactual_balance.
      unfold min_balanceN.
      rewrite Hmin.
      exact Hmin_le.
    }
    {
      destruct (nonce_exact (assumExactness orig_state)).
      {
        exact Hnonce.
      }
      {
        exact I.
      }
    }
  Qed.

  Lemma try_fix_account_mismatch_ret_prop_true_no_current
      (addr : evm.address) (actual_ac original_ac : AccountM)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (orig_loc : ptr) (orig_state : AssumedPreTxAccountState)
      (min_balance_bound actual_raw : N) :
    preTxState orig_state = Some original_ac ->
    min_balance (assumExactness orig_state) = Some min_balance_bound ->
    balance actual_ac = actual_raw ->
    (min_balance_bound <= actual_raw)%N ->
    w256_to_Z (block.block_account_nonce (coreAc original_ac)) =
      w256_to_Z (block.block_account_nonce (coreAc actual_ac)) ->
    addr ∉ map fst (map (fun '(a, (b, _)) => (a, b)) cur) ->
    try_fix_account_mismatch_ret_prop
      addr (Some actual_ac) orig cur true orig_loc orig_state true
      (try_fix_account_updated_orig_map addr (Some actual_ac) orig) cur.
  Proof using.
    intros Hpre Hmin Hactual_balance Hmin_le Hnonce Hnot.
    assert (Hcur_none : mapModelLookup cur addr = None).
    {
      apply map_model_lookup_none_of_not_elem.
      rewrite <- map_model_spine_fst.
      exact Hnot.
    }
    unfold try_fix_account_mismatch_ret_prop.
    rewrite Hpre.
    split.
    {
      reflexivity.
    }
    split.
    {
      unfold try_fix_account_final_cur_map.
      rewrite Hcur_none.
      reflexivity.
    }
    split.
    {
      exact (try_fix_account_sat_non_storage_true
        actual_ac original_ac orig_state min_balance_bound actual_raw
        Hpre Hmin Hactual_balance Hmin_le Hnonce).
    }
    {
      unfold try_fix_account_final_balance, accountFinalVal,
        try_fix_account_tx_slice.
      rewrite Hcur_none.
      reflexivity.
    }
  Qed.

  Lemma try_fix_account_mismatch_ret_prop_true_current_add
      (addr : evm.address) (actual_ac original_ac recent_ac : AccountM)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (upd : UpdatedAccountState)
      (min_balance_bound actual_raw : N) :
    preTxState orig_state = Some original_ac ->
    min_balance (assumExactness orig_state) = Some min_balance_bound ->
    balance actual_ac = actual_raw ->
    (min_balance_bound <= actual_raw)%N ->
    w256_to_Z (block.block_account_nonce (coreAc original_ac)) =
      w256_to_Z (block.block_account_nonce (coreAc actual_ac)) ->
    mapModelLookup cur addr = Some (cur_loc, [(upd_loc, upd)]) ->
    postTxState upd = Some recent_ac ->
    (balance original_ac < balance actual_ac)%N ->
    try_fix_account_mismatch_ret_prop
      addr (Some actual_ac) orig cur true orig_loc orig_state true
      (try_fix_account_updated_orig_map addr (Some actual_ac) orig)
      (try_fix_account_updated_cur_map addr actual_ac original_ac cur).
  Proof using.
    intros Hpre Hmin Hactual_balance Hmin_le Hnonce Hcur Hpost Hlt.
    unfold try_fix_account_mismatch_ret_prop.
    rewrite Hpre.
    split.
    {
      reflexivity.
    }
    split.
    {
      unfold try_fix_account_final_cur_map.
      rewrite Hcur.
      reflexivity.
    }
    split.
    {
      exact (try_fix_account_sat_non_storage_true
        actual_ac original_ac orig_state min_balance_bound actual_raw
        Hpre Hmin Hactual_balance Hmin_le Hnonce).
    }
    {
      unfold try_fix_account_final_balance, accountFinalVal,
        try_fix_account_tx_slice.
      rewrite Hcur.
      rewrite (mapModelLookup_try_fix_account_updated_cur_map_head
        cur addr cur_loc upd_loc actual_ac original_ac upd [] Hcur).
      unfold try_fix_account_original_update,
        try_fix_account_balance_update, try_fix_account_current_update.
      rewrite Hpre.
      rewrite Hpost.
      rewrite Hmin.
      replace (asbool (balance original_ac < balance actual_ac)%N)
        with true.
      2: {
        symmetry.
        apply bool_decide_true.
        exact Hlt.
      }
      cbn [preTxState postTxState txUpdates assumExactness min_balance
        option_map balance].
      unfold postTxActualBalNonce.
      rewrite Hpost.
      cbn [preAssumption postTxState txUpdates originalLoc
        assumExactness min_balance option_map isNone].
      destruct (nonce_exact (assumExactness orig_state)).
      all: change (isNone (Some min_balance_bound)) with false.
      all: autorewrite with try_fix_account_balance.
      all: rewrite (try_fix_account_add_balance_mod
        (balance recent_ac) (balance actual_ac) (balance original_ac)
        Hlt).
      all: reflexivity.
    }
  Qed.

  Lemma try_fix_account_mismatch_ret_prop_true_current_sub
      (addr : evm.address) (actual_ac original_ac recent_ac : AccountM)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (orig_loc cur_loc upd_loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (upd : UpdatedAccountState)
      (min_balance_bound actual_raw : N) :
    preTxState orig_state = Some original_ac ->
    min_balance (assumExactness orig_state) = Some min_balance_bound ->
    balance actual_ac = actual_raw ->
    (min_balance_bound <= actual_raw)%N ->
    w256_to_Z (block.block_account_nonce (coreAc original_ac)) =
      w256_to_Z (block.block_account_nonce (coreAc actual_ac)) ->
    mapModelLookup cur addr = Some (cur_loc, [(upd_loc, upd)]) ->
    postTxState upd = Some recent_ac ->
    (balance actual_ac < balance original_ac)%N ->
    (balance original_ac - balance actual_ac <= balance recent_ac)%N ->
    (balance recent_ac < uint256_modulus)%N ->
    try_fix_account_mismatch_ret_prop
      addr (Some actual_ac) orig cur true orig_loc orig_state true
      (try_fix_account_updated_orig_map addr (Some actual_ac) orig)
      (try_fix_account_updated_cur_map addr actual_ac original_ac cur).
  Proof using.
    intros Hpre Hmin Hactual_balance Hmin_le Hnonce Hcur Hpost Hlt
      Hrecent_ge Hrecent_bound.
    unfold try_fix_account_mismatch_ret_prop.
    rewrite Hpre.
    split.
    {
      reflexivity.
    }
    split.
    {
      unfold try_fix_account_final_cur_map.
      rewrite Hcur.
      reflexivity.
    }
    split.
    {
      exact (try_fix_account_sat_non_storage_true
        actual_ac original_ac orig_state min_balance_bound actual_raw
        Hpre Hmin Hactual_balance Hmin_le Hnonce).
    }
    {
      unfold try_fix_account_final_balance, accountFinalVal,
        try_fix_account_tx_slice.
      rewrite Hcur.
      rewrite (mapModelLookup_try_fix_account_updated_cur_map_head
        cur addr cur_loc upd_loc actual_ac original_ac upd [] Hcur).
      unfold try_fix_account_original_update,
        try_fix_account_balance_update, try_fix_account_current_update.
      rewrite Hpre.
      rewrite Hpost.
      rewrite Hmin.
      replace (asbool (balance original_ac < balance actual_ac)%N)
        with false.
      2: {
        symmetry.
        apply bool_decide_false.
        lia.
      }
      cbn [preTxState postTxState txUpdates assumExactness min_balance
        option_map balance].
      unfold postTxActualBalNonce.
      rewrite Hpost.
      cbn [preAssumption postTxState txUpdates originalLoc
        assumExactness min_balance option_map isNone].
      destruct (nonce_exact (assumExactness orig_state)).
      all: change (isNone (Some min_balance_bound)) with false.
      all: autorewrite with try_fix_account_balance.
      all: rewrite (try_fix_account_sub_balance_mod
        (balance recent_ac) (balance original_ac) (balance actual_ac)
        Hlt Hrecent_ge Hrecent_bound).
      all: reflexivity.
    }
  Qed.

  Lemma borrow_map_payload
      {K V : Type} `{Countable K}
      (kty vty : type) (kR : Qp -> K -> Rep) (vR : Qp -> V -> Rep)
      (map_ptr : ptr) (m : MapModel K V) (k : K) (loc : ptr) (v : V) :
    mapModelLookup m k = Some (loc, v) ->
    map_ptr |-> AnkerMapPayloadsR kty vty kR vR 1%Qp m
    |--
    loc |-> pairFstOffset kty vty |-> kR (1 / 2)%Qp k
    ** loc ,, pairSndOffset kty vty |-> vR 1%Qp v
    ** map_ptr |-> AnkerMapPayloadsR kty vty kR vR 1%Qp (removeKey m k).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (k, (loc, v)) ∈ m).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_N :
      nth_error m (N.to_nat (N.of_nat i)) = Some (k, (loc, v))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    rewrite (@borrowIndex_at _ _ _ _ 1 K V _
      kty vty kR vR m (N.of_nat i) (k, (loc, v)) k map_ptr
      Hnth_N eq_refl).
    unfold pairR.
    go.
  Qed.

  Definition borrow_map_payload_F
      {K V : Type} `{Countable K}
      (kty vty : type) (kR : Qp -> K -> Rep) (vR : Qp -> V -> Rep)
      (map_ptr : ptr) (m : MapModel K V) (k : K) (loc : ptr) (v : V)
      (Hlookup : mapModelLookup m k = Some (loc, v)) :=
    [FWD] (@borrow_map_payload K V _ _ kty vty kR vR
             map_ptr m k loc v Hlookup).

  Lemma reinsert_map_payload
      {K V : Type} `{Countable K}
      (kty vty : type) (kR : Qp -> K -> Rep) (vR : Qp -> V -> Rep)
      (map_ptr : ptr) (m : MapModel K V) (k : K) (loc : ptr) (v : V) :
    mapModelLookup m k = Some (loc, v) ->
    loc |-> pairFstOffset kty vty |-> kR (1 / 2)%Qp k
    ** loc ,, pairSndOffset kty vty |-> vR 1%Qp v
    ** map_ptr |-> AnkerMapPayloadsR kty vty kR vR 1%Qp (removeKey m k)
    |--
    map_ptr |-> AnkerMapPayloadsR kty vty kR vR 1%Qp m.
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (k, (loc, v)) ∈ m).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_N :
      nth_error m (N.to_nat (N.of_nat i)) = Some (k, (loc, v))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    erewrite (@borrowIndex_at _ _ _ _ 1 K V _
      kty vty kR vR m (N.of_nat i) (k, (loc, v)) k map_ptr
      Hnth_N eq_refl).
    unfold pairR.
    go.
  Qed.

  Definition reinsert_map_payload_B
      {K V : Type} `{Countable K}
      (kty vty : type) (kR : Qp -> K -> Rep) (vR : Qp -> V -> Rep)
      (map_ptr : ptr) (m : MapModel K V) (k : K) (loc : ptr) (v : V)
      (Hlookup : mapModelLookup m k = Some (loc, v)) :=
    [BWD] (@reinsert_map_payload K V _ _ kty vty kR vR
             map_ptr m k loc v Hlookup).

  Definition version_stack_unfolded_R
      (q : Qp) (lt : list (ptr * UpdatedAccountState)) : Rep :=
    VersionStackSpineR "monad::AccountState" q (map fst lt)
    ** pureR
      ([∗ list] p ∈ lt,
        let '(loc, val0) := p in
        (loc : ptr) |-> UpdatedAccountStateR q val0).

  Lemma reinsert_current_head_payload_unfolded
      (map_ptr : ptr)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address)
      (loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2)%Qp addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** upd_loc |-> UpdatedAccountStateR 1 upd
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR version_stack_unfolded_R
          1 (removeKey cur addr)
    |--
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR version_stack_unfolded_R 1 cur.
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, (upd_loc, upd) :: tl)) ∈ cur).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [idx Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_N :
      nth_error cur (N.to_nat (N.of_nat idx)) =
      Some (addr, (loc, (upd_loc, upd) :: tl))).
    {
      rewrite Nat2N.id.
      exact Hnth.
    }
    erewrite (@borrowIndex_at _ _ _ _ 1
      evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR version_stack_unfolded_R
      cur (N.of_nat idx) (addr, (loc, (upd_loc, upd) :: tl))
      addr map_ptr Hnth_N eq_refl).
    unfold pairR, version_stack_unfolded_R.
    simpl.
    go.
  Qed.

  Definition reinsert_current_head_payload_unfolded_B
      map_ptr cur addr loc upd_loc upd tl Hlookup :=
    [BWD] (reinsert_current_head_payload_unfolded
             map_ptr cur addr loc upd_loc upd tl Hlookup).

  Lemma reinsert_current_head_map_unfolded
      (map_ptr : ptr)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address)
      (loc upd_loc : ptr)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    map_ptr |-> AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR 1
          (map (fun '(a, (b, _)) => (a, b)) cur)
    ** loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2)%Qp addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** upd_loc |-> UpdatedAccountStateR 1 upd
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR version_stack_unfolded_R
          1 (removeKey cur addr)
    |--
    map_ptr |-> AnkerMapR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR
          (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 cur.
  Proof using CU MODd Sigma.
    intro Hlookup.
    rewrite AnkerMapSplit_at.
    unfold VersionStackR.
    go using reinsert_current_head_payload_unfolded_B.
  Qed.

  Definition reinsert_current_head_map_unfolded_B
      map_ptr cur addr loc upd_loc upd tl Hlookup :=
    [BWD] (reinsert_current_head_map_unfolded
             map_ptr cur addr loc upd_loc upd tl Hlookup).

  Lemma removeKey_try_fix_account_updated_orig_map_same
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (actual : option AccountM) :
    removeKey (try_fix_account_updated_orig_map addr actual orig) addr =
    removeKey orig addr.
  Proof using.
    induction orig as [| [addr' [loc orig_state]] tl IH]; simpl.
    {
      reflexivity.
    }
    destruct (decide (addr' = addr)) as [-> | Hneq].
    {
      assert (Heq : asbool (addr = addr) = true).
      {
        apply bool_decide_eq_true_2.
        reflexivity.
      }
      rewrite Heq.
      simpl.
      assert (Hneqfalse : asbool (addr ≠ addr) = false).
      {
        apply bool_decide_eq_false_2.
        intro Hneq.
        exact (Hneq eq_refl).
      }
      rewrite Hneqfalse.
      exact IH.
    }
    {
      assert (Heqfalse : asbool (addr' = addr) = false).
      {
        apply bool_decide_eq_false_2.
        exact Hneq.
      }
      rewrite Heqfalse.
      simpl.
      assert (Hneqtrue : asbool (addr' ≠ addr) = true).
      {
        apply bool_decide_eq_true_2.
        exact Hneq.
      }
      rewrite Hneqtrue.
      f_equal.
      exact IH.
    }
  Qed.

  Lemma map_key_ptr_try_fix_account_updated_orig_map
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (actual : option AccountM) :
    map (fun '(a, (loc, _)) => (a, loc))
      (try_fix_account_updated_orig_map addr actual orig) =
    map (fun '(a, (loc, _)) => (a, loc)) orig.
  Proof using.
    unfold try_fix_account_updated_orig_map.
    rewrite map_map.
    apply map_ext.
    intros [addr' [loc orig_state]].
    simpl.
    destruct (bool_decide (addr' = addr)); reflexivity.
  Qed.

  Lemma original_spine_try_fix_account_updated_orig_map
      (map_ptr : ptr)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (actual : option AccountM) :
    map_ptr |-> AnkerMapSpineR
      "monad::Address" "monad::OriginalAccountState"
      addressToN addressR 1
      (map (fun '(a, (loc, _)) => (a, loc)) orig)
    |-- map_ptr |-> AnkerMapSpineR
      "monad::Address" "monad::OriginalAccountState"
      addressToN addressR 1
      (map (fun '(a, (loc, _)) => (a, loc))
         (try_fix_account_updated_orig_map addr actual orig)).
  Proof using.
    rewrite (map_key_ptr_try_fix_account_updated_orig_map
      orig addr actual).
    go.
  Qed.

  Definition original_spine_try_fix_account_updated_orig_map_B
      map_ptr orig addr actual :=
    [BWD] (original_spine_try_fix_account_updated_orig_map
      map_ptr orig addr actual).

  Lemma reinsert_try_fix_account_updated_original_payload
      (map_ptr : ptr)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (loc : ptr)
      (orig_state : AssumedPreTxAccountState)
      (actual : option AccountM) :
    mapModelLookup orig addr = Some (loc, orig_state) ->
    map_ptr |-> AnkerMapPayloadsR
      "monad::Address" "monad::OriginalAccountState"
      addressR OriginalAccountStateR 1 (removeKey orig addr)
    ** loc |-> pairFstOffset
      "monad::Address" "monad::OriginalAccountState"
      |-> addressR (1 / 2) addr
    ** loc ,, pairSndOffset
      "monad::Address" "monad::OriginalAccountState"
      |-> OriginalAccountStateR 1
        (try_fix_account_original_update actual orig_state)
    |-- map_ptr |-> AnkerMapPayloadsR
      "monad::Address" "monad::OriginalAccountState"
      addressR OriginalAccountStateR 1
      (try_fix_account_updated_orig_map addr actual orig).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, orig_state)) ∈ orig).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [i Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_upd :
      nth_error (try_fix_account_updated_orig_map addr actual orig)
        (N.to_nat (N.of_nat i)) =
      Some (addr, (loc,
        try_fix_account_original_update actual orig_state))).
    {
      rewrite Nat2N.id.
      unfold try_fix_account_updated_orig_map.
      rewrite nth_error_map.
      rewrite Hnth.
      simpl.
      rewrite (bool_decide_eq_true_2 (addr = addr)).
      2: reflexivity.
      reflexivity.
    }
    rewrite <- (removeKey_try_fix_account_updated_orig_map_same
      orig addr actual).
    erewrite (@borrowIndex_at _ _ _ _ 1
      evm.address AssumedPreTxAccountState _
      "monad::Address" "monad::OriginalAccountState"
      addressR OriginalAccountStateR
      (try_fix_account_updated_orig_map addr actual orig) (N.of_nat i)
      (addr, (loc, try_fix_account_original_update actual orig_state))
      addr map_ptr);
      [| exact Hnth_upd | reflexivity].
    unfold pairR.
    go.
  Qed.

  Definition reinsert_try_fix_account_updated_original_payload_B
      map_ptr orig addr loc orig_state actual Hlookup :=
    [BWD] (reinsert_try_fix_account_updated_original_payload
      map_ptr orig addr loc orig_state actual Hlookup).

  Lemma removeKey_try_fix_account_updated_cur_map_same
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address) (actual original : AccountM) :
    removeKey (try_fix_account_updated_cur_map addr actual original cur) addr =
    removeKey cur addr.
  Proof using.
    induction cur as [| [addr' [loc updates]] tl IH]; simpl.
    {
      reflexivity.
    }
    destruct (decide (addr' = addr)) as [-> | Hneq].
    {
      assert (Heq : asbool (addr = addr) = true).
      {
        apply bool_decide_eq_true_2.
        reflexivity.
      }
      rewrite Heq.
      simpl.
      assert (Hneqfalse : asbool (addr ≠ addr) = false).
      {
        apply bool_decide_eq_false_2.
        intro Hneq.
        exact (Hneq eq_refl).
      }
      rewrite Hneqfalse.
      exact IH.
    }
    {
      assert (Heqfalse : asbool (addr' = addr) = false).
      {
        apply bool_decide_eq_false_2.
        exact Hneq.
      }
      rewrite Heqfalse.
      simpl.
      assert (Hneqtrue : asbool (addr' ≠ addr) = true).
      {
        apply bool_decide_eq_true_2.
        exact Hneq.
      }
      rewrite Hneqtrue.
      f_equal.
      exact IH.
    }
  Qed.

  Lemma map_key_ptr_try_fix_account_updated_cur_map
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address) (actual original : AccountM) :
    map (fun '(a, (loc, _)) => (a, loc))
      (try_fix_account_updated_cur_map addr actual original cur) =
    map (fun '(a, (loc, _)) => (a, loc)) cur.
  Proof using.
    unfold try_fix_account_updated_cur_map.
    rewrite map_map.
    apply map_ext.
    intros [addr' [loc updates]].
    simpl.
    destruct (bool_decide (addr' = addr)); reflexivity.
  Qed.

  Lemma current_spine_try_fix_account_updated_cur_map
      (map_ptr : ptr)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address) (actual original : AccountM) :
    map_ptr |-> AnkerMapSpineR
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressToN addressR 1
      (map (fun '(a, (loc, _)) => (a, loc)) cur)
    |-- map_ptr |-> AnkerMapSpineR
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressToN addressR 1
      (map (fun '(a, (loc, _)) => (a, loc))
         (try_fix_account_updated_cur_map addr actual original cur)).
  Proof using.
    rewrite (map_key_ptr_try_fix_account_updated_cur_map
      cur addr actual original).
    go.
  Qed.

  Definition current_spine_try_fix_account_updated_cur_map_B
      map_ptr cur addr actual original :=
    [BWD] (current_spine_try_fix_account_updated_cur_map
      map_ptr cur addr actual original).

  Lemma reinsert_try_fix_account_updated_current_payload_unfolded
      (map_ptr : ptr)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address)
      (loc upd_loc : ptr)
      (actual original : AccountM)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2)%Qp addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** upd_loc |-> UpdatedAccountStateR 1
         (try_fix_account_current_update actual original upd)
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR version_stack_unfolded_R
          1 (removeKey cur addr)
    |--
    map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR version_stack_unfolded_R 1
          (try_fix_account_updated_cur_map addr actual original cur).
  Proof using CU MODd Sigma.
    intro Hlookup.
    assert (Hmem : (addr, (loc, (upd_loc, upd) :: tl)) ∈ cur).
    {
      eapply elem_of_list_to_map_2.
      exact Hlookup.
    }
    destruct (list_elem_of_lookup_1 _ _ Hmem) as [idx Hnth].
    rewrite lookup_nth_error in Hnth.
    assert (Hnth_upd :
      nth_error (try_fix_account_updated_cur_map addr actual original cur)
        (N.to_nat (N.of_nat idx)) =
      Some (addr, (loc,
        (upd_loc, try_fix_account_current_update actual original upd) :: tl))).
    {
      rewrite Nat2N.id.
      unfold try_fix_account_updated_cur_map.
      rewrite nth_error_map.
      rewrite Hnth.
      simpl.
      rewrite (bool_decide_eq_true_2 (addr = addr)).
      2: reflexivity.
      reflexivity.
    }
    rewrite <- (removeKey_try_fix_account_updated_cur_map_same
      cur addr actual original).
    erewrite (@borrowIndex_at _ _ _ _ 1
      evm.address (list (ptr * UpdatedAccountState)) _
      "monad::Address" "monad::VersionStack<monad::AccountState>"
      addressR version_stack_unfolded_R
      (try_fix_account_updated_cur_map addr actual original cur)
      (N.of_nat idx)
      (addr, (loc,
        (upd_loc, try_fix_account_current_update actual original upd) :: tl))
      addr map_ptr);
      [| exact Hnth_upd | reflexivity].
    unfold pairR, version_stack_unfolded_R.
    simpl.
    go.
  Qed.

  Definition reinsert_try_fix_account_updated_current_payload_unfolded_B
      map_ptr cur addr loc upd_loc actual original upd tl Hlookup :=
    [BWD] (reinsert_try_fix_account_updated_current_payload_unfolded
             map_ptr cur addr loc upd_loc actual original upd tl Hlookup).

  Lemma reinsert_try_fix_account_updated_current_map_unfolded
      (map_ptr : ptr)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr : evm.address)
      (loc upd_loc : ptr)
      (actual original : AccountM)
      (upd : UpdatedAccountState)
      (tl : list (ptr * UpdatedAccountState)) :
    mapModelLookup cur addr = Some (loc, (upd_loc, upd) :: tl) ->
    map_ptr |-> AnkerMapSpineR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR 1
          (map (fun '(a, (b, _)) => (a, b)) cur)
    ** loc |-> pairFstOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> addressR (1 / 2)%Qp addr
    ** loc ,, pairSndOffset
             "monad::Address" "monad::VersionStack<monad::AccountState>"
         |-> VersionStackSpineR "monad::AccountState" 1
              (upd_loc :: map fst tl)
    ** upd_loc |-> UpdatedAccountStateR 1
         (try_fix_account_current_update actual original upd)
    ** ([∗ list] p ∈ tl,
          let '(loc0, val0) := p in
          (loc0 : ptr) |-> UpdatedAccountStateR 1 val0)
    ** map_ptr |-> AnkerMapPayloadsR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressR version_stack_unfolded_R
          1 (removeKey cur addr)
    |--
    map_ptr |-> AnkerMapR
          "monad::Address" "monad::VersionStack<monad::AccountState>"
          addressToN addressR
          (VersionStackR "monad::AccountState" UpdatedAccountStateR)
          1 (try_fix_account_updated_cur_map addr actual original cur).
  Proof using CU MODd Sigma.
    intro Hlookup.
    rewrite AnkerMapSplit_at.
    unfold VersionStackR.
    go using
      current_spine_try_fix_account_updated_cur_map_B,
      reinsert_try_fix_account_updated_current_payload_unfolded_B.
  Qed.

  Definition reinsert_try_fix_account_updated_current_map_unfolded_B
      map_ptr cur addr loc upd_loc actual original upd tl Hlookup :=
    [BWD] (reinsert_try_fix_account_updated_current_map_unfolded
             map_ptr cur addr loc upd_loc actual original upd tl Hlookup).

  Local Transparent AccountStateRcore.

  Lemma AccountStateRcore_separated_unfold
      (p : ptr) (q : Qp) (acct : option AccountM) :
    p |-> AccountStateRcore q acct
    |--
    Exists transient_map : list (N * N),
      p ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.optionR "monad::Account"%cpp_type
              AccountR q acct
      ** p ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR q (storageMapOf acct)
      ** p ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR q transient_map
      ** p |-> structR "monad::AccountState"%cpp_name (cQp.mut q).
  Proof using CU MODd Sigma.
    unfold AccountStateRcore.
    go.
  Qed.

  Definition AccountStateRcore_separated_unfold_F p q acct :=
    [FWD] (AccountStateRcore_separated_unfold p q acct).

  Lemma AccountStateRcore_separated_fold
      (p : ptr) (q : Qp) (acct : option AccountM)
      (transient_map : list (N * N)) :
    p ,, o_field CU "monad::AccountState::account_"
      |-> optional_specs.optionR "monad::Account"%cpp_type
            AccountR q acct
    ** p ,, o_field CU "monad::AccountState::storage_"
      |-> StorageMapR q (storageMapOf acct)
    ** p ,, o_field CU "monad::AccountState::transient_storage_"
      |-> StorageMapR q transient_map
    ** p |-> structR "monad::AccountState"%cpp_name (cQp.mut q)
    |-- p |-> AccountStateRcore q acct.
  Proof using CU MODd Sigma.
    unfold AccountStateRcore.
    go.
  Qed.

  Definition AccountStateRcore_separated_fold_B
      p q acct transient_map :=
    [BWD] (AccountStateRcore_separated_fold
             p q acct transient_map).

  Lemma AccountStateRcore_some_fields_fold
      (p : ptr) (acct : AccountM) (transient_map : list (N * N)) :
    balance acct =
      w256_to_N (block.block_account_balance (coreAc acct)) ->
    p ,, o_field CU "monad::AccountState::account_"
      |-> optional_specs.spineR "monad::Account" 1$m
        (Some (p ,, o_field CU "monad::AccountState::account_"
          ,, optional_specs.value_offset "monad::Account"))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::balance"
      |-> u256R 1
            (w256_to_N (block.block_account_balance (coreAc acct)))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::code_hash"
      |-> bytes32R 1
            (code_hash_of_program (block.block_account_code (coreAc acct)))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::nonce"
      |-> primR "unsigned long" 1$m
            (w256_to_Z (block.block_account_nonce (coreAc acct)))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::incarnation"
      |-> IncarnationR 1 (incarnation acct)
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      |-> structR "monad::Account"%cpp_name 1$m
    ** p ,, o_field CU "monad::AccountState::storage_"
      |-> StorageMapR 1 (storageMapOf (Some acct))
    ** p ,, o_field CU "monad::AccountState::transient_storage_"
      |-> StorageMapR 1 transient_map
    ** p |-> structR "monad::AccountState"%cpp_name 1$m
    |-- p |-> AccountStateRcore 1 (Some acct).
  Proof using CU MODd Sigma.
    intro Hbalance.
    unfold AccountStateRcore.
    go using
      account_option_layout_fold_B,
      optionR_account_some_separated_fold_B,
      AccountR_separated_fold_B.
  Qed.

  Definition AccountStateRcore_some_fields_fold_B
      p acct transient_map Hbalance :=
    [BWD] (AccountStateRcore_some_fields_fold
             p acct transient_map Hbalance).

  Local Opaque AccountStateRcore.

  Lemma UpdatedAccountStateR_separated_fold
      (p : ptr) (q : Qp) (upd : UpdatedAccountState) :
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

  Lemma UpdatedAccountStateR_separated_none_fold
      (p : ptr) (q : Qp) (upd : UpdatedAccountState) :
    postTxState upd = None ->
    p |-> AccountStateRcore q None
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR q (substateModel upd)
    |-- p |-> UpdatedAccountStateR q upd.
  Proof using CU MODd Sigma.
    intro Hrecent.
    rewrite <- Hrecent.
    apply UpdatedAccountStateR_separated_fold.
  Qed.

  Definition UpdatedAccountStateR_separated_none_fold_B p q upd Hrecent :=
    [BWD] (UpdatedAccountStateR_separated_none_fold p q upd Hrecent).

  Lemma UpdatedAccountStateR_try_fix_current_update_add_fold
      (p : ptr) (actual original recent : AccountM)
      (upd : UpdatedAccountState)
      (transient_map : list (N * N)) :
    postTxState upd = Some recent ->
    (balance original < balance actual)%N ->
    p ,, o_field CU "monad::AccountState::account_"
      |-> optional_specs.spineR "monad::Account" 1$m
        (Some (p ,, o_field CU "monad::AccountState::account_"
          ,, optional_specs.value_offset "monad::Account"))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::balance"
      |-> u256R 1
            ((balance recent + (balance actual - balance original)) mod
             uint256_word_modulus)
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::code_hash"
      |-> bytes32R 1
            (code_hash_of_program (block.block_account_code (coreAc recent)))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::nonce"
      |-> primR "unsigned long" 1$m
            (w256_to_Z (block.block_account_nonce (coreAc recent)))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::incarnation"
      |-> IncarnationR 1 (incarnation recent)
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      |-> structR "monad::Account"%cpp_name 1$m
    ** p ,, o_field CU "monad::AccountState::storage_"
      |-> StorageMapR 1 (storageMapOf (Some recent))
    ** p ,, o_field CU "monad::AccountState::transient_storage_"
      |-> StorageMapR 1 transient_map
    ** p |-> structR "monad::AccountState"%cpp_name 1$m
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 (substateModel upd)
    |--
    p |-> UpdatedAccountStateR 1
      (try_fix_account_current_update actual original upd).
  Proof using CU MODd Sigma.
    intros Hpost Hlt.
    unfold try_fix_account_current_update.
    rewrite Hpost.
    rewrite bool_decide_eq_true_2.
    2: exact Hlt.
    cbn [postTxState substateModel].
    wapply (StorageMapR_account_set_balance
      (p ,, o_field CU "monad::AccountState::storage_")
      1 recent
      ((balance recent + (balance actual - balance original)) mod
       uint256_word_modulus)).
    go using
      account_option_layout_fold_B,
      AccountR_account_set_balance_mod_fold_B,
      optionR_account_some_separated_fold_B,
      AccountStateRcore_separated_fold_B,
      UpdatedAccountStateR_separated_fold_B.
  Qed.

  Definition UpdatedAccountStateR_try_fix_current_update_add_fold_B
      p actual original recent upd transient_map Hpost Hlt :=
    [BWD] (UpdatedAccountStateR_try_fix_current_update_add_fold
             p actual original recent upd transient_map Hpost Hlt).

  Lemma UpdatedAccountStateR_try_fix_current_update_sub_fold
      (p : ptr) (actual original recent : AccountM)
      (upd : UpdatedAccountState)
      (transient_map : list (N * N)) :
    postTxState upd = Some recent ->
    (balance actual < balance original)%N ->
    p ,, o_field CU "monad::AccountState::account_"
      |-> optional_specs.spineR "monad::Account" 1$m
        (Some (p ,, o_field CU "monad::AccountState::account_"
          ,, optional_specs.value_offset "monad::Account"))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::balance"
      |-> u256R 1
            (Z.to_N
              ((Z.of_N (balance recent) -
                Z.of_N (balance original - balance actual)) mod
               Z.of_N uint256_modulus)%Z)
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::code_hash"
      |-> bytes32R 1
            (code_hash_of_program (block.block_account_code (coreAc recent)))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::nonce"
      |-> primR "unsigned long" 1$m
            (w256_to_Z (block.block_account_nonce (coreAc recent)))
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      ,, o_field CU "monad::Account::incarnation"
      |-> IncarnationR 1 (incarnation recent)
    ** p ,, o_field CU "monad::AccountState::account_"
      ,, optional_specs.value_offset "monad::Account"%cpp_type
      |-> structR "monad::Account"%cpp_name 1$m
    ** p ,, o_field CU "monad::AccountState::storage_"
      |-> StorageMapR 1 (storageMapOf (Some recent))
    ** p ,, o_field CU "monad::AccountState::transient_storage_"
      |-> StorageMapR 1 transient_map
    ** p |-> structR "monad::AccountState"%cpp_name 1$m
    ** p ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 (substateModel upd)
    |--
    p |-> UpdatedAccountStateR 1
      (try_fix_account_current_update actual original upd).
  Proof using CU MODd Sigma.
    intros Hpost Hlt.
    unfold try_fix_account_current_update.
    rewrite Hpost.
    replace (asbool (balance original < balance actual)%N) with false by
      (symmetry; apply bool_decide_false; lia).
    cbn [postTxState substateModel].
    wapply
      (StorageMapR_account_set_balance
         (p ,, o_field CU "monad::AccountState::storage_")
         1 recent
         (Z.to_N
            ((Z.of_N (balance recent) -
              Z.of_N (balance original - balance actual)) mod
             Z.of_N uint256_modulus)%Z)).
    go using
      account_option_layout_fold_B,
      optionR_account_some_separated_fold_B,
      (AccountR_account_set_balance_zmod_fold_B
         (p ,, o_field CU "monad::AccountState::account_"
          ,, optional_specs.value_offset "monad::Account"%cpp_type)
         recent
         (Z.of_N (balance recent) -
          Z.of_N (balance original - balance actual))%Z),
      AccountStateRcore_separated_fold_B,
      UpdatedAccountStateR_separated_fold_B.
  Qed.

  Definition UpdatedAccountStateR_try_fix_current_update_sub_fold_B
      p actual original recent upd transient_map Hpost Hlt :=
    [BWD] (UpdatedAccountStateR_try_fix_current_update_sub_fold
             p actual original recent upd transient_map Hpost Hlt).

  Lemma OriginalAccountStateR_separated_unfold
      (p : ptr) (q : Qp) (orig_state : AssumedPreTxAccountState) :
    p |-> OriginalAccountStateR q orig_state
    |--
    Exists transient_map : list (N * N),
      p |-> structR "monad::OriginalAccountState"%cpp_name (cQp.mut q)
      ** p ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
          |-> boolR (cQp.mut q)
            (~~ bool_decide (is_Some (min_balance (assumExactness orig_state))))
      ** p ,, o_field CU "monad::OriginalAccountState::min_balance_"
          |-> match min_balance (assumExactness orig_state) with
              | Some n => u256R q n
              | None => Exists nb : N, u256R q nb
              end
      ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
          ,, o_field CU "monad::AccountState::account_"
          |-> optional_specs.optionR "monad::Account"%cpp_type
                AccountR q (preTxState orig_state)
      ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
          ,, o_field CU "monad::AccountState::storage_"
          |-> StorageMapR q (preTxStorage orig_state)
      ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
          ,, o_field CU "monad::AccountState::transient_storage_"
          |-> StorageMapR q transient_map
      ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
          |-> structR "monad::AccountState"%cpp_name (cQp.mut q)
      ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
          ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
          |-> AccountSubstateR q unusedAccountSubstate.
  Proof using CU MODd Sigma.
    unfold OriginalAccountStateR.
    go.
  Qed.

  Definition OriginalAccountStateR_separated_unfold_F p q orig_state :=
    [FWD] (OriginalAccountStateR_separated_unfold p q orig_state).

  Lemma OriginalAccountStateR_separated_fold
      (p : ptr) (q : Qp) (orig_state : AssumedPreTxAccountState)
      (transient_map : list (N * N)) :
    p |-> structR "monad::OriginalAccountState"%cpp_name (cQp.mut q)
    ** p ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
        |-> boolR (cQp.mut q)
          (~~ bool_decide (is_Some (min_balance (assumExactness orig_state))))
    ** p ,, o_field CU "monad::OriginalAccountState::min_balance_"
        |-> match min_balance (assumExactness orig_state) with
            | Some n => u256R q n
            | None => Exists nb : N, u256R q nb
            end
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.optionR "monad::Account"%cpp_type
              AccountR q (preTxState orig_state)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR q (preTxStorage orig_state)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR q transient_map
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        |-> structR "monad::AccountState"%cpp_name (cQp.mut q)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR q unusedAccountSubstate
    |--
    p |-> OriginalAccountStateR q orig_state.
  Proof using CU MODd Sigma.
    unfold OriginalAccountStateR.
    go.
  Qed.

  Definition OriginalAccountStateR_separated_fold_B
      p q orig_state transient_map :=
    [BWD] (OriginalAccountStateR_separated_fold
             p q orig_state transient_map).

  Lemma OriginalAccountStateR_separated_some_fold
      (p : ptr) (q : Qp) (orig_state : AssumedPreTxAccountState)
      (acct : AccountM) (transient_map : list (N * N)) :
    preTxState orig_state = Some acct ->
    p |-> structR "monad::OriginalAccountState"%cpp_name (cQp.mut q)
    ** p ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
        |-> boolR (cQp.mut q)
          (~~ bool_decide (is_Some (min_balance (assumExactness orig_state))))
    ** p ,, o_field CU "monad::OriginalAccountState::min_balance_"
        |-> match min_balance (assumExactness orig_state) with
            | Some n => u256R q n
            | None => Exists nb : N, u256R q nb
            end
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.optionR "monad::Account"%cpp_type
              AccountR q (Some acct)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR q (preTxStorage orig_state)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR q transient_map
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        |-> structR "monad::AccountState"%cpp_name (cQp.mut q)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR q unusedAccountSubstate
    |--
    p |-> OriginalAccountStateR q orig_state.
  Proof using CU MODd Sigma.
    intro Hpre.
    rewrite <- Hpre.
    apply OriginalAccountStateR_separated_fold.
  Qed.

  Definition OriginalAccountStateR_separated_some_fold_B
      p q orig_state acct transient_map Hpre :=
    [BWD] (OriginalAccountStateR_separated_some_fold
             p q orig_state acct transient_map Hpre).

  Lemma OriginalAccountStateR_try_fix_account_balance_update_some_fold
      (p : ptr) (orig_state : AssumedPreTxAccountState)
      (original actual : AccountM)
      (transient_map : list (N * N)) (min_balance_value : N) :
    preTxState orig_state = Some original ->
    min_balance (assumExactness orig_state) = Some min_balance_value ->
    p |-> structR "monad::OriginalAccountState"%cpp_name 1$m
    ** p ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
        |-> boolR 1$m false
    ** p ,, o_field CU "monad::OriginalAccountState::min_balance_"
        |-> u256R 1 min_balance_value
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.optionR "monad::Account"%cpp_type
              AccountR 1
              (Some (account_set_balance original (balance actual)))
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR 1 (preTxStorage orig_state)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR 1 transient_map
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        |-> structR "monad::AccountState"%cpp_name 1$m
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 unusedAccountSubstate
    |--
    p |-> OriginalAccountStateR 1
      (try_fix_account_balance_update (Some actual) orig_state).
  Proof using CU MODd Sigma.
    intros Hpre Hmin.
    unfold OriginalAccountStateR, try_fix_account_balance_update.
    rewrite Hpre.
    cbn [preTxState preTxStorage assumExactness min_balance].
    rewrite Hmin.
    change (~~ bool_decide (is_Some (Some min_balance_value)))
      with false.
    go.
  Qed.

  Definition OriginalAccountStateR_try_fix_account_balance_update_some_fold_B
      p orig_state original actual transient_map min_balance_value Hpre Hmin :=
    [BWD] (OriginalAccountStateR_try_fix_account_balance_update_some_fold
             p orig_state original actual transient_map
             min_balance_value Hpre Hmin).

  Lemma OriginalAccountStateR_try_fix_account_original_update_some_fold
      (p : ptr) (orig_state : AssumedPreTxAccountState)
      (original actual : AccountM)
      (transient_map : list (N * N)) (min_balance_value : N) :
    preTxState orig_state = Some original ->
    p |-> structR "monad::OriginalAccountState"%cpp_name 1$m
    ** p ,, o_field CU "monad::OriginalAccountState::validate_exact_balance_"
        |-> boolR 1$m true
    ** p ,, o_field CU "monad::OriginalAccountState::min_balance_"
        |-> u256R 1 min_balance_value
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::account_"
        |-> optional_specs.optionR "monad::Account"%cpp_type
              AccountR 1
              (Some (account_set_balance original (balance actual)))
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::storage_"
        |-> StorageMapR 1 (preTxStorage orig_state)
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_field CU "monad::AccountState::transient_storage_"
        |-> StorageMapR 1 transient_map
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        |-> structR "monad::AccountState"%cpp_name 1$m
    ** p ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
        ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
        |-> AccountSubstateR 1 unusedAccountSubstate
    |--
    p |-> OriginalAccountStateR 1
      (try_fix_account_original_update (Some actual) orig_state).
  Proof using CU MODd Sigma.
    intro Hpre.
    unfold try_fix_account_original_update,
      try_fix_account_balance_update,
      update_assum_exactness_assumed,
      exact_balance_update.
    rewrite Hpre.
    cbn [preTxState preTxStorage assumExactness min_balance].
    go using OriginalAccountStateR_separated_fold_B.
  Qed.

  Definition OriginalAccountStateR_try_fix_account_original_update_some_fold_B
      p orig_state original actual transient_map min_balance_value Hpre :=
    [BWD] (OriginalAccountStateR_try_fix_account_original_update_some_fold
             p orig_state original actual transient_map
             min_balance_value Hpre).

  Definition map_model_iterR_snd_map_F {K V : Type} :=
    [FWD] (@map_model_iterR_snd_map_at K V).
  Definition map_model_iterR_snd_map_B {K V : Type} :=
    [BWD] (@map_model_iterR_snd_map_rev_at K V).
  Definition map_model_iterR_end_map_B {K V : Type} :=
    [BWD] (@map_model_iterR_end_map_rev_at K V).

  #[local] Hint Resolve
    map_model_spine_lengthN_sym
    map_model_find_index_not_end
    map_model_spine_lookup_ploc_exists
    map_model_lookup_none_of_not_elem
    map_model_lookup_some_not_spine_absurd
    map_model_lookup_of_spine_lookup
    : pure.

  #[local] Hint Resolve
    map_model_iterR_snd_map_F
    : sl_opacity.

  #[local] Hint Rewrite
    (@map_model_spine_snd evm.address AssumedPreTxAccountState)
    (@map_model_spine_fst evm.address AssumedPreTxAccountState)
    (@map_model_spine_lengthN evm.address AssumedPreTxAccountState)
    (@map_model_spine_snd evm.address (list (ptr * UpdatedAccountState)))
    (@map_model_spine_fst evm.address (list (ptr * UpdatedAccountState)))
    (@map_model_spine_lengthN evm.address (list (ptr * UpdatedAccountState)))
    : syntactic.

  #[local] Hint Opaque
    optional_account_has_value_spec
    optional_account_value_spec
    optional_account_bool_spec
    optional_account_arrow_spec
    optional_account_arrow_const_spec
    is_dead_spec
    uint256_max_spec
    uint256dtor
    uint256_copy_ctor_spec
    u256_eq_spec
    u256_lt_spec
    u256_gt_spec
    u256_ge_spec
    u256_minus_spec
    u256_sub_assign_spec
    u256_add_assign_spec
    accountstate_min_balance_spec
    accountstate_validate_exact_balance_spec
    accountstate_set_validate_exact_balance_spec
    optional_specs.optionR
    AccountR
    OriginalAccountStateR
    UpdatedAccountStateR
    AccountStateRcore
    VersionStackR
    AnkerMapR
    AnkerMapPayloadsR
    AnkerMapSpineR
    AnkerMapIterR
    : sl_opacity.

  #[local] Hint Resolve
    observeU256F
    observeAnkerMapSpineTypePtrF
    observeAnkerMapSpineTypePtrRF
    observeAnkerIterFf
    observeAnkerIterRFf
    observeAnkerIterConstFf
    observeAnkerIterConstRFf
    type_ptr_reference_to_B_local
    anker_iter_keep_type_ptr_C
    anker_iter_keep_const_type_ptr_C
    anker_map_spine_keep_type_ptr_C
    observe_type_ptr_fwd
    observe_type_ptr_box_fwd
    type_ptr_elim_reference_to_C
    wp_initialize_unfold_B
    wp_init_mcall_minvoke_B
    wp_minvoke_direct_I_inline_C
    wp_minvoke_direct_I_unmaterialized_C
    wp_init_cast_noop_B
    wp_lval_mcall_minvoke_B
    wp_minvoke_direct_GL_unmaterialized_C
    version_stack_spine_keep_type_ptr_C
    observeVersionStackSpineTypePtrF
    : sl_opacity.

  (* Temporarily suspended with user authorization on 2026-09-07.
     The upgraded call rule cannot handle the unsupported Incarnation bitfield
     type passed by value. See brickmisc/issues/incarnation-callability.md.
     Keep both the unfinished body proof and its spec registration inactive;
     the checked helper lemmas above remain available.

  cpp.spec "monad::State::try_fix_account_mismatch(const monad::Address&, const std::optional<monad::Account>&)"
    from state_cpp.source as state_try_fix_account_mismatch_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \arg{actualp : ptr} "actual" (Vref actualp)
      \prepost{qnull}
        _global "monad::NULL_HASH" |-> bytes32R qnull null_code_hash
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{actual} actualp |-> optional_specs.optionR
        "monad::Account" AccountR 1 actual
      \pre{orig cur relaxed orig_loc orig_state}
        StateTryFixAccountMismatchR this orig cur relaxed
      \pre [| mapModelLookup orig addr = Some (orig_loc, orig_state) |]
      \pre [| try_fix_account_balance_mismatch orig_state actual |]
      \pre [| try_fix_account_current_top_level (mapModelLookup cur addr) |]
      \pre [| try_fix_account_balance_invariant orig cur |]
      \post{retb : bool} [Vbool retb]
        Exists orig_final,
        Exists cur_final,
          StateTryFixAccountMismatchR this orig_final cur_final relaxed
          ** [| try_fix_account_balance_invariant orig_final cur_final |]
          ** [|
            try_fix_account_mismatch_ret_prop
              addr actual orig cur relaxed orig_loc orig_state retb
              orig_final cur_final |]).

  Lemma prf_state_try_fix_account_mismatch :
    verify?[state_cpp.source] state_try_fix_account_mismatch_spec.
  Proof using MODd.
    verify_spec.
    unfold StateTryFixAccountMismatchR.
    go using asplitF.
    destruct t.
    {
      go.
      assert (False) by
        (eapply map_model_lookup_some_not_spine_absurd; eauto).
      contradiction.
    }
    {
      go.
      destruct (map_model_spine_lookup_ploc_exists orig addr i)
        as [ploc Hploc].
      {
        assumption.
      }
      go using observeAnkerIterPointeeF.
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::OriginalAccountState" false ?qi i ?spine] =>
          rewrite (anker_iter_keep_type_ptr
            iterp "monad::Address" "monad::OriginalAccountState"
            false i spine)
      end.
      go using
        (@map_model_iterR_snd_map_B
          evm.address AssumedPreTxAccountState),
        (@map_model_iterR_end_map_B
          evm.address AssumedPreTxAccountState),
        type_ptr_reference_to_B_local,
        anker_iter_keep_type_ptr_C,
        observeAnkerMapSpineTypePtrF,
        observeAnkerMapSpineTypePtrRF,
        observeAnkerIterFf,
        observeAnkerIterRFf,
        observeAnkerIterConstRFf,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C,
        wp_initialize_unfold_B,
        wp_init_mcall_minvoke_B,
        wp_minvoke_direct_I_inline_C,
        wp_minvoke_direct_I_unmaterialized_C,
        wp_init_cast_noop_B.
      destruct (map_model_lookup_of_spine_lookup orig addr i ploc)
        as [orig_state_at Hlookup_at].
      {
        assumption.
      }
      {
        assumption.
      }
      {
        exact Hploc.
      }
      match goal with
      | Hlookup_pre :
          mapModelLookup orig addr = Some (orig_loc, orig_state) |- _ =>
          rewrite Hlookup_pre in Hlookup_at
      end.
      injection Hlookup_at as Hploc_eq Horig_state_eq.
      subst ploc orig_state_at.
      match goal with
      | |- context[
          ?iterp |-> AnkerMapIterR
            "monad::Address" "monad::OriginalAccountState" false ?qi
            i (map (fun x => x.2.1) orig)] =>
          rewrite (anker_iter_keep_pointee_type_ptr
            iterp orig_loc "monad::Address" "monad::OriginalAccountState"
            i (map (fun x => x.2.1) orig) Hploc);
          rewrite (anker_iter_keep_pointee_value_field_type_ptr
            iterp orig_loc "monad::Address" "monad::OriginalAccountState"
            i (map (fun x => x.2.1) orig) Hploc)
      end.
      go using
        borrow_map_payload_F,
        OriginalAccountStateR_separated_unfold_F,
        observeAnkerIterPointeeF,
        observeAnkerIterPointeeValueFieldF,
        type_ptr_reference_to_B_local,
        observe_type_ptr_fwd,
        observe_type_ptr_box_fwd,
        type_ptr_elim_reference_to_C.
      wp_if.
      {
        go.
        iExists orig, cur.
        unfold StateTryFixAccountMismatchR.
        go using
          OriginalAccountStateR_separated_fold_B,
          reinsert_map_payload_B,
          asplitB.
      }
      {
        go.
        wp_if.
        {
          go.
          iExists orig, cur.
          unfold StateTryFixAccountMismatchR.
          go using
            OriginalAccountStateR_separated_fold_B,
            reinsert_map_payload_B,
            asplitB.
        }
        {
          destruct (preTxState orig_state) as [original_ac|] eqn:Horiginal_ac.
          2: {
            match goal with
            | H : is_Some None |- _ =>
                destruct H as [? Hnone];
                discriminate
            end.
          }
          destruct actual as [actual_ac|] eqn:Hactual_ac.
          2: {
            intros [Hsome _].
            destruct Hsome as [? Hnone].
            discriminate.
          }
          go using
            optionR_account_some_separated_unfold_F,
            account_option_layout_unfold_F,
            AccountR_separated_unfold_F.
          go using
            account_option_layout_fold_B,
            optionR_account_some_separated_fold_B,
            AccountR_separated_fold_B.
          iExists original_ac.
          go using
            account_option_layout_fold_B,
            optionR_account_some_separated_fold_B,
            AccountR_separated_fold_B,
            type_ptr_reference_to_B_local.
          iExists actual_ac.
          go using
            account_option_layout_fold_B,
            optionR_account_some_separated_fold_B,
            AccountR_separated_fold_B,
            type_ptr_reference_to_B_local.
          go using
            account_option_layout_fold_B,
            optionR_account_some_separated_fold_B,
            AccountR_separated_fold_B,
            OriginalAccountStateR_separated_some_fold_B,
            reinsert_map_payload_B.
          go using
            (@map_model_iterR_snd_map_B
              evm.address (list (ptr * UpdatedAccountState))),
            (@map_model_iterR_end_map_B
              evm.address (list (ptr * UpdatedAccountState))),
            type_ptr_reference_to_B_local,
            anker_iter_keep_type_ptr_C,
            observeAnkerMapSpineTypePtrF,
            observeAnkerMapSpineTypePtrRF,
            observeAnkerIterFf,
            observeAnkerIterRFf,
            observeAnkerIterConstFf,
            observe_type_ptr_fwd,
            observe_type_ptr_box_fwd,
            type_ptr_elim_reference_to_C,
            wp_initialize_unfold_B,
            wp_init_mcall_minvoke_B,
            wp_minvoke_direct_I_inline_C,
            wp_minvoke_direct_I_unmaterialized_C,
            wp_init_cast_noop_B.
          go using optional_specs.trivial_optional_some_split_F,
            AccountR_separated_unfold_F.
          wp_if.
          {
            go.
            iExists orig, cur.
            unfold StateTryFixAccountMismatchR.
            go using
              account_option_layout_fold_B,
              optionR_account_some_separated_fold_B,
              AccountR_separated_fold_B.
            go using
              account_option_layout_fold_B,
              optionR_account_some_separated_fold_B,
              AccountR_separated_fold_B,
              OriginalAccountStateR_separated_some_fold_B,
              reinsert_map_payload_B.
          }
          {
            go.
            iExists original_ac.
            go using
              account_option_layout_fold_B,
              optionR_account_some_separated_fold_B,
              AccountR_separated_fold_B,
              observe_IncarnationR_type_ptr_F,
              type_ptr_reference_to_B_local.
            iExists (1 : Qp), (incarnation original_ac).
            go using optional_specs.trivial_optional_some_split_F,
              AccountR_separated_unfold_F.
            go using
              eval.eval_1_B,
              observe_IncarnationR_type_ptr_F,
              type_ptr_reference_to_B_local.
            iExists actual_ac.
            go using
              account_option_layout_fold_B,
              optionR_account_some_separated_fold_B,
              AccountR_separated_fold_B,
              observe_IncarnationR_type_ptr_F,
              type_ptr_reference_to_B_local.
            iExists (1 : Qp), (incarnation actual_ac).
            go using optional_specs.trivial_optional_some_split_F,
              AccountR_separated_unfold_F.
            iExists (1 : Qp), (1 : Qp),
              (incarnation original_ac), (incarnation actual_ac).
            go.
            go.
            go using
              wp_destroy_val_named_C,
              incarnation_dtor_spec.
            iExists (incarnation actual_ac).
            go.
            go using
              destroy.wp_destroy_val_named_B,
              wp_destroy_val_named_C,
              incarnation_dtor_spec.
            iExists (incarnation original_ac).
            go.
            wp_if.
            {
              go.
              iExists orig, cur.
              unfold StateTryFixAccountMismatchR.
              go using
                account_option_layout_fold_B,
                optionR_account_some_separated_fold_B,
                AccountR_separated_fold_B.
              go using
                OriginalAccountStateR_separated_some_fold_B,
                reinsert_map_payload_B.
            }
            {
              go.
              iExists original_ac.
              go using
                optional_specs.trivial_optional_some_split_F,
                AccountR_separated_unfold_F,
                account_option_layout_fold_B,
                optionR_account_some_separated_fold_B,
                AccountR_separated_fold_B,
                type_ptr_reference_to_B_local.
              iExists actual_ac.
              go using
                optional_specs.trivial_optional_some_split_F,
                AccountR_separated_unfold_F,
                account_option_layout_fold_B,
                optionR_account_some_separated_fold_B,
                AccountR_separated_fold_B,
                type_ptr_reference_to_B_local.
              wp_if.
              {
                intro Hnonce_mismatch.
                step.
                step.
                step.
                step.
                step.
                step.
                step.
                step.
                step.
                step.
                step.
                step.
                step.
                go.
                iExists orig, cur.
                unfold StateTryFixAccountMismatchR.
                go using
                  account_option_layout_fold_B,
                  optionR_account_some_separated_fold_B,
                  AccountR_separated_fold_B.
                go using
                  OriginalAccountStateR_separated_some_fold_B,
                  reinsert_map_payload_B.
              }
              {
                go.
                assert (Hbalance_neq :
                  balance original_ac <> balance actual_ac).
                {
                  match goal with
                  | Hpre :
                      preTxState orig_state = Some original_ac,
                    Hmismatch :
                      try_fix_account_balance_mismatch
                        orig_state (Some actual_ac) |- _ =>
                      exact (try_fix_account_balance_mismatch_neq
                        orig_state actual_ac original_ac Hpre Hmismatch)
                  end.
                }
                go.
                iExists original_ac.
                go using optional_specs.trivial_optional_some_split_F,
                  AccountR_separated_unfold_F,
                  AccountR_separated_fold_B.
                iExists actual_ac.
                go using optional_specs.trivial_optional_some_split_F,
                  AccountR_separated_unfold_F,
                  AccountR_separated_fold_B.
                wp_if.
                {
                  intro Hrelaxed_false.
                  go.
                  iExists orig, cur.
                  unfold StateTryFixAccountMismatchR.
                  go using
                    account_option_layout_fold_B,
                    optionR_account_some_separated_fold_B,
                    AccountR_separated_fold_B.
                  go using
                    OriginalAccountStateR_separated_some_fold_B,
                    reinsert_map_payload_B.
                }
                {
                  go.
                  iExists orig_state.
                  go using
                    account_option_layout_fold_B,
                    optionR_account_some_separated_fold_B,
                    AccountR_separated_fold_B,
                    OriginalAccountStateR_separated_some_fold_B.
                  wp_if.
                  {
                    go.
                    iExists orig, cur.
                    unfold StateTryFixAccountMismatchR.
                    go using
                      account_option_layout_fold_B,
                      optionR_account_some_separated_fold_B,
                      AccountR_separated_fold_B.
                    go using reinsert_map_payload_B.
                  }
                  {
                    go.
                    match goal with
                    | H : is_Some
                            (min_balance (assumExactness orig_state)) |- _ =>
                        destruct H as [min_balance_bound Hmin_balance]
                    end.
                    go using
                      OriginalAccountStateR_separated_unfold_F,
                      type_ptr_reference_to_B_local.
                    iExists actual_ac.
                    go using
                      account_option_layout_fold_B,
                      optionR_account_some_separated_fold_B,
                      AccountR_separated_fold_B,
                      OriginalAccountStateR_separated_some_fold_B,
                      type_ptr_reference_to_B_local.
                    iExists orig_state.
                    rewrite Horiginal_ac.
                    go using
                      optionR_account_some_separated_unfold_F,
                      account_option_layout_unfold_F,
                      AccountR_separated_unfold_F,
                      OriginalAccountStateR_separated_some_fold_B,
                      type_ptr_reference_to_B_local.
                    iExists (1 : Qp), min_balance_bound.
                    go using
                      OriginalAccountStateR_separated_unfold_F,
                      type_ptr_reference_to_B_local.
                    rewrite Hmin_balance.
                    go.
                    wp_if.
                    {
                      go.
                      iExists orig, cur.
                      unfold StateTryFixAccountMismatchR.
                      go using
                        account_option_layout_fold_B,
                        optionR_account_some_separated_fold_B,
                        AccountR_separated_fold_B.
                      go using
                        OriginalAccountStateR_separated_fold_B,
                        reinsert_map_payload_B.
                      rewrite Hmin_balance.
                      go.
                    }
                    {
                      go.
                      destruct t.
                      {
                        match goal with
                        | |- context[
                            ?iterp |-> AnkerMapIterR
                              "monad::Address"
                              "monad::VersionStack<monad::AccountState>" false ?qi
                              ?cur_i ?spine] =>
                            rewrite (anker_iter_keep_type_ptr
                              iterp "monad::Address"
                              "monad::VersionStack<monad::AccountState>"
                              false cur_i spine)
                        end.
                        go using
                          (@map_model_iterR_snd_map_F
                            evm.address (list (ptr * UpdatedAccountState))),
                          (@map_model_iterR_end_map_B
                            evm.address (list (ptr * UpdatedAccountState))),
                          type_ptr_reference_to_B_local,
                          anker_iter_keep_type_ptr_C,
                          observeAnkerMapSpineTypePtrF,
                          observeAnkerMapSpineTypePtrRF,
                          observeAnkerIterFf,
                          observeAnkerIterRFf,
                          observeAnkerIterConstFf,
                          observeAnkerIterConstRFf,
                          observe_type_ptr_fwd,
                          observe_type_ptr_box_fwd,
                          type_ptr_elim_reference_to_C,
                          wp_initialize_unfold_B,
                          wp_init_mcall_minvoke_B,
                          wp_minvoke_direct_I_inline_C,
                          wp_minvoke_direct_I_unmaterialized_C,
                          wp_init_cast_noop_B.
                        iExists actual_ac.
                        go using
                          account_option_layout_fold_B,
                          optionR_account_some_separated_fold_B,
                          AccountR_separated_fold_B,
                          type_ptr_reference_to_B_local.
                        rewrite Horiginal_ac.
                        go using
                          optionR_account_some_separated_unfold_F,
                          account_option_layout_unfold_F,
                          AccountR_separated_unfold_F,
                          optionR_account_some_separated_fold_B,
                          account_option_layout_fold_B,
                          AccountR_separated_fold_B,
                          type_ptr_reference_to_B_local.
                        iExists (try_fix_account_balance_update
                          (Some actual_ac) orig_state).
                        unfold try_fix_account_balance_update.
                        rewrite Horiginal_ac.
                        cbn [preTxState preTxStorage assumExactness].
                        assert (Hactual_balance_bound :
                          (balance actual_ac < uint256_modulus)%N).
                        {
                          eapply account_balance_bound_from_core;
                            [eassumption|].
                          match goal with
                          | Hbound : w256_to_N _ < 2 ^ 256 |- _ =>
                              exact (lt_uint256_modulus_of_pow _ Hbound)
                          end.
                        }
                        rewrite (try_fix_account_balance_update_some
                          actual_ac original_ac orig_state Horiginal_ac).
                        go using
                          account_option_layout_fold_B,
                          AccountR_account_set_balance_fold_B,
                          optionR_account_some_separated_fold_B,
                          (OriginalAccountStateR_try_fix_account_balance_update_some_fold_B
                             (orig_loc ,, o_field CU
                               "std::pair<monad::Address, monad::OriginalAccountState>::second")
                             orig_state original_ac actual_ac transient_map
                             min_balance_bound Horiginal_ac Hmin_balance),
                          type_ptr_reference_to_B_local.
                        change
                          (update_assum_exactness_assumed
                             exact_balance_update
                             (try_fix_account_balance_update
                               (Some actual_ac) orig_state))
                          with
                          (try_fix_account_original_update
                             (Some actual_ac) orig_state).
                        go.
                        iExists
                          (try_fix_account_updated_orig_map
                            addr (Some actual_ac) orig), cur.
                        unfold StateTryFixAccountMismatchR.
                        go using
                          original_spine_try_fix_account_updated_orig_map_B,
                          reinsert_try_fix_account_updated_original_payload_B,
                          asplitB.
                        match goal with
                        | |- environments.envs_entails _ [| ?P |] =>
                            rewrite (only_provable_True P
                              ltac:(change
                                (try_fix_account_mismatch_ret_prop
                                  addr (Some actual_ac) orig cur true
                                  orig_loc orig_state true
                                  (try_fix_account_updated_orig_map
                                    addr (Some actual_ac) orig) cur);
                                eapply
                                  try_fix_account_mismatch_ret_prop_true_no_current;
                                eauto))
                        end.
                        go.
                      }
                      {
                        go.
                        go using
                          (@map_model_iterR_snd_map_F
                            evm.address (list (ptr * UpdatedAccountState))),
                          (@map_model_iterR_end_map_B
                            evm.address (list (ptr * UpdatedAccountState))),
                          type_ptr_reference_to_B_local,
                          anker_iter_keep_type_ptr_C,
                          observeAnkerMapSpineTypePtrF,
                          observeAnkerMapSpineTypePtrRF,
                          observeAnkerIterFf,
                          observeAnkerIterRFf,
                          observeAnkerIterConstFf,
                          observeAnkerIterConstRFf,
                          observe_type_ptr_fwd,
                          observe_type_ptr_box_fwd,
                          type_ptr_elim_reference_to_C,
                          wp_initialize_unfold_B,
                          wp_init_mcall_minvoke_B,
                          wp_minvoke_direct_I_inline_C,
                          wp_minvoke_direct_I_unmaterialized_C,
                          wp_init_cast_noop_B.
                        match goal with
                        | Hcur_spine :
                            option_map fst
                              (nth_error (map _ cur) (N.to_nat i)) =
                            Some addr |- _ =>
                            destruct (map_model_spine_lookup_ploc_exists
                              cur addr i Hcur_spine) as [cur_loc Hcur_loc]
                        end.
                        destruct (map_model_lookup_of_spine_lookup
                          cur addr i cur_loc)
                          as [updates Hcur_lookup].
                        {
                          match goal with
                          | Hnodup : NoDup (map fst (map _ cur)) |- _ =>
                              exact Hnodup
                          end.
                        }
                        {
                          match goal with
                          | Hcur_spine :
                              option_map fst
                                (nth_error (map _ cur) (N.to_nat i)) =
                              Some addr |- _ =>
                              exact Hcur_spine
                          end.
                        }
                        {
                          exact Hcur_loc.
                        }
                        assert (Hupdates_len : length updates = 1%nat).
                        {
                          match goal with
                          | Htop :
                              try_fix_account_current_top_level
                                (mapModelLookup cur addr) |- _ =>
                              unfold try_fix_account_current_top_level in Htop;
                              rewrite Hcur_lookup in Htop;
                              exact Htop
                          end.
                        }
                        destruct updates as [| [upd_loc upd] updates_tail].
                        {
                          discriminate Hupdates_len.
                        }
                        destruct updates_tail as [| [upd_loc' upd'] updates_tail'].
                        2: {
                          discriminate Hupdates_len.
                        }
                        cbn in Hupdates_len.
                        iExists cur_loc.
                        match goal with
                        | |- context[
                            ?iterp |-> AnkerMapIterR
                              "monad::Address"
                              "monad::VersionStack<monad::AccountState>" false ?qi
                              i ?spine] =>
                            rewrite (anker_iter_keep_pointee_type_ptr
                              iterp cur_loc
                              "monad::Address"
                              "monad::VersionStack<monad::AccountState>"
                              i spine Hcur_loc)
                        end.
                        go using
                          observeAnkerIterPointeeF,
                          type_ptr_reference_to_B_local,
                          anker_iter_keep_type_ptr_C,
                          anker_iter_keep_const_type_ptr_C,
                          anker_map_spine_keep_type_ptr_C,
                          observeAnkerMapSpineTypePtrF,
                          observeAnkerMapSpineTypePtrRF,
                          observeAnkerIterFf,
                          observeAnkerIterRFf,
                          observeAnkerIterConstFf,
                          observeAnkerIterConstRFf,
                          observe_type_ptr_fwd,
                          observe_type_ptr_box_fwd,
                          type_ptr_elim_reference_to_C,
                          wp_initialize_unfold_B,
                          wp_init_mcall_minvoke_B,
                          wp_minvoke_direct_I_inline_C,
                          wp_minvoke_direct_I_unmaterialized_C,
                          wp_init_cast_noop_B.
                        iExists [(upd_loc, upd)].
                        unfold VersionStackR.
                        iExists 1%Qp.
                        go using borrow_map_payload_F.
                        go using
                          AccountStateRcore_separated_unfold_F,
                          type_ptr_reference_to_B_local.
                        destruct (postTxState upd) as [recent_ac|] eqn:Hrecent.
                        2: {
                          change (~~ asbool (is_Some None)) with true.
                          go using
                            AccountStateRcore_separated_fold_B,
                            UpdatedAccountStateR_separated_fold_B,
                            OriginalAccountStateR_separated_some_fold_B,
                            reinsert_map_payload_B.
                          iExists orig, cur.
                          unfold StateTryFixAccountMismatchR.
                          rewrite Horiginal_ac.
                          unfold VersionStackR.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountStateRcore_separated_fold_B,
                            UpdatedAccountStateR_separated_none_fold_B,
                            (OriginalAccountStateR_separated_some_fold_B
                              (orig_loc ,, o_field CU
                                "std::pair<monad::Address, monad::OriginalAccountState>::second")
                              1%Qp orig_state original_ac _transient_map_1
                              Horiginal_ac),
                            reinsert_current_head_map_unfolded_B,
                            reinsert_map_payload_B,
                            asplitB.
                            rewrite Hmin_balance.
                            rewrite Hrecent.
                            go using
                              AccountStateRcore_some_fields_fold_B.
                        }
                        change (~~ asbool (is_Some (Some recent_ac))) with false.
                        go.
                        iExists actual_ac.
                        go using
                          account_option_layout_fold_B,
                          optionR_account_some_separated_fold_B,
                          AccountR_separated_fold_B,
                          type_ptr_reference_to_B_local.
                        rewrite Horiginal_ac.
                        go using
                          optional_specs.trivial_optional_some_split_F,
                          AccountR_separated_unfold_F,
                          account_option_layout_fold_B,
                          optionR_account_some_separated_fold_B,
                          AccountR_separated_fold_B,
                          type_ptr_reference_to_B_local.
                        go using u256_gt_spec.
                        wp_if.
                        {
                          go.
                          iExists actual_ac.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountR_separated_fold_B,
                            type_ptr_reference_to_B_local.
                          iExists original_ac.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountR_separated_fold_B,
                            type_ptr_reference_to_B_local.
                          go using u256_minus_spec,
                            optional_specs.trivial_optional_some_split_F,
                            AccountR_separated_unfold_F.
                          iExists recent_ac.
                          go using optional_specs.trivial_optional_some_split_F,
                            AccountR_separated_unfold_F,
                            AccountR_separated_fold_B.
                          wp_if.
                          {
                            go.
                            iExists orig, cur.
                            unfold StateTryFixAccountMismatchR.
                            unfold VersionStackR.
                            go using
                              account_option_layout_fold_B,
                              optionR_account_some_separated_fold_B,
                              AccountR_separated_fold_B,
                              AccountStateRcore_separated_fold_B,
                              UpdatedAccountStateR_separated_fold_B,
                              reinsert_current_head_map_unfolded_B.
                            go using
                              account_option_layout_fold_B,
                              optionR_account_some_separated_fold_B,
                              AccountR_separated_fold_B,
                              (OriginalAccountStateR_separated_some_fold_B
                                (orig_loc ,, o_field CU
                                  "std::pair<monad::Address, monad::OriginalAccountState>::second")
                                1%Qp orig_state original_ac _transient_map_1
                                Horiginal_ac),
                              reinsert_map_payload_B,
                            asplitB.
                            rewrite Hmin_balance.
                            rewrite Hrecent.
                            go using
                              AccountStateRcore_some_fields_fold_B.
                          }
                          {
                            go.
                            iExists recent_ac.
                            go using
                              account_option_layout_fold_B,
                              optionR_account_some_separated_fold_B,
                              AccountR_separated_fold_B,
                              type_ptr_reference_to_B_local.
                            go using u256_add_assign_spec,
                              optional_specs.trivial_optional_some_split_F,
                              AccountR_separated_unfold_F.
                            iExists actual_ac.
                            go using
                              account_option_layout_fold_B,
                              optionR_account_some_separated_fold_B,
                              AccountR_separated_fold_B,
                              type_ptr_reference_to_B_local.
                            iExists original_ac.
                            go using
                              account_option_layout_fold_B,
                              optionR_account_some_separated_fold_B,
                              AccountR_separated_fold_B,
                              type_ptr_reference_to_B_local.
                            go using u256_assign_spec,
                              optional_specs.trivial_optional_some_split_F,
                              AccountR_separated_unfold_F.
                            iExists (try_fix_account_balance_update
                              (Some actual_ac) orig_state).
                            assert (Hactual_balance_bound :
                              (balance actual_ac < uint256_modulus)%N).
                            {
                              eapply account_balance_bound_from_core;
                                [eassumption|].
                              match goal with
                              | Hbound : w256_to_N _ < 2 ^ 256 |- _ =>
                                  exact (lt_uint256_modulus_of_pow _ Hbound)
                              end.
                            }
                            go using
                              account_option_layout_fold_B,
                              AccountR_account_set_balance_fold_B,
                              optionR_account_some_separated_fold_B,
                              (OriginalAccountStateR_try_fix_account_balance_update_some_fold_B
                                 (orig_loc ,, o_field CU
                                   "std::pair<monad::Address, monad::OriginalAccountState>::second")
                                 orig_state original_ac actual_ac
                                 _transient_map_1 min_balance_bound
                                 Horiginal_ac Hmin_balance),
                              type_ptr_reference_to_B_local.
                            change
                              (update_assum_exactness_assumed
                                 exact_balance_update
                                 (try_fix_account_balance_update
                                   (Some actual_ac) orig_state))
                              with
                              (try_fix_account_original_update
                                 (Some actual_ac) orig_state).
                            match goal with
                            | Hlt : ?orig_raw < ?actual_raw,
                              Hrecent_bal :
                                balance recent_ac = ?recent_raw,
                              Hactual_bal :
                                balance actual_ac = ?actual_raw,
                              Horig_bal :
                                balance original_ac = ?orig_raw |- _ =>
                                assert (Hactual_raw_bound :
                                  (actual_raw < uint256_modulus)%N) by
                                  (rewrite <- Hactual_bal;
                                   exact Hactual_balance_bound);
                                rewrite (add_delta_mod_of_u256_sub_twopower
                                  recent_raw actual_raw orig_raw
                                  Hlt Hactual_raw_bound);
                                rewrite <- Hrecent_bal;
                                rewrite <- Hactual_bal;
                                rewrite <- Horig_bal;
                                rewrite <- Horig_bal in Hlt;
                                rewrite <- Hactual_bal in Hlt
                            end.
                            go using
                              UpdatedAccountStateR_try_fix_current_update_add_fold_B.
                            iExists
                              (try_fix_account_updated_orig_map
                                addr (Some actual_ac) orig),
                              (try_fix_account_updated_cur_map
                                addr actual_ac original_ac cur).
                            unfold StateTryFixAccountMismatchR.
                            unfold VersionStackR.
                            go using
                              account_option_layout_fold_B,
                              optionR_account_some_separated_fold_B,
                              AccountR_separated_fold_B,
                              original_spine_try_fix_account_updated_orig_map_B,
                              reinsert_try_fix_account_updated_original_payload_B,
                              current_spine_try_fix_account_updated_cur_map_B,
                              UpdatedAccountStateR_try_fix_current_update_add_fold_B,
                              reinsert_try_fix_account_updated_current_payload_unfolded_B,
                              asplitB.
                            unfold try_fix_account_current_update.
                            rewrite Hrecent.
                            replace
                              (asbool
                                (balance original_ac < balance actual_ac)%N)
                              with true by
                              (symmetry; apply bool_decide_eq_true_2;
                               match goal with
                               | Hlt :
                                   context
                                     [balance original_ac <
                                      balance actual_ac] |- _ =>
                                   exact Hlt
                               end).
                            cbn [postTxState substateModel].
                            wapply
                              (StorageMapR_account_set_balance
                                 (upd_loc ,, o_field CU
                                   "monad::AccountState::storage_")
                                 1 recent_ac
                                 ((balance recent_ac +
                                   (balance actual_ac -
                                    balance original_ac)) mod
                                  uint256_word_modulus)).
                              go using
                                account_option_layout_fold_B,
                                optionR_account_some_separated_fold_B,
                                AccountR_account_set_balance_mod_fold_B,
                                AccountStateRcore_separated_fold_B.
                              match goal with
                              | |- environments.envs_entails _ [| ?P |] =>
                                  rewrite (only_provable_True P
                                    ltac:(change
                                      (try_fix_account_mismatch_ret_prop
                                        addr (Some actual_ac) orig cur true
                                        orig_loc orig_state true
                                        (try_fix_account_updated_orig_map
                                          addr (Some actual_ac) orig)
                                        (try_fix_account_updated_cur_map
                                          addr actual_ac original_ac cur));
                                      eapply
                                        try_fix_account_mismatch_ret_prop_true_current_add;
                                      eauto))
                              end.
                              go.
                            }
                        }
                        {
                          go.
                          iExists original_ac.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountR_separated_fold_B,
                            type_ptr_reference_to_B_local.
                          iExists actual_ac.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountR_separated_fold_B,
                            type_ptr_reference_to_B_local.
                          go using u256_minus_spec,
                            optional_specs.trivial_optional_some_split_F,
                            AccountR_separated_unfold_F.
                          assert (Hactual_lt_original :
                            (balance actual_ac < balance original_ac)%N).
                          {
                            match goal with
                            | Hle : ?actual_raw <= ?orig_raw,
                              Hactual_bal :
                                balance actual_ac = ?actual_raw,
                              Horig_bal :
                                balance original_ac = ?orig_raw,
                              Hneq :
                                balance original_ac <>
                                balance actual_ac |- _ =>
                                rewrite Hactual_bal;
                                rewrite Horig_bal;
                                lia
                            end.
                          }
                          assert (Horig_balance_bound :
                            (balance original_ac < uint256_modulus)%N).
                          {
                            eapply account_balance_bound_from_core;
                              [eassumption|].
                            match goal with
                            | Hbound : w256_to_N _ < 2 ^ 256 |- _ =>
                                exact (lt_uint256_modulus_of_pow _ Hbound)
                            end.
                          }
                          assert (Hrecent_covers_delta :
                            (balance original_ac - balance actual_ac <=
                             balance recent_ac)%N).
                          {
                            eauto with pure.
                          }
                          iExists recent_ac.
                          go using optional_specs.trivial_optional_some_split_F,
                            AccountR_separated_unfold_F,
                            AccountR_separated_fold_B.
                          iExists recent_ac.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountR_separated_fold_B,
                            type_ptr_reference_to_B_local.
                          go using u256_sub_assign_spec,
                            optional_specs.trivial_optional_some_split_F,
                            AccountR_separated_unfold_F.
                          iExists actual_ac.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountR_separated_fold_B,
                            type_ptr_reference_to_B_local.
                          iExists original_ac.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountR_separated_fold_B,
                            type_ptr_reference_to_B_local.
                          go using u256_assign_spec,
                            optional_specs.trivial_optional_some_split_F,
                            AccountR_separated_unfold_F.
                          iExists (try_fix_account_balance_update
                            (Some actual_ac) orig_state).
                          assert (Hactual_balance_bound :
                            (balance actual_ac < uint256_modulus)%N).
                          {
                            eapply account_balance_bound_from_core;
                              [eassumption|].
                            match goal with
                            | Hbound : w256_to_N _ < 2 ^ 256 |- _ =>
                                exact (lt_uint256_modulus_of_pow _ Hbound)
                            end.
                          }
                          go using
                            account_option_layout_fold_B,
                            AccountR_account_set_balance_fold_B,
                            optionR_account_some_separated_fold_B,
                            (OriginalAccountStateR_try_fix_account_balance_update_some_fold_B
                               (orig_loc ,, o_field CU
                                 "std::pair<monad::Address, monad::OriginalAccountState>::second")
                               orig_state original_ac actual_ac
                               _transient_map_1 min_balance_bound
                               Horiginal_ac Hmin_balance),
                            type_ptr_reference_to_B_local.
                          change
                            (update_assum_exactness_assumed
                               exact_balance_update
                               (try_fix_account_balance_update
                                 (Some actual_ac) orig_state))
                            with
                            (try_fix_account_original_update
                               (Some actual_ac) orig_state).
                          repeat match goal with
                          | Hbal : balance recent_ac = _ |-
                              context
                                [w256_to_N
                                  (block.block_account_balance
                                     (coreAc recent_ac))] =>
                              rewrite <- Hbal
                          | Hbal : balance original_ac = _ |-
                              context
                                [w256_to_N
                                  (block.block_account_balance
                                     (coreAc original_ac))] =>
                              rewrite <- Hbal
                          | Hbal : balance actual_ac = _ |-
                              context
                                [w256_to_N
                                  (block.block_account_balance
                                     (coreAc actual_ac))] =>
                              rewrite <- Hbal
                          end.
                          rewrite
                            (sub_assign_delta_of_u256_sub_twopower
                               (balance recent_ac)
                               (balance original_ac)
                               (balance actual_ac)
                               Hactual_lt_original
                               Horig_balance_bound).
                          go using
                            UpdatedAccountStateR_try_fix_current_update_sub_fold_B.
                          iExists
                            (try_fix_account_updated_orig_map
                              addr (Some actual_ac) orig),
                            (try_fix_account_updated_cur_map
                              addr actual_ac original_ac cur).
                          unfold StateTryFixAccountMismatchR.
                          unfold VersionStackR.
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                            AccountR_separated_fold_B,
                            original_spine_try_fix_account_updated_orig_map_B,
                            reinsert_try_fix_account_updated_original_payload_B,
                            current_spine_try_fix_account_updated_cur_map_B,
                            UpdatedAccountStateR_try_fix_current_update_sub_fold_B,
                            reinsert_try_fix_account_updated_current_payload_unfolded_B,
                            asplitB.
                          unfold try_fix_account_current_update.
                          rewrite Hrecent.
                          replace
                            (asbool
                              (balance original_ac < balance actual_ac)%N)
                            with false by
                            (symmetry; apply bool_decide_false; lia).
                          cbn [postTxState substateModel].
                          wapply
                            (StorageMapR_account_set_balance
                               (upd_loc ,, o_field CU
                                 "monad::AccountState::storage_")
                               1 recent_ac
                               (Z.to_N
                                  ((Z.of_N (balance recent_ac) -
                                    Z.of_N
                                      (balance original_ac -
                                       balance actual_ac)) mod
                                   Z.of_N uint256_modulus)%Z)).
                          go using
                            account_option_layout_fold_B,
                            optionR_account_some_separated_fold_B,
                              (AccountR_account_set_balance_zmod_fold_B
                                 (upd_loc ,, o_field CU
                                   "monad::AccountState::account_"
                                  ,, optional_specs.value_offset
                                       "monad::Account"%cpp_type)
                                 recent_ac
                                 (Z.of_N (balance recent_ac) -
                                  Z.of_N
                                    (balance original_ac -
                                     balance actual_ac))%Z),
                              AccountStateRcore_separated_fold_B.
                            match goal with
                            | |- environments.envs_entails _ [| ?P |] =>
                                rewrite (only_provable_True P
                                  ltac:(change
                                    (try_fix_account_mismatch_ret_prop
                                      addr (Some actual_ac) orig cur true
                                      orig_loc orig_state true
                                      (try_fix_account_updated_orig_map
                                        addr (Some actual_ac) orig)
                                      (try_fix_account_updated_cur_map
                                        addr actual_ac original_ac cur));
                                    eapply
                                      try_fix_account_mismatch_ret_prop_true_current_sub;
                                    eauto with pure;
                                    try match goal with
                                    | Hbal :
                                        balance recent_ac =
                                        w256_to_N
                                          (block.block_account_balance
                                             (coreAc recent_ac)),
                                      Hbound :
                                        w256_to_N
                                          (block.block_account_balance
                                             (coreAc recent_ac)) <
                                        2 ^ 256
                                      |- balance recent_ac <
                                         uint256_modulus =>
                                        rewrite Hbal;
                                        exact
                                          (lt_uint256_modulus_of_pow
                                             _ Hbound)
                                    end))
                            end.
                            go.
                          }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  Qed.
  *)
End with_Sigma.
