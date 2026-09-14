Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import skylabs.brick.libstdcpp.algorithms.spec.
Require Import skylabs.brick.libstdcpp.new.spec_exc.

Require Import skylabs.auto.cpp.prelude.test.

Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import skylabs.lang.cpp.cpp.
Require Import stdpp.gmap.
Require Import stdpp.fin_maps.
Require Import stdpp.fin_map_dom.
Require Import monad.proofs.misc.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.cpp.spec.
From AAC_tactics Require Import AAC.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import skylabs.prelude.list_numbers.
Import cQp_compat.
Set Default Goal Selector "!".
Set Warnings "+sl-impossible-patterns".
#[local] Open Scope lens_scope.

Local Transparent isSC isAcSC.
#[local] Arguments Lens.set : simpl never.
#[local] Arguments Lens.over : simpl never.
#[local] Arguments lens_compose : simpl never.

Lemma N_le_ZtoN_of_Zle (n: N) (z: Z) :
  (0 <= z)%Z ->
  (Z.of_N n <= z)%Z ->
  (n <= Z.to_N z)%N.
Proof using.
  intros Hz Hle.
  apply N2Z.inj_le.
  rewrite (Z2N.id z Hz).
  exact Hle.
Qed.

Lemma balance_update_balance (ac: AccountM) (bal: N) :
  balance (ac &: _balance .= bal) = bal.
Proof using.
  destruct ac as [coreAc inc rel del bal0].
  unfold Lens.set, lens_compose; simpl.
  destruct coreAc; simpl; reflexivity.
Qed.

Lemma balance_update_nonce (ac: AccountM) (nonce: Z) :
  balance (ac &: _nonce .= nonce) = balance ac.
Proof using.
  destruct ac as [coreAc inc rel del bal0].
  unfold Lens.set, lens_compose; simpl.
  destruct coreAc; simpl; reflexivity.
Qed.

Lemma balance_update_storage (ac: AccountM) (st: evm.storage) :
  balance (ac &: _coreAc .@ _block_account_storage .= st) = balance ac.
Proof using.
  destruct ac as [coreAc inc rel del bal0].
  unfold Lens.set, lens_compose; simpl.
  destruct coreAc; simpl; reflexivity.
Qed.

(* validModel after updating assumption exactness, given a local bound for the updated exactness. *)

Lemma code_entries_of_preTxAssumed_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness) :
  code_entries_of_preTxAssumed (update_assum_exactness_map m updates) =
  code_entries_of_preTxAssumed m.
Proof using.
  induction m as [|[addr [loc aps]] tl IH]; simpl; [reflexivity|].
  unfold code_entry_of_assumed.
  destruct (updates !! addr) as [ex|] eqn:Hupd; simpl;
    destruct (preTxState aps) as [am|] eqn:Hpre; simpl;
    rewrite IH; reflexivity.
Qed.

Lemma codeMapOfPreTxAssumedAccounts_update_assum_exactness_state
    (st: StateM) (updates: gmap evm.address AssumptionExactness) :
  codeMapOfPreTxAssumedAccounts (update_assum_exactness_state st updates) =
  codeMapOfPreTxAssumedAccounts st.
Proof using.
  unfold codeMapOfPreTxAssumedAccounts, update_assum_exactness_state; simpl.
  rewrite code_entries_of_preTxAssumed_update_assum_exactness_map.
  reflexivity.
Qed.

Lemma codeMapOfNewStates_update_assum_exactness_state
    (st: StateM) (updates: gmap evm.address AssumptionExactness) :
  codeMapOfNewStates (update_assum_exactness_state st updates) =
  codeMapOfNewStates st.
Proof using.
  unfold codeMapOfNewStates, update_assum_exactness_state; simpl.
  reflexivity.
Qed.

Lemma all_code_entries_update_assum_exactness_state
    (st: StateM) (updates: gmap evm.address AssumptionExactness) :
  all_code_entries (update_assum_exactness_state st updates) =
  all_code_entries st.
Proof using.
  unfold all_code_entries, update_assum_exactness_state; simpl.
  rewrite codeMapOfPreTxAssumedAccounts_update_assum_exactness_state.
  reflexivity.
Qed.

Lemma min_balance_stricter_refl (old: option N) :
  min_balance_stricter old old.
Proof using.
  destruct old; simpl; [apply N.le_refl|reflexivity].
Qed.

Lemma min_balance_stricter_trans (old mid new: option N) :
  min_balance_stricter old mid ->
  min_balance_stricter mid new ->
  min_balance_stricter old new.
Proof using.
  destruct old as [m|], mid as [m1|], new as [m2|]; simpl; try tauto.
  - intros H1 H2. eapply N.le_trans; eauto.
Qed.

Lemma assumption_exactness_stricter_refl (old: AssumptionExactness) :
  assumption_exactness_stricter old old.
Proof using.
  unfold assumption_exactness_stricter.
  split; [apply min_balance_stricter_refl|tauto].
Qed.

Lemma assumption_exactness_stricter_trans
    (old mid new: AssumptionExactness) :
  assumption_exactness_stricter old mid ->
  assumption_exactness_stricter mid new ->
  assumption_exactness_stricter old new.
Proof using.
  unfold assumption_exactness_stricter.
  intros [Hmin1 Hnonce1] [Hmin2 Hnonce2].
  split.
  - eapply min_balance_stricter_trans; eauto.
  - intros Hold. apply Hnonce2, Hnonce1, Hold.
Qed.

Lemma assumption_exactness_stricter_min_balance_update
    (old: AssumptionExactness) (orig cur debit: N) :
  assumption_exactness_stricter old (min_balance_update old orig cur debit).
Proof using.
  unfold min_balance_update.
  destruct old as [mb ne]; simpl.
  destruct (check_min_balance_ok cur debit) eqn:Hok; simpl.
  - destruct mb as [old_min|]; simpl.
    + split.
      * destruct (N.ltb (N.sub cur debit) orig) eqn:Hlt; simpl.
        -- apply N.le_max_l.
        -- apply N.le_refl.
      * tauto.
    + split; [apply min_balance_stricter_refl|tauto].
  - split; [destruct mb; simpl; [tauto|reflexivity]|tauto].
Qed.

Lemma min_balance_update_lower_bound
    (old: AssumptionExactness) (orig cur debit: N) :
  check_min_balance_ok cur debit = true ->
  match min_balance (min_balance_update old orig cur debit) with
  | Some m => (N.sub orig (N.sub cur debit) <= m)%N
  | None => True
  end.
Proof using.
  intro Hok.
  unfold min_balance_update.
  rewrite Hok.
  destruct old as [mb ne]; simpl.
  destruct mb as [old_min|]; simpl; [|exact I].
  set (diff := N.sub cur debit).
  destruct (N.ltb diff orig) eqn:Hltb.
  - apply N.le_max_r.
  - assert (Hge : (orig <= diff)%N).
    { apply (proj1 (N.ltb_ge diff orig)). exact Hltb. }
    assert (Hsub0 : (orig - diff)%N = 0%N).
    { apply (proj2 (N.sub_0_le orig diff)). exact Hge. }
    rewrite Hsub0. apply N.le_0_l.
Qed.

Lemma assumption_exactness_stricter_min_balance_update_twice
    (old: AssumptionExactness)
    (orig1 cur1 debit1 orig2 cur2 debit2: N) :
  assumption_exactness_stricter old
    (min_balance_update
       (min_balance_update old orig1 cur1 debit1)
       orig2 cur2 debit2).
Proof using.
  eapply assumption_exactness_stricter_trans.
  - apply assumption_exactness_stricter_min_balance_update.
  - apply assumption_exactness_stricter_min_balance_update.
Qed.

Lemma satAccountNonStorageAssumptions_stricter
    (relaxed: bool) (au: TxAssumptionsAndUpdates) (ex: AssumptionExactness)
    (actual: option AccountM) :
  assumption_exactness_stricter (assumExactness (preAssumption au)) ex ->
  (min_balance ex = None -> min_balance (assumExactness (preAssumption au)) = None) ->
  satAccountNonStorageAssumptions relaxed
    (Some (update_assum_exactness_assumed (fun _ => ex) (preAssumption au))) actual ->
  satAccountNonStorageAssumptions relaxed (Some (preAssumption au)) actual.
Proof using.
  intros Hstr Hmb Hsat.
  unfold satAccountNonStorageAssumptions in *; simpl in *.
  destruct (preTxState (preAssumption au)) as [cs|] eqn:Hpre;
    destruct actual as [csActual|]; simpl in *.
  { destruct Hstr as [Hmin Hnonce].
    destruct relaxed; cbn in *.
    { destruct Hsat as [Hbal Hnonce_sat].
      change (min_balance ex) with
        (min_balance (assumExactness
                        (update_assum_exactness_assumed (fun _ => ex) (preAssumption au))))
        in Hbal.
      split.
      { destruct (min_balance (assumExactness (preAssumption au))) as [mold|] eqn:Hold.
        { destruct (min_balance ex) as [mnew|] eqn:Hnew.
          { simpl in Hmin.
            unfold min_balanceN in Hbal.
            rewrite Hnew in Hbal. simpl in Hbal.
            unfold min_balanceN.
            rewrite Hold.
            simpl.
            eapply N.le_trans; [exact Hmin|exact Hbal]. }
          { exfalso. specialize (Hmb eq_refl). discriminate. } }
        { destruct (min_balance ex) as [mnew|] eqn:Hnew.
          { simpl in Hmin. contradiction. }
          { rewrite Hnew in Hbal. simpl in Hbal. exact Hbal. } } }
      { destruct (nonce_exact (assumExactness (preAssumption au))) eqn:Hnonce_old; simpl in *.
        { specialize (Hnonce eq_refl). rewrite Hnonce in Hnonce_sat. exact Hnonce_sat. }
        { exact I. } } }
    { destruct Hsat as [[Hbal_exact Hbal_min] Hnonce_sat].
      split.
      { split.
        { exact Hbal_exact. }
        { destruct (min_balance (assumExactness (preAssumption au))) as [mold|] eqn:Hold.
          { destruct (min_balance ex) as [mnew|] eqn:Hnew.
            { simpl in Hmin.
              unfold min_balanceN in Hbal_min.
              rewrite Hnew in Hbal_min. simpl in Hbal_min.
              unfold min_balanceN.
              rewrite Hold.
              simpl.
              eapply N.le_trans; [exact Hmin|exact Hbal_min]. }
            { exfalso. specialize (Hmb eq_refl). discriminate. } }
          { exact I. } } }
      { exact Hnonce_sat. } } }
  { exact Hsat. }
  { exact Hsat. }
  { exact I. }
Qed.

Lemma satAccountNonStorageAssumptions_stricter_bound
    (relaxed: bool) (au: TxAssumptionsAndUpdates) (ex: AssumptionExactness)
    (actual: option AccountM) :
  assumption_exactness_stricter (assumExactness (preAssumption au)) ex ->
  (match preTxState (preAssumption au) with
   | Some cs =>
       if isSome (min_balance (assumExactness (preAssumption au)))
       then (min_balanceN (assumExactness (preAssumption au)) <= cs .^ _balance)%N
       else True
   | None => True
   end) ->
  satAccountNonStorageAssumptions relaxed
    (Some (update_assum_exactness_assumed (fun _ => ex) (preAssumption au))) actual ->
  satAccountNonStorageAssumptions relaxed (Some (preAssumption au)) actual.
Proof using.
  intros Hstr Hbound Hsat.
  unfold satAccountNonStorageAssumptions in *; simpl in *.
  destruct (preTxState (preAssumption au)) as [cs|] eqn:Hpre;
    destruct actual as [csActual|]; simpl in *.
  { destruct Hstr as [Hmin Hnonce].
    destruct relaxed; cbn in *.
    { destruct Hsat as [Hbal Hnonce_sat].
      change (min_balance ex) with
        (min_balance (assumExactness
                        (update_assum_exactness_assumed (fun _ => ex) (preAssumption au))))
        in Hbal.
      split.
      { destruct (min_balance (assumExactness (preAssumption au))) as [mold|] eqn:Hold.
        { simpl in Hbound.
          destruct (min_balance ex) as [mnew|] eqn:Hnew.
          { simpl in Hmin.
            unfold min_balanceN in Hbal.
            rewrite Hnew in Hbal. simpl in Hbal.
            unfold min_balanceN.
            rewrite Hold.
            simpl.
            eapply N.le_trans; [exact Hmin|exact Hbal]. }
          { rewrite Hnew in Hbal. simpl in Hbal.
            rewrite Hbal in Hbound.
            exact Hbound. } }
        { destruct (min_balance ex) as [mnew|] eqn:Hnew.
          { simpl in Hmin. contradiction. }
          { rewrite Hnew in Hbal. simpl in Hbal. exact Hbal. } } }
      { destruct (nonce_exact (assumExactness (preAssumption au))) eqn:Hnonce_old; simpl in *.
        { specialize (Hnonce eq_refl). rewrite Hnonce in Hnonce_sat. exact Hnonce_sat. }
        { exact I. } } }
    { destruct Hsat as [[Hbal_exact Hbal_min] Hnonce_sat].
      split.
      { split.
        { exact Hbal_exact. }
        { destruct (min_balance (assumExactness (preAssumption au))) as [mold|] eqn:Hold.
          { simpl in Hbound.
            destruct (min_balance ex) as [mnew|] eqn:Hnew.
            { simpl in Hmin.
              unfold min_balanceN in Hbal_min.
              rewrite Hnew in Hbal_min. simpl in Hbal_min.
              unfold min_balanceN.
              rewrite Hold.
              simpl.
              eapply N.le_trans; [exact Hmin|exact Hbal_min]. }
            { rewrite <- Hbal_exact.
              exact Hbound. } }
          { exact I. } } }
      { exact Hnonce_sat. } } }
  { exact Hsat. }
  { exact Hsat. }
  { exact I. }
Qed.

Lemma satAccountAssumptions_stricter
    (relaxed: bool) (au: TxAssumptionsAndUpdates) (ex: AssumptionExactness)
    (actual: option AccountM) :
  assumption_exactness_stricter (assumExactness (preAssumption au)) ex ->
  (min_balance ex = None -> min_balance (assumExactness (preAssumption au)) = None) ->
  satAccountAssumptions relaxed
    (Some (update_assum_exactness_assumed (fun _ => ex) (preAssumption au))) actual ->
  satAccountAssumptions relaxed (Some (preAssumption au)) actual.
Proof using.
  intros Hstr Hmb [Hnon Hstor]. split.
  - eapply satAccountNonStorageAssumptions_stricter; eauto.
  - unfold satAccountStrageAssumptions in *; simpl in *; exact Hstor.
Qed.

Lemma mapModelLookup_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) :
  mapModelLookup (update_assum_exactness_map m updates) addr =
  match mapModelLookup m addr with
  | Some (loc, aps0) =>
      let aps :=
        match updates !! addr with
        | Some ex =>
            {| preTxState := preTxState aps0;
               preTxStorage := preTxStorage aps0;
               assumExactness := ex |}
        | None => aps0
        end in
      Some (loc, aps)
  | None => None
  end.
Proof using.
  induction m as [|[addr0 [loc0 aps0]] tl IH]; simpl.
  - reflexivity.
  - unfold mapModelLookup in *.
    cbn [update_assum_exactness_map list_to_map].
    destruct (decide (addr = addr0)) as [Heq|Hneq].
    + subst addr.
      destruct (updates !! addr0) as [ex|] eqn:Hupd; simpl;
        repeat rewrite lookup_insert;
        repeat match goal with
        | |- context[decide (?x = ?x)] =>
            destruct (decide (x = x)) as [_|Hfalse];
            [|contradiction Hfalse; reflexivity]
        end;
        reflexivity.
    + destruct (updates !! addr0) as [ex|] eqn:Hupd; simpl.
      * rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
        rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
        exact IH.
      * rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
        rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
        exact IH.
Qed.

Lemma mapModelLookup_update_assum_exactness_map_Some
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (loc: ptr) (aps: AssumedPreTxAccountState) :
  mapModelLookup (update_assum_exactness_map m updates) addr = Some (loc, aps) ->
  exists aps0,
    mapModelLookup m addr = Some (loc, aps0)
    /\ preTxState aps = preTxState aps0
    /\ preTxStorage aps = preTxStorage aps0
    /\ assumExactness aps =
         match updates !! addr with
         | Some ex => ex
         | None => assumExactness aps0
         end.
Proof using.
  intro Hlookup.
  rewrite mapModelLookup_update_assum_exactness_map in Hlookup.
  destruct (mapModelLookup m addr) as [[loc0 aps0]|] eqn:Horig.
  - simpl in Hlookup.
    destruct (updates !! addr) as [ex|] eqn:Hupd; inversion Hlookup; subst.
    + eexists. split; [first [exact Horig | reflexivity]|].
      repeat split; reflexivity.
    + eexists. split; [first [exact Horig | reflexivity]|].
      repeat split; reflexivity.
  - discriminate.
Qed.

Lemma updates_stricter_insert
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (loc: ptr) (aps: AssumedPreTxAccountState)
    (orig1 cur1 debit1 orig2 cur2 debit2: N) :
  updates_stricter st updates ->
  mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr =
    Some (loc, aps) ->
  updates_stricter st
    (<[addr :=
         min_balance_update
           (min_balance_update (assumExactness aps) orig1 cur1 debit1)
           orig2 cur2 debit2]> updates).
Proof using.
  unfold updates_stricter.
	  intros Hupd Hlookup addr' ex' Hlookup'.
	  destruct (decide (addr' = addr)) as [->|Hneq].
	  - rewrite lookup_insert in Hlookup'.
	    destruct (decide (addr = addr)) as [_|Haddr_neq];
	      [|contradiction Haddr_neq; reflexivity].
	    inversion Hlookup'; subst.
    pose proof (mapModelLookup_update_assum_exactness_map_Some
      (preTxAssumedState st) updates addr loc aps Hlookup) as
        (aps0 & Hpre & _Hpretx & _Hprestorage & Hassum).
    destruct (updates !! addr) as [ex0|] eqn:Hupd_lookup.
    + destruct (Hupd _ _ Hupd_lookup) as (loc0 & aps1 & Hpre1 & Hstr1).
      change (mapModelLookup (preTxAssumedState st) addr = Some (loc0, aps1)) in Hpre1.
      rewrite Hpre in Hpre1. inversion Hpre1; subst loc0 aps1.
      simpl in Hassum.
      (* ex0 is the old exactness, aps has the updated exactness. *)
	      assert (Hstr2 :
	                assumption_exactness_stricter ex0
	                  (min_balance_update
	                     (min_balance_update ex0 orig1 cur1 debit1)
	                     orig2 cur2 debit2)).
	      { apply assumption_exactness_stricter_min_balance_update_twice. }
	      assert (Hstr2' :
	                assumption_exactness_stricter ex0
	                  (min_balance_update
	                     (min_balance_update (assumExactness aps) orig1 cur1 debit1)
	                     orig2 cur2 debit2)).
	      { rewrite Hassum. exact Hstr2. }
	      exists loc, aps0. split; [exact Hpre|].
	      eapply assumption_exactness_stricter_trans; [exact Hstr1|exact Hstr2'].
    + simpl in Hassum.
      exists loc, aps0. split; [exact Hpre|].
      rewrite Hassum.
      apply assumption_exactness_stricter_min_balance_update_twice.
  - rewrite lookup_insert_ne in Hlookup';
      [|intro Heq; apply Hneq; symmetry; exact Heq].
    eapply Hupd; eauto.
Qed.

Lemma stateCodeMapInvariants_update_assum_exactness_state_insert
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness) :
  stateCodeMapInvariants (update_assum_exactness_state st updates) ->
  stateCodeMapInvariants (update_assum_exactness_state st (<[addr := ex]> updates)).
Proof using.
  intro Hinv.
  unfold stateCodeMapInvariants, update_assum_exactness_state in *; simpl in *.
  rewrite (codeMapOfNewStates_update_assum_exactness_state st updates) in Hinv.
  rewrite (all_code_entries_update_assum_exactness_state st updates) in Hinv.
  rewrite (codeMapOfPreTxAssumedAccounts_update_assum_exactness_state st updates) in Hinv.
  rewrite (codeMapOfNewStates_update_assum_exactness_state st (<[addr := ex]> updates)).
  rewrite (all_code_entries_update_assum_exactness_state st (<[addr := ex]> updates)).
  rewrite (codeMapOfPreTxAssumedAccounts_update_assum_exactness_state st (<[addr := ex]> updates)).
  exact Hinv.
Qed.

Lemma takeN_S_r2 {T} (x: T) xs n :
  nth_error xs (N.to_nat n) = Some x ->
  takeN (1 + n) xs = takeN n xs ++ [x].
Proof using.
  intros Hnth.
  rewrite (comm N.add).
  apply takeN_S_r.
  unfold lookup, list_lookupN; simpl.
  rewrite lookup_nth_error.
  exact Hnth.
Qed.

Lemma gdom_insert_subset_takeN_succ
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness)
    (i: N) (loc: ptr) (tl: list (ptr * UpdatedAccountState)) :
  gdom updates ⊆ map fst (takeN i (newStates st)) ->
  nth_error (newStates st) (N.to_nat i) = Some (addr, (loc, tl)) ->
  gdom (<[addr := ex]> updates) ⊆ map fst (takeN (1 + i) (newStates st)).
Proof using.
  intros Hsub Hnth k Hk.
  unfold gdom in Hk.
  apply list_elem_of_fmap_1 in Hk as [[k' v'] [Hkv Hmem]].
  simpl in Hkv; subst k'.
  apply elem_of_map_to_list in Hmem.
  apply lookup_insert_Some in Hmem as [Haddr|[Hneq Hlookup]].
  - destruct Haddr as [Hkaddr _].
    subst k.
    assert (Htake : takeN (1 + i) (newStates st) =
                    takeN i (newStates st) ++ [(addr, (loc, tl))]).
    { apply takeN_S_r2. exact Hnth. }
    rewrite Htake.
    rewrite map_app.
    apply elem_of_app; right.
    simpl; left; reflexivity.
  - assert (Hkdom : k ∈ gdom updates).
    { unfold gdom.
      apply (proj2 (list_elem_of_fmap _ _ _)).
      exists (k, v'); split; [reflexivity|].
      apply elem_of_map_to_list.
      exact Hlookup.
    }
    specialize (Hsub _ Hkdom).
    assert (Htake : takeN (1 + i) (newStates st) =
                    takeN i (newStates st) ++ [(addr, (loc, tl))]).
    { apply takeN_S_r2. exact Hnth. }
    rewrite Htake.
    rewrite map_app.
    apply elem_of_app; left; exact Hsub.
Qed.

Lemma allFinalBalSufficient_takeN_succ
    (st: StateM) (ctx: MonadChainContext) (hist: ExtraAcStates) (tx: TxWithHdr)
    (i: N) (addr: evm.address) (loc: ptr)
    (tl: list (ptr * UpdatedAccountState)) :
  (forall preTxState : StateOfAccounts,
      satisfiesAssumptions st preTxState ->
      true =
        allFinalBalSufficient 3 (preTxState, hist) (applyUpdates st preTxState)
          (map fst (takeN i (newStates st))) tx) ->
  nth_error (newStates st) (N.to_nat i) =
    Some (addr, (loc, tl)) ->
  (forall preTxState : StateOfAccounts,
      satisfiesAssumptions st preTxState ->
      finalBalSufficient 3 (preTxState, hist) (applyUpdates st preTxState) tx addr = true) ->
  forall preTxState : StateOfAccounts,
    satisfiesAssumptions st preTxState ->
    true =
      allFinalBalSufficient 3 (preTxState, hist) (applyUpdates st preTxState)
        (map fst (takeN (1 + i) (newStates st))) tx.
Proof using.
  intros Hprev Hnth Hone preTxState Hsat.
  specialize (Hprev preTxState Hsat).
  specialize (Hone preTxState Hsat).
  unfold allFinalBalSufficient in *.
  pose proof (takeN_S_r2 (addr, (loc, tl)) (newStates st) i Hnth) as Htake.
  assert (Htake_map :
            map fst (takeN (1 + i) (newStates st)) =
            map fst (takeN i (newStates st) ++ [(addr, (loc, tl))])).
  { rewrite Htake. reflexivity. }
  rewrite Htake_map.
  rewrite map_app.
  rewrite forallb_app.
  rewrite <- Hprev.
  rewrite andb_true_l.
  simpl.
  rewrite andb_true_r.
  rewrite <- Hone.
  reflexivity.
Qed.

Lemma nth_error_take_nat {A} (l : list A) (n i : nat) :
  i < n ->
  nth_error (take n l) i = nth_error l i.
Proof using.
  revert n i.
  induction l as [|a tl IH]; intros n i Hlt; simpl.
  - destruct n; [lia|]. destruct i; reflexivity.
  - destruct n as [|n']; [lia|].
    destruct i as [|i']; simpl.
    + reflexivity.
    + apply IH. lia.
Qed.

Lemma length_take_le {A} (n : nat) (l : list A) :
  length (take n l) <= n.
Proof using.
  revert n. induction l as [|a tl IH]; intros [|n]; simpl;
    try apply le_n; try apply le_0_n.
  apply le_n_S. apply IH.
Qed.

Lemma mapModelLookup_update_assum_exactness_map_insert_ne
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr a: evm.address) (ex: AssumptionExactness) :
  a <> addr ->
  mapModelLookup (update_assum_exactness_map m (<[addr := ex]> updates)) a =
  mapModelLookup (update_assum_exactness_map m updates) a.
Proof using.
  intro Hneq.
  rewrite !mapModelLookup_update_assum_exactness_map.
  destruct (mapModelLookup m a) as [[loc aps]|] eqn:Horig; simpl; [|reflexivity].
  rewrite lookup_insert_ne; [reflexivity|].
  intro Heq; apply Hneq; symmetry; exact Heq.
Qed.

Lemma assumptionAndUpdateOfAddr_update_assum_exactness_state_insert_ne
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr a: evm.address) (ex: AssumptionExactness) :
  a <> addr ->
  assumptionAndUpdateOfAddr (update_assum_exactness_state st (<[addr := ex]> updates)) a =
  assumptionAndUpdateOfAddr (update_assum_exactness_state st updates) a.
Proof using.
  intro Hneq.
  unfold assumptionAndUpdateOfAddr, update_assum_exactness_state; simpl.
  change ((update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) !! a)
    with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) a).
  change ((update_assum_exactness_map (preTxAssumedState st) updates) !! a)
    with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) a).
  rewrite mapModelLookup_update_assum_exactness_map_insert_ne; [reflexivity|exact Hneq].
Qed.

Lemma assumptionOfAddr_update_assum_exactness_state_insert_ne
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr a: evm.address) (ex: AssumptionExactness) :
  a <> addr ->
  assumptionOfAddr
    (preTxAssumedState (update_assum_exactness_state st (<[addr := ex]> updates))) a =
  assumptionOfAddr
    (preTxAssumedState (update_assum_exactness_state st updates)) a.
Proof using.
  intro Hneq.
  unfold update_assum_exactness_state, assumptionOfAddr; simpl.
  change ((update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) !! a)
    with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) a).
  change ((update_assum_exactness_map (preTxAssumedState st) updates) !! a)
    with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) a).
  rewrite mapModelLookup_update_assum_exactness_map_insert_ne; [reflexivity|exact Hneq].
Qed.

Lemma sliceInvariants_assumption_exactness_stricter
    (au: TxAssumptionsAndUpdates) (ex: AssumptionExactness) :
  assumption_exactness_stricter (assumExactness (preAssumption au)) ex ->
  sliceInvariants au ->
  sliceInvariants
    {| preAssumption :=
         {| preTxState := preTxState (preAssumption au);
            preTxStorage := preTxStorage (preAssumption au);
            assumExactness := ex |};
       originalLoc := originalLoc au;
       txUpdates := txUpdates au |}.
Proof using.
  destruct au as [aps orig tx]; simpl.
  destruct aps as [pre storage oldex]; simpl.
  unfold sliceInvariants, assumption_exactness_stricter,
    min_balance_stricter; simpl.
  intros [Hmin _] Hslice.
  destruct (min_balance oldex) as [old_min|] eqn:Hold.
  {
    destruct (min_balance ex) as [new_min|] eqn:Hnew.
    {
      simpl in Hmin.
      destruct tx as [[cur_loc [upd_loc upd]]|]; simpl in *; [|exact I].
      destruct (postTxState upd) as [updated|]; simpl in *; [|exact I].
      destruct pre as [assumed|]; simpl in *; [|exact I].
      eapply N.le_trans; [exact Hslice|exact Hmin].
    }
    {
      destruct tx; exact I.
    }
  }
  {
    destruct (min_balance ex) as [new_min|] eqn:Hnew.
    {
      contradiction.
    }
    {
      destruct tx; exact I.
    }
  }
Qed.

Lemma validSliceInvariants_update_assum_exactness_state_insert
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness)
    (loc: ptr) (aps: AssumedPreTxAccountState) :
  validSliceInvariants (update_assum_exactness_state st updates) ->
  mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr =
    Some (loc, aps) ->
  assumption_exactness_stricter (assumExactness aps) ex ->
  validSliceInvariants (update_assum_exactness_state st (<[addr := ex]> updates)).
Proof using.
  intros Hslice Hlookup Hstr a au Hau.
  destruct (decide (a = addr)) as [Heq|Hneq].
  {
    subst a.
    unfold assumptionAndUpdateOfAddr, update_assum_exactness_state in Hau |- *.
    simpl in Hau |- *.
    change ((update_assum_exactness_map (preTxAssumedState st)
               (<[addr:=ex]> updates)) !! addr)
      with (mapModelLookup
              (update_assum_exactness_map (preTxAssumedState st)
                 (<[addr:=ex]> updates)) addr) in Hau.
    rewrite mapModelLookup_update_assum_exactness_map in Hau.
    destruct (mapModelLookup_update_assum_exactness_map_Some
                (preTxAssumedState st) updates addr loc aps Hlookup)
      as (aps0 & Horig & Hpre & Hstorage & _Hassum).
    rewrite Horig in Hau.
    simpl in Hau.
    rewrite lookup_insert in Hau.
    simpl in Hau.
    inversion Hau; subst au; clear Hau.
    specialize (Hslice addr
      {| preAssumption := aps;
         originalLoc := loc;
         txUpdates :=
           (newStates st !! addr) ≫=
             (fun a : ptr * list (ptr * UpdatedAccountState) =>
                match head a.2 with
                | Some (loc0, upd) => Some (a.1, (loc0, upd))
                | None => None
                end) |}).
    assert (Hold :
        assumptionAndUpdateOfAddr (update_assum_exactness_state st updates) addr =
        Some
          {| preAssumption := aps;
             originalLoc := loc;
             txUpdates :=
               (newStates st !! addr) ≫=
                 (fun a : ptr * list (ptr * UpdatedAccountState) =>
                    match head a.2 with
                    | Some (loc0, upd) => Some (a.1, (loc0, upd))
                    | None => None
                    end) |}).
    {
      unfold assumptionAndUpdateOfAddr, update_assum_exactness_state.
      simpl.
      change ((update_assum_exactness_map (preTxAssumedState st) updates) !! addr)
        with (mapModelLookup
                (update_assum_exactness_map (preTxAssumedState st) updates) addr).
      rewrite Hlookup.
      reflexivity.
    }
    specialize (Hslice Hold).
    rewrite <- Hpre.
    rewrite <- Hstorage.
    set (txs :=
      (newStates st !! addr) ≫=
        (fun a : ptr * list (ptr * UpdatedAccountState) =>
           match head a.2 with
           | Some (loc0, upd) => Some (a.1, (loc0, upd))
           | None => None
           end)) in *.
    unfold sliceInvariants in Hslice |- *.
    destruct Hstr as [Hmin _].
    unfold min_balance_stricter in Hmin.
    destruct (min_balance (assumExactness aps)) as [old_min|] eqn:Hold_min.
	    {
	      destruct (min_balance ex) as [new_min|] eqn:Hnew_min.
	      {
        rewrite Hold_min in Hslice.
	        simpl in Hslice |- *.
	        destruct (decide (addr = addr)) as [_|Haddr_neq];
	          [|contradiction Haddr_neq; reflexivity].
	        simpl in Hslice |- *.
	        simpl in Hmin.
        destruct txs as [[cur_loc [upd_loc upd]]|]; simpl in *.
        {
          destruct (postTxState upd) as [updated|]; simpl in *.
          {
            destruct (preTxState aps) as [assumed|]; simpl in *.
            {
              rewrite Hnew_min.
              eapply N.le_trans; [exact Hslice|exact Hmin].
            }
            {
              try rewrite Hnew_min; exact I.
            }
          }
          {
            try rewrite Hnew_min; exact I.
          }
        }
        {
          try rewrite Hnew_min; exact I.
        }
      }
      {
        simpl.
        destruct (decide (addr = addr)) as [_|Haddr_neq];
          [|contradiction Haddr_neq; reflexivity].
        rewrite Hnew_min.
        destruct txs; exact I.
      }
    }
    {
      destruct (min_balance ex) as [new_min|] eqn:Hnew_min.
      {
        contradiction.
      }
      {
        simpl.
        destruct (decide (addr = addr)) as [_|Haddr_neq];
          [|contradiction Haddr_neq; reflexivity].
        rewrite Hnew_min.
        destruct txs; exact I.
      }
    }
  }
  {
    apply Hslice with (addr := a).
    rewrite <- (assumptionAndUpdateOfAddr_update_assum_exactness_state_insert_ne
                  st updates addr a ex Hneq).
    exact Hau.
  }
Qed.

Lemma validModel_update_assum_exactness_state_insert
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness)
    (loc: ptr) (aps: AssumedPreTxAccountState) :
  validModel (update_assum_exactness_state st updates) ->
  mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr =
    Some (loc, aps) ->
  assumption_exactness_stricter (assumExactness aps) ex ->
  (match preTxState aps with
   | Some cs =>
       if isSome (min_balance ex)
       then (min_balanceN ex <= cs .^ _balance)%N
       else True
   | None => True
   end) ->
  validModel (update_assum_exactness_state st (<[addr := ex]> updates)).
Proof using.
  intros Hvalid Hlookup Hstr Hbound.
  unfold validModel in *.
  destruct Hvalid as [Hsub [Hstate [Hpost Hslice]]].
  split.
  { assert (Hsub0 :
        map fst (newStates st) ⊆ map fst (preTxAssumedState st)).
    { rewrite <- (map_fst_update_assum_exactness_map
                    (preTxAssumedState st) updates).
      exact Hsub. }
    unfold update_assum_exactness_state; simpl.
    rewrite (map_fst_update_assum_exactness_map
               (preTxAssumedState st) (<[addr := ex]> updates)).
    exact Hsub0. }
  split.
  { (* validStateM *)
    intros a.
    destruct (decide (a = addr)) as [Heq|Hneq].
    { subst a.
      (* validAU for updated addr *)
      unfold assumptionAndUpdateOfAddr, update_assum_exactness_state; simpl.
      change ((update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) !! addr)
        with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) addr).
      rewrite mapModelLookup_update_assum_exactness_map.
      destruct (mapModelLookup_update_assum_exactness_map_Some
                  (preTxAssumedState st) updates addr loc aps Hlookup)
        as (aps0 & Horig & Hpre & _Hprestorage & _Hassum).
      rewrite Horig. simpl.
      rewrite lookup_insert.
      unfold validAU; simpl.
      rewrite Hpre in Hbound.
      destruct (decide (addr = addr)) as [_|Haddr_neq];
        [|contradiction Haddr_neq; reflexivity].
      exact Hbound. }
    { (* validAU for other addrs unchanged *)
      specialize (Hstate a) as Hau.
      rewrite (assumptionAndUpdateOfAddr_update_assum_exactness_state_insert_ne
                 st updates addr a ex Hneq).
      exact Hau. } }
  split.
  { (* validPostNone is insensitive to exactness updates *)
    intros a loc1 tl loc0 aps1 Hnew Hpre.
    pose proof (mapModelLookup_update_assum_exactness_map_Some
                  (preTxAssumedState st) (<[addr := ex]> updates) a loc0 aps1 Hpre)
      as (aps0 & Horig & Hpre0 & _Hprestorage & _Hassum).
    set (aps2 :=
      match updates !! a with
      | Some ex' => {| preTxState := preTxState aps0;
                       preTxStorage := preTxStorage aps0;
                       assumExactness := ex' |}
      | None => aps0
      end).
    assert (Hpre_updates :
        mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) a =
          Some (loc0, aps2)).
    { rewrite mapModelLookup_update_assum_exactness_map.
      rewrite Horig. simpl.
      destruct (updates !! a) as [ex'|] eqn:Hupd; reflexivity. }
    destruct tl as [|[locu upd] tl']; simpl.
    { specialize (Hpost a loc1 [] loc0 aps2 Hnew Hpre_updates).
      exact Hpost. }
    intro Hnone.
    specialize (Hpost a loc1 ((locu, upd) :: tl') loc0 aps2 Hnew).
    specialize (Hpost Hpre_updates).
    specialize (Hpost Hnone).
    unfold aps2 in Hpost.
    destruct (updates !! a) as [ex'|] eqn:Hupd; simpl in Hpost;
      rewrite <- Hpre0 in Hpost; exact Hpost. }
  {
    eapply validSliceInvariants_update_assum_exactness_state_insert; eauto.
  }
Qed.

Lemma validModel_update_assum_exactness_state_insert_map_fst
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness)
    (loc: ptr) (aps: AssumedPreTxAccountState) :
  validModel (update_assum_exactness_state st updates) ->
  mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr =
    Some (loc, aps) ->
  assumption_exactness_stricter (assumExactness aps) ex ->
  (match preTxState aps with
   | Some cs =>
       if isSome (min_balance ex)
       then (min_balanceN ex <= cs .^ _balance)%N
       else True
   | None => True
   end) ->
  validModel (update_assum_exactness_state st (<[addr := ex]> updates)).
Proof using.
  intros Hvalid Hlookup Hstr Hbound.
  exact (validModel_update_assum_exactness_state_insert
           st updates addr ex loc aps Hvalid Hlookup Hstr Hbound).
Qed.

Lemma validModel_subset (st: StateM) :
  validModel st -> map fst (newStates st) ⊆ map fst (preTxAssumedState st).
Proof using.
  intros [Hsub _]. exact Hsub.
Qed.

Lemma validModel_validStateM (st: StateM) :
  validModel st -> validStateM st.
Proof using.
  intros [_ [Hstate _]]. exact Hstate.
Qed.

Lemma validModel_validPostNone (st: StateM) :
  validModel st -> validPostNone st.
Proof using.
  intros [_ [_ [Hpost _]]]. exact Hpost.
Qed.

Lemma validModel_validSliceInvariants (st: StateM) :
  validModel st -> validSliceInvariants st.
Proof using.
  intros [_ [_ [_ Hslice]]]. exact Hslice.
Qed.

Lemma validModel_of_components_update_assum_exactness_state
    (st: StateM) (updates: gmap evm.address AssumptionExactness) :
  map fst (newStates st) ⊆ map fst (preTxAssumedState st) ->
  validStateM (update_assum_exactness_state st updates) ->
  validPostNone (update_assum_exactness_state st updates) ->
  validSliceInvariants (update_assum_exactness_state st updates) ->
  validModel (update_assum_exactness_state st updates).
Proof using.
  intros Hsub Hstate Hpost Hslice.
  unfold validModel.
  split.
  { unfold update_assum_exactness_state; simpl.
    rewrite (map_fst_update_assum_exactness_map (preTxAssumedState st) updates).
    exact Hsub. }
  split.
  { exact Hstate. }
  split.
  { exact Hpost. }
  { exact Hslice. }
Qed.

Lemma validModel_bound_of_lookup
    (st: StateM) (addr: evm.address) (loc: ptr) (aps: AssumedPreTxAccountState) :
  validModel st ->
  mapModelLookup (preTxAssumedState st) addr = Some (loc, aps) ->
  match preTxState aps with
  | Some cs =>
      if isSome (min_balance (assumExactness aps))
      then (min_balanceN (assumExactness aps) <= cs .^ _balance)%N
      else True
  | None => True
  end.
Proof using.
  intros Hvalid Hlookup.
  pose proof (validModel_validStateM st Hvalid) as Hstate.
  specialize (Hstate addr) as Hau.
  unfold assumptionAndUpdateOfAddr in Hau.
  change (preTxAssumedState st !! addr)
    with (mapModelLookup (preTxAssumedState st) addr) in Hau.
  rewrite Hlookup in Hau.
  simpl in Hau.
  exact Hau.
Qed.

Lemma validStateM_bound_of_lookup
    (st: StateM) (addr: evm.address) (loc: ptr) (aps: AssumedPreTxAccountState) :
  validStateM st ->
  mapModelLookup (preTxAssumedState st) addr = Some (loc, aps) ->
  match preTxState aps with
  | Some cs =>
      if isSome (min_balance (assumExactness aps))
      then (min_balanceN (assumExactness aps) <= cs .^ _balance)%N
      else True
  | None => True
  end.
Proof using.
  intros Hstate Hlookup.
  specialize (Hstate addr) as Hau.
  unfold assumptionAndUpdateOfAddr in Hau.
  change (preTxAssumedState st !! addr)
    with (mapModelLookup (preTxAssumedState st) addr) in Hau.
  rewrite Hlookup in Hau.
  simpl in Hau.
  exact Hau.
Qed.

Lemma validModel_post_none_of_lookup
    (st: StateM) (addr: evm.address) (loc: ptr) (tl: list (ptr * UpdatedAccountState))
    (loc0: ptr) (aps: AssumedPreTxAccountState) :
  validModel st ->
  mapModelLookup (newStates st) addr = Some (loc, tl) ->
  mapModelLookup (preTxAssumedState st) addr = Some (loc0, aps) ->
  match tl with
  | [] => False
  | (_, upd) :: _ => postTxState upd = None -> preTxState aps = None
  end.
Proof using.
  intros Hvalid Hnew Hpre.
  pose proof (validModel_validPostNone st Hvalid) as Hpost.
  eapply Hpost; eauto.
Qed.

Lemma min_balance_update_upper_bound
    (old: AssumptionExactness) (orig cur debit: N) :
  (match min_balance old with
   | Some m => (m <= orig)%N
   | None => True
   end) ->
  match min_balance (min_balance_update old orig cur debit) with
  | Some m => (m <= orig)%N
  | None => True
  end.
Proof using.
  intro Hold.
  unfold min_balance_update.
  destruct old as [mb ne]; simpl in *.
  destruct (check_min_balance_ok cur debit) eqn:Hok; simpl.
  { destruct mb as [old_min|]; simpl in *.
    { destruct (N.ltb (N.sub cur debit) orig) eqn:Hltb; simpl.
      { apply N.max_lub.
        { exact Hold. }
        { apply (N2Z.inj_le). lia. } }
      { exact Hold. } }
    { exact I. } }
  { exact I. }
Qed.

Lemma min_balance_update_twice_bound_of_validStateM
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (loc: ptr) (aps: AssumedPreTxAccountState)
    (cur reserve max_reserve: N) :
  validStateM (update_assum_exactness_state st updates) ->
  mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr =
    Some (loc, aps) ->
  match preTxState aps with
  | Some cs =>
      if isSome
           (min_balance
              (min_balance_update
                 (min_balance_update (assumExactness aps)
                    (original_balance_pessimistic_model_map
                       (update_assum_exactness_map (preTxAssumedState st) updates) addr)
                    (original_balance_pessimistic_model_map
                       (update_assum_exactness_map (preTxAssumedState st) updates) addr)
                    max_reserve)
                 (original_balance_pessimistic_model_map
                    (update_assum_exactness_map (preTxAssumedState st) updates) addr)
                 cur reserve))
      then
        (min_balanceN
           (min_balance_update
              (min_balance_update (assumExactness aps)
                 (original_balance_pessimistic_model_map
                    (update_assum_exactness_map (preTxAssumedState st) updates) addr)
                 (original_balance_pessimistic_model_map
                    (update_assum_exactness_map (preTxAssumedState st) updates) addr)
                 max_reserve)
              (original_balance_pessimistic_model_map
                 (update_assum_exactness_map (preTxAssumedState st) updates) addr)
              cur reserve) <= cs .^ _balance)%N
      else True
  | None => True
  end.
Proof using.
  intros Hstate Hlookup.
  set (orig :=
        original_balance_pessimistic_model_map
          (update_assum_exactness_map (preTxAssumedState st) updates) addr).
  set (ex0 := min_balance_update (assumExactness aps) orig orig max_reserve).
  set (ex := min_balance_update ex0 orig cur reserve).
  destruct (preTxState aps) as [cs|] eqn:Hpre; simpl; [|exact I].
  destruct (isSome (min_balance ex)) eqn:Hrel.
  {
    destruct (min_balance ex) as [m|] eqn:Hmb_ex; [|discriminate].
    simpl.
    assert (Hold_bound :
        match min_balance (assumExactness aps) with
        | Some m0 => (m0 <= cs .^ _balance)%N
        | None => True
        end).
    { pose proof (validStateM_bound_of_lookup
                    (update_assum_exactness_state st updates) addr loc aps
                    Hstate Hlookup) as Hbound.
      rewrite Hpre in Hbound.
      simpl in Hbound.
      destruct (min_balance (assumExactness aps)) as [m0|] eqn:Hmb0; simpl in *.
      { unfold min_balanceN in Hbound.
        rewrite Hmb0 in Hbound.
        simpl in Hbound.
        exact Hbound. }
      { exact I. } }
    assert (Horig_eq : orig = cs .^ _balance).
    { unfold orig.
      unfold original_balance_pessimistic_model_map, preTxAccountOf_map.
      rewrite Hlookup. simpl. rewrite Hpre. reflexivity. }
    assert (Hold_le_orig :
        match min_balance (assumExactness aps) with
        | Some m0 => (m0 <= orig)%N
        | None => True
        end).
    { rewrite Horig_eq.
      exact Hold_bound. }
    assert (Hex0_le :
        match min_balance ex0 with
        | Some m0 => (m0 <= orig)%N
        | None => True
        end).
    { unfold ex0.
      apply min_balance_update_upper_bound.
      exact Hold_le_orig. }
    assert (Hex_le :
        match min_balance (min_balance_update ex0 orig cur reserve) with
        | Some m0 => (m0 <= orig)%N
        | None => True
        end).
    { apply min_balance_update_upper_bound.
      exact Hex0_le. }
    change (min_balance (min_balance_update ex0 orig cur reserve)) with (min_balance ex) in Hex_le.
    rewrite Hmb_ex in Hex_le.
    rewrite Horig_eq in Hex_le.
    unfold min_balanceN.
    rewrite Hmb_ex.
    simpl.
    exact Hex_le.
  }
  {
    exact I.
  }
Qed.

#[export] Hint Resolve
  validModel_of_components_update_assum_exactness_state
  assumption_exactness_stricter_min_balance_update_twice
  min_balance_update_twice_bound_of_validStateM : pure.

Lemma satisfiesAssumptions_update_assum_exactness_state_insert
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness)
    (preTxState: AugmentedState) (loc: ptr) (aps: AssumedPreTxAccountState) :
  mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr = Some (loc, aps) ->
  assumption_exactness_stricter (assumExactness aps) ex ->
  (min_balance ex = None -> min_balance (assumExactness aps) = None) ->
  satisfiesAssumptions (update_assum_exactness_state st (<[addr := ex]> updates)) preTxState.1 ->
  satisfiesAssumptions (update_assum_exactness_state st updates) preTxState.1.
Proof using.
  intros Hlookup Hstr Hmb Hsat a.
  unfold satisfiesAssumptions in Hsat.
  specialize (Hsat a).
  destruct (decide (a = addr)) as [Heq|Hneq].
  - subst a.
    unfold assumptionAndUpdateOfAddr, update_assum_exactness_state in Hsat |- *; simpl in *.
    change ((update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) !! addr)
      with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) addr) in Hsat.
    change ((update_assum_exactness_map (preTxAssumedState st) updates) !! addr)
      with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr).
	    destruct (mapModelLookup_update_assum_exactness_map_Some
	                (preTxAssumedState st) updates addr loc aps Hlookup)
		      as (aps0 & Horig & Hpre & Hstorage & _Hassum).
	    assert (Hass_new :
	        assumptionOfAddr
	          (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates))
	          addr =
	        Some (update_assum_exactness_assumed (fun _ => ex) aps)).
	    { assert (Hlookup_new :
	          mapModelLookup
	            (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates))
	            addr =
	          Some (loc, update_assum_exactness_assumed (fun _ => ex) aps)).
	      { rewrite mapModelLookup_update_assum_exactness_map.
        rewrite Horig. simpl.
        rewrite lookup_insert.
        destruct (decide (addr = addr)) as [_|Haddr_neq];
          [|contradiction Haddr_neq; reflexivity].
        rewrite <- Hpre.
        rewrite <- Hstorage.
        reflexivity. }
	      unfold assumptionOfAddr.
	      change ((update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) !! addr)
	        with (mapModelLookup
	                (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates))
	                addr).
	      rewrite Hlookup_new. reflexivity. }
	    assert (Hass_old :
	        assumptionOfAddr
	          (update_assum_exactness_map (preTxAssumedState st) updates)
	          addr = Some aps).
	    { unfold assumptionOfAddr.
	      change ((update_assum_exactness_map (preTxAssumedState st) updates) !! addr)
	        with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr).
	      rewrite Hlookup. reflexivity. }
	    rewrite Hass_new in Hsat.
	    rewrite Hass_old.
	    eapply (satAccountAssumptions_stricter
	              (relaxedValidation st)
	              {| preAssumption := aps;
	                 originalLoc := loc;
	                 txUpdates := None |}
	              ex
	              (Some (preTxState.1 addr))); eauto.
  - rewrite (assumptionOfAddr_update_assum_exactness_state_insert_ne st updates addr a ex Hneq) in Hsat.
    exact Hsat.
Qed.

Lemma satAccountAssumptions_stricter_bound
    (relaxed: bool) (au: TxAssumptionsAndUpdates) (ex: AssumptionExactness)
    (actual: option AccountM) :
  assumption_exactness_stricter (assumExactness (preAssumption au)) ex ->
  (match preTxState (preAssumption au) with
   | Some cs =>
       if isSome (min_balance (assumExactness (preAssumption au)))
       then (min_balanceN (assumExactness (preAssumption au)) <= cs .^ _balance)%N
       else True
   | None => True
   end) ->
  satAccountAssumptions relaxed
    (Some (update_assum_exactness_assumed (fun _ => ex) (preAssumption au))) actual ->
  satAccountAssumptions relaxed (Some (preAssumption au)) actual.
Proof using.
  intros Hstr Hbound [Hnon Hstor]. split.
  - eapply satAccountNonStorageAssumptions_stricter_bound; eauto.
  - unfold satAccountStrageAssumptions in *; simpl in *; exact Hstor.
Qed.

Lemma satisfiesAssumptions_update_assum_exactness_state_insert_bound
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness)
    (preTxState0: AugmentedState) (loc: ptr) (aps: AssumedPreTxAccountState) :
  mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr = Some (loc, aps) ->
  assumption_exactness_stricter (assumExactness aps) ex ->
  (match preTxState aps with
   | Some cs =>
       if isSome (min_balance (assumExactness aps))
       then (min_balanceN (assumExactness aps) <= cs .^ _balance)%N
       else True
   | None => True
   end) ->
  satisfiesAssumptions (update_assum_exactness_state st (<[addr := ex]> updates)) preTxState0.1 ->
  satisfiesAssumptions (update_assum_exactness_state st updates) preTxState0.1.
Proof using.
  intros Hlookup Hstr Hbound Hsat a.
  unfold satisfiesAssumptions in Hsat.
  specialize (Hsat a).
  destruct (decide (a = addr)) as [Heq|Hneq].
  { subst a.
    unfold update_assum_exactness_state in Hsat |- *; simpl in *.
    destruct (mapModelLookup_update_assum_exactness_map_Some
                (preTxAssumedState st) updates addr loc aps Hlookup)
	      as (aps0 & Horig & Hpre & Hstorage & _Hassum).
    assert (Hass_new :
        assumptionOfAddr
          (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates))
          addr =
        Some (update_assum_exactness_assumed (fun _ => ex) aps)).
    { assert (Hlookup_new :
          mapModelLookup
            (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates))
            addr =
          Some (loc, update_assum_exactness_assumed (fun _ => ex) aps)).
      { rewrite mapModelLookup_update_assum_exactness_map.
        rewrite Horig. simpl.
        rewrite lookup_insert.
        destruct (decide (addr = addr)) as [_|Haddr_neq];
          [|contradiction Haddr_neq; reflexivity].
        rewrite <- Hpre.
        rewrite <- Hstorage.
        reflexivity. }
      unfold assumptionOfAddr.
      change ((update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates)) !! addr)
        with (mapModelLookup
                (update_assum_exactness_map (preTxAssumedState st) (<[addr := ex]> updates))
                addr).
      rewrite Hlookup_new. reflexivity. }
    assert (Hass_old :
        assumptionOfAddr
          (update_assum_exactness_map (preTxAssumedState st) updates)
          addr = Some aps).
    { unfold assumptionOfAddr.
      change ((update_assum_exactness_map (preTxAssumedState st) updates) !! addr)
        with (mapModelLookup (update_assum_exactness_map (preTxAssumedState st) updates) addr).
      rewrite Hlookup. reflexivity. }
    rewrite Hass_new in Hsat.
    rewrite Hass_old.
    eapply (satAccountAssumptions_stricter_bound
              (relaxedValidation st)
              {| preAssumption := aps;
                 originalLoc := loc;
                 txUpdates := None |}
              ex
              (Some (preTxState0.1 addr))); eauto.
  }
  { rewrite (assumptionOfAddr_update_assum_exactness_state_insert_ne st updates addr a ex Hneq) in Hsat.
    exact Hsat. }
Qed.

Lemma applyUpdates_update_assum_exactness_state_insert_ne
    (st: StateM) (updates: gmap evm.address AssumptionExactness)
    (addr a: evm.address) (ex: AssumptionExactness) (preTxState: StateOfAccounts) :
  a <> addr ->
  applyUpdates (update_assum_exactness_state st (<[addr := ex]> updates)) preTxState a =
  applyUpdates (update_assum_exactness_state st updates) preTxState a.
Proof using.
  intro Hneq.
  unfold applyUpdates.
  rewrite (assumptionAndUpdateOfAddr_update_assum_exactness_state_insert_ne st updates addr a ex Hneq).
  reflexivity.
Qed.

Lemma allFinalBalSufficient_eq_of_applyUpdates_eq_on
    (preTxState: AugmentedState) (post1 post2: StateOfAccounts)
    (changedAccounts: list evm.address) (t: TxWithHdr) :
  (forall a, a ∈ changedAccounts -> post1 a = post2 a) ->
  allFinalBalSufficient 3 preTxState post1 changedAccounts t =
  allFinalBalSufficient 3 preTxState post2 changedAccounts t.
Proof using.
  intro Heq.
  unfold allFinalBalSufficient.
  induction changedAccounts as [|a tl IH]; simpl; [reflexivity|].
  unfold finalBalSufficient, isSC, balanceOfAc.
  assert (Ha : a ∈ a :: tl).
  { apply elem_of_cons. left. reflexivity. }
  rewrite !(Heq a Ha).
  rewrite IH; [reflexivity|].
  intros a' Ha'. apply Heq. right; exact Ha'.
Qed.

Lemma addr_not_in_takeN_of_nth_error
    (l: list (evm.address * (ptr * list (ptr * UpdatedAccountState))))
    (i: N) (addr: evm.address) (loc: ptr) (tl: list (ptr * UpdatedAccountState)) :
  NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) l)) ->
  nth_error l (N.to_nat i) = Some (addr, (loc, tl)) ->
  addr ∉ map fst (takeN i l).
Proof using.
  intros Hnodup Hnth Hin.
  apply list_elem_of_fmap in Hin as [[addr' [loc' tl']] [Hfst Hin_l]].
  simpl in Hfst; subst addr'.
  apply list_elem_of_lookup_1 in Hin_l as [j Hj].
  assert (Hjlen : (j < length (takeN i l))%nat).
  { eapply lookup_lt_Some. exact Hj. }
  assert (Hjlt : (j < N.to_nat i)%nat).
  { unfold takeN in Hjlen.
    eapply Nat.lt_le_trans; [exact Hjlen|].
    apply length_take_le. }
  assert (Hj_l : nth_error l j = Some (addr, (loc', tl'))).
  { unfold takeN in Hj.
    rewrite lookup_nth_error in Hj.
    rewrite <- (nth_error_take_nat l (N.to_nat i) j Hjlt).
    exact Hj. }
  pose proof (nth_error_map_key_ptr l j addr loc' tl' Hj_l) as Hnth_j.
  pose proof (nth_error_map_key_ptr l (N.to_nat i) addr loc tl Hnth) as Hnth_i.
  pose proof (nodup_map_fst_nth_error_eq_nat
                (map (fun '(a, (b, _)) => (a, b)) l)
                j (N.to_nat i) addr loc' loc
                Hnodup Hnth_j Hnth_i) as Heq.
  lia.
Qed.

Lemma allFinalBalSufficient_takeN_i_update_assum_exactness_state_insert
    (stm: StateM) (ctx: MonadChainContext) (hist: ExtraAcStates) (tx: TxWithHdr)
    (i: N) (addr: evm.address) (loc: ptr)
    (tl: list (ptr * UpdatedAccountState))
    (updates: gmap evm.address AssumptionExactness) (ex: AssumptionExactness)
    (preTxState0: StateOfAccounts) (loc0: ptr) (aps: AssumedPreTxAccountState) :
  NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) (newStates stm))) ->
  nth_error (newStates stm) (N.to_nat i) = Some (addr, (loc, tl)) ->
  (forall preTxState : StateOfAccounts,
      satisfiesAssumptions (update_assum_exactness_state stm updates) preTxState ->
      true =
        allFinalBalSufficient 3 (preTxState, hist)
          (applyUpdates (update_assum_exactness_state stm updates) preTxState)
          (map fst (takeN i (newStates stm))) tx) ->
  validModel (update_assum_exactness_state stm updates) ->
  mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) updates) addr =
    Some (loc0, aps) ->
  assumption_exactness_stricter (assumExactness aps) ex ->
  satisfiesAssumptions (update_assum_exactness_state stm (<[addr := ex]> updates)) preTxState0 ->
  true =
    allFinalBalSufficient 3 (preTxState0, hist)
      (applyUpdates (update_assum_exactness_state stm (<[addr := ex]> updates)) preTxState0)
      (map fst (takeN i (newStates stm))) tx.
Proof using.
  intros Hnodup Hnth Hb Hvalid Hlookup Hstr Hsat.
  pose proof (validModel_bound_of_lookup
                (update_assum_exactness_state stm updates) addr loc0 aps Hvalid Hlookup)
    as Hbound.
  assert (Haddr_notin :
      addr ∉ map fst (takeN i (newStates stm))).
  { eapply addr_not_in_takeN_of_nth_error; eauto. }
  specialize (Hb preTxState0).
  assert (Hsat_old :
      satisfiesAssumptions (update_assum_exactness_state stm updates) preTxState0).
  {
    eapply (satisfiesAssumptions_update_assum_exactness_state_insert_bound
              stm updates addr ex (preTxState0, hist) loc0 aps); eauto.
  }
  specialize (Hb Hsat_old).
  rewrite Hb.
  apply allFinalBalSufficient_eq_of_applyUpdates_eq_on.
  intros a Ha.
  symmetry.
  apply applyUpdates_update_assum_exactness_state_insert_ne.
  intro Heq. subst a. exact (Haddr_notin Ha).
Qed.

Lemma finalBalSufficient_from_context
    (st: StateM) (ctx: MonadChainContext)
    (pbs preTxState0: AugmentedState)
    (i: N) (nthelemAddr: evm.address)
    (nthElemPtr nthElemVstackTopPtr: ptr)
    (nthElemVstackTop: UpdatedAccountState)
    (nthElemVstackTl: list (ptr * UpdatedAccountState))
    (tx: TxWithHdr) (loc: ptr) (aps: AssumedPreTxAccountState) :
  NoDup (map fst (newStates st)) ->
  nth_error (newStates st) (N.to_nat i) =
    Some (nthelemAddr,
          (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
  mapModelLookup (preTxAssumedState st) nthelemAddr = Some (loc, aps) ->
  satisfiesAssumptions st preTxState0.1 ->
  historyConsistent ctx preTxState0.2 ->
  configuredReserveBalOfAddr preTxState0.2 nthelemAddr = DefReserve ->
  (postTxState nthElemVstackTop = None -> preTxState aps = None) ->
  isAcSC (postTxState nthElemVstackTop) = false ->
  nthelemAddr <> sender tx ->
  (N.min (DefReserve)
     (original_balance_pessimistic_model_map
        (preTxAssumedState st) nthelemAddr)
   <= balanceOfAccount (postTxState nthElemVstackTop))%N ->
  (let orig :=
     original_balance_pessimistic_model_map (preTxAssumedState st) nthelemAddr in
   let cur := balanceOfAccount (postTxState nthElemVstackTop) in
   let debit := N.min (DefReserve) orig in
   match min_balance (assumExactness aps) with
   | Some m => (N.sub orig (N.sub cur debit) <= m)%N
   | None => True
   end) ->
  finalBalSufficient 3 preTxState0 (applyUpdates st preTxState0.1) tx nthelemAddr = true.
Proof using.
  intros Hnodup Hnth Hlookup Hsat Hhist Hreserve_cfg0 Hpost_none_pre_none Hsc Hneq Hbal Hminlb.
  unfold finalBalSufficient.
  set (post := applyUpdates st preTxState0.1).
  destruct (isSC post nthelemAddr) eqn:Hscpost; [reflexivity|].
  rewrite bool_decide_false; [|intro Heq; apply Hneq; symmetry; exact Heq].
  apply bool_decide_true.
  set (reserve := DefReserve).
  assert (Hreserve_cfg :
      configuredReserveBalOfAddr preTxState0.2 nthelemAddr = reserve).
  { unfold reserve. exact Hreserve_cfg0. }
  set (orig := original_balance_pessimistic_model_map (preTxAssumedState st) nthelemAddr).
  set (cur := balanceOfAccount (postTxState nthElemVstackTop)).
  set (debit := N.min reserve orig).
  set (actualPre := balanceOfAc preTxState0.1 nthelemAddr).
  assert (Hcur : (debit <= cur)%N) by exact Hbal.
  assert (Hmem :
      (nthelemAddr,
       (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ∈
      newStates st).
  { apply list_elem_of_lookup_2 with (i := N.to_nat i).
    rewrite lookup_nth_error. exact Hnth. }
  assert (Hlookup_new :
      newStates st !! nthelemAddr =
        Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
  { apply elem_of_list_to_map_1; [exact Hnodup|exact Hmem]. }
  set (au := {| preAssumption := aps;
                originalLoc := loc;
                txUpdates := Some (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop)) |}).
  pose proof Hlookup as Hlookup'.
  change (preTxAssumedState st !! nthelemAddr = Some (loc, aps)) in Hlookup'.
  assert (Hau : assumptionAndUpdateOfAddr st nthelemAddr = Some au).
  { unfold assumptionAndUpdateOfAddr. rewrite Hlookup'. simpl.
    rewrite Hlookup_new. simpl. reflexivity. }
  assert (Hass :
      assumptionOfAddr (preTxAssumedState st) nthelemAddr = Some aps).
  { unfold assumptionOfAddr. rewrite Hlookup'. reflexivity. }
  specialize (Hsat nthelemAddr).
  rewrite Hass in Hsat.
  unfold satAccountAssumptions in Hsat.
  destruct Hsat as [Hnon _Hstor].
  unfold satAccountNonStorageAssumptions in Hnon.
  simpl in Hnon.
  set (csActual := preTxState0.1 nthelemAddr) in *.
  destruct (preTxState aps) as [csAssumed|] eqn:Hpre in Hnon; simpl in Hnon.
  2:{ contradiction. }
  set (assumEx := assumExactness aps) in *.
  set (assumedBal := csAssumed .^ _balance) in *.
  assert (Hactual_ge :
      (N.sub orig (N.sub cur debit) <= actualPre)%N).
  { subst orig cur debit actualPre assumedBal.
    destruct (relaxedValidation st) eqn:Hrel.
	    - simpl in Hnon.
	      destruct (min_balance assumEx) as [m|] eqn:Hmb; simpl in Hnon.
	      + destruct Hnon as [Hbal_assum _Hnonce].
	        rewrite /min_balanceN Hmb in Hbal_assum.
	        assert (Hmle : (m <= csActual .^ _balance)%N).
	        { exact Hbal_assum. }
	        apply (N.le_trans _ m); [exact Hminlb|exact Hmle].
      + destruct Hnon as [Hbal_assum _Hnonce].
        subst csActual.
        assert (Horig_eq :
            original_balance_pessimistic_model_map (preTxAssumedState st) nthelemAddr =
              csAssumed .^ _balance).
        { unfold original_balance_pessimistic_model_map, preTxAccountOf_map.
          rewrite Hlookup. simpl. rewrite Hpre. reflexivity. }
        assert (Hactual_eq' :
            balanceOfAc preTxState0.1 nthelemAddr =
              (preTxState0.1 nthelemAddr) .^ _balance).
        { unfold balanceOfAc. simpl. reflexivity. }
        assert (Hactual_eq :
            balanceOfAc preTxState0.1 nthelemAddr = csAssumed .^ _balance).
        { exact (eq_trans Hactual_eq' (eq_sym Hbal_assum)). }
        rewrite Hactual_eq.
        rewrite <- Horig_eq.
        apply N.le_sub_l.
    - simpl in Hnon.
      destruct Hnon as [[Hbal_assum _Hmin_ok] _Hnonce].
      subst csActual.
      assert (Horig_eq :
          original_balance_pessimistic_model_map (preTxAssumedState st) nthelemAddr =
            csAssumed .^ _balance).
      { unfold original_balance_pessimistic_model_map, preTxAccountOf_map.
        rewrite Hlookup. simpl. rewrite Hpre. reflexivity. }
      assert (Hactual_eq' :
          balanceOfAc preTxState0.1 nthelemAddr =
            (preTxState0.1 nthelemAddr) .^ _balance).
      { unfold balanceOfAc. simpl. reflexivity. }
      assert (Hactual_eq :
          balanceOfAc preTxState0.1 nthelemAddr = csAssumed .^ _balance).
      { exact (eq_trans Hactual_eq' (eq_sym Hbal_assum)). }
      rewrite Hactual_eq.
      rewrite <- Horig_eq.
      apply N.le_sub_l. }
  subst actualPre.
  subst orig cur debit.
  unfold balanceOfAc.
  unfold post.
  unfold applyUpdates.
  rewrite Hau. simpl.
  set (fv := accountFinalVal (relaxedValidation st) au (Some (preTxState0.1 nthelemAddr))).
  destruct fv as [fv'|] eqn:Hfv; simpl.
  { (* account exists in post-state *)
    subst fv.
    unfold balanceOfAccount in *.
    unfold accountFinalVal in Hfv.
    destruct (txUpdates au) as [[ptr0 [ptr1 upd]]|] eqn:Htx.
    2:{ exfalso. unfold au in Htx. simpl in Htx. discriminate. }
    destruct (postTxState upd) as [csUpdated|] eqn:Hpost.
    2:{
      exfalso.
      simpl in Hfv.
      discriminate Hfv.
    }
    simpl in Hfv.
    set (origN := csAssumed .^ _balance) in *.
    set (curN := csUpdated .^ _balance) in *.
    set (debitN := N.min reserve origN) in *.
    assert (Horig_eq :
        original_balance_pessimistic_model_map (preTxAssumedState st) nthelemAddr = origN).
    { unfold original_balance_pessimistic_model_map, preTxAccountOf_map.
      rewrite Hlookup. simpl. rewrite Hpre. reflexivity. }
    assert (Hupd_eq : upd = nthElemVstackTop).
    { unfold au in Htx. simpl in Htx. inversion Htx. reflexivity. }
    assert (Hpost' : postTxState nthElemVstackTop = Some csUpdated).
    { rewrite <- Hupd_eq. exact Hpost. }
    assert (HcurN : (debitN <= curN)%N).
    { rewrite Hpost' in Hbal. simpl in Hbal.
      unfold debitN, curN. rewrite <- Horig_eq. exact Hbal. }
    destruct (relaxedValidation st) eqn:Hrel.
    { destruct (preTxState (preAssumption au)) as [csAssumed'|] eqn:Hpre'; simpl in Hfv.
      { destruct (min_balance (assumExactness (preAssumption au))) as [mb|] eqn:Hmb; simpl in Hfv.
        { (* min_balance Some: patched balance *)
          destruct (nonce_exact (assumExactness (preAssumption au))) eqn:Hnonce; simpl in Hfv.
          { inversion Hfv; subst; clear Hfv.
            set (postTxBal :=
                   (csActual .^ _balance + (csUpdated .^ _balance - csAssumed' .^ _balance))%Z).
            assert (Hpost_ge_debit :
                (Z.of_N debitN <= postTxBal)%Z).
            { (* derive from Hactual_ge and arithmetic in Z *)
              subst postTxBal.
              apply (N2Z.inj_le _) in Hactual_ge.
              rewrite N2Z.inj_sub_max in Hactual_ge.
              rewrite Hpost' in Hactual_ge; simpl in Hactual_ge.
              rewrite Horig_eq in Hactual_ge.
              fold debitN in Hactual_ge.
              change (match csUpdated with | {| balance := balance |} => balance end)
                with (csUpdated .^ _balance) in Hactual_ge.
              fold curN in Hactual_ge.
              assert (Hactual_ge' :
                  (Z.of_N origN - Z.of_N (curN - debitN) <=
                   Z.of_N (balanceOfAc preTxState0.1 nthelemAddr))%Z).
              { eapply Z.le_trans; [apply Z.le_max_r|exact Hactual_ge]. }
              rewrite N2Z.inj_sub in Hactual_ge'; [| exact HcurN].
              assert (Hassumed_eq : csAssumed' = csAssumed).
              { unfold au in Hpre'. simpl in Hpre'.
                rewrite Hpre in Hpre'. inversion Hpre'. reflexivity. }
              subst csAssumed'.
              change (csActual .^ _balance)
                with (balanceOfAc preTxState0.1 nthelemAddr).
              change (csUpdated .^ _balance) with curN.
              change (csAssumed .^ _balance) with origN.
              (* use lia on Z *)
              nia. }
            assert (Hpost_nonneg : (0 <= postTxBal)%Z).
            { nia. }
            assert (Hbal_fv' : balance fv' = Z.to_N postTxBal).
            { pose proof H0 as H0'.
              pose proof Hmb as Hmb'.
              pose proof Hnonce as Hnonce'.
              unfold au in Hmb'. simpl in Hmb'.
              unfold au in Hnonce'. simpl in Hnonce'.
              rewrite Hpre in H0'. simpl in H0'.
              rewrite Hnonce' in H0'. simpl in H0'.
              rewrite Hmb' in H0'. simpl in H0'.
              inversion H0'; subst fv'; clear H0'.
              assert (Hassumed_eq : csAssumed' = csAssumed).
              { unfold au in Hpre'. simpl in Hpre'.
                rewrite Hpre in Hpre'. inversion Hpre'. reflexivity. }
              subst csAssumed'.
              unfold postTxBal. simpl.
              rewrite balance_update_balance. reflexivity. }
            rewrite Hpost. simpl.
            rewrite H0. simpl.
            rewrite Hbal_fv'.
            rewrite Hreserve_cfg.
            apply (N_le_ZtoN_of_Zle
                     (N.min reserve (balance (preTxState0.1 nthelemAddr)))
                     postTxBal); try exact Hpost_nonneg.
            destruct (N.le_dec reserve origN) as [Hle|Hgt].
            { assert (Hmin_le :
                  (N.min reserve (balance (preTxState0.1 nthelemAddr)) <= reserve)%N).
              { apply N.le_min_l. }
              eapply Z.le_trans; [apply N2Z.inj_le; exact Hmin_le|].
              assert (Hdebit_eq : debitN = reserve).
              { apply N.min_l. exact Hle. }
              rewrite Hdebit_eq in Hpost_ge_debit.
              exact Hpost_ge_debit. }
            { assert (Horle : (origN <= reserve)%N).
              { apply N.lt_le_incl.
                apply (proj1 (N.compare_gt_iff reserve origN)).
                apply (proj2 (N.compare_nle_iff reserve origN)).
                exact Hgt. }
              assert (Hdebit_eq : debitN = origN).
              { apply N.min_r. exact Horle. }
              assert (Hcur_ge_orig : (origN <= curN)%N).
              { rewrite Hdebit_eq in HcurN. exact HcurN. }
              assert (Hmin_le :
                  (N.min reserve (balance (preTxState0.1 nthelemAddr)) <=
                   balance (preTxState0.1 nthelemAddr))%N).
              { apply N.le_min_r. }
              eapply Z.le_trans.
              { apply N2Z.inj_le. exact Hmin_le. }
              apply (N2Z.inj_le) in Hcur_ge_orig.
              assert (Hassumed_eq : csAssumed' = csAssumed).
              { unfold au in Hpre'. simpl in Hpre'.
                rewrite Hpre in Hpre'. inversion Hpre'. reflexivity. }
              subst csAssumed'.
              unfold postTxBal. simpl.
              change (balance (preTxState0.1 nthelemAddr)) with (csActual .^ _balance).
              change (csUpdated .^ _balance) with curN.
              change (csAssumed .^ _balance) with origN.
              assert (Hdiff_nonneg : (0 <= Z.of_N curN - Z.of_N origN)%Z).
              { apply (proj2 (Z.le_0_sub (Z.of_N origN) (Z.of_N curN))).
                exact Hcur_ge_orig. }
              replace (Z.of_N (csActual .^ _balance))
                with (Z.of_N (csActual .^ _balance) + 0)%Z by nia.
              apply (proj1 (Z.add_le_mono_l
                              0 (Z.of_N curN - Z.of_N origN)
                              (Z.of_N (csActual .^ _balance)))).
              exact Hdiff_nonneg. } }
          { inversion Hfv; subst; clear Hfv.
            set (postTxBal :=
                   (csActual .^ _balance + (csUpdated .^ _balance - csAssumed' .^ _balance))%Z).
            assert (Hpost_ge_debit :
                (Z.of_N debitN <= postTxBal)%Z).
            { (* derive from Hactual_ge and arithmetic in Z *)
              subst postTxBal.
              apply (N2Z.inj_le _) in Hactual_ge.
              rewrite N2Z.inj_sub_max in Hactual_ge.
              rewrite Hpost' in Hactual_ge; simpl in Hactual_ge.
              rewrite Horig_eq in Hactual_ge.
              fold debitN in Hactual_ge.
              change (match csUpdated with | {| balance := balance |} => balance end)
                with (csUpdated .^ _balance) in Hactual_ge.
              fold curN in Hactual_ge.
              assert (Hactual_ge' :
                  (Z.of_N origN - Z.of_N (curN - debitN) <=
                   Z.of_N (balanceOfAc preTxState0.1 nthelemAddr))%Z).
              { eapply Z.le_trans; [apply Z.le_max_r|exact Hactual_ge]. }
              rewrite N2Z.inj_sub in Hactual_ge'; [| exact HcurN].
              assert (Hassumed_eq : csAssumed' = csAssumed).
              { unfold au in Hpre'. simpl in Hpre'.
                rewrite Hpre in Hpre'. inversion Hpre'. reflexivity. }
              subst csAssumed'.
              change (csActual .^ _balance)
                with (balanceOfAc preTxState0.1 nthelemAddr).
              change (csUpdated .^ _balance) with curN.
              change (csAssumed .^ _balance) with origN.
              (* use lia on Z *)
              nia. }
            assert (Hpost_nonneg : (0 <= postTxBal)%Z).
            { nia. }
            assert (Hbal_fv' : balance fv' = Z.to_N postTxBal).
            { pose proof H0 as H0'.
              pose proof Hmb as Hmb'.
              pose proof Hnonce as Hnonce'.
              unfold au in Hmb'. simpl in Hmb'.
              unfold au in Hnonce'. simpl in Hnonce'.
              rewrite Hpre in H0'. simpl in H0'.
              rewrite Hnonce' in H0'. simpl in H0'.
              rewrite Hmb' in H0'. simpl in H0'.
              inversion H0'; subst fv'; clear H0'.
              assert (Hassumed_eq : csAssumed' = csAssumed).
              { unfold au in Hpre'. simpl in Hpre'.
                rewrite Hpre in Hpre'. inversion Hpre'. reflexivity. }
              subst csAssumed'.
              unfold postTxBal. simpl.
              rewrite balance_update_nonce. rewrite balance_update_balance. reflexivity. }
            rewrite Hpost. simpl.
            rewrite H0. simpl.
            rewrite Hbal_fv'.
            assert (Hmin_le_post :
                (Z.of_N (N.min reserve (balance (preTxState0.1 nthelemAddr))) <=
                 postTxBal)%Z).
            { destruct (N.le_dec reserve origN) as [Hle|Hgt].
              { assert (Hmin_le_reserve :
                    (N.min reserve (balance (preTxState0.1 nthelemAddr)) <= reserve)%N).
                { apply N.le_min_l. }
                assert (Hdebit_eq : debitN = reserve).
                { apply N.min_l. exact Hle. }
                rewrite Hdebit_eq in Hpost_ge_debit.
                eapply Z.le_trans.
                { apply N2Z.inj_le. exact Hmin_le_reserve. }
                exact Hpost_ge_debit. }
              { assert (Horle : (origN <= reserve)%N).
                { apply N.lt_le_incl.
                  apply (proj1 (N.compare_gt_iff reserve origN)).
                  apply (proj2 (N.compare_nle_iff reserve origN)).
                  exact Hgt. }
                assert (Hdebit_eq : debitN = origN).
                { apply N.min_r. exact Horle. }
                assert (Hcur_ge_orig : (origN <= curN)%N).
                { rewrite Hdebit_eq in HcurN. exact HcurN. }
                assert (Hmin_le_actual :
                    (N.min reserve (balance (preTxState0.1 nthelemAddr)) <=
                     balance (preTxState0.1 nthelemAddr))%N).
                { apply N.le_min_r. }
                assert (Hassumed_eq : csAssumed' = csAssumed).
                { unfold au in Hpre'. simpl in Hpre'.
                  rewrite Hpre in Hpre'. inversion Hpre'. reflexivity. }
                subst csAssumed'.
                unfold postTxBal. simpl.
                change (balance (preTxState0.1 nthelemAddr)) with (csActual .^ _balance).
                change (csUpdated .^ _balance) with curN.
                change (csAssumed .^ _balance) with origN.
                assert (Hdiff_nonneg : (0 <= Z.of_N curN - Z.of_N origN)%Z).
                { apply (proj2 (Z.le_0_sub (Z.of_N origN) (Z.of_N curN))).
                  apply (N2Z.inj_le) in Hcur_ge_orig. exact Hcur_ge_orig. }
                eapply Z.le_trans.
                { apply N2Z.inj_le. exact Hmin_le_actual. }
                assert (Hpost_ge_actual :
                    (Z.of_N (csActual .^ _balance) + 0 <=
                     Z.of_N (csActual .^ _balance) +
                     (Z.of_N curN - Z.of_N origN))%Z).
                { apply (Z.add_le_mono_l
                           0 (Z.of_N curN - Z.of_N origN)
                           (Z.of_N (csActual .^ _balance))).
                  exact Hdiff_nonneg. }
                rewrite Z.add_0_r in Hpost_ge_actual.
                exact Hpost_ge_actual. } }
            rewrite Hreserve_cfg.
            apply (N_le_ZtoN_of_Zle
                     (N.min reserve (balance (preTxState0.1 nthelemAddr))) postTxBal).
            { exact Hpost_nonneg. }
            { exact Hmin_le_post. } } }
        { (* min_balance None: balance equals spec *)
          destruct (nonce_exact (assumExactness (preAssumption au))) eqn:Hnonce; simpl in Hfv.
          {
            inversion Hfv; subst; clear Hfv.
            destruct Hnon as [Hbal_assum _].
            simpl in Hbal_assum.
            rewrite Hmb in Hbal_assum. simpl in Hbal_assum.
            assert (Hbal_eq : balance csActual = origN).
            { unfold origN. symmetry. exact Hbal_assum. }
            pose proof H0 as H0'.
            rewrite Hpre in H0'. simpl in H0'.
            rewrite Hnonce in H0'. simpl in H0'.
            rewrite Hmb in H0'. simpl in H0'.
            inversion H0'; subst fv'; clear H0'.
            pose proof Hnonce as Hnonce_aps.
            pose proof Hmb as Hmb_aps.
            unfold au in Hnonce_aps; simpl in Hnonce_aps.
            unfold au in Hmb_aps; simpl in Hmb_aps.
            rewrite Hpost. simpl.
            rewrite Hpre. simpl.
            rewrite Hnonce_aps. simpl.
            rewrite Hmb_aps. simpl.
            rewrite Hbal_eq.
            unfold debitN in HcurN.
            repeat
              match goal with
              | |- context[balance ((_nonce .= ?n) ?b)] =>
                  change (balance ((_nonce .= n) b)) with (balance (b &: _nonce .= n));
                  rewrite balance_update_nonce
              end.
            repeat
              match goal with
              | |- context[balance ((_coreAc .@ _block_account_storage .= ?st) ?b)] =>
                  change (balance ((_coreAc .@ _block_account_storage .= st) b)) with
                  (balance (b &: _coreAc .@ _block_account_storage .= st));
                rewrite balance_update_storage
            end.
            rewrite Hreserve_cfg.
            exact HcurN.
          }
          {
            inversion Hfv; subst; clear Hfv.
            destruct Hnon as [Hbal_assum _].
            simpl in Hbal_assum.
            rewrite Hmb in Hbal_assum. simpl in Hbal_assum.
            assert (Hbal_eq : balance csActual = origN).
            { unfold origN. symmetry. exact Hbal_assum. }
            pose proof H0 as H0'.
            rewrite Hpre in H0'. simpl in H0'.
            rewrite Hnonce in H0'. simpl in H0'.
            rewrite Hmb in H0'. simpl in H0'.
            inversion H0'; subst fv'; clear H0'.
            pose proof Hnonce as Hnonce_aps.
            pose proof Hmb as Hmb_aps.
            unfold au in Hnonce_aps; simpl in Hnonce_aps.
            unfold au in Hmb_aps; simpl in Hmb_aps.
            rewrite Hpost. simpl.
            rewrite Hpre. simpl.
            rewrite Hnonce_aps. simpl.
            rewrite Hmb_aps. simpl.
            rewrite Hbal_eq.
            unfold debitN in HcurN.
            repeat
              match goal with
              | |- context[balance ((_nonce .= ?n) ?b)] =>
                  change (balance ((_nonce .= n) b)) with (balance (b &: _nonce .= n));
                  rewrite balance_update_nonce
              end.
            repeat
              match goal with
              | |- context[balance ((_coreAc .@ _block_account_storage .= ?st) ?b)] =>
                  change (balance ((_coreAc .@ _block_account_storage .= st) b)) with
                    (balance (b &: _coreAc .@ _block_account_storage .= st));
                  rewrite balance_update_storage
              end.
            rewrite Hreserve_cfg.
            exact HcurN.
          }
        }
      }
      { (* fallback: base used *)
        exfalso.
        unfold au in Hpre'. simpl in Hpre'.
        rewrite Hpre in Hpre'. discriminate.
      }
    }
	    { (* relaxedValidation = false: base used *)
	      inversion Hfv; subst; clear Hfv.
	      destruct Hnon as [[Hbal_assum _Hmin_ok] _Hnonce].
	      simpl in Hbal_assum.
	      assert (Hbal_eq : balance csActual = origN).
	      { unfold origN. symmetry. exact Hbal_assum. }
      rewrite Hpost. simpl.
      repeat
        match goal with
        | |- context[balance ((_coreAc .@ _block_account_storage .= ?st) ?b)] =>
            change (balance ((_coreAc .@ _block_account_storage .= st) b)) with
              (balance (b &: _coreAc .@ _block_account_storage .= st));
            rewrite balance_update_storage
        end.
      rewrite Hbal_eq.
      unfold debitN in HcurN.
      rewrite Hreserve_cfg.
      exact HcurN.
    }
  }
  { (* account deleted; dummyAc balance = 0 *)
    subst fv.
    unfold accountFinalVal in Hfv.
    destruct (txUpdates au) as [[ptr0 [ptr1 upd]]|] eqn:Htx.
    { destruct (postTxState upd) as [csUpdated|] eqn:Hpost; simpl in Hfv.
      { exfalso.
        destruct (relaxedValidation st) eqn:Hrel; simpl in Hfv.
        { destruct (preTxState aps) eqn:Hpre'; simpl in Hfv; discriminate. }
        { discriminate. } }
      { assert (Hupd_eq : upd = nthElemVstackTop).
        { unfold au in Htx. simpl in Htx. inversion Htx. reflexivity. }
        assert (Hpost' : postTxState nthElemVstackTop = None).
        { rewrite <- Hupd_eq. exact Hpost. }
        exfalso.
        specialize (Hpost_none_pre_none Hpost').
        rewrite Hpre in Hpost_none_pre_none.
        discriminate. } }
    { simpl in Hfv. discriminate Hfv. }
  }
Qed.

Lemma finalBalSufficient_from_context_state
    (st: StateM) (ctx: MonadChainContext)
    (hist: ExtraAcStates)
    (preTxState0: StateOfAccounts)
    (i: N) (nthelemAddr: evm.address)
    (nthElemPtr nthElemVstackTopPtr: ptr)
    (nthElemVstackTop: UpdatedAccountState)
    (nthElemVstackTl: list (ptr * UpdatedAccountState))
    (tx: TxWithHdr) (loc: ptr) (aps: AssumedPreTxAccountState)
    (max_reserve: N) :
  NoDup (map fst (newStates st)) ->
  nth_error (newStates st) (N.to_nat i) =
    Some (nthelemAddr,
          (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
  mapModelLookup (preTxAssumedState st) nthelemAddr = Some (loc, aps) ->
  satisfiesAssumptions st preTxState0 ->
  historyConsistent ctx hist ->
  configuredReserveBalOfAddr hist nthelemAddr = max_reserve ->
  max_reserve = DefReserve ->
  (postTxState nthElemVstackTop = None -> preTxState aps = None) ->
  isAcSC (postTxState nthElemVstackTop) = false ->
  nthelemAddr <> sender tx ->
  (N.min max_reserve
     (original_balance_pessimistic_model_map
        (preTxAssumedState st) nthelemAddr)
   <= balanceOfAccount (postTxState nthElemVstackTop))%N ->
  (let orig :=
     original_balance_pessimistic_model_map (preTxAssumedState st) nthelemAddr in
   let cur := balanceOfAccount (postTxState nthElemVstackTop) in
   let debit := N.min max_reserve orig in
   match min_balance (assumExactness aps) with
   | Some m => (N.sub orig (N.sub cur debit) <= m)%N
   | None => True
   end) ->
  finalBalSufficient 3 (preTxState0, hist) (applyUpdates st preTxState0) tx nthelemAddr = true.
Proof using.
  intros Hnodup Hnth Hlookup Hsat Hhist Hreserve_hist Hreserve_at Hpost_none_pre_none Hsc Hneq Hbal Hminlb.
  assert (Hreserve_eq : DefReserve = max_reserve).
  { symmetry. exact Hreserve_at. }
  assert (Hreserve_cfg : configuredReserveBalOfAddr hist nthelemAddr = DefReserve).
  { rewrite Hreserve_hist. exact Hreserve_at. }
  eapply (@finalBalSufficient_from_context
            st ctx (preTxState0, hist) (preTxState0, hist) i nthelemAddr
            nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl tx loc aps).
  { exact Hnodup. }
  { exact Hnth. }
  { exact Hlookup. }
  { exact Hsat. }
  { exact Hhist. }
  { exact Hreserve_cfg. }
  { exact Hpost_none_pre_none. }
  { exact Hsc. }
  { exact Hneq. }
  { pose proof Hbal as Hbal'.
    rewrite <- Hreserve_eq in Hbal'.
    exact Hbal'. }
  { pose proof Hminlb as Hminlb'.
    rewrite <- Hreserve_eq in Hminlb'.
    exact Hminlb'. }
Qed.

Lemma NoDup_map_fst_newStates_of_map_key_ptr
    (st: StateM) :
  NoDup (map (fun x => (let '(a, (b, _)) := x in (a, b)).1) (newStates st)) ->
  NoDup (map fst (newStates st)).
Proof using.
  intro Hnodup.
  rewrite (map_ext
             (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) => fst x)
             (fun x => (let '(a, (b, _)) := x in (a, b)).1)).
  - exact Hnodup.
  - intros [addr [loc tl]]. reflexivity.
Qed.

Lemma allFinalBalSufficient_takeN_succ_update_assum_exactness_state_insert_gen
    (stm: StateM) (ctx: MonadChainContext) (hist: ExtraAcStates) (tx: TxWithHdr)
    (i: N) (addr: evm.address)
    (updates: gmap evm.address AssumptionExactness)
    (max_reserve: N)
    (nthElemPtr nthElemVstackTopPtr: ptr)
    (nthElemVstackTop: UpdatedAccountState)
    (nthElemVstackTl: list (ptr * UpdatedAccountState))
    (x: ptr) (x0: AssumedPreTxAccountState) :
  NoDup
    (map
       (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
          (let '(a, (b, _)) := x in (a, b)).1) (newStates stm)) ->
  nth_error (newStates stm) (N.to_nat i) =
    Some (addr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
  (forall preTxState : StateOfAccounts,
      satisfiesAssumptions (update_assum_exactness_state stm updates) preTxState ->
      true =
        allFinalBalSufficient 3 (preTxState, hist)
          (applyUpdates (update_assum_exactness_state stm updates) preTxState)
          (map fst (takeN i (newStates stm))) tx) ->
  mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) updates) addr =
    Some (x, x0) ->
  validModel (update_assum_exactness_state stm updates) ->
  isAcSC (postTxState nthElemVstackTop) = false ->
  addr <> sender tx ->
  (N.min max_reserve
     (original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) updates) addr)
   <= balanceOfAccount (postTxState nthElemVstackTop))%N ->
  max_reserve = DefReserve ->
  configuredReserveBalOfAddr hist addr = max_reserve ->
  forall preTxState : StateOfAccounts,
    let orig :=
      original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) updates) addr in
    let cur := balanceOfAccount (postTxState nthElemVstackTop) in
    let reserve := N.min max_reserve orig in
    let ex0 := min_balance_update (assumExactness x0) orig orig max_reserve in
    let ex := min_balance_update ex0 orig cur reserve in
    satisfiesAssumptions (update_assum_exactness_state stm (<[addr := ex]> updates)) preTxState ->
    historyConsistent ctx hist ->
    true =
      allFinalBalSufficient 3 (preTxState, hist)
        (applyUpdates (update_assum_exactness_state stm (<[addr := ex]> updates)) preTxState)
        (map fst (takeN (1 + i) (newStates stm))) tx.
Proof using.
  intros Hnodup Hnth Hb Hlookup Hvalid Hsc Hneq Hbal Hreserve_at Hreserve_hist preTxState.
  cbv zeta.
  intros Hsat Hhist.
  assert (Hnodup' :
      NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) (newStates stm)))).
  { rewrite map_map. simpl. exact Hnodup. }
  set (orig :=
      original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) updates) addr).
  set (cur := balanceOfAccount (postTxState nthElemVstackTop)).
  set (reserve := N.min max_reserve orig).
  set (ex0 := min_balance_update (assumExactness x0) orig orig max_reserve).
  set (ex := min_balance_update ex0 orig cur reserve).
  assert (Hok : check_min_balance_ok cur reserve = true).
  { unfold check_min_balance_ok.
    apply bool_decide_eq_true.
    exact Hbal. }
  assert (Hsome :
      is_Some
        (mapModelLookup
           (update_assum_exactness_map (preTxAssumedState stm) (<[addr := ex]> updates))
           addr)).
  { pose proof (mapModelLookup_update_assum_exactness_map_Some
                  (preTxAssumedState stm) updates addr x x0 Hlookup)
      as (aps0 & Horig & _Hpre & _Hprestorage & _Hassum).
    rewrite mapModelLookup_update_assum_exactness_map.
    rewrite Horig. simpl.
    rewrite lookup_insert. eauto. }
  assert (Hstr : assumption_exactness_stricter (assumExactness x0) ex).
  { unfold ex, ex0.
    apply (assumption_exactness_stricter_min_balance_update_twice
             (assumExactness x0) orig orig max_reserve orig cur reserve). }
  eapply (allFinalBalSufficient_takeN_succ
            (update_assum_exactness_state stm (<[addr := ex]> updates))
            ctx hist tx i addr nthElemPtr
            ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
  { intros preTxState0 Hsat0.
    eapply (allFinalBalSufficient_takeN_i_update_assum_exactness_state_insert
              stm ctx hist tx i addr nthElemPtr
              ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)
              updates ex preTxState0 x x0).
    { exact Hnodup'. }
    { exact Hnth. }
    { exact Hb. }
    { exact Hvalid. }
    { exact Hlookup. }
    { exact Hstr. }
    { exact Hsat0. }
  }
  { simpl. exact Hnth. }
  { intros preTxState0 Hsat0.
    assert (Hbal' :
        (N.min max_reserve
           (original_balance_pessimistic_model_map
              (update_assum_exactness_map (preTxAssumedState stm) (<[addr := ex]> updates)) addr)
         <= balanceOfAccount (postTxState nthElemVstackTop))%N).
    { rewrite original_balance_pessimistic_model_map_update_assum_exactness_map.
      rewrite (original_balance_pessimistic_model_map_update_assum_exactness_map
                 (preTxAssumedState stm) updates addr) in Hbal.
      exact Hbal. }
    assert (Hok' :
        check_min_balance_ok
          (balanceOfAccount (postTxState nthElemVstackTop))
          (N.min max_reserve
             (original_balance_pessimistic_model_map
                (update_assum_exactness_map (preTxAssumedState stm) (<[addr := ex]> updates))
                addr)) = true).
    { unfold check_min_balance_ok.
      apply bool_decide_eq_true.
      exact Hbal'. }
    destruct Hsome as [[loc1 aps1] Hlookup1].
    pose proof (mapModelLookup_update_assum_exactness_map_Some
                  (preTxAssumedState stm) (<[addr := ex]> updates)
                  addr loc1 aps1 Hlookup1)
      as (aps_pre & Hpre_lookup & Hpre_tx & _Hprestorage & Hassum1).
    pose proof (mapModelLookup_update_assum_exactness_map_Some
                  (preTxAssumedState stm) updates addr x x0 Hlookup)
      as (aps_pre0 & Hpre_lookup0 & Hpre_tx0 & _Hprestorage0 & _Hassum0).
    assert (Hpre_eq : aps_pre = aps_pre0).
    { rewrite Hpre_lookup in Hpre_lookup0. inversion Hpre_lookup0. reflexivity. }
    assert (Hmem :
        (addr,
         (nthElemPtr,
          (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ∈
        newStates stm).
    { apply list_elem_of_lookup_2 with (i := N.to_nat i).
      rewrite lookup_nth_error.
      exact Hnth. }
    assert (Hlookup_new :
        mapModelLookup (newStates stm) addr =
          Some (nthElemPtr,
                (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)).
    { apply elem_of_list_to_map_1.
      - apply NoDup_map_fst_newStates_of_map_key_ptr. exact Hnodup.
      - exact Hmem. }
    assert (Hpost_none_pre_none0 :
        postTxState nthElemVstackTop = None -> exec_specs.preTxState x0 = None).
    { eapply (validModel_post_none_of_lookup
                (update_assum_exactness_state stm updates)
                addr nthElemPtr
                ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)
                x x0).
      - exact Hvalid.
      - exact Hlookup_new.
      - exact Hlookup. }
    assert (Hpost_none_pre_none' :
        postTxState nthElemVstackTop = None -> exec_specs.preTxState aps1 = None).
    { intro Hpost.
      rewrite Hpre_tx.
      rewrite Hpre_eq.
      rewrite <- Hpre_tx0.
      exact (Hpost_none_pre_none0 Hpost). }
    assert (Hassum1' : assumExactness aps1 = ex).
    { rewrite Hassum1. rewrite lookup_insert.
      destruct (decide (addr = addr)) as [_|Haddr_neq];
        [|contradiction Haddr_neq; reflexivity].
      reflexivity. }
    assert (Hnodup_fst :
        NoDup (map fst (newStates (update_assum_exactness_state stm (<[addr := ex]> updates))))).
    { unfold update_assum_exactness_state; simpl.
      rewrite (map_ext (fun x => fst x)
                       (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
                          (let '(a, (b, _)) := x in (a, b)).1)).
      - exact Hnodup.
      - intros [a1 [b1 tl1]]. reflexivity. }
    assert (Hminlb :
        let orig0 :=
          original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm) (<[addr := ex]> updates)) addr in
        let cur0 := balanceOfAccount (postTxState nthElemVstackTop) in
        let debit0 := N.min max_reserve orig0 in
        match min_balance (assumExactness aps1) with
        | Some m => (N.sub orig0 (N.sub cur0 debit0) <= m)%N
        | None => True
        end).
    { rewrite Hassum1'.
      subst ex.
      simpl.
      assert (Horig0 :
          original_balance_pessimistic_model_map
            (update_assum_exactness_map (preTxAssumedState stm)
               (<[addr:=min_balance_update ex0 orig cur reserve]> updates)) addr = orig).
      { unfold orig.
        rewrite original_balance_pessimistic_model_map_update_assum_exactness_map.
        rewrite original_balance_pessimistic_model_map_update_assum_exactness_map.
        reflexivity. }
      rewrite Horig0.
      eapply min_balance_update_lower_bound.
      exact Hok. }
    eapply (@finalBalSufficient_from_context_state
              (update_assum_exactness_state stm (<[addr := ex]> updates))
              ctx hist preTxState0 i addr
              nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl
              tx loc1 aps1 max_reserve).
    { exact Hnodup_fst. }
    { exact Hnth. }
    { exact Hlookup1. }
    { exact Hsat0. }
    { exact Hhist. }
    { exact Hreserve_hist. }
    { exact Hreserve_at. }
    { exact Hpost_none_pre_none'. }
    { exact Hsc. }
    { exact Hneq. }
    { exact Hbal'. }
    { exact Hminlb. } }
  { exact Hsat. }
Qed.

Lemma allFinalBalSufficient_takeN_succ_update_assum_exactness_state_insert
    (stm: StateM) (ctx: MonadChainContext) (hist: ExtraAcStates) (tx: TxWithHdr)
    (i: N) (addr: evm.address)
    (updates: gmap evm.address AssumptionExactness)
    (nthElemPtr nthElemVstackTopPtr: ptr)
    (nthElemVstackTop: UpdatedAccountState)
    (nthElemVstackTl: list (ptr * UpdatedAccountState))
    (x: ptr) (x0: AssumedPreTxAccountState) :
  NoDup
    (map
       (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
          (let '(a, (b, _)) := x in (a, b)).1) (newStates stm)) ->
  nth_error (newStates stm) (N.to_nat i) =
    Some (addr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
  (forall preTxState : StateOfAccounts,
      satisfiesAssumptions (update_assum_exactness_state stm updates) preTxState ->
      historyConsistent ctx hist ->
      true =
        allFinalBalSufficient 3 (preTxState, hist)
          (applyUpdates (update_assum_exactness_state stm updates) preTxState)
          (map fst (takeN i (newStates stm))) tx) ->
  mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) updates) addr =
    Some (x, x0) ->
  validModel (update_assum_exactness_state stm updates) ->
  isAcSC (postTxState nthElemVstackTop) = false ->
  addr <> sender tx ->
  (N.min DefReserve
     (original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) updates) addr)
   <= balanceOfAccount (postTxState nthElemVstackTop))%N ->
  configuredReserveBalOfAddr hist addr = DefReserve ->
  forall preTxState : StateOfAccounts,
    let orig :=
      original_balance_pessimistic_model_map
        (update_assum_exactness_map (preTxAssumedState stm) updates) addr in
    let cur := balanceOfAccount (postTxState nthElemVstackTop) in
    let reserve := N.min DefReserve orig in
    let ex0 := min_balance_update (assumExactness x0) orig orig DefReserve in
    let ex := min_balance_update ex0 orig cur reserve in
    satisfiesAssumptions (update_assum_exactness_state stm (<[addr := ex]> updates)) preTxState ->
    historyConsistent ctx hist ->
    true =
      allFinalBalSufficient 3 (preTxState, hist)
        (applyUpdates (update_assum_exactness_state stm (<[addr := ex]> updates)) preTxState)
        (map fst (takeN (1 + i) (newStates stm))) tx.
Proof using.
  intros Hnodup Hnth Hb Hlookup Hvalid Hsc Hneq Hbal Hreserve_hist preTxState.
  cbv zeta.
  intros Hsat Hhist.
  eapply (allFinalBalSufficient_takeN_succ_update_assum_exactness_state_insert_gen
            stm ctx hist tx i addr updates DefReserve
            nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl x x0).
  { exact Hnodup. }
  { exact Hnth. }
  { intros preTxState0 Hsat0.
    exact (Hb preTxState0 Hsat0 Hhist). }
  { exact Hlookup. }
  { exact Hvalid. }
  { exact Hsc. }
  { exact Hneq. }
  { exact Hbal. }
  { reflexivity. }
  { exact Hreserve_hist. }
  { exact Hsat. }
  { exact Hhist. }
Qed.

(* Compatibility wrappers over duplicate core lemmas.
   These are candidates to inline at call sites later. *)
Lemma map_key_ptr_update_assum_exactness_at
    (m: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address)
    (f: AssumptionExactness -> AssumptionExactness) :
  map (fun p => let '(a, (b, _)) := p in (a, b))
      (update_assum_exactness_at addr f m) =
  map (fun p => let '(a, (b, _)) := p in (a, b)) m.
Proof using.
  exact (core_lemmas.map_key_ptr_update_assum_exactness_at m addr f).
Qed.

Lemma map_key_ptr_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness) :
  map (fun p => let '(a, (b, _)) := p in (a, b))
      (update_assum_exactness_map m updates) =
  map (fun p => let '(a, (b, _)) := p in (a, b)) m.
Proof using.
  exact (core_lemmas.map_key_ptr_update_assum_exactness_map m updates).
Qed.

Lemma map_key_ptr_check_min_original_balance_update
    (orig: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address) (max_reserve: N) :
  map (fun p => let '(a, (b, _)) := p in (a, b))
      (check_min_original_balance_update orig addr max_reserve) =
  map (fun p => let '(a, (b, _)) := p in (a, b)) orig.
Proof using.
  exact
    (core_lemmas.map_key_ptr_check_min_original_balance_update
       orig addr max_reserve).
Qed.

Lemma NoDup_map_fst_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness) :
  NoDup (map fst m) ->
  NoDup (map fst (update_assum_exactness_map m updates)).
Proof using.
  intro Hnodup.
  rewrite map_fst_update_assum_exactness_map.
  exact Hnodup.
Qed.

Lemma NoDup_map_fst_map_key_ptr_newStates
    (st: StateM) :
  NoDup (map fst (newStates st)) ->
  NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) (newStates st))).
Proof using.
  intro Hnodup.
  rewrite map_map.
  rewrite (map_ext (fun x : evm.address * (ptr * list (ptr * UpdatedAccountState)) =>
                      fst (let '(a, (b, _)) := x in (a, b))) fst).
  - exact Hnodup.
  - intros [addr [loc tl]]. reflexivity.
Qed.
  
(* prove the lemma below. feel free to add any relevant hypothesis in the comments to the lemma as a hypothesis.

  1 goal (ID 2029682)
  
  thread_info : biIndex
  _Σ : gFunctors
  Sigma : cpp_logic thread_info _Σ
  CU : genv
  MODd : source ⊧ CU
  _x_ : ptr → mpred
  ctx : MonadChainContext
  _i_ : nat
  statep : ptr
  stm : StateM
  pbs : AugmentedState
  bs : BlockState.glocs
  _H_ : (Z.of_nat _i_ < lengthZ (transactions (currentBlock (blocks ctx))))%Z
  nthelemAddr : evm.address
  nthElemPtr, nthElemVstackTopPtr : ptr
  nthElemVstackTop : UpdatedAccountState
  nthElemVstackTl : list (ptr * UpdatedAccountState)
  _t_ : gmap evm.address AssumptionExactness
  _x_27 : ptr
  GUARDS : GWs.GUARDS
  _st_0, st : std.vector.InternalState
  _H_0, _H_2 : (0 ≤ lengthZ (transactions (currentBlock (blocks ctx))))%Z
  _x_8 : bitsize.bound bitsize.W64 Unsigned (lengthZ (transactions (currentBlock (blocks ctx))))
  tx := nth _i_ (txsWithHdr (cblock ctx)) dummyTx : TxWithHdr
  Hx : InstantiationOfType Transaction tx.1
  _H_1, _H_3 : lengthN (transactions (currentBlock (blocks ctx))) = Z.to_N (lengthZ (transactions (currentBlock (blocks ctx))) - 0)
  _x_9, _x_10, _x_11 : bitsize.bound bitsize.W64 Unsigned (lengthZ (transactions (currentBlock (blocks ctx))))
  _H_4 : map fst (newStates stm) ⊆ map fst (preTxAssumedState stm)
  _H_5 : stateCodeMapInvariants stm
  _H_6 : NoDup (map (λ x : evm.address * (ptr * list (ptr * UpdatedAccountState)), (let '(a, (b, _)) := x in (a, b)).1) (newStates stm))
  _H_7 : [] ⊆ []
  t : N
  _H_8 : (t ≤ lengthN (newStates stm))%N
  _a_ : updates_stricter stm _t_
  a0 : gdom _t_ ⊆ map fst (takeN t (newStates stm))
  b :
    ∀ preTxState : AugmentedState,
      satisfiesAssumptions stm preTxState.1
      → historyConsistent ctx preTxState.2
        → true = allFinalBalSufficient 3 preTxState (applyUpdates stm preTxState.1) (map fst (takeN t (newStates stm))) tx
  _p_ : t ≠ lengthN (newStates stm)
  Hltnth :
    nth_error (newStates stm) (N.to_nat t) = Some (nthelemAddr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl))
  _H_9 : map fst (newStates stm) ⊆ map fst (preTxAssumedState stm)
  _H_10 :
    stateCodeMapInvariants
      {|
        relaxedValidation := relaxedValidation stm;
        preTxAssumedState := update_assum_exactness_map (preTxAssumedState stm) _t_;
        newStates := newStates stm;
        blockStatePtr := blockStatePtr stm;
        indices := indices stm;
        blockStateGloc := blockStateGloc stm;
        dbBlockStateCodeMapLb := dbBlockStateCodeMapLb stm;
        codeMap := codeMap stm
      |}
  _H_11 :
    NoDup
      (map (λ x : evm.address * (ptr * AssumedPreTxAccountState), (let '(a, (b, _)) := x in (a, b)).1)
         (update_assum_exactness_map (preTxAssumedState stm) _t_))
  Hvsnonempty : (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl ≠ []
  Heqsc : isAcSC (postTxState nthElemVstackTop) = false
  _H_13 :
    NoDup
      (map (λ x : evm.address * (ptr * AssumedPreTxAccountState), (let '(a, (b, _)) := x in (a, b)).1)
         (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr
            (DefReserve)))
  n, n0 : nthelemAddr ≠ sender tx
  _H_14 :
    is_Some
      (mapModelLookup
         (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr
            (DefReserve))
         nthelemAddr)
  _H_12 :
    (DefReserve
     `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr
     ≤ balanceOfAccount (postTxState nthElemVstackTop))%N
  x0 : AssumedPreTxAccountState
  H0 :
    update_assum_exactness_at nthelemAddr
      (λ ex : AssumptionExactness,
         min_balance_update ex (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr)
           (balanceOfAccount (postTxState nthElemVstackTop))
           (DefReserve
            `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr))
      (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr
         (DefReserve)) =
    update_assum_exactness_map (preTxAssumedState stm)
      (<[nthelemAddr:=(λ ex : AssumptionExactness,
                         min_balance_update ex
                           (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr)
                           (balanceOfAccount (postTxState nthElemVstackTop))
                           (DefReserve
                            `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_)
                                    nthelemAddr))
                        (min_balance_update (assumExactness x0)
                           (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr)
                           (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr)
                           (DefReserve))]>
         _t_)
  _H_15 :
    NoDup
      (map fst
         (map (λ pat : evm.address * (ptr * AssumedPreTxAccountState), let (a1, y) := pat in let (b0, _) := y in (a1, b0))
            (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) nthelemAddr
               (DefReserve))))
  i : N
  H : NoDup (map fst (map (λ '(a, (b, _)), (a, b)) (newStates stm)))
        ============================
        *)
  Lemma updatesPreserveSpine  (stm : StateM) (max_reserve : N)
    (nthelemAddr : evm.address) (nthElemVstackTop : UpdatedAccountState) (tt : gmap evm.address AssumptionExactness) 
    (x0 : AssumedPreTxAccountState):
      (map (λ pat : evm.address * (ptr * AssumedPreTxAccountState), let (a1, y) := pat in let (b0, _) := y in (a1, b0))
         (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) tt) nthelemAddr
            max_reserve)) =
      (map (λ '(a, (b, _)), (a, b))
         (update_assum_exactness_map (preTxAssumedState stm)
            (<[nthelemAddr:=min_balance_update
                              (min_balance_update (assumExactness x0)
                                 (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) tt)
                                    nthelemAddr)
                                 (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) tt)
                                    nthelemAddr)
                                 max_reserve)
                              (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) tt) nthelemAddr)
                              (balanceOfAccount (postTxState nthElemVstackTop))
                              (max_reserve
                               `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) tt)
                                       nthelemAddr)]>
               tt))).
  Proof.
    rewrite (map_key_ptr_check_min_original_balance_update
               (update_assum_exactness_map (preTxAssumedState stm) tt)
               nthelemAddr
               max_reserve).
    rewrite (map_key_ptr_update_assum_exactness_map (preTxAssumedState stm) tt).
    rewrite (map_key_ptr_update_assum_exactness_map
               (preTxAssumedState stm)
               (<[nthelemAddr:=min_balance_update
                                     (min_balance_update (assumExactness x0)
                                        (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) tt)
                                           nthelemAddr)
                                        (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) tt)
                                           nthelemAddr)
                                        max_reserve)
                                     (original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) tt)
                                        nthelemAddr)
                                     (balanceOfAccount (postTxState nthElemVstackTop))
                                     (max_reserve
                                      `min` original_balance_pessimistic_model_map (update_assum_exactness_map (preTxAssumedState stm) tt)
                                              nthelemAddr)]>
                tt)).
    reflexivity.
  Qed.
