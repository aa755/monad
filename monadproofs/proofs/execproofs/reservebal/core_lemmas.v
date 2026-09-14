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
Require Import stdpp.fin_map_dom.
Require Import monad.proofs.misc.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.cpp.spec.
From AAC_tactics Require Import AAC.
Require Import monad.proofs.exec_specs.
Import cQp_compat.
Set Warnings "+sl-impossible-patterns".
Set Default Goal Selector "!".
#[local] Open Scope lens_scope.

Local Transparent isSC isAcSC.
#[local] Arguments Lens.set : simpl never.
#[local] Arguments Lens.over : simpl never.
#[local] Arguments lens_compose : simpl never.

Lemma update_assum_exactness_map_insert
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness) :
  update_assum_exactness_map m (<[addr := ex]> updates) =
  update_assum_exactness_at addr (fun _ => ex) (update_assum_exactness_map m updates).
Proof using.
  unfold update_assum_exactness_map, update_assum_exactness_at.
  rewrite map_map.
  apply map_ext; intros [addr' [loc aps]]; simpl.
  destruct (decide (addr' = addr)) as [Heq|Hneq].
  - subst addr'. rewrite lookup_insert. simpl.
    destruct (decide (addr = addr)) as [_|Hneq]; [|contradiction Hneq; reflexivity].
    destruct (updates !! addr) as [ex'|] eqn:Hupd; simpl;
      (replace (asbool (addr = addr)) with true
         by (symmetry; apply bool_decide_eq_true_2; reflexivity));
      simpl; reflexivity.
  - rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq]. simpl.
    destruct (updates !! addr') as [ex'|] eqn:Hupd; simpl;
      (rewrite (bool_decide_eq_false_2 (addr' = addr) Hneq); simpl; reflexivity).
Qed.

Lemma update_assum_exactness_map_insert_at
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (ex: AssumptionExactness) :
  update_assum_exactness_at addr (fun _ => ex) (update_assum_exactness_map m updates) =
  update_assum_exactness_map m (<[addr := ex]> updates).
Proof using.
  symmetry; apply update_assum_exactness_map_insert.
Qed.

Lemma map_fst_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness) :
  map fst (update_assum_exactness_map m updates) = map fst m.
Proof using.
  unfold update_assum_exactness_map.
  rewrite map_map.
  apply map_ext; intros [addr [loc aps]]; simpl.
  destruct (updates !! addr); reflexivity.
Qed.

Lemma nodup_map_fst_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness) :
  NoDup
    (map (fun x : evm.address * (ptr * AssumedPreTxAccountState) =>
            (let '(a, (b, _)) := x in (a, b)).1)
         (update_assum_exactness_map m updates)) ->
  NoDup (map fst (update_assum_exactness_map m updates)).
Proof using.
  intro Hnodup.
  rewrite (map_ext (fun x => fst x)
                   (fun x : evm.address * (ptr * AssumedPreTxAccountState) =>
                      (let '(a, (b, _)) := x in (a, b)).1)).
  - exact Hnodup.
  - intros [addr [loc aps]]; reflexivity.
Qed.

Lemma map_key_ptr_update_assum_exactness_at
    (m: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address)
    (f: AssumptionExactness -> AssumptionExactness) :
  map (fun p => let '(a, (b, _)) := p in (a, b))
      (update_assum_exactness_at addr f m) =
  map (fun p => let '(a, (b, _)) := p in (a, b)) m.
Proof using.
  unfold update_assum_exactness_at.
  rewrite map_map.
  apply map_ext; intros [addr' [loc aps]]; simpl.
  destruct (bool_decide (addr' = addr)); reflexivity.
Qed.

Lemma map_key_ptr_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness) :
  map (fun p => let '(a, (b, _)) := p in (a, b))
      (update_assum_exactness_map m updates) =
  map (fun p => let '(a, (b, _)) := p in (a, b)) m.
Proof using.
  unfold update_assum_exactness_map.
  rewrite map_map.
  apply map_ext; intros [addr [loc aps]]; simpl.
  destruct (updates !! addr); reflexivity.
Qed.

Lemma nodup_map_fst_map_key_ptr
    {V} (m : list (evm.address * (ptr * V))) :
  NoDup (map (fun x => (let '(a, (b, _)) := x in (a, b)).1) m) ->
  NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) m)).
Proof using.
  intro Hnodup.
  rewrite map_map.
  replace (map (fun x => fst (let '(a, (b, _)) := x in (a, b))) m)
     with (map (fun x => (let '(a, (b, _)) := x in (a, b)).1) m)
    by (apply map_ext; intros [addr [loc v]]; reflexivity).
  exact Hnodup.
Qed.

Lemma map_key_ptr_check_min_original_balance_update
    (orig: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address) (max_reserve: N) :
  map (fun p => let '(a, (b, _)) := p in (a, b))
      (check_min_original_balance_update orig addr max_reserve) =
  map (fun p => let '(a, (b, _)) := p in (a, b)) orig.
Proof using.
  unfold check_min_original_balance_update.
  apply map_key_ptr_update_assum_exactness_at.
Qed.

Lemma nth_error_map_key_ptr
    {K V} (m : list (K * (ptr * V))) (i : nat)
    (k : K) (loc : ptr) (v : V) :
  nth_error m i = Some (k, (loc, v)) ->
  nth_error (map (fun '(a, (b, _)) => (a, b)) m) i = Some (k, loc).
Proof using.
  intro Hnth.
  rewrite nth_error_map.
  rewrite Hnth.
  reflexivity.
Qed.

Lemma nth_error_transactions_with_header_some
    (ctx : MonadChainContext) (i : nat) :
  (Z.of_nat i < lengthZ (transactions (currentBlock (blocks ctx))))%Z ->
  option_map (fun t0 : Transaction => (t0, header (currentBlock (blocks ctx))))
    (nth_error (transactions (currentBlock (blocks ctx))) i) =
  Some
    (nth i
      (map (fun t0 : Transaction => (t0, header (currentBlock (blocks ctx))))
         (transactions (currentBlock (blocks ctx))))
      dummyTx).
Proof using.
  intro Hlt.
  pose proof (drop_S2 (transactions (currentBlock (blocks ctx))) i Hlt)
    as [x [Hnth _]].
  rewrite lookup_nth_error in Hnth.
  rewrite Hnth.
  simpl.
  assert (Hnthm :
    nth_error
      (map (fun t0 : Transaction => (t0, header (currentBlock (blocks ctx))))
         (transactions (currentBlock (blocks ctx)))) i =
    Some (x, header (currentBlock (blocks ctx)))).
  { rewrite nth_error_map. now rewrite Hnth. }
  f_equal.
  symmetry.
  eapply nth_error_nth; eauto.
Qed.

Lemma nodup_map_fst_nth_error_eq_nat
    {K} (l: list (K * ptr)) (i j: nat) (k: K) (loc1 loc2: ptr) :
  NoDup (map fst l) ->
  nth_error l i = Some (k, loc1) ->
  nth_error l j = Some (k, loc2) ->
  i = j.
Proof using.
  revert i j k loc1 loc2.
  induction l as [|[k0 loc0] tl IH]; intros i j k loc1 loc2 Hnodup Hi Hj.
  - exfalso.
    rewrite nth_error_nil in Hi.
    discriminate.
  - simpl in Hnodup. inversion Hnodup as [|? ? Hnotin HnodupTl]; subst.
    destruct i as [|i']; destruct j as [|j']; simpl in Hi, Hj.
    + inversion Hi; inversion Hj; reflexivity.
    + inversion Hi; subst k loc1.
      assert (HjIn : In (k0, loc2) tl) by (eapply nth_error_In; eauto).
      exfalso. apply Hnotin.
      apply list_elem_of_In.
      exact (in_map fst _ _ HjIn).
    + inversion Hj; subst k loc2.
      assert (HiIn : In (k0, loc1) tl) by (eapply nth_error_In; eauto).
      exfalso. apply Hnotin.
      apply list_elem_of_In.
      exact (in_map fst _ _ HiIn).
    + apply f_equal. apply (IH i' j' k loc1 loc2); assumption.
Qed.

Lemma nodup_map_fst_nth_error_eq_N
    {K} (l: list (K * ptr)) (i j: N) (k: K) (loc1 loc2: ptr) :
  NoDup (map fst l) ->
  nth_error l (N.to_nat i) = Some (k, loc1) ->
  nth_error l (N.to_nat j) = Some (k, loc2) ->
  i = j.
Proof using.
  intros Hnodup Hi Hj.
  apply N2Nat.inj.
  eapply nodup_map_fst_nth_error_eq_nat; eauto.
Qed.

Section versionstack_helpers.
  Context {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ}.
  Context {CU : genv}.

Lemma current_match_to_versionstack_aux
    (statep: ptr) (stm: StateM) (i t: N)
    (nthelemAddr: evm.address) (nthElemPtr nthElemVstackTopPtr: ptr)
    (nthElemVstackTop: UpdatedAccountState) (nthElemVstackTl: list (ptr * UpdatedAccountState)) :
  NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) (newStates stm))) ->
  nth_error (newStates stm) (N.to_nat t) =
    Some (nthelemAddr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
  statep ,, o_field CU "monad::State::current_"
  |-> match nth_error (map (fun '(a, (b0, _)) => (a, b0)) (newStates stm)) (N.to_nat i) with
      | Some (k, loc) =>
          [| k = nthelemAddr |] ∗
          pureR
            (loc ,, pairSndOffset "monad::Address" "monad::VersionStack<monad::AccountState>"
             |-> (VersionStackSpineR "monad::AccountState" 1
                    (nthElemVstackTopPtr :: map fst nthElemVstackTl) ∗
                  pureR
                    (nthElemVstackTopPtr |-> UpdatedAccountStateR 1 nthElemVstackTop ∗
                     ([∗ list] p ∈ nthElemVstackTl,
                        let '(loc0, val0) := p in (loc0:ptr) |-> UpdatedAccountStateR 1 val0))))
      | None => False
      end
  |-- nthElemPtr ,, pairSndOffset "monad::Address" "monad::VersionStack<monad::AccountState>"
      |-> VersionStackR "monad::AccountState" UpdatedAccountStateR 1
           ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl) ** [| i = t |].
Proof using.
  intros Hnodup Hnth_state.
  destruct (nth_error (map (fun '(a, (b0, _)) => (a, b0)) (newStates stm)) (N.to_nat i))
    as [[k loc]|] eqn:Hnth_i; simpl.
  - try (work; done).
    rewrite _at_sep.
    rewrite _at_pureR.
    rewrite _at_only_provable.
    unfold VersionStackR.
    simpl.
    assert (Hnth_t :
              nth_error (map (fun '(a, (b, _)) => (a, b)) (newStates stm)) (N.to_nat t) =
                Some (nthelemAddr, nthElemPtr)).
    { rewrite nth_error_map.
      rewrite Hnth_state.
      reflexivity. }
    destruct (decide (k = nthelemAddr)) as [Hk|Hk].
    + rewrite (only_provable_True (k = nthelemAddr)); [| exact Hk].
      rewrite left_id.
      assert (Hnth_i' :
                nth_error (map (fun '(a, (b, _)) => (a, b)) (newStates stm)) (N.to_nat i) =
                  Some (nthelemAddr, loc)).
      { rewrite Hnth_i. now rewrite Hk. }
      pose proof (nodup_map_fst_nth_error_eq_N
                    (map (fun '(a, (b, _)) => (a, b)) (newStates stm))
                    i t nthelemAddr loc nthElemPtr
                    Hnodup Hnth_i' Hnth_t) as Hit.
      rewrite Hit in Hnth_i'.
      rewrite Hnth_t in Hnth_i'.
      inversion Hnth_i'; subst loc.
      rewrite (only_provable_True (i = t)); [| exact Hit ].
      rewrite right_id.
      reflexivity.
    + rewrite (only_provable_False (k = nthelemAddr) Hk).
      work.
  - simpl. work.
Qed.

Lemma current_match_to_versionstack
    (statep: ptr) (stm: StateM) (i t: N)
    (nthelemAddr: evm.address) (nthElemPtr nthElemVstackTopPtr: ptr)
    (nthElemVstackTop: UpdatedAccountState) (nthElemVstackTl: list (ptr * UpdatedAccountState)) :
  NoDup (map fst (map (fun '(a, (b, _)) => (a, b)) (newStates stm))) ->
  nth_error (newStates stm) (N.to_nat t) =
    Some (nthelemAddr, (nthElemPtr, (nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl)) ->
  statep ,, o_field CU "monad::State::current_"
  |-> match option_map (λ '(a, (b0, _)), (a, b0)) (nth_error (newStates stm) (N.to_nat i)) with
      | Some (k, loc) =>
          [| k = nthelemAddr |] ∗
          pureR
            (loc ,, pairSndOffset "monad::Address" "monad::VersionStack<monad::AccountState>"
             |-> (VersionStackSpineR "monad::AccountState" 1
                    (nthElemVstackTopPtr :: map fst nthElemVstackTl) ∗
                  pureR
                    (nthElemVstackTopPtr |-> UpdatedAccountStateR 1 nthElemVstackTop ∗
                     ([∗ list] p ∈ nthElemVstackTl,
                        let '(loc0, val0) := p in (loc0:ptr) |-> UpdatedAccountStateR 1 val0))))
      | None => False
      end
  |-- nthElemPtr ,, pairSndOffset "monad::Address" "monad::VersionStack<monad::AccountState>"
      |-> VersionStackR "monad::AccountState" UpdatedAccountStateR 1
           ((nthElemVstackTopPtr, nthElemVstackTop) :: nthElemVstackTl) ** [| i = t |].
Proof using.
  intros.
  rewrite <- nth_error_map.
  apply current_match_to_versionstack_aux; auto.
Qed.

End versionstack_helpers.

Lemma isAcSC_update_storage (ac: AccountM) (st: evm.storage) :
  isAcSC (Some (ac &: _coreAc .@ _block_account_storage .= st)) = isAcSC (Some ac).
Proof using.
  destruct ac as [coreAc inc rel del bal].
  unfold isAcSC.
  unfold Lens.set, lens_compose; simpl.
  destruct coreAc; simpl; reflexivity.
Qed.

Lemma isAcSC_update_balance (ac: AccountM) (bal: N) :
  isAcSC (Some (ac &: _balance .= bal)) = isAcSC (Some ac).
Proof using.
  destruct ac as [coreAc inc rel del bal0].
  unfold isAcSC.
  unfold Lens.set, lens_compose; simpl.
  destruct coreAc; simpl; reflexivity.
Qed.

Lemma isAcSC_update_nonce (ac: AccountM) (nonce: Z) :
  isAcSC (Some (ac &: _nonce .= nonce)) = isAcSC (Some ac).
Proof using.
  destruct ac as [coreAc inc rel del bal].
  unfold isAcSC.
  unfold Lens.set, lens_compose; simpl.
  destruct coreAc; simpl; reflexivity.
Qed.

Lemma isAcSC_true_of_code_hash (a1: AccountM) :
  isDelegationMarker (block.block_account_code (coreAc a1)) = false ->
  code_hash_of_program (block.block_account_code (coreAc a1)) <> 0%N ->
  isAcSC (Some a1) = true.
Proof using.
  intros Hdel Hhash.
  unfold isAcSC.
  rewrite Hdel; simpl.
  rewrite andb_true_r.
  apply bool_decide_eq_true_2.
  exact Hhash.
Qed.

(* TODO(dup): delete duplicate definitions/lemmas from reservebal/reserve_balance.v
   after the proof stabilizes.
   - update_assum_exactness_map
   - update_assum_exactness_map_insert / _insert_at
   - preTxAccountOf_map_update_assum_exactness_at
   - original_balance_pessimistic_model_map_update_assum_exactness_at
   - original_balance_pessimistic_model_map_check_min_original_balance_update
   - current_balance_pessimistic_model_stack_cons
   - mapModelLookup_is_Some_check_min_original_balance_update
*)

Lemma isDelegationMarker_false_of_length_zero (p: evm.program) :
  EVMOpSem.evm.program_length p = 0%Z ->
  isDelegationMarker p = false.
Proof using.
  intro Hlen.
  unfold isDelegationMarker.
  apply andb_false_intro1.
  apply Z.eqb_neq.
  intro Heq.
  rewrite Hlen in Heq.
  unfold delegation_indicator_size in Heq.
  discriminate Heq.
Qed.

Lemma code_entries_nonzero_of_stateCodeMapInvariants (st: StateM) :
  stateCodeMapInvariants st ->
  code_entries_nonzero (code_entries_of_state (newStates st)).
Proof using.
  intros Hinv.
  destruct Hinv as (_ & _ & _ & _ & Hnonzero).
  unfold code_entries_nonzero in *.
  intros h c Hmem Hhash.
  apply (Hnonzero h c);
    unfold all_code_entries;
    repeat (apply elem_of_app; left);
    assumption.
Qed.

Local Opaque isAcSC.

Definition hist_constant_default_reserve (hist: ExtraAcStates) : Prop :=
  True.

Lemma historyConsistent_of_hist_with_default_reserve
    (ctx: MonadChainContext) (hist: ExtraAcStates) :
  historyConsistent ctx hist /\ hist_constant_default_reserve hist ->
  historyConsistent ctx hist.
Proof.
  intros [H _]. exact H.
Qed.

Lemma hist_constant_default_reserve_of_conj
    (ctx: MonadChainContext) (hist: ExtraAcStates) :
  historyConsistent ctx hist /\ hist_constant_default_reserve hist ->
  hist_constant_default_reserve hist.
Proof.
  intros [_ H]. exact H.
Qed.

#[export] Hint Resolve
  historyConsistent_of_hist_with_default_reserve
  hist_constant_default_reserve_of_conj : pure.

Lemma mapModelLookup_is_Some_of_mem
    {K V} `{Countable K} (m: MapModel K V) (k: K) :
  k ∈ map fst m ->
  is_Some (mapModelLookup m k).
Proof using.
  induction m as [|[k' v'] tl IH]; intro Hmem.
  - apply elem_of_nil in Hmem. contradiction.
  - simpl in Hmem.
    destruct (decide (k = k')) as [->|Hneq].
    + rewrite /mapModelLookup /=. simpl. rewrite lookup_insert.
      destruct (decide (k' = k')) as [_|Hneq]; [|contradiction Hneq; reflexivity].
      eauto.
    + rewrite /mapModelLookup /=. simpl.
      rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
      apply IH.
      apply elem_of_cons in Hmem as [Hmem|Hmem]; [contradiction|exact Hmem].
Qed.

Lemma mapModelLookup_is_Some_of_subset_nth
    {K V1 V2} `{Countable K} (m1 : MapModel K V1) (m2 : MapModel K V2)
    (i: nat) (k: K) (v: ModelWithPtr V1) :
  map fst m1 ⊆ map fst m2 ->
  nth_error m1 i = Some (k, v) ->
  is_Some (mapModelLookup m2 k).
Proof using.
  intros Hsubset Hnth.
  assert (Hmem : (k, v) ∈ m1).
  { apply list_elem_of_lookup_2 with (i := i).
    rewrite lookup_nth_error. exact Hnth. }
  assert (Hin : k ∈ map fst m1).
  { apply (proj2 (list_elem_of_fmap _ _ _)).
    exists (k, v). split; [reflexivity|exact Hmem]. }
  apply mapModelLookup_is_Some_of_mem.
  apply Hsubset. exact Hin.
Qed.

Lemma mapModelLookup_is_Some_implies_mem
    {K V} `{Countable K} (m: MapModel K V) (k: K) :
  is_Some (mapModelLookup m k) ->
  k ∈ map fst m.
Proof using.
  induction m as [|[k' v'] tl IH]; intro Hsome.
  - rewrite /mapModelLookup /= in Hsome.
    destruct Hsome as [v Hlookup].
    rewrite lookup_empty in Hlookup. discriminate.
  - rewrite /mapModelLookup /= in Hsome.
    destruct (decide (k = k')) as [Heq|Hneq];
      [subst k'; simpl; left; reflexivity
      |rewrite lookup_insert_ne in Hsome;
         [|intro Heq'; apply Hneq; symmetry; exact Heq'];
       simpl; right; exact (IH Hsome)].
Qed.

Lemma map_fst_update_assum_exactness_at
    (addr: evm.address) (f: AssumptionExactness -> AssumptionExactness)
    (m: MapModel evm.address AssumedPreTxAccountState) :
  map fst (update_assum_exactness_at addr f m) = map fst m.
Proof using.
  induction m as [|[addr' [loc aps]] tl IH]; simpl; [reflexivity|].
  destruct (bool_decide (addr' = addr)); simpl; f_equal; exact IH.
Qed.

Lemma mapModelLookup_is_Some_update_assum_exactness_at
    (addr: evm.address) (f: AssumptionExactness -> AssumptionExactness)
    (m: MapModel evm.address AssumedPreTxAccountState) :
  is_Some (mapModelLookup m addr) ->
  is_Some (mapModelLookup (update_assum_exactness_at addr f m) addr).
Proof using.
  intro Hsome.
  apply mapModelLookup_is_Some_of_mem.
  rewrite map_fst_update_assum_exactness_at.
  exact (mapModelLookup_is_Some_implies_mem m addr Hsome).
Qed.

Lemma mapModelLookup_is_Some_check_min_original_balance_update
    (orig: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address) (max_reserve: N) :
  is_Some (mapModelLookup orig addr) ->
  is_Some
    (mapModelLookup
       (check_min_original_balance_update orig addr max_reserve) addr).
Proof using.
  intro Hsome.
  unfold check_min_original_balance_update.
  apply mapModelLookup_is_Some_update_assum_exactness_at.
  exact Hsome.
Qed.

Lemma mapModelLookup_exists_of_is_Some
    (m: MapModel evm.address AssumedPreTxAccountState) (addr: evm.address) :
  is_Some (mapModelLookup m addr) ->
  exists loc aps, mapModelLookup m addr = Some (loc, aps).
Proof using.
  intros [v Hv]. destruct v as [loc aps]. exists loc, aps. exact Hv.
Qed.

Lemma mapModelLookup_eq_of_elem
    {K V} `{Countable K} (m: MapModel K V) (k: K)
    (v v': ModelWithPtr V) :
  NoDup (map fst m) ->
  mapModelLookup m k = Some v ->
  (k, v') ∈ m ->
  v' = v.
Proof using.
  intros Hnodup Hlookup Hmem.
  unfold mapModelLookup in Hlookup.
  have Hmem' : (list_to_map m : gmap K (ModelWithPtr V)) !! k = Some v' :=
    elem_of_list_to_map_1 _ _ _ Hnodup Hmem.
  rewrite Hmem' in Hlookup. inversion Hlookup; reflexivity.
Qed.

Lemma update_assum_exactness_at_const_of_lookup
    (m: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address) (f: AssumptionExactness -> AssumptionExactness)
    (loc: ptr) (aps: AssumedPreTxAccountState) :
  NoDup (map fst m) ->
  mapModelLookup m addr = Some (loc, aps) ->
  update_assum_exactness_at addr f m =
  update_assum_exactness_at addr (fun _ => f (assumExactness aps)) m.
Proof using.
  intros Hnodup Hlookup.
  unfold update_assum_exactness_at.
  apply map_ext_in; intros [addr' [loc' aps']] Hin; simpl.
  destruct (decide (addr' = addr)) as [Heq|Hneq].
  - subst addr'. rewrite (bool_decide_eq_true_2 (addr = addr)); [|reflexivity]. simpl.
    apply list_elem_of_In in Hin.
    pose proof (mapModelLookup_eq_of_elem m addr (loc, aps) (loc', aps') Hnodup Hlookup Hin)
      as Heq.
    inversion Heq; subst.
    reflexivity.
  - rewrite (bool_decide_eq_false_2 (addr' = addr) Hneq). simpl. reflexivity.
Qed.

Lemma update_assum_exactness_at_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (f: AssumptionExactness -> AssumptionExactness)
    (loc: ptr) (aps: AssumedPreTxAccountState) :
  NoDup (map fst (update_assum_exactness_map m updates)) ->
  mapModelLookup (update_assum_exactness_map m updates) addr = Some (loc, aps) ->
  update_assum_exactness_at addr f (update_assum_exactness_map m updates) =
  update_assum_exactness_map m (<[addr := f (assumExactness aps)]> updates).
Proof using.
  intros Hnodup Hlookup.
  pose proof (update_assum_exactness_at_const_of_lookup
    (update_assum_exactness_map m updates) addr f loc aps Hnodup Hlookup) as Hconst.
  rewrite Hconst.
  apply update_assum_exactness_map_insert_at.
Qed.

Lemma update_assum_exactness_at_compose
    (addr: evm.address)
    (f g: AssumptionExactness -> AssumptionExactness)
    (m: MapModel evm.address AssumedPreTxAccountState) :
  update_assum_exactness_at addr f (update_assum_exactness_at addr g m) =
  update_assum_exactness_at addr (fun ex => f (g ex)) m.
Proof using.
  unfold update_assum_exactness_at.
  rewrite map_map.
  apply map_ext; intros [addr' [loc aps]]; simpl.
  destruct (decide (addr' = addr)) as [Heq|Hneq].
  - subst addr'. rewrite (bool_decide_eq_true_2 (addr = addr)); [|reflexivity]. simpl.
    rewrite (bool_decide_eq_true_2 (addr = addr)); [|reflexivity]. simpl.
    reflexivity.
  - rewrite (bool_decide_eq_false_2 (addr' = addr) Hneq); simpl.
    rewrite (bool_decide_eq_false_2 (addr' = addr) Hneq); simpl.
    reflexivity.
Qed.

Lemma update_assum_exactness_at_check_min_original_balance_update
    (orig: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address) (max_reserve: N)
    (f: AssumptionExactness -> AssumptionExactness) :
  update_assum_exactness_at addr f (check_min_original_balance_update orig addr max_reserve) =
  update_assum_exactness_at addr
    (fun ex =>
       f (min_balance_update ex
            (original_balance_pessimistic_model_map orig addr)
            (original_balance_pessimistic_model_map orig addr)
            max_reserve)) orig.
Proof using.
  unfold check_min_original_balance_update.
  set (orig_bal := original_balance_pessimistic_model_map orig addr).
  rewrite (update_assum_exactness_at_compose addr f
    (fun ex => min_balance_update ex orig_bal orig_bal max_reserve) orig).
  subst orig_bal. reflexivity.
Qed.

Lemma update_assum_exactness_at_check_min_original_balance_update_to_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (max_reserve: N)
    (f: AssumptionExactness -> AssumptionExactness)
    (loc: ptr) (aps: AssumedPreTxAccountState) :
  NoDup (map fst (update_assum_exactness_map m updates)) ->
  mapModelLookup (update_assum_exactness_map m updates) addr = Some (loc, aps) ->
  update_assum_exactness_at addr f
    (check_min_original_balance_update (update_assum_exactness_map m updates) addr max_reserve) =
  update_assum_exactness_map m
    (<[addr :=
        f (min_balance_update (assumExactness aps)
             (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
             (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
             max_reserve)]> updates).
Proof using.
  intros Hnodup Hlookup.
  rewrite (update_assum_exactness_at_check_min_original_balance_update
    (update_assum_exactness_map m updates) addr max_reserve f).
  rewrite (update_assum_exactness_at_update_assum_exactness_map
    m updates addr
    (fun ex =>
       f (min_balance_update ex
            (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
            (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
            max_reserve))
    loc aps Hnodup Hlookup).
  reflexivity.
Qed.

Lemma update_assum_exactness_at_check_min_original_balance_update_to_map_exists
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) (max_reserve: N)
    (f: AssumptionExactness -> AssumptionExactness) :
  NoDup (map fst (update_assum_exactness_map m updates)) ->
  is_Some (mapModelLookup (update_assum_exactness_map m updates) addr) ->
  exists (loc: ptr) (aps: AssumedPreTxAccountState),
    mapModelLookup (update_assum_exactness_map m updates) addr = Some (loc, aps) /\
    update_assum_exactness_at addr f
      (check_min_original_balance_update (update_assum_exactness_map m updates) addr max_reserve) =
    update_assum_exactness_map m
      (<[addr :=
          f (min_balance_update (assumExactness aps)
               (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
               (original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr)
               max_reserve)]> updates).
Proof using.
  intros Hnodup Hsome.
  destruct Hsome as [[loc aps] Hlookup].
  exists loc, aps.
  split; auto.
  eapply update_assum_exactness_at_check_min_original_balance_update_to_map; eauto.
Qed.

Lemma preTxAccountOf_map_update_assum_exactness_at
    (addr k: evm.address) (f: AssumptionExactness -> AssumptionExactness)
    (m: MapModel evm.address AssumedPreTxAccountState) :
  preTxAccountOf_map (update_assum_exactness_at addr f m) k =
  preTxAccountOf_map m k.
Proof using.
  unfold preTxAccountOf_map, mapModelLookup.
  induction m as [|[k' [loc aps]] tl IH]; simpl; [reflexivity|].
  simpl update_assum_exactness_at.
  destruct (bool_decide (k' = addr)) eqn:Haddr; simpl;
    destruct (decide (k = k')) as [Heq|Hneq].
  {
    subst k. repeat rewrite lookup_insert.
    repeat match goal with
    | |- context[decide (?x = ?x)] =>
        destruct (decide (x = x)) as [_|Hfalse];
        [|contradiction Hfalse; reflexivity]
    end.
    reflexivity.
  }
  {
    rewrite lookup_insert_ne; [|intro Heq'; apply Hneq; symmetry; exact Heq'].
    rewrite lookup_insert_ne; [|intro Heq'; apply Hneq; symmetry; exact Heq'].
    exact IH.
  }
  {
    subst k. repeat rewrite lookup_insert.
    repeat match goal with
    | |- context[decide (?x = ?x)] =>
        destruct (decide (x = x)) as [_|Hfalse];
        [|contradiction Hfalse; reflexivity]
    end.
    reflexivity.
  }
  {
    rewrite lookup_insert_ne; [|intro Heq'; apply Hneq; symmetry; exact Heq'].
    rewrite lookup_insert_ne; [|intro Heq'; apply Hneq; symmetry; exact Heq'].
    exact IH.
  }
Qed.

Lemma preTxAccountOf_map_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) :
  preTxAccountOf_map (update_assum_exactness_map m updates) addr =
  preTxAccountOf_map m addr.
Proof using.
  unfold preTxAccountOf_map, mapModelLookup.
  induction m as [|[addr0 [loc0 aps0]] tl IH]; simpl; [reflexivity|].
  simpl update_assum_exactness_map.
  destruct (decide (addr = addr0)) as [Heq|Hneq].
  - subst addr.
    destruct (updates !! addr0) as [ex|] eqn:Hupd; simpl;
      repeat rewrite lookup_insert;
      repeat match goal with
      | |- context[decide (?x = ?x)] =>
          destruct (decide (x = x)) as [_|Hfalse];
          [|contradiction Hfalse; reflexivity]
      end;
      reflexivity.
  - destruct (updates !! addr0) as [ex|] eqn:Hupd; simpl.
    + rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
      rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
      exact IH.
    + rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
      rewrite lookup_insert_ne; [|intro Heq; apply Hneq; symmetry; exact Heq].
      exact IH.
Qed.

Lemma original_balance_pessimistic_model_map_update_assum_exactness_at
    (addr k: evm.address) (f: AssumptionExactness -> AssumptionExactness)
    (m: MapModel evm.address AssumedPreTxAccountState) :
  original_balance_pessimistic_model_map (update_assum_exactness_at addr f m) k =
  original_balance_pessimistic_model_map m k.
Proof using.
  unfold original_balance_pessimistic_model_map.
  rewrite preTxAccountOf_map_update_assum_exactness_at.
  reflexivity.
Qed.

Lemma original_balance_pessimistic_model_map_update_assum_exactness_map
    (m: MapModel evm.address AssumedPreTxAccountState)
    (updates: gmap evm.address AssumptionExactness)
    (addr: evm.address) :
  original_balance_pessimistic_model_map (update_assum_exactness_map m updates) addr =
  original_balance_pessimistic_model_map m addr.
Proof using.
  unfold original_balance_pessimistic_model_map.
  rewrite preTxAccountOf_map_update_assum_exactness_map.
  reflexivity.
Qed.

Lemma original_balance_pessimistic_model_map_check_min_original_balance_update
    (orig: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address) (max_reserve: N) :
  original_balance_pessimistic_model_map
    (check_min_original_balance_update orig addr max_reserve) addr =
  original_balance_pessimistic_model_map orig addr.
Proof using.
  unfold check_min_original_balance_update.
  rewrite original_balance_pessimistic_model_map_update_assum_exactness_at.
  reflexivity.
Qed.

Lemma current_balance_pessimistic_model_stack_cons
    (loc: ptr) (upd: UpdatedAccountState) (tl: list (ptr * UpdatedAccountState)) :
  current_balance_pessimistic_model_stack ((loc, upd) :: tl) =
  balanceOfAccount (postTxState upd).
Proof using.
  unfold current_balance_pessimistic_model_stack, recentAccountOf_stack.
  simpl. reflexivity.
Qed.


Lemma isSCpreserved (stm: StateM) (preTxState1 preTxState2: StateOfAccounts)
    (addr: evm.address) (au: TxAssumptionsAndUpdates) :
  assumptionAndUpdateOfAddr stm addr = Some au ->
  txUpdates au <> None ->
  isSC (applyUpdates stm preTxState1) addr = isSC (applyUpdates stm preTxState2) addr.
Proof using.
  intros Hlookup Hupdates.
  unfold isSC, applyUpdates.
  repeat rewrite Hlookup.
  destruct (txUpdates au) as [[ptr1 [ptr2 txUpds]]|] eqn:Htx; [|exfalso; apply Hupdates; reflexivity].
  unfold accountFinalVal.
  rewrite Htx.
  simpl.
  destruct (postTxState txUpds) as [csUpdated|] eqn:Hpost; simpl; [|reflexivity].
  destruct (relaxedValidation stm) eqn:Hrel; simpl.
  - destruct (preTxState (preAssumption au)) as [csAssumed|] eqn:Hassumed; simpl;
      [|repeat (rewrite isAcSC_update_storage); reflexivity].
    destruct (isNone (min_balance (assumExactness (preAssumption au)))) eqn:Hmin; simpl.
    + destruct (nonce_exact (assumExactness (preAssumption au))) eqn:Hnonce_exact; simpl.
      * repeat (rewrite isAcSC_update_storage). reflexivity.
      * repeat (rewrite isAcSC_update_nonce). repeat (rewrite isAcSC_update_storage). reflexivity.
    + destruct (nonce_exact (assumExactness (preAssumption au))) eqn:Hnonce_exact; simpl.
      * repeat (rewrite isAcSC_update_balance). repeat (rewrite isAcSC_update_storage). reflexivity.
      * repeat (rewrite isAcSC_update_nonce). repeat (rewrite isAcSC_update_balance). repeat (rewrite isAcSC_update_storage). reflexivity.
  - repeat (rewrite isAcSC_update_storage). reflexivity.
Qed.

Lemma isSCpreserved_nth
    (stm: StateM) (preTxState1 preTxState2: StateOfAccounts)
    (t: N) (addr: evm.address)
    (ptr_loc topPtr: ptr) (top: UpdatedAccountState)
    (tl: list (ptr * UpdatedAccountState)) :
  NoDup (map fst (newStates stm)) ->
  map fst (newStates stm) ⊆ map fst (preTxAssumedState stm) ->
  nth_error (newStates stm) (N.to_nat t) =
    Some (addr, (ptr_loc, (topPtr, top) :: tl)) ->
  isSC (applyUpdates stm preTxState1) addr = isSC (applyUpdates stm preTxState2) addr.
Proof using.
  intros Hnodup Hsubset Hnth.
  assert (Hmem :
      (addr, (ptr_loc, (topPtr, top) :: tl)) ∈ newStates stm).
  { apply list_elem_of_lookup_2 with (i := N.to_nat t).
    rewrite lookup_nth_error.
    exact Hnth. }
  assert (Hlookup_new : newStates stm !! addr = Some (ptr_loc, (topPtr, top) :: tl)).
  { apply elem_of_list_to_map_1; [exact Hnodup|exact Hmem]. }
  assert (Hin_new : addr ∈ map fst (newStates stm)).
  { apply (proj2 (list_elem_of_fmap _ _ _)).
    exists (addr, (ptr_loc, (topPtr, top) :: tl)).
    split; [reflexivity|exact Hmem]. }
  assert (Hin_pre : addr ∈ map fst (preTxAssumedState stm)) by (apply Hsubset; exact Hin_new).
  assert (Hpre_dom :
      addr ∈ dom (list_to_map (preTxAssumedState stm) : gmap evm.address (ModelWithPtr AssumedPreTxAccountState))).
  { rewrite dom_list_to_map. apply elem_of_list_to_set. exact Hin_pre. }
  destruct (preTxAssumedState stm !! addr) as [p|] eqn:Hpre.
  2:{
    assert (Hnone :
        ((list_to_map (preTxAssumedState stm)
          : gmap evm.address (ModelWithPtr AssumedPreTxAccountState)) !! addr) = None).
    { change (preTxAssumedState stm !! addr)
        with ((list_to_map (preTxAssumedState stm)
               : gmap evm.address (ModelWithPtr AssumedPreTxAccountState)) !! addr).
      exact Hpre. }
    assert (Hnot : addr ∉ dom (list_to_map (preTxAssumedState stm)
                              : gmap evm.address (ModelWithPtr AssumedPreTxAccountState))).
    { apply not_elem_of_dom_2. exact Hnone. }
    exact (False_rect _ (Hnot Hpre_dom)).
  }
  set (au := {| preAssumption := snd p;
                originalLoc := fst p;
                txUpdates := Some (ptr_loc, (topPtr, top)) |}).
  assert (Hlookup : assumptionAndUpdateOfAddr stm addr = Some au).
  { unfold assumptionAndUpdateOfAddr. rewrite Hpre. simpl.
    rewrite Hlookup_new. simpl. reflexivity. }
  assert (Htx : txUpdates au <> None) by discriminate.
  exact (isSCpreserved stm preTxState1 preTxState2 addr au Hlookup Htx).
Qed.

Lemma isSC_applyUpdates_true_nth
    (stm: StateM) (preTxSt: StateOfAccounts)
    (t: N) (addr: evm.address)
    (ptr_loc topPtr: ptr) (top: UpdatedAccountState)
    (tl: list (ptr * UpdatedAccountState)) (a1: AccountM) :
  NoDup (map fst (newStates stm)) ->
  map fst (newStates stm) ⊆ map fst (preTxAssumedState stm) ->
  nth_error (newStates stm) (N.to_nat t) =
    Some (addr, (ptr_loc, (topPtr, top) :: tl)) ->
  postTxState top = Some a1 ->
  isAcSC (Some a1) = true ->
  isSC (applyUpdates stm preTxSt) addr = true.
Proof using.
  intros Hnodup Hsubset Hnth Hpost Hsc_a1.
  assert (Hmem :
      (addr, (ptr_loc, (topPtr, top) :: tl)) ∈ newStates stm).
  { apply list_elem_of_lookup_2 with (i := N.to_nat t).
    rewrite lookup_nth_error.
    exact Hnth. }
  assert (Hlookup_new : newStates stm !! addr = Some (ptr_loc, (topPtr, top) :: tl)).
  { apply elem_of_list_to_map_1; [exact Hnodup|exact Hmem]. }
  assert (Hin_new : addr ∈ map fst (newStates stm)).
  { apply (proj2 (list_elem_of_fmap _ _ _)).
    exists (addr, (ptr_loc, (topPtr, top) :: tl)).
    split; [reflexivity|exact Hmem]. }
  assert (Hin_pre : addr ∈ map fst (preTxAssumedState stm)) by (apply Hsubset; exact Hin_new).
  assert (Hpre_dom :
      addr ∈ dom (list_to_map (preTxAssumedState stm) : gmap evm.address (ModelWithPtr AssumedPreTxAccountState))).
  { rewrite dom_list_to_map. apply elem_of_list_to_set. exact Hin_pre. }
  destruct (preTxAssumedState stm !! addr) as [p|] eqn:Hpre.
  2:{
    assert (Hnone :
        ((list_to_map (preTxAssumedState stm)
          : gmap evm.address (ModelWithPtr AssumedPreTxAccountState)) !! addr) = None).
    { change (preTxAssumedState stm !! addr)
        with ((list_to_map (preTxAssumedState stm)
               : gmap evm.address (ModelWithPtr AssumedPreTxAccountState)) !! addr).
      exact Hpre. }
    assert (Hnot : addr ∉ dom (list_to_map (preTxAssumedState stm)
                              : gmap evm.address (ModelWithPtr AssumedPreTxAccountState))).
    { apply not_elem_of_dom_2. exact Hnone. }
    exact (False_rect _ (Hnot Hpre_dom)).
  }
  set (au := {| preAssumption := snd p;
                originalLoc := fst p;
                txUpdates := Some (ptr_loc, (topPtr, top)) |}).
  assert (Hlookup : assumptionAndUpdateOfAddr stm addr = Some au).
  { unfold assumptionAndUpdateOfAddr. rewrite Hpre. simpl.
    rewrite Hlookup_new. simpl. reflexivity. }
  unfold isSC, applyUpdates.
  rewrite Hlookup.
  set (fv := accountFinalVal (relaxedValidation stm) au (Some (preTxSt addr))).
  change (isAcSC (Some (match fv with | None => dummyAc | Some fv' => fv' end)) = true).
  destruct fv as [fv'|] eqn:Hfv; simpl.
  - unfold fv in Hfv.
    unfold accountFinalVal in Hfv.
    unfold au in Hfv; simpl in Hfv.
    rewrite Hpost in Hfv.
    destruct (relaxedValidation stm) eqn:Hrel; simpl in Hfv.
    + destruct (exec_specs.preTxState (preAssumption au)) as [csAssumed|] eqn:Hassumed;
        simpl in Hfv.
      * unfold au in Hassumed; simpl in Hassumed.
        rewrite Hassumed in Hfv; simpl in Hfv.
        destruct (isNone (min_balance (assumExactness (preAssumption au)))) eqn:Hmin; simpl in Hfv.
        -- unfold au in Hmin; simpl in Hmin.
           rewrite Hmin in Hfv; simpl in Hfv.
           destruct (nonce_exact (assumExactness (preAssumption au))) eqn:Hnonce; simpl in Hfv.
           ++ unfold au in Hnonce; simpl in Hnonce.
              rewrite Hnonce in Hfv; simpl in Hfv.
              inversion Hfv; subst fv'.
              repeat rewrite isAcSC_update_storage. exact Hsc_a1.
           ++ unfold au in Hnonce; simpl in Hnonce.
              rewrite Hnonce in Hfv; simpl in Hfv.
              inversion Hfv; subst fv'.
              repeat rewrite isAcSC_update_nonce; repeat rewrite isAcSC_update_storage; exact Hsc_a1.
        -- unfold au in Hmin; simpl in Hmin.
           rewrite Hmin in Hfv; simpl in Hfv.
           destruct (nonce_exact (assumExactness (preAssumption au))) eqn:Hnonce; simpl in Hfv.
           ++ unfold au in Hnonce; simpl in Hnonce.
              rewrite Hnonce in Hfv; simpl in Hfv.
              inversion Hfv; subst fv'.
              repeat rewrite isAcSC_update_balance; repeat rewrite isAcSC_update_storage; exact Hsc_a1.
           ++ unfold au in Hnonce; simpl in Hnonce.
              rewrite Hnonce in Hfv; simpl in Hfv.
              inversion Hfv; subst fv'.
              repeat rewrite isAcSC_update_nonce; repeat rewrite isAcSC_update_balance;
              repeat rewrite isAcSC_update_storage; exact Hsc_a1.
      * unfold au in Hassumed; simpl in Hassumed.
        rewrite Hassumed in Hfv; simpl in Hfv.
        inversion Hfv; subst fv'.
        repeat rewrite isAcSC_update_storage; exact Hsc_a1.
    + inversion Hfv; subst fv'.
      repeat rewrite isAcSC_update_storage; exact Hsc_a1.
  - unfold fv in Hfv.
    assert (Hsome :
              exists v,
                accountFinalVal (relaxedValidation stm) au (Some (preTxSt addr)) =
                Some v).
    { unfold accountFinalVal; unfold au; simpl.
      rewrite Hpost.
      destruct (relaxedValidation stm) eqn:Hrel; simpl.
      - destruct (exec_specs.preTxState (preAssumption au)) as [csAssumed|] eqn:Hassumed; simpl.
        + rewrite Hassumed. eexists; reflexivity.
        + rewrite Hassumed. eexists; reflexivity.
      - eexists; reflexivity.
    }
    destruct Hsome as [v Hv].
    rewrite Hv in Hfv; discriminate.
Qed.
Lemma isSC_applyUpdates_true_nth_code
    (stm: StateM) (preTxSt: StateOfAccounts)
    (t: N) (addr: evm.address)
    (ptr_loc topPtr: ptr) (top: UpdatedAccountState)
    (tl: list (ptr * UpdatedAccountState)) (a1: AccountM) :
  NoDup (map fst (newStates stm)) ->
  map fst (newStates stm) ⊆ map fst (preTxAssumedState stm) ->
  nth_error (newStates stm) (N.to_nat t) =
    Some (addr, (ptr_loc, (topPtr, top) :: tl)) ->
  postTxState top = Some a1 ->
  isDelegationMarker (block.block_account_code (coreAc a1)) = false ->
  code_hash_of_program (block.block_account_code (coreAc a1)) <> 0%N ->
  isSC (applyUpdates stm preTxSt) addr = true.
Proof using.
  intros Hnodup Hsubset Hnth Hpost Hdel Hhash.
  apply (isSC_applyUpdates_true_nth stm preTxSt t addr ptr_loc topPtr top tl a1); try assumption.
  apply isAcSC_true_of_code_hash; assumption.
Qed.

Print Assumptions isSC_applyUpdates_true_nth_code.

Definition code_hashes_nodup (st: StateM) : Prop :=
  NoDup (map fst (code_entries_of_state (newStates st))).

(*
Lemma state_is_delegated_model_eq
    (st: StateM) (codeMapLb: gmap N evm.program) (hash: N) :
  state_is_delegated_model st codeMapLb hash =
    if (hash =? 0)%N then false else
      match computeCodeMap st !! hash with
      | Some code => isDelegationMarker code
      | None =>
          match codeMapLb !! hash with
          | Some code => isDelegationMarker code
          | None => false
          end
      end.
Proof. reflexivity. Qed.
 *)

Local Transparent isAcSC.

Lemma isDelegationMarker_true_of_isAcSC_false (am: AccountM) :
  code_hash_of_program (block.block_account_code (coreAc am)) <> 0%N ->
  isAcSC (Some am) = false ->
  isDelegationMarker (block.block_account_code (coreAc am)) = true.
Proof using.
  intros Hhash Hsc.
  unfold isAcSC in Hsc.
  destruct (bool_decide
              (code_hash_of_program (block.block_account_code (coreAc am)) <> 0%N)) eqn:Hdec.
  - simpl in Hsc.
    apply negb_false_iff in Hsc; exact Hsc.
  - apply bool_decide_eq_false_1 in Hdec; contradiction.
Qed.

Local Opaque isAcSC.

Lemma code_entries_of_state_member
    (m: MapModel evm.address (list (ptr * UpdatedAccountState)))
    (addr: evm.address) (ptr_loc topPtr: ptr) (top: UpdatedAccountState)
    (tl: list (ptr * UpdatedAccountState)) (am: AccountM) :
  (addr, (ptr_loc, (topPtr, top) :: tl)) ∈ m ->
  postTxState top = Some am ->
  (code_hash_of_program (block.block_account_code (coreAc am)),
   block.block_account_code (coreAc am)) ∈ code_entries_of_state m.
Proof using.
  intros Hmem Hpost.
  induction m as [|[addr' [ptr' updates']] m IH]; simpl in *.
  - inversion Hmem.
  - rewrite elem_of_cons in Hmem.
    destruct Hmem as [Hmem | Hmem].
    { inversion Hmem; subst; simpl; rewrite Hpost; simpl; left; reflexivity. }
    { destruct updates' as [|[ptru up] tl']; simpl.
      { apply IH; assumption. }
      destruct (postTxState up); simpl.
      { apply elem_of_cons; right; apply IH; assumption. }
      { apply IH; assumption. } }
Qed.

Lemma isDelegationMarker_false_of_code_hash_zero_postTxState
    (st: StateM) (t: N) (addr: evm.address)
    (ptr_loc topPtr: ptr) (top: UpdatedAccountState)
    (tl: list (ptr * UpdatedAccountState)) :
  stateCodeMapInvariants st ->
  nth_error (newStates st) (N.to_nat t) =
    Some (addr, (ptr_loc, (topPtr, top) :: tl)) ->
  (match postTxState top with
   | Some am => code_hash_of_program (block.block_account_code (coreAc am))
   | None => 0
   end =? 0)%N = true ->
  false =
    match postTxState top with
    | Some am => isDelegationMarker (block.block_account_code (coreAc am))
    | None => false
    end.
Proof using.
  intros Hinv Hnth Hhashb.
  destruct (postTxState top) as [am|] eqn:Hpost; simpl in *.
  - apply N.eqb_eq in Hhashb.
    assert (Hmem :
        (addr, (ptr_loc, (topPtr, top) :: tl)) ∈ newStates st).
    { apply list_elem_of_lookup_2 with (i := N.to_nat t).
      rewrite lookup_nth_error.
      exact Hnth. }
    assert (Hentry :
        (code_hash_of_program (block.block_account_code (coreAc am)),
         block.block_account_code (coreAc am)) ∈ code_entries_of_state (newStates st)).
    { apply (code_entries_of_state_member (newStates st) addr ptr_loc topPtr top tl am);
        assumption. }
    pose proof (code_entries_nonzero_of_stateCodeMapInvariants st Hinv) as Hnz.
    specialize (Hnz _ _ Hentry Hhashb) as Hlen.
    apply eq_sym.
    apply isDelegationMarker_false_of_length_zero.
    exact Hlen.
  - reflexivity.
Qed.

Lemma code_entries_functional_of_stateCodeMapInvariants (st: StateM) :
  stateCodeMapInvariants st ->
  code_entries_functional (code_entries_of_state (newStates st)).
Proof using.
  intros Hinv.
  destruct Hinv as (_ & _ & _ & Hfun & _).
  unfold code_entries_functional in *.
  intros h c1 c2 H1 H2.
  apply (Hfun h c1 c2);
    unfold all_code_entries;
    repeat (apply elem_of_app; left);
    assumption.
Qed.

Lemma computeCodeMap_lookup_of_newStates
    (st: StateM) (t: N) (addr: evm.address)
    (ptr_loc topPtr: ptr) (top: UpdatedAccountState)
    (tl: list (ptr * UpdatedAccountState)) (am: AccountM) :
  code_entries_functional (code_entries_of_state (newStates st)) ->
  nth_error (newStates st) (N.to_nat t) =
    Some (addr, (ptr_loc, (topPtr, top) :: tl)) ->
  postTxState top = Some am ->
  codeMapOfNewStates st !!
    code_hash_of_program (block.block_account_code (coreAc am)) =
    Some (block.block_account_code (coreAc am)).
Proof using.
  intros Hfun Hnth Hpost.
  assert (Hmem :
      (addr, (ptr_loc, (topPtr, top) :: tl)) ∈ newStates st).
  { apply list_elem_of_lookup_2 with (i := N.to_nat t).
    rewrite lookup_nth_error.
    exact Hnth. }
  assert (Hentry :
      (code_hash_of_program (block.block_account_code (coreAc am)),
       block.block_account_code (coreAc am)) ∈ code_entries_of_state (newStates st)).
  { apply (code_entries_of_state_member (newStates st) addr ptr_loc topPtr top tl am);
      assumption. }
  unfold codeMapOfNewStates.
  apply (elem_of_list_to_map_1' (code_entries_of_state (newStates st))
           (code_hash_of_program (block.block_account_code (coreAc am)))
           (block.block_account_code (coreAc am))).
  - intros y Hy.
    apply (Hfun (code_hash_of_program (block.block_account_code (coreAc am)))
                (block.block_account_code (coreAc am)) y);
      assumption.
  - exact Hentry.
Qed.

Lemma read_code_program_of_newStates
    (st: StateM) (t: N) (addr: evm.address)
    (ptr_loc topPtr: ptr) (top: UpdatedAccountState)
    (tl: list (ptr * UpdatedAccountState)) (am: AccountM) :
  stateCodeMapInvariants st ->
  nth_error (newStates st) (N.to_nat t) =
    Some (addr, (ptr_loc, (topPtr, top) :: tl)) ->
  postTxState top = Some am ->
  read_code_program st
    (code_hash_of_program (block.block_account_code (coreAc am))) =
    Some (block.block_account_code (coreAc am)).
Proof using.
  intros Hinv Hnth Hpost.
  pose proof (code_entries_functional_of_stateCodeMapInvariants st Hinv) as Hfun.
  unfold read_code_program.
  rewrite (computeCodeMap_lookup_of_newStates st t addr ptr_loc topPtr top tl am Hfun);
    try assumption.
  reflexivity.
Qed.

(*
Lemma state_is_delegated_model_true_of_isAcSC_false
    (st: StateM) (codeMapLb: gmap N evm.program) (t: N)
    (addr: evm.address) (ptr_loc topPtr: ptr) (top: UpdatedAccountState)
    (tl: list (ptr * UpdatedAccountState)) (am: AccountM) :
  NoDup (map fst (code_entries_of_state (newStates st))) ->
  nth_error (newStates st) (N.to_nat t) =
    Some (addr, (ptr_loc, (topPtr, top) :: tl)) ->
  postTxState top = Some am ->
  isAcSC (Some am) = false ->
  code_hash_of_program (block.block_account_code (coreAc am)) <> 0%N ->
  state_is_delegated_model st codeMapLb
    (code_hash_of_program (block.block_account_code (coreAc am))) = true.
Proof using.
  intros Hnodup Hnth Hpost Hsc Hhash.
  set (hash := code_hash_of_program (block.block_account_code (coreAc am))).
  set (code := block.block_account_code (coreAc am)).
  assert (Hlookup : computeCodeMap st !! hash = Some code).
  { subst hash code. apply (computeCodeMap_lookup_of_newStates st t addr ptr_loc topPtr top tl am);
      assumption. }
  assert (Hdel : isDelegationMarker code = true).
  { subst code. apply isDelegationMarker_true_of_isAcSC_false; assumption. }
  unfold state_is_delegated_model.
  destruct (hash =? 0)%N eqn:Hhashb.
  - apply N.eqb_eq in Hhashb. subst hash. contradiction.
  - simpl. rewrite Hlookup. rewrite Hdel. reflexivity.
Qed.
*)
