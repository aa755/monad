Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.invariants.
Require Import skylabs.auto.cpp.proof.

Require Import skylabs.auto.cpp.tactics4.
Require Import monad.asts.reserve_balance_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.ranges_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.fiber_specs.
Import optional_specs.
Import fiber_specs.
Require Import stdpp.gmap.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.execproofs.reservebal.core_lemmas.
Require Import monad.proofs.execproofs.reservebal.update_exactness_lemmas.
Require Import monad.proofs.execproofs.reservebal.non_sender_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_low_balance_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_sufficient_balance_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_history_lemmas.
Require Import monad.proofs.execproofs.reservebal.reservebal_specs.
Require Import monad.proofs.execproofs.reservebal.sender_seen_in_current_prefix_proof.
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
  Local Transparent
    sender_in_recent_historyb delundel_in_recent_historyb
    sender_in_current_prefixb delundel_in_current_prefixb.
  Local Transparent tx_seen_within_k delundel_seen_within_k.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context {MODd : reserve_balance_cpp.source ⊧ CU}.

  Ltac slauto := (slautot ltac:(autorewrite with syntactic (*equiv iff slbwd *); try iExistsDef; (*try rewrite left_id; *) (*try solveRefereceTo; *) try autounfold with unfold; try Forward.forward_reason; try Forward.rwHyps (*; try optionSomeBig;  try instOptionR*))); try iPureIntro.

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
  #[local] Instance observeAnkerSetTypePtr q keys :
    Observe (type_ptrR address_set_table_ty)
      (ankerl_specs.AnkerSetR "monad::Address" addressToN addressR q keys).
  Proof using.
    unfold ankerl_specs.AnkerSetR.
    exact _.
  Qed.
  Definition observeAnkerSetTypePtr_F :=
    ltac:(mk_at_obs_fwd observeAnkerSetTypePtr).
  #[local] Hint Resolve observeAnkerSetTypePtr_F : sl_opacity.
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

Local Transparent dels undels addrsDelUndelByTx.
Local Transparent MonadChainContextR.

Set Nested Proofs Allowed.

Local Lemma no_recent_historyb_from_not_in_parent_grandparent
    (ctx : MonadChainContext) (tx : TxWithHdr)
    (parentblock grandparentblock : Block) :
  parentBlock (blocks ctx) = Some parentblock ->
  grandParentBlock (blocks ctx) = Some grandparentblock ->
  sender tx ∉ sendersAndAuthorities parentblock ->
  sender tx ∉ sendersAndAuthorities grandparentblock ->
  sender_in_recent_historyb ctx tx = false /\
  delundel_in_recent_historyb ctx tx = false.
Proof using MODd.
  intros Hpb Hgpb Hnotp Hnotgp.
  split.
  - unfold sender_in_recent_historyb.
    rewrite Hpb Hgpb.
    simpl.
    rewrite bool_decide_false;
      [| eapply not_in_sendersAndAuthorities_not_sender_in_block; exact Hnotp ].
    rewrite bool_decide_false;
      [| eapply not_in_sendersAndAuthorities_not_sender_in_block; exact Hnotgp ].
    reflexivity.
  - unfold delundel_in_recent_historyb.
    rewrite Hpb Hgpb.
    simpl.
    rewrite bool_decide_false;
      [| eapply not_in_sendersAndAuthorities_not_authority_in_block; exact Hnotp ].
    rewrite bool_decide_false;
      [| eapply not_in_sendersAndAuthorities_not_authority_in_block; exact Hnotgp ].
    reflexivity.
Qed.

Local Lemma no_recent_historyb_from_not_in_parent
    (ctx : MonadChainContext) (tx : TxWithHdr) (parentblock : Block) :
  parentBlock (blocks ctx) = Some parentblock ->
  grandParentBlock (blocks ctx) = None ->
  sender tx ∉ sendersAndAuthorities parentblock ->
  sender_in_recent_historyb ctx tx = false /\
  delundel_in_recent_historyb ctx tx = false.
Proof using MODd.
  intros Hpb Hgpb Hnotp.
  split.
  - unfold sender_in_recent_historyb.
    rewrite Hpb Hgpb.
    simpl.
    rewrite bool_decide_false;
      [| eapply not_in_sendersAndAuthorities_not_sender_in_block; exact Hnotp ].
    reflexivity.
  - unfold delundel_in_recent_historyb.
    rewrite Hpb Hgpb.
    simpl.
    rewrite bool_decide_false;
      [| eapply not_in_sendersAndAuthorities_not_authority_in_block; exact Hnotp ].
    reflexivity.
Qed.

Local Lemma no_recent_historyb_from_no_parent_no_grandparent
    (ctx : MonadChainContext) (tx : TxWithHdr) :
  parentBlock (blocks ctx) = None ->
  grandParentBlock (blocks ctx) = None ->
  sender_in_recent_historyb ctx tx = false /\
  delundel_in_recent_historyb ctx tx = false.
Proof using MODd.
  intros Hpb Hgpb.
  split;
    [ unfold sender_in_recent_historyb
    | unfold delundel_in_recent_historyb ];
    rewrite Hpb Hgpb; reflexivity.
Qed.

Local Lemma historyConsistent_false_branches_imply_not_seen_within_k
    (ctx : MonadChainContext) (hist : ExtraAcStates)
    (i : nat) (tx : TxWithHdr) :
  historyConsistent ctx hist ->
  nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
  sender_in_recent_historyb ctx tx = false ->
  delundel_in_recent_historyb ctx tx = false ->
  sender_in_current_prefixb ctx i tx = false ->
  delundel_in_current_prefixb ctx i tx = false ->
  tx_seen_within_k hist tx = false /\
  delundel_seen_within_k hist tx = false.
Proof using MODd.
  intros Hhist Hnth Hsender_recent_false Hdel_recent_false
    Hsender_prefix_false Hdel_prefix_false.
  pose proof (Hhist i tx Hnth) as [Htxseen Hdelseen].
  rewrite Htxseen Hdelseen.
  rewrite Hsender_recent_false Hdel_recent_false.
  rewrite Hsender_prefix_false Hdel_prefix_false.
  simpl.
  auto.
Qed.

Local Lemma not_seen_prefix_implies_no_current_authority
    (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) :
  nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
  ~ sender_seen_in_current_prefix ctx i tx ->
  Some (sender tx) ∈ txAuthoritiesDelFrom tx.1 ->
  False.
Proof using MODd.
  intros Hnth Hnot_seen_prefix HinCur.
  apply Hnot_seen_prefix.
  eapply current_authority_implies_sender_seen_in_current_prefix; eauto.
Qed.

Local Lemma sender_lookup_code_of_satisfiesAssumptions
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (tx : TxWithHdr)
    (preTxState : StateOfAccounts)
    (loc : ptr) (aps : AssumedPreTxAccountState)
    (assumedAc : AccountM) :
  satisfiesAssumptions' true orig preTxState ->
  mapModelLookup orig (sender tx) = Some (loc, aps) ->
  exec_specs.preTxState aps = Some assumedAc ->
  account_code (preTxState (sender tx)) = account_code assumedAc.
Proof using MODd.
  intros Hsat Hlookup Haps.
  specialize (Hsat (sender tx)).
  unfold satAccountAssumptions, satAccountStrageAssumptions, assumptionOfAddr in Hsat.
  pose proof (Hlookup : orig !! sender tx = Some (loc, aps)) as Hlookup'.
  rewrite Hlookup' in Hsat.
  rewrite Haps in Hsat.
  simpl in Hsat.
  destruct Hsat as [_ [Hcode _]].
  exact Hcode.
Qed.

Local Lemma sender_lookup_none_absurd_of_satisfiesAssumptions
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (tx : TxWithHdr)
    (preTxState : StateOfAccounts)
    (loc : ptr) (aps : AssumedPreTxAccountState) :
  satisfiesAssumptions' true orig preTxState ->
  mapModelLookup orig (sender tx) = Some (loc, aps) ->
  exec_specs.preTxState aps = None ->
  False.
Proof using MODd.
  intros Hsat Hlookup Haps.
  specialize (Hsat (sender tx)).
  unfold satAccountAssumptions, satAccountNonStorageAssumptions,
    satAccountStrageAssumptions, assumptionOfAddr in Hsat.
  pose proof (Hlookup : orig !! sender tx = Some (loc, aps)) as Hlookup'.
  rewrite Hlookup' in Hsat.
  rewrite Haps in Hsat.
  simpl in Hsat.
  destruct Hsat as [Hfalse _].
  exact Hfalse.
Qed.

Local Lemma parent_set_membership_forbids_emptying
    (ctx : MonadChainContext) (hist : ExtraAcStates)
    (i : nat) (tx : TxWithHdr)
    (parentblock : Block) (preTxState : StateOfAccounts) :
  historyConsistent ctx hist ->
  nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
  parentBlock (blocks ctx) = Some parentblock ->
  sender tx ∈ sendersAndAuthorities parentblock ->
  false = isAllowedToEmpty 3 (preTxState, hist) [] tx.
Proof using MODd.
  intros Hhist Hnth Hpb Hsender_auth.
  pose proof
    (parent_set_membership_implies_recent_seen
       ctx tx parentblock Hpb Hsender_auth)
    as [Hrecent|Hrecent].
  - eapply historyConsistent_window_forbids_emptying;
      [exact Hhist | exact Hnth | left; exact Hrecent].
  - eapply historyConsistent_window_forbids_emptying;
      [exact Hhist | exact Hnth | right; left; exact Hrecent].
Qed.

Local Lemma grandparent_set_membership_forbids_emptying
    (ctx : MonadChainContext) (hist : ExtraAcStates)
    (i : nat) (tx : TxWithHdr)
    (grandparentblock : Block) (preTxState : StateOfAccounts) :
  historyConsistent ctx hist ->
  nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
  grandParentBlock (blocks ctx) = Some grandparentblock ->
  sender tx ∈ sendersAndAuthorities grandparentblock ->
  false = isAllowedToEmpty 3 (preTxState, hist) [] tx.
Proof using MODd.
  intros Hhist Hnth Hgpb Hsender_auth.
  pose proof
    (grandparent_set_membership_implies_recent_seen
       ctx tx grandparentblock Hgpb Hsender_auth)
    as [Hrecent|Hrecent].
  - eapply historyConsistent_window_forbids_emptying;
      [exact Hhist | exact Hnth | left; exact Hrecent].
  - eapply historyConsistent_window_forbids_emptying;
      [exact Hhist | exact Hnth | right; left; exact Hrecent].
Qed.

Local Lemma no_recent_history_context_allows_emptying
    (ctx : MonadChainContext) (hist : ExtraAcStates)
    (i : nat) (tx : TxWithHdr)
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (preTxState : StateOfAccounts) :
  historyConsistent ctx hist ->
  nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
  sender_in_recent_historyb ctx tx = false ->
  delundel_in_recent_historyb ctx tx = false ->
  ~ sender_seen_in_current_prefix ctx i tx ->
  satisfiesAssumptions' true orig preTxState ->
  match mapModelLookup orig (sender tx) with
  | Some (_, aps) =>
      false =
      ((match exec_specs.preTxState aps with
        | Some am => isDelegationMarker (block.block_account_code (coreAc am))
        | None => false
        end
         && asbool (sender tx ∉ undels tx.1.2))
       || asbool (sender tx ∈ dels tx.1.2))
  | None => False
  end ->
  true = isAllowedToEmpty 3 (preTxState, hist) [] tx.
Proof using MODd.
  intros Hhist Hnth Hsender_recent_false Hdel_recent_false
    Hnot_seen_prefix Hsat Hallow.
  pose proof
    (no_sender_seen_in_current_prefix_implies_prefix_bools_false
       ctx i tx Hnot_seen_prefix)
    as [Hsender_prefix_false Hdel_prefix_false].
  pose proof
    (historyConsistent_false_branches_imply_not_seen_within_k
       ctx hist i tx Hhist Hnth
       Hsender_recent_false Hdel_recent_false
       Hsender_prefix_false Hdel_prefix_false)
    as [Htx_false Hdel_false].
  destruct (mapModelLookup orig (sender tx)) as [[loc aps]|] eqn:Hlookup.
  2: contradiction.
  destruct (exec_specs.preTxState aps) as [assumedAc|] eqn:Haps.
  - pose proof
      (sender_lookup_code_of_satisfiesAssumptions
         orig tx preTxState loc aps assumedAc
         Hsat Hlookup Haps)
      as Hcode.
    pose proof
      (sender_clean_implies_emptying_side_conditions
         tx preTxState assumedAc
         Hcode Hallow
         (fun HinCur =>
            not_seen_prefix_implies_no_current_authority
              ctx i tx Hnth Hnot_seen_prefix HinCur))
      as [Hdelegated Hcur_delundelb].
    eapply no_recent_history_allows_emptying;
      [exact Hdelegated | exact Htx_false | exact Hdel_false | exact Hcur_delundelb].
  - exfalso.
    eapply sender_lookup_none_absurd_of_satisfiesAssumptions; eauto.
Qed.

  #[local] Existing Instance exec_specs.SpecFor_address_set_contains.
  #[local] Existing Instance ranges_specs.SpecFor_std_ranges_contains.
  #[local] Existing Instance exec_specs.SpecFor_ranges_contains_optional_address.
  #[local] Existing Instance ranges_specs.SpecFor_identity_ctor.
  #[local] Existing Instance ranges_specs.SpecFor_identity_dtor.

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


  #[local] Hint Rewrite cblock_eq_currentBlock_local : syntactic.
  #[local] Hint Resolve sender_authority_history_empty_local : pure.
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


Lemma prf : verify[source] can_sender_dip_into_reserve_spec.
Proof using MODd.
  verify_spec'.
  name_locals.
  first
    [ match goal with
      | H : historyConsistent ctx hist |- _ => rename H into Hhist
      end
    | fail 1 "historyConsistent hypothesis not found" ].
  first
    [ match goal with
      | H : nth_error _ i = Some tx |- _ => rename H into Hnth
      end
    | fail 1 "nth_error hypothesis not found" ].
  go.
  wp_if.
  {
    intros ->.
    go.
    iSplit.
    Remove Hints MonadChainContextR_F : sl_opacity.
    {
      fold SenderAuthoritiesSetR in *.
      wapplyRev (@MonadChainContextR_equiv _ _ _ CU qctx ctx ctxp).
      go.
    }
    iPureIntro.
    intros preTxState Hsat.
    eapply delegated_sender_forbids_emptying; eauto.
  }
  {
    go.
    destruct (grandParentBlock (senders_and_authoritiesp ctx)) as [grandparentsetp|] eqn:Hgp.
    {
      destruct (grandParentBlock (blocks ctx)) as [grandparentblock|] eqn:Hgpb.
      2:
      {
        simpl.
        go.
      }
      simpl.
      go.
      unfold SenderAuthoritiesSetR in *.
      iExists EvmAddr, _, addressToN, addressR, qctx,
        (sendersAndAuthorities grandparentblock), qs, (sender tx).
      go.
      destruct (decide (sender tx ∈ sendersAndAuthorities grandparentblock))
        as [Hin|Hnin].
      {
        rewrite bool_decide_true; [| exact Hin].
        unfold MonadChainContextR.
        rewrite Hgp Hgpb.
        simpl.
        go.
        iPureIntro.
        intros preTxState Hsat.
        clear Hsat.
        eapply grandparent_set_membership_forbids_emptying; eauto.
      }
      {
        rewrite bool_decide_false; [| exact Hnin].
        go.
        destruct (parentBlock (senders_and_authoritiesp ctx)) as [parentsetp|] eqn:Hp.
        {
          destruct (parentBlock (blocks ctx)) as [parentblock|] eqn:Hpb.
          2:
          {
            simpl.
            go.
          }
          simpl.
          go.
          unfold MonadChainContextR.
          rewrite Hp Hpb Hgp Hgpb.
          simpl.
          unfold SenderAuthoritiesSetR in *.
          go.
          iExists EvmAddr, _, addressToN, addressR, qctx,
            (sendersAndAuthorities parentblock), qs, (sender tx).
          go.
          destruct (decide (sender tx ∈ sendersAndAuthorities parentblock))
            as [Hinp|Hninp].
          {
            rewrite bool_decide_true; [| exact Hinp].
            go.
            iPureIntro.
            intros preTxState Hsat.
            clear Hsat.
            eapply parent_set_membership_forbids_emptying; eauto.
          }
          {
            rewrite bool_decide_false; [| exact Hninp].
            go.
            unfold SenderAuthoritiesSetR in *.
            (* The old helper returned whether the prefix contained the sender.
               Its inlined returns now discharge the caller's decision contract. *)
            assert (Hseen_result :
              sender_seen_in_current_prefix ctx i tx ->
              forall preTxState,
                satisfiesAssumptions' true orig preTxState ->
                false = isAllowedToEmpty 3 (preTxState, hist) [] tx).
            {
              intros Hseen preTxState _.
              eapply sender_seen_in_current_prefix_forbids_emptying;
                [exact Hhist | exact Hnth | exact Hseen].
            }
            assert (Hnot_result :
              ~ sender_seen_in_current_prefix ctx i tx ->
              forall preTxState,
                satisfiesAssumptions' true orig preTxState ->
                true = isAllowedToEmpty 3 (preTxState, hist) [] tx).
            {
              intros Hnot_seen preTxState Hsat.
              pose proof
                (no_recent_historyb_from_not_in_parent_grandparent
                   ctx tx parentblock grandparentblock
                   Hpb Hgpb Hninp Hnin)
                as [Hsender_recent_false Hdel_recent_false].
              eapply no_recent_history_context_allows_emptying; eauto.
            }
            iExists EvmAddr, _, addressToN, addressR, qctx,
              (sendersAndAuthorities (currentBlock (blocks ctx))), qs, (sender tx).
            go.
            wp_if.
            { intros Hin.
              assert (Hindex_bound :
                (Z.of_nat i < lengthZ (transactions (cblock ctx)))%Z)
                by exact _H_1.
              go.
    (* Before iteration j, no earlier sender or authority has matched.
       The current transaction contributes authorities, but not its own sender. *)
    wp_for (fun _ =>
      Exists (j : N),
        j_addr |-> ulongR 1 (Z.of_N j) **
        sendersp ctx
        |-> std.vector.spineR
              "monad::Address"
              "std::allocator<monad::Address>"
              qctx$m size st **
        std.vector.base_pointer st
        |-> arrayLR "monad::Address" 0 size
              (λ v : EvmAddr, addressR qctx v)
              (map sender (txsWithHdr (cblock ctx))) **
        [| (j <= N.succ (N.of_nat i))%N /\
           forall k : N,
             (k < j)%N ->
             (((k < N.of_nat i)%N ->
               nth_error (map sender (txsWithHdr (cblock ctx))) (N.to_nat k) <> Some (sender tx)) /\
             forall auths,
               nth_error (map txAuthoritiesDelFrom (transactions (cblock ctx))) (N.to_nat k) = Some auths ->
               Some (sender tx) ∉ auths) |]).
      go.
      unshelve go.
      lazymatch goal with
      | t : N |- _ => set (idx := t)
      end.

    destruct (decide (Z.of_N idx < Z.of_nat i)%Z) as [Htlt|Hnlt].
    { replace (asbool (Z.of_N idx < Z.of_nat i)%Z) with true by
        (symmetry; apply bool_decide_true; exact Htlt).
        assert (Htle : (Z.of_N idx <= Z.of_nat i)%Z) by lia.
        go.
        assert
        (Hsize :
           size = lengthZ
             (transactions (cblock ctx))).
      {
        assert (Hsize_nonneg : (0 ≤ size)%Z) by lia.
        change (cblock ctx) with (currentBlock (blocks ctx)).
        eapply senders_size_from_size_sub0_local; [exact Hsize_nonneg |].
        match goal with
        | Hlen :
            lengthN
              (map sender
                 (map
                    (λ t0 : Transaction,
                       (t0, header (currentBlock (blocks ctx))))
                    (transactions (currentBlock (blocks ctx))))) =
            Z.to_N (size - 0) |- _ =>
            exact Hlen
        | Hlen :
            lengthN
              (map sender
                 (map
                    (λ t0 : Transaction,
                       (t0, header (currentBlock (blocks ctx))))
                    (transactions (currentBlock (blocks ctx))))) =
            Z.to_N size |- _ =>
            replace (Z.to_N (size - 0)) with (Z.to_N size) by lia;
            exact Hlen
        end.
      }
      assert
        (Hsenders_len :
           lengthN
             (map sender
                (map
                   (λ t0 : Transaction,
                      (t0, header (currentBlock (blocks ctx))))
                   (transactions (currentBlock (blocks ctx))))) =
           Z.to_N size).
      {
        change (cblock ctx) with (currentBlock (blocks ctx)).
        match goal with
        | Hlen :
            lengthN
              (map sender
                 (map
                    (λ t0 : Transaction,
                       (t0, header (currentBlock (blocks ctx))))
                    (transactions (currentBlock (blocks ctx))))) =
            Z.to_N (size - 0) |- _ =>
            exact (lengthN_sub0_normalize_local _ _ Hlen)
        | Hlen :
            lengthN
              (map sender
                 (map
                    (λ t0 : Transaction,
                       (t0, header (currentBlock (blocks ctx))))
                    (transactions (currentBlock (blocks ctx))))) =
            Z.to_N size |- _ =>
            exact Hlen
        end.
      }
      assert
        (Hsenders_bound :
           (0 ≤ Z.of_N idx + 1 ≤
            lengthZ (transactions (cblock ctx)))%Z).
      {
        split.
        {
          apply Z.add_nonneg_nonneg.
          { apply N2Z.is_nonneg. }
          { lia. }
        }
        lia.
      }
          iExists (cQp.m qctx),
            (map sender
               (map
                  (λ t0 : Transaction, (t0, header (cblock ctx)))
                  (transactions (cblock ctx)))).
          change (cQp.frac (cQp.m qctx)) with qctx.
          change (cblock ctx) with (currentBlock (blocks ctx)).
          sep with sl_opacity* br_hints #db_skylabs_syntactic pure
            typeclass_instances using Hsenders_len, Hsenders_bound.
      assert
        (Hidx :
           (0 ≤ Z.of_N idx <
            lengthZ (transactions (cblock ctx)))%Z).
      {
        split.
        { apply N2Z.is_nonneg. }
        lia.
      }
      set (senders :=
        map sender
          (map
             (λ t0 : Transaction,
                (t0, header (currentBlock (blocks ctx))))
             (transactions (currentBlock (blocks ctx))))).
      assert
        (Hlookup_sender :
           senders !! N.to_nat idx =
           Some (nth (N.to_nat idx) senders (sender dummyTx))).
      {
        apply nth_lookup_of_lt_lengthZ_local.
        unfold senders.
        autorewrite with syntactic.
        lia.
      }
      assert
        (Hlookup_range :
           rangeZ 0 size !! N.to_nat idx =
           Some (Z.of_N idx)).
      {
        apply std.lookup_rangeZ.
        split.
        { rewrite Hsize. exact Hidx. }
        { rewrite Z.add_0_l N_nat_Z.
          reflexivity.
        }
      }
      assert
        (Hsenders_mid :
           SolveArith (0 <= Z.of_N idx /\ Z.of_N idx < size)%Z) by
        (constructor; lia).
      pose proof
        (arrayLR_extract_middle_lookup_equiv_local
           "monad::Address"%cpp_type (std.vector.base_pointer st)
           0%Z (Z.of_N idx) size
           (λ v : EvmAddr, addressR qctx v) senders Hsenders_mid)
        as HextractSenders.
      setoid_rewrite HextractSenders at 1.
      sep with sl_opacity* br_hints #db_skylabs_syntactic pure typeclass_instances.
            set (bv := nth (N.to_nat idx) senders (sender dummyTx)).
            assert
              (Hlookup :
                 senders !! Z.of_N idx = Some bv).
            {
              apply (proj2 (lookupZ_Some_to_nat senders (Z.of_N idx) bv)).
              split.
              { lia. }
              {
                replace (Z.to_nat (Z.of_N idx)) with (N.to_nat idx) by lia.
                exact Hlookup_sender.
              }
            }
            assert (Ht_bv : t = bv) by congruence.
            subst t.
              destruct (decide (sender tx = bv)) as [Heq | Hneq].
        { replace (asbool (sender tx = bv)) with true by
            (symmetry; apply bool_decide_true; exact Heq).
                    go.
          change
            (map sender
               (map
                (λ t0 : Transaction,
                   (t0, header (currentBlock (blocks ctx))))
                (transactions (currentBlock (blocks ctx)))))
          with senders.
            rewrite /MonadChainContextR /SenderAuthoritiesSetR.
                  assert
                    (Hlookup_seen :
                       senders !! Z.of_N idx = Some (sender tx)).
                  {
                    rewrite Hlookup.
                    f_equal.
                    symmetry.
                    exact Heq.
                  }
                  unfold senders in Hlookup_seen.
                    pose proof
            (sender_seen_in_current_prefix_sender_lookupZ_local
               ctx i tx idx Htlt Hlookup_seen eq_refl)
            as Hseen.
                pose proof (only_provable_bwd (PROP:=mpred) (Hseen_result Hseen)) as Hseen_B.
        change
          (map sender
             (map
                (λ t0 : Transaction,
                   (t0, header (currentBlock (blocks ctx))))
                (transactions (currentBlock (blocks ctx)))))
          with senders.
        go using HextractSenders, Hseen_B;
          try change
            (map sender
               (map
                  (λ t0 : Transaction,
                     (t0, header (currentBlock (blocks ctx))))
                  (transactions (currentBlock (blocks ctx)))))
            with senders;
          try setoid_rewrite HextractSenders;
          go.
        }
              { replace (asbool (sender tx = bv)) with false by
                  (symmetry; apply bool_decide_false; exact Hneq).
          unfold senders.
            go.
          lazymatch goal with
                 | t : N |- _ => idtac
                 | _t_ : N |- _ => set (t := _t_)
                   | j : N |- _ => set (t := j)
                   end.
              assert
                (Hauths_size :
                   _size_ =
                   lengthZ (transactions (cblock ctx))).
            {
              change (cblock ctx) with (currentBlock (blocks ctx)).
              eapply authorities_size_from_size_sub0_local; [assumption |].
              match goal with
              | Hlen :
                  lengthN
                    (map txAuthoritiesDelFrom
                       (transactions (currentBlock (blocks ctx)))) =
                  Z.to_N (_size_ - 0) |- _ =>
                  exact Hlen
              | Hlen :
                  lengthN
                    (map txAuthoritiesDelFrom
                       (transactions (currentBlock (blocks ctx)))) =
                  Z.to_N _size_ |- _ =>
                  replace (Z.to_N (_size_ - 0)) with (Z.to_N _size_) by lia;
                  exact Hlen
              end.
            }
            assert
              (Hauths_bound :
                 (0 ≤ Z.of_N _t_ + 1 ≤
                  lengthZ (transactions (cblock ctx)))%Z).
            {
              lia.
            }
          iExists (cQp.m qctx),
            (map txAuthoritiesDelFrom (transactions (currentBlock (blocks ctx)))).
          change (cblock ctx) with (currentBlock (blocks ctx)).
          change (cQp.frac (cQp.m qctx)) with qctx.
          go.
          set (auths :=
            map txAuthoritiesDelFrom
              (transactions (currentBlock (blocks ctx)))).
          assert
                (Hlookup_auth :
                   auths !! N.to_nat _t_ =
                   Some (nth (N.to_nat _t_) auths [])).
          {
            apply nth_lookup_of_lt_lengthZ_local.
            unfold auths.
            autorewrite with syntactic.
            lia.
	          }
          set (auths_t := nth (N.to_nat _t_) auths []).
          assert (Hauth_lookup : auths !! Z.of_N _t_ = Some auths_t).
          {
            unfold auths_t.
            exact (lookupZ_of_lookupN_local _ _ _ Hlookup_auth).
          }
          assert
            (Hauth_lookup0 :
               auths !! (Z.of_N _t_ - 0)%Z = Some auths_t).
          {
            replace (Z.of_N _t_ - 0)%Z with (Z.of_N _t_) by lia.
            exact Hauth_lookup.
          }
          assert
            (Hauth_lookup_cblock :
               map txAuthoritiesDelFrom (transactions (cblock ctx))
               !! Z.of_N _t_ = Some auths_t).
          {
            unfold auths in Hauth_lookup.
            change (currentBlock (blocks ctx)) with (cblock ctx) in Hauth_lookup.
            exact Hauth_lookup.
          }
	        assert
	          (Hauths_mid :
	             SolveArith
	               (0 <= Z.of_N _t_ /\
                Z.of_N _t_ <
                lengthZ (transactions (cblock ctx)))%Z) by
          (constructor; lia).
	        pose proof
	          (arrayLR_extract_middle_known_equiv_local
	             optional_address_vector_ty_local
	             (std.vector.base_pointer _st_) 0%Z (Z.of_N _t_)
	             (lengthZ (transactions (cblock ctx)))
	             (optional_address_vectorR_local qctx) auths Hauths_mid
               auths_t Hauth_lookup0)
	          as HextractAuth.
	        unfold optional_address_vectorR_local,
	          optional_address_vector_ty_local,
          optional_address_ty_local in HextractAuth.
	                  change (cQp.frac (cQp.m qctx)) with qctx in *.
		                setoid_rewrite HextractAuth at 1.
		                step.
		                step.
		                iExists qctx, auths_t, (cQp.m 1).
		                unfold idx in *.
		                (* Instantiates the ranges::contains precondition for
		                   the extracted authority vector; after the Brick
		                   vector migration this automation step can take a
		                   few minutes. *)
		                go.
                destruct (decide (Some (sender tx) ∈ auths_t)) as [Hmem | Hnmem].
		                { replace (asbool (Some (sender tx) ∈ auths_t)) with true by
		                    (symmetry; apply bool_decide_true; exact Hmem).
		                  assert (Hseen_prefix : sender_seen_in_current_prefix ctx i tx).
	                  {
	                    eapply (earlier_authority_implies_sender_seen_in_current_prefix
	                              ctx i tx _t_ auths_t).
	                    { exact Hnth. }
	                    { exact Htle. }
	                    { exact Hauth_lookup_cblock. }
	                    { exact Hmem. }
	                  }
              pose proof (Hseen_result Hseen_prefix) as Hret_false.
              rewrite /MonadChainContextR /SenderAuthoritiesSetR.
              change
                (map sender
                   (map
                      (λ t0 : Transaction,
                         (t0, header (currentBlock (blocks ctx))))
                      (transactions (currentBlock (blocks ctx)))))
              with senders.
	              change
		                (map txAuthoritiesDelFrom
		                   (transactions (currentBlock (blocks ctx))))
		                with auths.
		                      (* Executes the true branch after ranges::contains;
		                         with the Brick vector resources split out this
		                         automation step can take a few minutes. *)
		                      go.
                                          }
	                  { replace (asbool (Some (sender tx) ∈ auths_t)) with false by
	                      (symmetry; apply bool_decide_false; exact Hnmem).
	                    pose (HcombineSenders_B := [BWD->] HextractSenders).
	                    (* Reassembles the sender vector after the first
	                       branch fails; Brick vector cancellation can take a
	                       few minutes here. *)
	                    go using HcombineSenders_B,
	                      typed_sliceR_elim_type_ptr_C, type_ptr_valid.

        }
    }
    }
      {
        replace (asbool (Z.of_N t < Z.of_nat i)%Z) with false by
          (symmetry; apply bool_decide_false; exact Hnlt).
        wp_if.
        { intro Htle.
          assert (Ht_eq : Z.of_N t = Z.of_nat i) by lia.
          go.
            assert
              (Hauths_size :
                 _size_ =
                 lengthZ (transactions (cblock ctx))).
            {
              change (cblock ctx) with (currentBlock (blocks ctx)).
              eapply authorities_size_from_size_sub0_local; [assumption |].
              match goal with
              | Hlen :
                  lengthN
                    (map txAuthoritiesDelFrom
                       (transactions (currentBlock (blocks ctx)))) =
                  Z.to_N (_size_ - 0) |- _ =>
                  exact Hlen
              | Hlen :
                  lengthN
                    (map txAuthoritiesDelFrom
                       (transactions (currentBlock (blocks ctx)))) =
                  Z.to_N _size_ |- _ =>
                  replace (Z.to_N (_size_ - 0)) with (Z.to_N _size_) by lia;
                  exact Hlen
              end.
            }
            change (cblock ctx) with (currentBlock (blocks ctx)) in Hauths_size.
            change (cQp.frac (cQp.m qctx)) with qctx.
            rewrite Hauths_size.
          iExists (cQp.m qctx),
            (map txAuthoritiesDelFrom (transactions (currentBlock (blocks ctx)))).
          change (cQp.frac (cQp.m qctx)) with qctx.
          go.
          set (auths :=
            map txAuthoritiesDelFrom
              (transactions (currentBlock (blocks ctx)))).
          assert
            (Hlookup_auth :
               auths !! N.to_nat t =
               Some (nth (N.to_nat t) auths [])).
          {
            apply nth_lookup_of_lt_lengthZ_local.
            unfold auths.
            autorewrite with syntactic.
            lia.
          }
            assert
              (Hauths_idx :
                 (0 ≤ Z.of_N t <
                lengthZ (transactions (cblock ctx)))%Z).
          {
              change (cblock ctx) with (currentBlock (blocks ctx)).
              change (Z.of_N t) with (Z.of_N idx).
              lia.
            }
            assert
              (Hauths_mid :
                 SolveArith
                   (0 <= Z.of_N t /\
                    Z.of_N t <
                    lengthZ (transactions (cblock ctx)))%Z) by
              (constructor; exact Hauths_idx).
            pose proof
              (arrayLR_extract_middle_lookup_equiv_local
                 optional_address_vector_ty_local
                 (std.vector.base_pointer _st_) 0%Z (Z.of_N t)
                 (lengthZ (transactions (cblock ctx)))
                 (optional_address_vectorR_local qctx) auths Hauths_mid)
              as HextractAuth.
            unfold optional_address_vectorR_local,
              optional_address_vector_ty_local,
              optional_address_ty_local in HextractAuth.
          setoid_rewrite HextractAuth at 1.
          go.
            iExists qctx, t, (cQp.m 1).
          destruct (decide (Some (sender tx) ∈ t)) as [Hmem | Hnmem].
          { replace (asbool (Some (sender tx) ∈ t)) with true by
              (symmetry; apply bool_decide_true; exact Hmem).
            assert
              (Hauth_lookup :
                 map txAuthoritiesDelFrom
                   (transactions (cblock ctx)) !! Z.of_N _t_ = Some t).
            {
              match goal with
              | Hlookup :
                  auths !! Z.of_N _t_ = Some t |- _ =>
                  unfold auths in Hlookup;
                  change (currentBlock (blocks ctx)) with (cblock ctx) in Hlookup;
                  exact Hlookup
              | Hlookup :
                  map txAuthoritiesDelFrom
                    (transactions (cblock ctx)) !! Z.of_N _t_ = Some t |- _ =>
                  exact Hlookup
              end.
            }
            assert (Hseen_prefix : sender_seen_in_current_prefix ctx i tx).
            {
              eapply (earlier_authority_implies_sender_seen_in_current_prefix
                        ctx i tx _t_ t).
              { exact Hnth. }
              { rewrite Ht_eq. lia. }
              { exact Hauth_lookup. }
              { exact Hmem. }
            }
              pose proof (Hseen_result Hseen_prefix) as Hret_false.
	              change (cQp.frac (cQp.m qctx)) with qctx.
	              change (cQp.m (cQp.frac (cQp.m qctx))) with (cQp.m qctx).
	                go using HextractAuth.
	        }
          { replace (asbool (Some (sender tx) ∈ t)) with false by
              (symmetry; apply bool_decide_false; exact Hnmem).
            assert
              (Hauth_lookup :
                 map txAuthoritiesDelFrom
                   (transactions (cblock ctx)) !! N.to_nat _t_ = Some t).
            {
              match goal with
              | Hlookup :
                  auths !! Z.of_N _t_ = Some t |- _ =>
                  unfold auths in Hlookup;
                  change (currentBlock (blocks ctx)) with (cblock ctx) in Hlookup;
                  pose proof
                    (proj1
                       (lookupZ_Some_to_nat
                          (map txAuthoritiesDelFrom
                             (transactions (cblock ctx)))
                          (Z.of_N _t_) t) Hlookup)
                    as [_ Hlookup_nat];
                  replace (Z.to_nat (Z.of_N _t_)) with (N.to_nat _t_)
                    in Hlookup_nat by lia;
                  exact Hlookup_nat
              | Hlookup :
                  map txAuthoritiesDelFrom
                    (transactions (cblock ctx)) !! Z.of_N _t_ = Some t |- _ =>
                  pose proof
                    (proj1
                       (lookupZ_Some_to_nat
                          (map txAuthoritiesDelFrom
                             (transactions (cblock ctx)))
                          (Z.of_N _t_) t) Hlookup)
                    as [_ Hlookup_nat];
                  replace (Z.to_nat (Z.of_N _t_)) with (N.to_nat _t_)
                    in Hlookup_nat by lia;
                  exact Hlookup_nat
              end.
                }
                assert (HteqN : _t_ = N.of_nat i) by
                  (apply N2Z.inj; zify; nia).
                assert (Hnot_seen : ~ sender_seen_in_current_prefix ctx i tx) by
                  (eapply (sender_not_seen_from_last_authority_nth_local
                             ctx i tx _t_ t b);
                   [ exact HteqN | exact Hauth_lookup | exact Hnmem ]).
                  change (cQp.frac (cQp.m qctx)) with qctx.
                  change (cQp.m (cQp.frac (cQp.m qctx))) with (cQp.m qctx).
                  go.
                }
          }
          { intro Hnle.
            assert (Ht_succ : t = N.succ (N.of_nat i)) by lia.
            assert (Hnot_seen : ~ sender_seen_in_current_prefix ctx i tx) by
              (eapply sender_not_seen_from_loop_exit_local;
               [ exact b | exact Ht_succ ]).
            pose proof (Hnot_result Hnot_seen) as Hret_true.
            rewrite /MonadChainContextR /SenderAuthoritiesSetR.
              go.
          }
        }
            }
            { intros Hnotin.
              assert (Hnot_seen : ~ sender_seen_in_current_prefix ctx i tx).
              { intro Hseen. apply Hnotin.
                exact (sender_seen_in_current_prefix_in_current_set ctx i tx Hseen). }
              pose proof (Hnot_result Hnot_seen) as Hret_true.
              go.
            }
          }
        }
        {
          destruct (parentBlock (blocks ctx)) as [parentblock|] eqn:Hpb; simpl in *;
            [rewrite pureR_False; go |].
          simpl.
          go.
        }
      }
    }
    {
      destruct (grandParentBlock (blocks ctx)) as [grandparentblock|] eqn:Hgpb; simpl in *.
      {
        go.
      }
      {
        simpl.
        go.
      }
    }
  }
Qed.

End with_Sigma.

Set Printing Fully Qualified.
