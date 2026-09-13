Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.invariants.
Require Import skylabs.auto.cpp.proof.

Require Import skylabs.auto.cpp.tactics4.
Require Import monad.asts.reserve_balance_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.fiber_specs.
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
  Context  {MODd : reserve_balance_cpp.source ⊧ CU}.
  Lemma sender_seen_in_current_prefix_in_current_set
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) :
    sender_seen_in_current_prefix ctx i tx ->
    sender tx ∈ sendersAndAuthorities (currentBlock (blocks ctx)).
  Proof using CU MODd.
    intros (j & _ & [[_ Hsender] | (auths & Hauth & Hin)]).
    { unfold sendersAndAuthorities.
      apply elem_of_app.
      left.
      rewrite nth_error_lookup in Hsender.
      eapply list_elem_of_lookup_2 with (i := j).
      exact Hsender.
    }
    { unfold sendersAndAuthorities.
      apply elem_of_app.
      right.
      assert
        (HauthElem :
           auths ∈ map txAuthoritiesDelFrom (transactions (currentBlock (blocks ctx)))).
      {
        rewrite nth_error_lookup in Hauth.
        eapply list_elem_of_lookup_2 with (i := j).
        exact Hauth.
      }
      apply list_elem_of_fmap in HauthElem.
      destruct HauthElem as [txj [HtxjEq HtxjIn]].
      apply list_elem_of_bind.
      exists txj.
      split; [| exact HtxjIn].
      unfold txAuthoritiesDelFrom in HtxjEq.
      rewrite <- HtxjEq.
      apply list_elem_of_bind.
      exists (Some (sender tx)).
      split; [simpl; left; reflexivity | exact Hin].
    }
  Qed.

  Local Transparent dels undels addrsDelUndelByTx.

  Lemma current_authority_implies_sender_seen_in_current_prefix
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) :
    nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
    Some (sender tx) ∈ txAuthoritiesDelFrom tx.1 ->
    sender_seen_in_current_prefix ctx i tx.
  Proof using CU MODd.
    intros Hnth Hin.
    exists i.
    split.
    { lia. }
    right.
    exists (txAuthoritiesDelFrom tx.1).
    split.
    { unfold txsWithHdr in Hnth.
      rewrite nth_error_map in Hnth.
      simpl in Hnth.
      destruct (nth_error (transactions (cblock ctx)) i) as [txi|] eqn:Htxi;
        simpl in Hnth; try discriminate.
      inversion Hnth; subst.
      rewrite nth_error_map.
      simpl.
      rewrite Htxi.
      reflexivity.
    }
    exact Hin.
  Qed.

  Lemma earlier_authority_implies_sender_seen_in_current_prefix
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr)
      (j : N) (auths : list (option EvmAddr)) :
    nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
    (Z.of_N j <= Z.of_nat i)%Z ->
    map txAuthoritiesDelFrom (transactions (cblock ctx)) !! Z.of_N j = Some auths ->
    Some (sender tx) ∈ auths ->
    sender_seen_in_current_prefix ctx i tx.
  Proof using CU MODd.
    intros Hnth Hle Hlookup Hin.
    exists (N.to_nat j).
    split.
    { rewrite N_nat_Z.
      exact Hle.
    }
    right.
    exists auths.
    split.
	    { rewrite nth_error_lookup.
	      pose proof
	        (proj1
	           (lookupZ_Some_to_nat
	              (map txAuthoritiesDelFrom (transactions (cblock ctx)))
	              (Z.of_N j) auths) Hlookup)
	        as [_ Hlookup_nat].
	      replace (N.to_nat j) with (Z.to_nat (Z.of_N j)).
	      { exact Hlookup_nat. }
	      apply Nat2Z.inj.
	      rewrite N_nat_Z.
	      have Hznonneg : (0 <= Z.of_N j)%Z by lia.
	      rewrite (Z2Nat.id (Z.of_N j) Hznonneg).
	      reflexivity.
	    }
    exact Hin.
  Qed.

  Lemma in_addrsDelUndelByTx_implies_current_authority
      (tx : TxWithHdr) (addr : EvmAddr) :
    addr ∈ addrsDelUndelByTx tx ->
    Some addr ∈ txAuthoritiesDelFrom tx.1.
  Proof using CU MODd.
    unfold addrsDelUndelByTx, dels, undels, txAuthoritiesDelFrom.
    rewrite elem_of_app.
    intros [Hin|Hin].
    { apply list_elem_of_bind in Hin.
      destruct Hin as [a [Ha Hin]].
      destruct (del_from a) as [from|] eqn:Hfrom.
      2:{ simpl in Ha. rewrite elem_of_nil in Ha. contradiction. }
      destruct (is_undelegation a) eqn:Hundeleg.
      { simpl in Ha. rewrite elem_of_nil in Ha. contradiction. }
      { simpl in Ha.
        apply list_elem_of_singleton in Ha.
        subst addr.
        apply (proj2 (list_elem_of_fmap _ _ _)).
        exists a.
        split; [symmetry; exact Hfrom | exact Hin].
      }
    }
    apply list_elem_of_bind in Hin.
    destruct Hin as [a [Ha Hin]].
    destruct (del_from a) as [from|] eqn:Hfrom.
    2:{ simpl in Ha. rewrite elem_of_nil in Ha. contradiction. }
    destruct (is_undelegation a) eqn:Hundeleg.
    { simpl in Ha.
      apply list_elem_of_singleton in Ha.
      subst addr.
      apply (proj2 (list_elem_of_fmap _ _ _)).
      exists a.
      split; [symmetry; exact Hfrom | exact Hin].
    }
    { simpl in Ha. rewrite elem_of_nil in Ha. contradiction. }
  Qed.

  Lemma current_authority_implies_in_addrsDelUndelByTx
      (tx : TxWithHdr) (addr : EvmAddr) :
    Some addr ∈ txAuthoritiesDelFrom tx.1 ->
    addr ∈ addrsDelUndelByTx tx.
  Proof using CU MODd.
    unfold txAuthoritiesDelFrom, addrsDelUndelByTx, dels, undels.
    intros Hin.
    apply list_elem_of_fmap in Hin.
    destruct Hin as [a [Hfrom Hin]].
    destruct (del_from a) as [from|] eqn:Hdel_from.
    2:{ simpl in Hfrom. discriminate. }
    inversion Hfrom; subst from; clear Hfrom.
    rewrite elem_of_app.
    destruct (is_undelegation a) eqn:Hundeleg.
    { right.
      apply list_elem_of_bind.
      exists a.
      split; [| exact Hin].
      rewrite Hdel_from.
      rewrite Hundeleg.
      simpl.
      set_solver.
    }
    { left.
      apply list_elem_of_bind.
      exists a.
      split; [| exact Hin].
      rewrite Hdel_from.
      rewrite Hundeleg.
      simpl.
      set_solver.
    }
  Qed.

  Lemma in_dels_implies_in_addrsDelUndelByTx
      (tx : TxWithHdr) (addr : EvmAddr) :
    addr ∈ dels tx.1.2 ->
    addr ∈ addrsDelUndelByTx tx.
  Proof using CU MODd.
    intros Hin.
    unfold addrsDelUndelByTx.
    apply elem_of_app.
    left.
    exact Hin.
  Qed.

  Lemma in_undels_implies_in_addrsDelUndelByTx
      (tx : TxWithHdr) (addr : EvmAddr) :
    addr ∈ undels tx.1.2 ->
    addr ∈ addrsDelUndelByTx tx.
  Proof using CU MODd.
    intros Hin.
    unfold addrsDelUndelByTx.
    apply elem_of_app.
    right.
    exact Hin.
  Qed.

  Lemma authority_tail_membership_implies_txAuthoritiesDelFrom
      (b : Block) (addr : EvmAddr) :
    addr ∈ flat_map
             (fun tx =>
                flat_map
                  (fun oa =>
                     match oa with
                     | Some addr' => [addr']
                     | None => []
                     end)
                  (map del_from (authorities tx.2)))
             (transactions b) ->
    Some addr ∈ flat_map txAuthoritiesDelFrom (transactions b).
  Proof using CU MODd.
    intros Hin.
    apply list_elem_of_bind in Hin.
    destruct Hin as [txj [Hin HtxjIn]].
    apply list_elem_of_bind in Hin.
    destruct Hin as [oa [HaddrIn HoaIn]].
    destruct oa as [addr'|] eqn:Hoa.
    2:{ simpl in HaddrIn. rewrite elem_of_nil in HaddrIn. contradiction. }
    apply list_elem_of_singleton in HaddrIn.
    subst addr'.
    apply list_elem_of_bind.
    exists txj.
    split; [| exact HtxjIn].
    unfold txAuthoritiesDelFrom.
    apply list_elem_of_fmap.
    apply list_elem_of_fmap in HoaIn.
    destruct HoaIn as [a [Hdelfrom HaIn]].
    exists a.
    split.
    { simpl. exact Hdelfrom. }
    { exact HaIn. }
  Qed.

  Lemma not_in_sendersAndAuthorities_not_sender_in_block
      (b : Block) (addr : EvmAddr) :
    addr ∉ sendersAndAuthorities b ->
    addr ∉ map sender (txsWithHdr b).
  Proof using CU MODd.
    intros Hnot Hin.
    apply Hnot.
    unfold sendersAndAuthorities.
    apply elem_of_app.
    left.
    exact Hin.
  Qed.

  Lemma not_in_sendersAndAuthorities_not_authority_in_block
      (b : Block) (addr : EvmAddr) :
    addr ∉ sendersAndAuthorities b ->
    Some addr ∉ flat_map txAuthoritiesDelFrom (transactions b).
  Proof using CU MODd.
    intros Hnot Hin.
    apply Hnot.
    unfold sendersAndAuthorities.
    apply elem_of_app.
    right.
    apply list_elem_of_bind in Hin.
    destruct Hin as [txj [HtxjIn HaddrIn]].
    apply list_elem_of_bind.
    exists txj.
    split.
    { apply list_elem_of_bind.
      exists (Some addr).
      split; [simpl; left; reflexivity | exact HtxjIn].
    }
    { exact HaddrIn. }
  Qed.

  Lemma parent_set_membership_implies_recent_seen
      (ctx : MonadChainContext) (tx : TxWithHdr) (parentblock : Block) :
    parentBlock (blocks ctx) = Some parentblock ->
    sender tx ∈ sendersAndAuthorities parentblock ->
    sender_in_recent_historyb ctx tx = true \/
    delundel_in_recent_historyb ctx tx = true.
  Proof using CU MODd.
    intros Hp Hin.
    unfold sendersAndAuthorities in Hin.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hsender|Hauth].
	    { left.
	      unfold sender_in_recent_historyb.
	      rewrite Hp.
	      rewrite bool_decide_true; [|exact Hsender].
	      destruct (grandParentBlock (blocks ctx)); simpl; reflexivity.
	    }
	    { right.
	      unfold delundel_in_recent_historyb.
	      rewrite Hp.
	      rewrite bool_decide_true.
	      2:{ now apply authority_tail_membership_implies_txAuthoritiesDelFrom. }
	      destruct (grandParentBlock (blocks ctx)); simpl; reflexivity.
	    }
  Qed.

  Lemma grandparent_set_membership_implies_recent_seen
      (ctx : MonadChainContext) (tx : TxWithHdr) (grandparentblock : Block) :
    grandParentBlock (blocks ctx) = Some grandparentblock ->
    sender tx ∈ sendersAndAuthorities grandparentblock ->
    sender_in_recent_historyb ctx tx = true \/
    delundel_in_recent_historyb ctx tx = true.
  Proof using CU MODd.
    intros Hgp Hin.
    unfold sendersAndAuthorities in Hin.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hsender|Hauth].
    { left.
      unfold sender_in_recent_historyb.
      rewrite Hgp.
      destruct (parentBlock (blocks ctx)); simpl.
      { assert (Hsender_gp :
            bool_decide (sender tx ∈ map sender (txsWithHdr grandparentblock)) = true).
        { apply bool_decide_true; exact Hsender. }
        rewrite Hsender_gp.
        rewrite orb_true_r.
        reflexivity. }
      { rewrite bool_decide_true; [reflexivity|exact Hsender]. }
    }
	    { right.
	      unfold delundel_in_recent_historyb.
	      rewrite Hgp.
	      destruct (parentBlock (blocks ctx)); simpl.
	      { assert (Hauth_gp :
	            bool_decide
	              (Some (sender tx) ∈ flat_map txAuthoritiesDelFrom (transactions grandparentblock)) = true).
	        { apply bool_decide_true.
	          now apply authority_tail_membership_implies_txAuthoritiesDelFrom. }
	        rewrite Hauth_gp.
	        rewrite orb_true_r.
	        reflexivity. }
	      { rewrite bool_decide_true.
	        2:{ now apply authority_tail_membership_implies_txAuthoritiesDelFrom. }
	        reflexivity. }
	    }
  Qed.

  Lemma seen_within_k_forbids_emptying
      (preTxState : StateOfAccounts) (hist : ExtraAcStates) (tx : TxWithHdr) :
    tx_seen_within_k hist tx = true \/
    delundel_seen_within_k hist tx = true ->
    false = isAllowedToEmpty 3 (preTxState, hist) [] tx.
  Proof using CU MODd.
    intros [Htx|Hdel].
    - unfold isAllowedToEmpty, existsTxWithinK, indexWithinK, tx_seen_within_k in *.
      cbn in *.
      rewrite Htx.
      destruct
        (~~
           (addrDelegated preTxState (sender tx)
            || existsDelUndelTxWithinK 3 (preTxState, hist) tx
            || asbool (sender tx ∈ addrsDelUndelByTx tx ++ []))); reflexivity.
    - unfold isAllowedToEmpty, existsDelUndelTxWithinK, indexWithinK, delundel_seen_within_k in *.
      cbn in *.
      rewrite Hdel.
      destruct (addrDelegated preTxState (sender tx));
      destruct (asbool (sender tx ∈ addrsDelUndelByTx tx ++ []));
      reflexivity.
  Qed.

  Lemma historyConsistent_window_forbids_emptying
      (ctx : MonadChainContext) (hist : ExtraAcStates)
      (i : nat) (tx : TxWithHdr) (preTxState : StateOfAccounts) :
    historyConsistent ctx hist ->
    nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
    (sender_in_recent_historyb ctx tx = true \/
     delundel_in_recent_historyb ctx tx = true \/
     sender_in_current_prefixb ctx i tx = true \/
     delundel_in_current_prefixb ctx i tx = true) ->
    false = isAllowedToEmpty 3 (preTxState, hist) [] tx.
  Proof using CU MODd.
    intros Hhist Hnth Hseen.
    pose proof (Hhist i tx Hnth) as [Htxseen Hdelseen].
    eapply seen_within_k_forbids_emptying.
    destruct Hseen as [Hrecent | [Hrecent | [Hprefix | Hprefix]]].
    { left.
      rewrite Htxseen Hrecent.
      simpl.
      reflexivity.
    }
    { right.
      rewrite Hdelseen Hrecent.
      simpl.
      reflexivity.
    }
    { left.
      rewrite Htxseen Hprefix.
      destruct (sender_in_recent_historyb ctx tx); reflexivity.
    }
    { right.
      rewrite Hdelseen Hprefix.
      destruct (delundel_in_recent_historyb ctx tx); reflexivity.
    }
  Qed.

  Lemma sender_seen_in_current_prefix_forbids_emptying
      (ctx : MonadChainContext) (hist : ExtraAcStates)
      (i : nat) (tx : TxWithHdr) (preTxState : StateOfAccounts) :
    historyConsistent ctx hist ->
    nth_error (txsWithHdr (cblock ctx)) i = Some tx ->
    sender_seen_in_current_prefix ctx i tx ->
    false = isAllowedToEmpty 3 (preTxState, hist) [] tx.
  Proof using CU MODd.
    intros Hhist Hnth [j [Hle [[Hlt Hsender] | [auths [Hauth Hin]]]]].
    { eapply historyConsistent_window_forbids_emptying; [exact Hhist | exact Hnth |].
      right. right. left.
      unfold sender_in_current_prefixb.
      apply existsb_exists.
      exists j.
      split.
      { apply in_seq. lia. }
      { apply bool_decide_true. exact Hsender. }
    }
    destruct (decide (j < i)%nat) as [Hlt'|Hnlt].
    { eapply historyConsistent_window_forbids_emptying; [exact Hhist | exact Hnth |].
      right. right. right.
      unfold delundel_in_current_prefixb.
      apply existsb_exists.
      exists j.
      split.
      { apply in_seq. lia. }
      destruct (nth_error (map txAuthoritiesDelFrom (transactions (currentBlock (blocks ctx)))) j) eqn:Hlookup.
      { apply bool_decide_true.
        rewrite Hauth in Hlookup.
        inversion Hlookup; subst.
        exact Hin.
      }
      { rewrite Hauth in Hlookup. discriminate. }
    }
    assert (Hj : j = i) by lia.
    subst j.
    assert (Hauth_tx : auths = txAuthoritiesDelFrom tx.1).
	    { unfold txsWithHdr in Hnth.
	      rewrite nth_error_map in Hnth.
	      simpl in Hnth.
	      destruct (nth_error (transactions (cblock ctx)) i) as [txi|] eqn:Htxi;
	        simpl in Hnth; try discriminate.
	      inversion Hnth; subst; clear Hnth.
	      rewrite nth_error_map in Hauth.
	      simpl in Hauth.
	      rewrite Htxi in Hauth.
	      inversion Hauth.
      reflexivity.
    }
    subst auths.
    assert (Hcur : sender tx ∈ addrsDelUndelByTx tx).
    { eapply current_authority_implies_in_addrsDelUndelByTx.
      exact Hin.
    }
    assert (Hasbool : asbool (sender tx ∈ flat_map addrsDelUndelByTx (tx :: [])) = true).
    { apply bool_decide_true.
      simpl.
      rewrite app_nil_r.
      exact Hcur.
    }
    unfold isAllowedToEmpty.
    cbn.
    rewrite Hasbool.
    destruct (addrDelegated preTxState (sender tx));
    destruct (existsDelUndelTxWithinK 3 (preTxState, hist) tx);
    destruct (existsTxWithinK 3 (preTxState, hist) tx);
    reflexivity.
  Qed.

  Lemma sender_in_current_prefixb_true_implies_seen
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) :
    sender_in_current_prefixb ctx i tx = true ->
    sender_seen_in_current_prefix ctx i tx.
  Proof using CU MODd.
    unfold sender_in_current_prefixb.
    intros Hseen.
    apply existsb_exists in Hseen as [j [Hjseq Hjbool]].
    apply in_seq in Hjseq as [_ Hjlt].
    exists j.
    split; [lia|].
    left.
    split; [lia|].
    destruct
      (decide
         (nth_error (map sender (txsWithHdr (currentBlock (blocks ctx)))) j =
          Some (sender tx))) as [Hlookup|Hlookup]; simpl in Hjbool.
    { change (currentBlock (blocks ctx)) with (cblock ctx) in Hlookup.
      exact Hlookup. }
    rewrite (bool_decide_false _ Hlookup) in Hjbool.
    discriminate.
  Qed.

  Lemma delundel_in_current_prefixb_true_implies_seen
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) :
    delundel_in_current_prefixb ctx i tx = true ->
    sender_seen_in_current_prefix ctx i tx.
  Proof using CU MODd.
    unfold delundel_in_current_prefixb.
    intros Hseen.
    apply existsb_exists in Hseen as [j [Hjseq Hjbool]].
    apply in_seq in Hjseq as [_ Hjlt].
    exists j.
    split; [lia|].
    right.
    destruct
      (nth_error
         (map txAuthoritiesDelFrom (transactions (currentBlock (blocks ctx)))) j)
      as [auths|] eqn:Hauth; [|simpl in Hjbool; discriminate].
    exists auths.
    split.
    { change (currentBlock (blocks ctx)) with (cblock ctx) in Hauth.
      exact Hauth. }
    destruct (decide (Some (sender tx) ∈ auths)) as [Hin|Hin]; simpl in Hjbool.
    { exact Hin. }
    rewrite (bool_decide_false _ Hin) in Hjbool.
    discriminate.
  Qed.

  Lemma no_sender_seen_in_current_prefix_implies_prefix_bools_false
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) :
    ~ sender_seen_in_current_prefix ctx i tx ->
    sender_in_current_prefixb ctx i tx = false /\
    delundel_in_current_prefixb ctx i tx = false.
  Proof using CU MODd.
    intros Hnot.
    split.
    { destruct (sender_in_current_prefixb ctx i tx) eqn:Hsender; [|reflexivity].
      exfalso.
      apply Hnot.
      now eapply sender_in_current_prefixb_true_implies_seen.
    }
    destruct (delundel_in_current_prefixb ctx i tx) eqn:Hdel; [|reflexivity].
    exfalso.
    apply Hnot.
    now eapply delundel_in_current_prefixb_true_implies_seen.
  Qed.

  Lemma no_recent_history_allows_emptying
      (hist : ExtraAcStates)
      (tx : TxWithHdr)
      (preTxState : StateOfAccounts) :
    addrDelegated preTxState (sender tx) = false ->
    tx_seen_within_k hist tx = false ->
    delundel_seen_within_k hist tx = false ->
    asbool (sender tx ∈ addrsDelUndelByTx tx ++ []) = false ->
    true = isAllowedToEmpty 3 (preTxState, hist) [] tx.
  Proof using CU MODd.
    intros Hdelegated Htx_false Hdel_false Hcur_delundelb.
    unfold isAllowedToEmpty.
    cbn.
    unfold existsTxWithinK, existsDelUndelTxWithinK, indexWithinK.
    unfold tx_seen_within_k in Htx_false.
    unfold delundel_seen_within_k in Hdel_false.
    rewrite Hdelegated Htx_false Hdel_false Hcur_delundelb.
    reflexivity.
  Qed.

  Lemma sender_clean_implies_emptying_side_conditions
      (tx : TxWithHdr)
      (preTxState0 : StateOfAccounts)
      (assumedAc : AccountM) :
    account_code (preTxState0 (sender tx)) = account_code assumedAc ->
    false =
      (isDelegationMarker (block.block_account_code (coreAc assumedAc))
         && asbool (sender tx ∉ undels tx.1.2)
       || asbool (sender tx ∈ dels tx.1.2)) ->
    (Some (sender tx) ∈ txAuthoritiesDelFrom tx.1 -> False) ->
    addrDelegated preTxState0 (sender tx) = false /\
    asbool (sender tx ∈ addrsDelUndelByTx tx ++ []) = false.
  Proof using CU MODd.
    intros Hcode Hallow Hnot_cur_auth.
    assert (Hnot_cur_delundel : sender tx ∉ addrsDelUndelByTx tx).
    {
      intros Hcur.
      apply Hnot_cur_auth.
      eapply in_addrsDelUndelByTx_implies_current_authority.
      exact Hcur.
    }
    assert (Hnot_dels : sender tx ∉ dels tx.1.2).
    {
      intros Hdels.
      apply Hnot_cur_delundel.
      now apply in_dels_implies_in_addrsDelUndelByTx.
    }
    assert (Hnot_undels : sender tx ∉ undels tx.1.2).
    {
      intros Hundels.
      apply Hnot_cur_delundel.
      now apply in_undels_implies_in_addrsDelUndelByTx.
    }
    assert (Hdelsb : asbool (sender tx ∈ dels tx.1.2) = false).
    { apply bool_decide_false. exact Hnot_dels. }
    assert (Hundelsb : asbool (sender tx ∉ undels tx.1.2) = true).
    { apply bool_decide_true. exact Hnot_undels. }
    assert (Hmarker_false :
      isDelegationMarker (block.block_account_code (coreAc assumedAc)) = false).
    {
      destruct (isDelegationMarker (block.block_account_code (coreAc assumedAc))) eqn:Hmarker;
        [|reflexivity].
      simpl in Hallow.
      rewrite Hdelsb Hundelsb in Hallow.
      discriminate.
    }
    split.
    {
      unfold addrDelegated, delegatedTo, account_code in *.
      rewrite Hcode Hmarker_false.
      reflexivity.
    }
    rewrite app_nil_r.
    apply bool_decide_false.
    exact Hnot_cur_delundel.
  Qed.

Lemma delegated_sender_forbids_emptying
    (orig : MapModel evm.address AssumedPreTxAccountState)
    (hist : ExtraAcStates)
    (tx : TxWithHdr)
    (preTxState : StateOfAccounts) :
  satisfiesAssumptions' true orig preTxState ->
  match mapModelLookup orig (sender tx) with
  | Some (_, aps) =>
      true =
      ((match exec_specs.preTxState aps with
        | Some am => isDelegationMarker (block.block_account_code (coreAc am))
        | None => false
        end && asbool (sender tx ∉ undels tx.1.2))
       || asbool (sender tx ∈ dels tx.1.2))
  | None => False
  end ->
  false = isAllowedToEmpty 3 (preTxState, hist) [] tx.
Proof using CU MODd.
  intros Hsat Hdelegated.
  unfold isAllowedToEmpty.
  cbn.
  destruct (mapModelLookup orig (sender tx)) as [[loc aps]|] eqn:Hlookup.
  2:{ exfalso; exact Hdelegated. }
  specialize (Hsat (sender tx)).
  unfold satisfiesAssumptions', satAccountAssumptions,
    satAccountNonStorageAssumptions, satAccountStrageAssumptions,
    assumptionOfAddr in Hsat.
  change (orig !! sender tx = Some (loc, aps)) in Hlookup.
  rewrite Hlookup in Hsat.
  destruct (exec_specs.preTxState aps) as [assumedAc|] eqn:Haps; simpl in Hsat, Hdelegated.
  - rewrite Haps in Hsat.
    simpl in Hsat.
    destruct Hsat as [_ [Hcode _]].
    assert (Hdelegated_ac :
      addrDelegated preTxState (sender tx) =
      isDelegationMarker (block.block_account_code (coreAc assumedAc))).
    { unfold addrDelegated, delegatedTo, account_code in *.
      rewrite Hcode.
      destruct (isDelegationMarker (block.block_account_code (coreAc assumedAc))); reflexivity.
    }
    destruct (decide (sender tx ∈ dels tx.1.2)) as [Hdels|Hndels].
    + assert (Hasbool : asbool (sender tx ∈ addrsDelUndelByTx tx ++ []) = true).
      { apply bool_decide_true.
        apply elem_of_app.
        left.
        now apply in_dels_implies_in_addrsDelUndelByTx.
      }
      rewrite Hasbool orb_true_r. simpl. reflexivity.
    + assert (Hdelsb : asbool (sender tx ∈ dels tx.1.2) = false).
      { apply bool_decide_false. exact Hndels. }
      rewrite Hdelsb in Hdelegated.
      assert (Hmarker :
        isDelegationMarker (block.block_account_code (coreAc assumedAc)) = true).
      { destruct (isDelegationMarker (block.block_account_code (coreAc assumedAc))); simpl in Hdelegated; try discriminate.
        reflexivity.
      }
      rewrite Hdelegated_ac.
      rewrite Hmarker.
      simpl.
      reflexivity.
  - rewrite Haps in Hsat.
    simpl in Hsat.
    destruct Hsat as [Hfalse _].
    contradiction.
Qed.

End with_Sigma.
