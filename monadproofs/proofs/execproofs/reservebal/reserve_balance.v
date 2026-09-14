Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.invariants.

Require skylabs.auto.cpp.hints.builtins.
Require Import skylabs.auto.cpp.tactics4.
Require Import monad.asts.reserve_balance_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.evmc_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.fiber_specs.
Require Import monad.proofs.libspecs.span_specs.
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
Require Import monad.proofs.execproofs.reservebal.sender_rewrite_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_update_helpers.
Require Import monad.proofs.execproofs.reservebal.sender_low_balance_lemmas.
Require Import monad.proofs.execproofs.reservebal.sender_sufficient_balance_lemmas.
Import environments.

Set Warnings "+sl-impossible-patterns".
Open Scope Z_scope.

Remove Hints
  skylabs.auto.cpp.hints.builtins.wp_operand_builtin_call_B
  skylabs.auto.cpp.hints.builtins.wp_builtin_func_intro_B
  skylabs.auto.cpp.hints.builtins.builtin_move_B
  skylabs.auto.cpp.hints.builtins.builtin_forward_B
  skylabs.auto.cpp.hints.builtins.builtin_expect_B
  skylabs.auto.cpp.hints.builtins.builtin_unreachable_B
  skylabs.auto.cpp.hints.builtins.builtin_trap_B
  skylabs.auto.cpp.hints.builtins.builtin_launder_B
  skylabs.auto.cpp.hints.builtins.builtin_ffs_B
  skylabs.auto.cpp.hints.builtins.builtin_ffsl_B
  skylabs.auto.cpp.hints.builtins.builtin_ffsll_B
  skylabs.auto.cpp.hints.builtins.builtin_clz_B
  skylabs.auto.cpp.hints.builtins.builtin_clzl_B
  skylabs.auto.cpp.hints.builtins.builtin_clzll_B
  skylabs.auto.cpp.hints.builtins.builtin_ctz_B
  skylabs.auto.cpp.hints.builtins.builtin_ctzl_B
  skylabs.auto.cpp.hints.builtins.builtin_ctzll_B
  skylabs.auto.cpp.hints.builtins.builtin_bswap16_B
  skylabs.auto.cpp.hints.builtins.builtin_bswap32_int_B
  skylabs.auto.cpp.hints.builtins.builtin_bswap64_long_B
  skylabs.auto.cpp.hints.builtins.builtin_bswap64_longlong_B
  : db_skylabs_wp.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : reserve_balance_cpp.source ⊧ CU}.

  Definition builtin_expect_B_local := [BWD] builtins.wp_expect.

  #[local] Hint Resolve
    skylabs.auto.cpp.hints.builtins.wp_operand_builtin_call_B
    | 100 : db_skylabs_wp.
  #[local] Hint Resolve
    skylabs.auto.cpp.hints.builtins.wp_builtin_func_intro_B
    | 200 : db_skylabs_wp.
  #[local] Hint Resolve builtin_expect_B_local | 200 : db_skylabs_wp.

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).

  Lemma ignore_valid_bool_return_local (b : bool) (Q : mpred) :
    Q |-- (validP<"bool"> (Vbool b) -∗ Q).
  Proof using.
    go.
  Qed.

  Lemma drop_knowledge_right_local (P Q : mpred) `{!Knowledge Q} :
    P ** Q |-- P.
  Proof using.
    rewrite (affine Q) right_id.
    reflexivity.
  Qed.

  Lemma wp_break_sep_local
      (rho : region) (Q : Kpred) (P : mpred) :
    ▷ Q Break ** P |-- wp source rho Sbreak Q ** P.
  Proof using.
    apply bi.sep_mono; [apply wp_break | reflexivity].
  Qed.

  Lemma use_wand_local (P Q : mpred) : (P -∗ Q) ** P |-- Q.
  Proof using.
    rewrite bi.sep_comm.
    exact (bi.wand_elim_r P Q).
  Qed.

  Definition use_wand_local_F P Q :=
    [FWD] (use_wand_local P Q).

  Lemma use_wand_local_r (P Q : mpred) : P ** (P -∗ Q) |-- Q.
  Proof using.
    exact (bi.wand_elim_r P Q).
  Qed.

  Definition use_wand_local_r_F P Q :=
    [FWD] (use_wand_local_r P Q).

  Lemma use_anker_iter_type_ptr_wand
      (iter_addr : ptr) (ktycpp vtycpp : type)
      (is_const : bool) (i : N) (spine : list ptr) (Q : mpred) :
    iter_addr |-> AnkerMapIterR ktycpp vtycpp is_const 1$m i spine
    ** (iter_addr |-> AnkerMapIterR ktycpp vtycpp is_const 1$m i spine
        ** type_ptr (anker_iter_ty ktycpp vtycpp is_const) iter_addr
        -∗ Q)
    |-- Q.
  Proof using.
    go using anker_iter_keep_type_ptr_C, use_wand_local_r_F.
  Qed.

  Definition use_anker_iter_type_ptr_wand_F
      iter_addr ktycpp vtycpp is_const i spine Q :=
    [FWD] (use_anker_iter_type_ptr_wand
             iter_addr ktycpp vtycpp is_const i spine Q).

  Lemma use_forall_wand_local {A : Type}
      (x : A) (P Q : A -> mpred) :
    (∀ y, P y -∗ Q y) ** P x |-- Q x.
  Proof using.
    etrans.
    {
      apply bi.sep_mono; [apply bi.forall_elim | reflexivity].
    }
    rewrite bi.sep_comm.
    exact (bi.wand_elim_r (P x) (Q x)).
  Qed.

  Definition use_forall_wand_local_F {A : Type} x P Q :=
    [FWD] (@use_forall_wand_local A x P Q).

  Create HintDb wand.

  Ltac specialize_wands :=
    sep with wand* using use_wand_local_F, use_wand_local_r_F.

  Ltac specialize_forall_wands :=
    sep with wand* using use_forall_wand_local_F.

  Definition current_iter_neq_spec_for :
    SpecFor source
      "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<monad::Address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<monad::Address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<1b>::operator!=<1b>(const ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<monad::Address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<monad::Address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<1b>&) const"%cpp_name :=
    SpecFor_anker_iter_neq
      "monad::Address"%cpp_type
      "monad::VersionStack<monad::AccountState>"%cpp_type
      (Eint 1 Tbool) source.
  #[local] Existing Instance current_iter_neq_spec_for.

  Lemma observeDippedIntoReserveLambda_local
      (this addrp statep senderp gas_feesp : ptr) :
    Observe (type_ptr (Tnamed dipped_into_reserve_lam) this)
      (this |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp).
  Proof using.
    apply observe_intro; [exact _|].
    unfold DippedIntoReserveLambdaR.
    go.
  Qed.

  Definition observeDippedIntoReserveLambdaF_local
      (this addrp statep senderp gas_feesp : ptr) :=
    @observe_fwd _ _ _
      (observeDippedIntoReserveLambda_local
         this addrp statep senderp gas_feesp).

  Lemma observeDippedIntoReserveLambdaRefThis_local (this : ptr) :
    Observe (reference_to (Tnamed dipped_into_reserve_lam) this)
      (this |-> structR dipped_into_reserve_lam 1$m).
  Proof using.
    apply observe_intro; [exact _|].
    go.
  Qed.

  Definition observeDippedIntoReserveLambdaRefThisF_local (this : ptr) :=
    @observe_fwd _ _ _
      (observeDippedIntoReserveLambdaRefThis_local this).

  Lemma observeDippedIntoReserveLambdaReference_local
      (this addrp statep senderp gas_feesp : ptr) :
    Observe (reference_to (Tnamed dipped_into_reserve_lam) this)
      (this |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp).
  Proof using.
    apply observe_intro; [exact _|].
    unfold DippedIntoReserveLambdaR.
    go.
  Qed.

  Definition observeDippedIntoReserveLambdaReferenceF_local
      (this addrp statep senderp gas_feesp : ptr) :=
    @observe_fwd _ _ _
      (observeDippedIntoReserveLambdaReference_local
         this addrp statep senderp gas_feesp).

  Lemma DippedIntoReserveLambdaR_fold_local
      (this addrp statep senderp gas_feesp : ptr) :
    this ,, o_field CU (dipped_into_reserve_capture_field "addr")
      |-> refR<"monad::Address"> 1$m addrp
    ** this ,, o_field CU (dipped_into_reserve_capture_field "state")
      |-> refR<"monad::State"> 1$m statep
    ** this ,, o_field CU (dipped_into_reserve_capture_field "sender")
      |-> refR<"monad::Address"> 1$m senderp
    ** this ,, o_field CU (dipped_into_reserve_capture_field "gas_fees")
      |-> refR<"monad::uint256_t"> 1$m gas_feesp
    ** this |-> structR dipped_into_reserve_lam 1$m
    |-- this |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp.
  Proof using.
    unfold DippedIntoReserveLambdaR.
    go.
  Qed.

  Definition DippedIntoReserveLambdaR_fold_F
      this addrp statep senderp gas_feesp :=
    [FWD] (DippedIntoReserveLambdaR_fold_local
             this addrp statep senderp gas_feesp).

  Lemma DippedIntoReserveLambdaR_fold_call_local
      (this addrp statep senderp gas_feesp : ptr) :
    this ,, o_field CU (dipped_into_reserve_capture_field "sender")
      |-> refR<"monad::Address"> 1$m senderp
    ** this ,, o_field CU (dipped_into_reserve_capture_field "state")
      |-> refR<"monad::State"> 1$m statep
    ** this ,, o_field CU (dipped_into_reserve_capture_field "addr")
      |-> refR<"monad::Address"> 1$m addrp
    ** this ,, o_field CU (dipped_into_reserve_capture_field "gas_fees")
      |-> refR<"monad::uint256_t"> 1$m gas_feesp
    ** this |-> structR dipped_into_reserve_lam 1$m
    |-- this |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp.
  Proof using.
    unfold DippedIntoReserveLambdaR.
    go.
  Qed.

  Definition DippedIntoReserveLambdaR_fold_call_F
      this addrp statep senderp gas_feesp :=
    [FWD] (DippedIntoReserveLambdaR_fold_call_local
             this addrp statep senderp gas_feesp).

  Definition DippedIntoReserveLambdaR_fold_call_B
      this addrp statep senderp gas_feesp :=
    [BWD] (DippedIntoReserveLambdaR_fold_call_local
             this addrp statep senderp gas_feesp).

  Definition wp_init_condition_B_local := [BWD] wp_init_condition.

  #[local] Existing Instance state_check_min_balance_slice_spec_spec_instance.

  #[local] Instance learn_block_state_rfrag :
    AtLearnEq3 BlockState.Rfrag :=
    ltac:(solve_learnable).

  (*
"monad::(anon)::dipped_into_reserve(const monad::Address&, const monad::Transaction&, const intx::uint<256u>&, unsigned long, const monad::MonadChainContext&, monad::State&)" .<< 
      Atype (Tnamed ("monad::MonadTraits" .<< Avalue (Eint 10 "enum monad_revision") >>)) >>;
*)
    Set Printing Coercions.

    (*
               #[export] Hint Resolve pick_cfrac_and_split_C | 275 : sl_opacity.
  #[export] Hint Resolve pick_frac_and_split_C | 275 : sl_opacity.

  #[export] Hint Resolve _at_pick_cfrac_and_split_C | 275 : db_bluerock_syntactic.
  #[export] Hint Resolve _at_pick_frac_and_split_C | 275 : db_bluerock_syntactic.

  #[export] Hint Resolve primR_aggressive_frac_C | 280 : sl_opacity.
  #[export] Hint Resolve primR_agreement_F | 280 : sl_opacity.
    Remove Hints _at_pick_cfrac_and_split_C  _at_pick_frac_and_split_C : db_bluerock_syntactic. 
    Remove Hints pick_cfrac_and_split_C  pick_frac_and_split_C primR_aggressive_frac_C   : sl_opacity.
     *)
Ltac slautot rw := go; try name_locals; tryif progress(try (repeat (iExists _); go;  eagerUnifyC; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); rw; try (erewrite take_S_r;[| eauto;fail]))
  then slautot rw  else idtac.
    
  Ltac slauto := (slautot ltac:(autorewrite with syntactic (*equiv iff slbwd *); try iExistsDef; (*try rewrite left_id; *) (*try solveRefereceTo; *) try autounfold with unfold; try Forward.forward_reason; try Forward.rwHyps (*; try optionSomeBig;  try instOptionR*))); try iPureIntro.

Set Default Goal Selector "!".
  Set Printing Coercions.

  Set Printing Depth 99999999.

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

  Lemma nth_error_lengthN_succ {A : Type} (xs : list A) idx x :
    nth_error xs (N.to_nat idx) = Some x ->
    1 + idx <= lengthN xs.
  Proof using.
    intros Hltnth.
    pose proof (proj1 (nth_error_Some xs (N.to_nat idx))
      ltac:(congruence)) as Hlen.
    unfold lengthN.
    apply N2Z.inj_le.
    rewrite N2Z.inj_add.
    rewrite nat_N_Z.
    rewrite <- (N_nat_Z idx).
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hlen) as HlenZ.
    change (Z.of_N 1) with 1%Z.
    rewrite Z.add_1_l.
    apply Z.le_succ_l.
    exact HlenZ.
  Qed.

  Unset SsrIdents.
  Remove Hints MonadChainContextR_B : sl_opacity.


Opaque MonadChainContextR.
Opaque SenderAuthoritiesSetR.
Opaque uint256_word_modulus.
Opaque bytes32R.

Lemma prf:  verify[source] dipped_into_reserve_spec.
Proof using MODd.
  verify_spec'.
  name_locals.
  go.
  autorewrite with iff syntactic in *.
  subst.
  set (tx :=
    nth i
      (map (fun t : Transaction => (t, header (cblock ctx)))
         (transactions (cblock ctx)))
      dummyTx).
  match goal with
  | H : (Z.of_nat i <
         lengthZ (transactions (currentBlock (blocks ctx))))%Z |- _ =>
      rename H into Hi_bound
  end.
  assert (InstantiationOfType Transaction tx.1) as Hx by constructor.
  match goal with
  | H : validTx _ |- _ =>
      pose proof H as HvalidTx;
      destruct H as (Htx_nonce & Htx_gas & Htx_gas_price & Htx_fee)
  end.
  assert (H2_64_256 : (2 ^ 64 < 2 ^ 256)%N) by
    (apply N.pow_lt_mono_r; lia).
  assert (H2_128_256 : (2 ^ 128 < 2 ^ 256)%N) by
    (apply N.pow_lt_mono_r; lia).
  pose proof (nth_error_transactions_with_header_some ctx i Hi_bound) as Htxidx.
  fold tx in Htxidx.
  pose proof (tx_base_fee_per_gas_eq_of_txidx ctx i tx Htxidx)
    as Hfee_base.
  assert (Htx_gas_256 :
      (tx_gas_limit
         (nth i
            (map (fun t : Transaction => (t, header (cblock ctx)))
               (transactions (cblock ctx)))
            dummyTx).1.1 < 2 ^ 256)%N) by
    (eapply N.lt_trans; [exact Htx_gas | exact H2_64_256]).
  assert (Htx_gas_price_256 :
      (gas_price_cpp_model tx.1
         (exec_specs.base_fee_per_gas (cblock ctx)) < 2 ^ 256)%N).
  {
    rewrite <- Hfee_base.
    eapply N.lt_trans; [exact Htx_gas_price | exact H2_128_256].
  }
  go using
    skylabs.auto.cpp.hints.builtins.wp_operand_builtin_call_B,
    skylabs.auto.cpp.hints.builtins.wp_builtin_func_intro_B,
    builtin_expect_B_local.
  iExists tx.1.
  match goal with
    [|- context[newStates ?st] ]=> rename st into stm
  end.
  #[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
  run1.

  Remove Hints MonadChainContextR_F : sl_opacity.
  wapplyRev (@MonadChainContextR_equiv _ _ _ _ qctx).
  go.
  
  autorewrite with syntactic.
  go.
  name_locals.
  first
    [ rename __begin3_addr into beginp
    | rename __begin2_addr into beginp
    | rename __begin_addr into beginp
    | match goal with
      | Hbegin : type_ptr (Tnamed ?iter_ty) ?p |- _ =>
          match iter_ty with
          | context[Nid "iter_t"] => rename p into beginp
          end
      end ].
  wp_for (fun _ =>
    Exists (updates: gmap evm.address AssumptionExactness) (i:N),
      beginp |-> AnkerMapIterR "monad::Address" "monad::VersionStack<monad::AccountState>" true 1$m i (map (fun x=> x.2.1) (newStates stm))
        ** [| i <= lengthN (newStates stm)|] **
        let stf := update_assum_exactness_state stm updates in
        statep |-> StateR stf
        ** [| let checkedAcs := (map fst (takeN i (newStates stm))) in
              updates_stricter stm updates /\ (gdom updates) ⊆ checkedAcs /\
                forall (preTxState: StateOfAccounts),
                  satisfiesAssumptions stf preTxState ->
                  historyConsistent ctx hist ->
                  let postTxState :=  (applyUpdates stf preTxState) in
                  true = (allFinalBalSufficient 3 (preTxState, hist) postTxState checkedAcs tx) |]
         ).
  go.
  iExists (∅).
  progress unfold update_assum_exactness_state.
  rewrite empupd.
  go.
  provePure;[set_solver|].
  work.
  wapply (@observe_elim _ _ _
    (observeAnkerIter
      __end2_addr
      "monad::Address" "monad::VersionStack<monad::AccountState>" true
      (lengthN (newStates stm))
      (map (fun x => x.2.1) (newStates stm)))).
  wapply (@observe_elim _ _ _
    (observeAnkerIter
      beginp
      "monad::Address" "monad::VersionStack<monad::AccountState>" true
      t
      (map (fun x => x.2.1) (newStates stm)))).
  go using
    type_ptr_reference_to_B_local,
    anker_iter_keep_type_ptr_C,
    observeAnkerIterFt,
    observeAnkerIterRFt,
    observe_type_ptr_fwd,
    observe_type_ptr_box_fwd,
    type_ptr_elim_reference_to_C.
  go.
  wp_if.
  2:{
    (* loop terminates *)
    autorewrite with syntactic.
    go.
    progress (repeat iExists _; go).
    provePure;[| work; fail].
    intros.
    specialize (b0 preTxState).
    match goal with
    | Hhist : historyConsistent ctx hist |- _ =>
        specialize (b0 H Hhist)
    end.
    unfold takeN, lengthN in b0.
    rewrite Nat2N.id in b0.
    rewrite firstn_all in b0.
    autorewrite with syntactic in *; simpl; try reflexivity.
    change
      (nth i
         (map (fun t : Transaction => (t, header (cblock ctx)))
            (transactions (cblock ctx)))
         dummyTx) with tx.
    rewrite <- b0; reflexivity.
  }
  {
    (* loop continues *)
    go.
    autorewrite with syntactic.
    nthElemSomeName.
    assert (1 + t <= lengthN (newStates stm)) as Ht_succ_len by
      (eapply nth_error_lengthN_succ; eassumption).
    go.
    erewrite -> (ankerl_specs.borrowIndex);[| eassumption].
    go.
    go.
    autorewrite with syntactic.
    rewrite mpmp1.
    progress unfold validModel in *.
    simpl in *.
    rewrite bool_decide_true.
    2:{
      ren_hyp upds (gmap evm.address AssumptionExactness).
      apply nth_error_elem in Hltnth.
      set_solver.
    }
    go.
    Unset SsrIdents.
    destruct nthelem as [nthelemAddr [nthElemPtr nthElemVstack]].
    assert (nthElemVstack <> []) as Hvsnonempty by
      (eapply nth_error_newStates_nonempty_of_validPostNone_update_assum_exactness_state; eauto).
    simpl in *.
    destruct nthElemVstack as
      [| [nthElemVstackTopPtr nthElemVstackTop] nthElemVstackTl];
      [tauto |].
    simpl in *.
    go.
    name_locals.
    remember (isAcSC (postTxState nthElemVstackTop)) as sc.
    destruct sc.
    { (* the account of this iteration is a smart contract *)
      progress unfold isAcSC in Heqsc.
      case_match;[ | congruence].
      go.
      symmetry in Heqsc.
      autorewrite with iff in Heqsc.
      forward_reason.
      rewrite <- N.eqb_neq in Heqscl.
      Forward.rwHyps.
      rewrite N.eqb_neq in Heqscl.
      go.
      match goal with
      | H : postTxState ?nthElemVstackTop = Some ?a5,
        H2 : nth_error (newStates stm) (N.to_nat t) =
             Some (_, (_, (_, ?nthElemVstackTop) :: _)) |-
        _ =>
          iExists (block.block_account_code (coreAc a5))
      end.
      provePure.
      {
        erewrite read_code_program_of_newStates; eauto.
      }
      go.
      Forward.rwHyps.
      run1.
      go.
      iExistsTac ((eassumption)).
      go.
      autorewrite with syntactic.
      go.
      erewrite takeN_S_r2; [|eauto; fail].
      simpl.
      provePure.
      { 
        set_solver.
      }
      go.
      provePure.
      {
        intros.
        progress unfold allFinalBalSufficient.
        simpl.
        rewrite map_app.
        simpl.
        rewrite forallb_app.
        symmetry.
        autorewrite with iff.
        split;[symmetry;apply b0; auto |].
        simpl.
        autorewrite with iff.
        split;[| tauto].
        progress unfold finalBalSufficient.
        assert (NoDup (map fst (newStates stm))) as Hnd by (eapply NoDup_map_fst_newStates_of_map; eauto). (* TODO:move this whole section out in a separate lemma *)
        erewrite isSC_applyUpdates_true_nth_code; eauto.
      }
      go.
      unborrowAnkerPayload.
      go.
    }

    { (* the account of this iteration is NOT a smart contract *)
      revertAdr (effective_is_delegated_addr).
      match goal with
        |- envs_entails ?E _ =>
          (set e:= env_to_prop (env_spatial E))
      end.
      iIntrosDestructs.
      wp_if (fun _ => \pre e ** effective_is_delegated_addr |-> boolR 1$m false
                        \post e ** effective_is_delegated_addr |-> boolR 1$m (isAccountDelegated (postTxState nthElemVstackTop))).
      subst e.
      progress unfold isAccountDelegated.
      work.
      { (* if cond true *)
        case_match; simpl in *; try congruence;[].
        repeat iExists _; go.
        erewrite read_code_program_of_newStates; eauto;[].
        go.
        symmetry in Heqsc.
        autorewrite with syntactic in Heqsc.
        rewrite -> N_eqb_bool_decide in *.
        repeat case_bool_decide; try congruence;
          simpl in *; rewrite Heqsc; go.
      }
      { (* if cond false *)
        go.
        erewrite <- isDelegationMarker_false_of_code_hash_zero_postTxState; eauto.
      }
      go.
      iExists _.
      eagerUnifyU.
      go.
      provePure.
      {
        eapply mapModelLookup_is_Some_of_subset_nth; [| eauto].
        match goal with
        | H : _ ⊆ map fst
                  (update_assum_exactness_map (preTxAssumedState stm) _) |- _ =>
            apply H
        end.
      }
      go using
        observeDippedIntoReserveLambdaF_local,
        observeDippedIntoReserveLambdaRefThisF_local,
        wp_init_condition_B_local.
      match goal with
      | |- context[sender ?foo] => change foo with tx
      | _ => idtac
      end.
      go.
      progress unfold reserve_violation_threshold_model.
      destruct (decide (nthelemAddr = sender tx)); resolveDecide congruence.
      2:{ (* current addr is NOT the sender . this split is guided by the model, not the bbranching in C++ code *)
        simpl.
        repeat (rewrite bool_decide_false; [| congruence]).
        go using optional_specs.trivial_optional_some_split_F.
        repeat (
            iExists (newStates stm)
            || iExists (((nthElemVstackTopPtr,nthElemVstackTop)::nthElemVstackTl))
            || iExists _).
        unifyLoc (statep ,, o_field CU "monad::State::original_").
        assert (
            mapModelLookup (newStates stm) nthelemAddr =
              Some
                (nthElemPtr,
                  (nthElemVstackTopPtr, nthElemVstackTop)
                    :: nthElemVstackTl)) as HcurLookup.
        {
          unfold mapModelLookup.
          apply elem_of_list_to_map_1.
          {
            eapply NoDup_map_fst_newStates_of_map; eassumption.
          }
          apply list_elem_of_lookup_2 with (i := N.to_nat t).
          rewrite lookup_nth_error.
          exact Hltnth.
        }
        match goal with
        | |- context[StateCurrentLookupR statep ?q nthelemAddr (newStates stm)] =>
            unify q (1 : Qp)
        end.
        unfold StateCurrentLookupR.
        rewrite HcurLookup.
        go.
        Forward.rwHyps.
        autorewrite with syntactic.
        iExists t.
        rewrite nth_error_map.
        rewrite Hltnth.
        simpl.
        go.
        provePure.
        {
          eapply (mapModelLookup_is_Some_check_min_original_balance_update); eauto.
        }
        step.
        progress unfold check_min_balance_ok.
        autorewrite with syntactic in *.
        match goal with
          H: is_Some (mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _) nthelemAddr) |- _
          => pose proof H as Hupd
        end.
        eapply
          (update_assum_exactness_at_check_min_original_balance_update_to_map_exists
             (preTxAssumedState stm) _t_ nthelemAddr DefReserve
             (fun ex : AssumptionExactness =>
                min_balance_update ex
                  (original_balance_pessimistic_model_map
                     (update_assum_exactness_map (preTxAssumedState stm) _t_)
                     nthelemAddr)
                  (balanceOfAccount (postTxState nthElemVstackTop))
                  (DefReserve
                   `min`
                   original_balance_pessimistic_model_map
                     (update_assum_exactness_map (preTxAssumedState stm) _t_)
                     nthelemAddr))) in Hupd.
        2:
        {
          apply nodup_map_fst_update_assum_exactness_map; auto.
        }
        step.
        rewrite <-
          (skylabs.auto.cpp.hints.operators.wp_eval_not_bool source).
        rewrite <- !skylabs.auto.cpp.to_bool.bool_val_to_bool_intro.
        rewrite <- ignore_valid_bool_return_local.
        rewrite -interp_intro_id.
        rewrite -interp.interp_seq_interp.
        autorewrite with syntactic in *.
        step.
        step.
        step.
        match goal with
        | Hpost : state_original_account_state_post ?orig ?addr ?orig_final ?loc ?orig_state,
          Hsome : is_Some (mapModelLookup ?orig ?addr) |- _ =>
            destruct Hsome as [[orig_loc orig_state0] Horig_lookup];
            unfold state_original_account_state_post in Hpost;
            rewrite Horig_lookup in Hpost;
            destruct Hpost as [-> [-> ->]]
        end.
        unfold check_min_balance_recent_account_model,
          check_min_balance_update_model.
        rewrite HcurLookup.
        autorewrite with syntactic.
        destruct Hupd as (? & ? & ? & Hupd).
        rewrite Hupd.
        case_bool_decide_concl;
          fwd;
          go using optional_specs.trivial_optional_some_join_F;
          iExists _;
          unifyLoc (statep ,, o_field CU "monad::State::original_").
        all: (
          unfold txsWithHdr;
          autorewrite with syntactic;
          unborrowAnkerPayload;
          work;
          rewrite current_match_to_versionstack; eauto;
          work;
          cancelByUnfolding StateCodeMapR;
          provePure; [| work; fail]
        ).
        { eapply allFinalBalSufficient_takeN_succ_update_assum_exactness_state_insert; eauto with pure. }
        {
          intros.
          eapply nonSenderBalanceInsuff; eauto with pure; try autorewrite with syntactic; auto.
        }
      }
      { (* current iteration account is the sender *)
        go.
        rewrite Nltb_boo_decide.
        assert (
            match
              mapModelLookup (check_min_original_balance_update (update_assum_exactness_map (preTxAssumedState stm) _t_) (sender tx) DefReserve)
                (sender tx)
            with
            | Some (_, aps) =>
                match postTxState nthElemVstackTop with
                | Some am => isDelegationMarker (block.block_account_code (coreAc am))
                | None => false
                end =
                  match preTxState aps with
                  | Some am => isDelegationMarker (block.block_account_code (coreAc am))
                  | None => false
                  end && asbool (sender tx ∉ undels tx.1.2) || asbool (sender tx ∈ dels tx.1.2)
            | None => False
            end) as Hpreadd.
        {
          lazymatch goal with
          | Hpreadd_hyp :
              forall (i0 : N)
                     (nthElemPtr0 nthElemVstackTopPtr0 : ptr)
                     (nthElemVstackTop0 : UpdatedAccountState)
                     (nthElemVstackTl0 : list (ptr * UpdatedAccountState)), _ |- _ =>
              eapply (check_min_original_balance_update_match_preTxState_update_assum_exactness_map
                        (preTxAssumedState stm) _t_ (sender tx) DefReserve
                        (fun opre =>
                           match postTxState nthElemVstackTop with
                           | Some am =>
                               isDelegationMarker
                                 (block.block_account_code (coreAc am))
                           | None => false
                           end =
                           match opre with
                           | Some am =>
                               isDelegationMarker
                                 (block.block_account_code (coreAc am))
                           | None => false
                           end
                           && asbool (sender tx ∉ undels tx.1.2)
                           || asbool (sender tx ∈ dels tx.1.2)));
              eapply (Hpreadd_hyp t nthElemPtr nthElemVstackTopPtr nthElemVstackTop nthElemVstackTl)
          end.
          subst nthelemAddr.
          exact Hltnth.
        }
        applyToSomeHyp nth_error_transactions_with_header_some.
        (* hard to do join point reasoning.
           make the spec of can_sender_dip_into_reserve as easy as possible so that it directly applies from context.
         then just make cases. isAllowedToEmpty will be the same for all states satisfying assumptions. *)
        case_bool_decide_inner; go.
        { (* effective reserve balance insuff to cover fees *)
          (* we dont care about what is returned in this case as we will retry anyway *)
          (* currently, this will just not happen anyway *)
          go.
          go.
          iExistsTac ltac:(eassumption).
          iExists tx.
          iExists _,_.
          eagerUnifyC.
          go.
          autorewrite with syntactic.
          subst.
          go.
          iSplitR;[iPureIntro; apply Hpreadd|]. (* bug in go: doent solve a pure goal *)
          go.
          subst.
          go.
          unfold check_min_balance_ok.
          autorewrite with syntactic in *.
          match goal with
            H: is_Some (mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _) _) |- _
            => pose proof H as Hupd
          end.
          wp_if.
          {
            go.
            unfold txsWithHdr;
            autorewrite with syntactic;
            unborrowAnkerPayload;
            work;
            lazymatch goal with
            | Hnd :
                NoDup
                  (map _ (update_assum_exactness_map (preTxAssumedState ?stx) ?updatesx)),
              Hsome :
                is_Some
                  (mapModelLookup
                     (update_assum_exactness_map (preTxAssumedState ?stx) ?updatesx)
                     (sender ?tx0))
              |- _ =>
                pose proof Hnd as Hnd_upd;
                eapply state_original_check_min_rewrite_both_from_ctx in Hnd;
                  [| exact Hsome ]
            end;
            simpl in *;
            forward_reason;
            Forward.rwHyps;
            iExists _;
            unifyLoc (statep ,, o_field CU "monad::State::original_");
            go using
              observeDippedIntoReserveLambdaF_local,
              type_ptr_reference_to_B_local;
            cancelByUnfolding StateCodeMapR;
            iPureIntro.
            eapply senderReallyLowBalAndCannotDipIntoReseve; eauto with pure.
          }
          {
            go.
            {
              unfold txsWithHdr;
              autorewrite with syntactic;
              unborrowAnkerPayload;
              work;
              lazymatch goal with
              | Hnd :
                  NoDup
                    (map _ (update_assum_exactness_map (preTxAssumedState ?stx) ?updatesx)),
                Hsome :
                  is_Some
                    (mapModelLookup
                       (update_assum_exactness_map (preTxAssumedState ?stx) ?updatesx)
                       (sender ?tx0))
                |- _ =>
                  pose proof Hnd as Hnd_upd;
                  eapply state_original_check_min_rewrite_both_from_ctx in Hnd;
                    [| exact Hsome ]
              end;
              simpl in *;
              forward_reason;
              Forward.rwHyps;
              iExists _;
              unifyLoc (statep ,, o_field CU "monad::State::original_");
              go;
              cancelByUnfolding StateCodeMapR;
              iPureIntro.
              eapply senderReallyLowBalAndCanDipIntoReseve; eauto with pure.
            }
          }
          
        } 
        {
          go.
          simpl.
          go using optional_specs.trivial_optional_some_split_F.
          repeat (
              iExists (newStates stm)
              || iExists (((nthElemVstackTopPtr,nthElemVstackTop)::nthElemVstackTl))
              || iExists _).
          unifyPayload.
          subst nthelemAddr.
          assert (
              mapModelLookup (newStates stm) (sender tx) =
                Some
                  (nthElemPtr,
                    (nthElemVstackTopPtr, nthElemVstackTop)
                      :: nthElemVstackTl)) as HcurLookup.
          {
            unfold mapModelLookup.
            apply elem_of_list_to_map_1.
            {
              eapply NoDup_map_fst_newStates_of_map; eassumption.
            }
            apply list_elem_of_lookup_2 with (i := N.to_nat t).
            rewrite lookup_nth_error.
            exact Hltnth.
          }
          match goal with
          | |- context[StateCurrentLookupR statep ?q (sender tx) (newStates stm)] =>
              unify q (1 : Qp)
          end.
          unfold StateCurrentLookupR.
          rewrite HcurLookup.
          go.
          Forward.rwHyps.
          autorewrite with syntactic.
          iExists t.
          autorewrite with syntactic.
          rewrite Hltnth.
          simpl.
          set (gas_fee_model :=
            ((tx_gas_limit tx.1.1 *
              gas_price_model 10 tx.1
                (exec_specs.base_fee_per_gas (cblock ctx)))
             `mod` uint256_word_modulus)) in *.
          set (violation_threshold_model :=
            (DefReserve
             `min` original_balance_pessimistic_model_map
                     (update_assum_exactness_map
                        (preTxAssumedState stm) _t_)
                     (sender tx) -
             gas_fee_model)) in *.
          go.
          provePure.
          {
            eapply (mapModelLookup_is_Some_check_min_original_balance_update); eauto.
          }
          step.
          step.
          rewrite <-
            (skylabs.auto.cpp.hints.operators.wp_eval_not_bool source).
          rewrite <- !skylabs.auto.cpp.to_bool.bool_val_to_bool_intro.
          rewrite <- ignore_valid_bool_return_local.
          rewrite -interp_intro_id.
          rewrite -interp.interp_seq_interp.
          subst violation_threshold_model gas_fee_model.
          unfold check_min_balance_ok.
          autorewrite with syntactic in *.
          step.
          step.
          step.
          match goal with
            H: is_Some (mapModelLookup (update_assum_exactness_map (preTxAssumedState stm) _) _) |- _
            => pose proof H as Hupd
          end.
          eapply
            (update_assum_exactness_at_check_min_original_balance_update_to_map_exists
               (preTxAssumedState stm) _t_ (sender tx) DefReserve
               (fun ex : AssumptionExactness =>
                  min_balance_update ex
                    (original_balance_pessimistic_model_map
                       (update_assum_exactness_map (preTxAssumedState stm) _t_)
                       (sender tx))
                    (balanceOfAccount (postTxState nthElemVstackTop))
                    (DefReserve
                     `min`
                     original_balance_pessimistic_model_map
                       (update_assum_exactness_map (preTxAssumedState stm) _t_)
                       (sender tx) -
                     (tx_gas_limit tx.1.1 *
                      gas_price_model 10 tx.1
                        (exec_specs.base_fee_per_gas (cblock ctx)))
                       `mod` uint256_word_modulus))) in Hupd.
          2:
          {
            apply nodup_map_fst_update_assum_exactness_map; auto.
          }
          match goal with
          | Hpost :
              state_original_account_state_post
                (check_min_original_balance_update
                   (update_assum_exactness_map (preTxAssumedState stm) _t_)
                   (sender tx) DefReserve)
                (sender tx) ?orig_final ?loc ?orig_state,
            Hsome :
              is_Some
                (mapModelLookup
                   (check_min_original_balance_update
                      (update_assum_exactness_map (preTxAssumedState stm) _t_)
                      (sender tx) DefReserve)
                   (sender tx)) |- _ =>
              destruct Hsome as [[orig_loc orig_state0] Horig_lookup];
              unfold state_original_account_state_post in Hpost;
              rewrite Horig_lookup in Hpost;
              destruct Hpost as [-> [-> ->]]
          end.
          unfold check_min_balance_recent_account_model,
            check_min_balance_update_model.
          rewrite HcurLookup.
          autorewrite with syntactic.
          destruct Hupd as (? & ? & ? & Hupd).
          rewrite Hupd.
          case_bool_decide_concl;
            fwd;
            go using optional_specs.trivial_optional_some_join_F.
          { 
            unfold txsWithHdr.
            autorewrite with syntactic.
            unborrowAnkerPayload.
            work.
            rewrite current_match_to_versionstack; eauto.
            work.
            iExists _; 
              unifyLoc (statep ,, o_field CU "monad::State::original_").
            work.
            cancelByUnfolding StateCodeMapR.
            iPureIntro.
            eapply senderSuffBal; eauto.
          }
          
          { (* insufficient balance *)
            iExistsTac ltac:(eassumption).
            iExists tx.
            iExists _,_.
            unifyPayload.
            go.
            autorewrite with syntactic.
            go.
            go.
            iSplitR;
              [ iPureIntro;
                rewrite (rwlem2_rewrite ctx stm nthElemVstackTop _t_ tx x0 Hupd);
                tauto | ]. (* bug in go: doent solve a pure goal *)
            go.
            wp_if.
            all: (
              go;
              unfold txsWithHdr;
              autorewrite with syntactic;
              unborrowAnkerPayload;
              work;
              rewrite current_match_to_versionstack; eauto;
              work;
              iExists _;
              unifyLoc (statep ,, o_field CU "monad::State::original_");
              work;
              cancelByUnfolding StateCodeMapR;
              iPureIntro
            ).
            { eapply senderLowBalAndCannotDipIntoReseve; eauto. }
            {
              eapply senderLowBalAndCanDipIntoReseve; eauto; try lia.
              eapply validModel_of_components_update_assum_exactness_state; eauto.
            }
          }
        }
      }
    }
  }
Qed.


End with_Sigma.

(** To explain to agent:
- IPM.perm_left examples
- observe hints (ask it to write a section on this type of hints as it has done it many times)
- template specs. it learned from examples, but let it write a self-contained tutorial for future with references
- Learning hints
- 

*)

          

(*
The 2 occurrences of `MONAD_ASSERT_THROW` that are being deleted are basically the same: one for the uncached and one for the cached implementation of reserve balance.

There is a history of problems with this assert. In [November2025](https://github.com/category-labs/monad/commit/dfd5207b9ae874861f24e051a43db885ac94a20a), it was changed from `MONAD_ASSERT` to `MONAD_ASSERT_THROW` when it was discovered that this assert can fire when balance overrides are used in the RPC path. At that time, it was believed, including by me, that the assert can only fire in the RPC path but not when running as a live mainnet node where the transactions are coming from consensus which checks reserve balance conditions. 

While doing the Coq proof of this C++ code, I found that although it would not fire in live mainnet context, the reasoning is much more tricky than I thought initially thought. Perhaps the authors/reviewers had the same misunderstanding. Also, the reasoning may actually not hold if we further optimize the reserve balance design to be more permissive to users (e.g. allow multiple emptying transactions, track statically known credits to non-delegated accounts): if we do that, this deleted assert may crash the node under some interleavings of optimistic execution.

The issue is that even though consensus has ensured this assert condition, it estimates that by considering transactions sequentially (debiting fees (and value for emptying txs) one by one). But at this point in code, we may be doing speculative execution so the accound balances and account codes (which determines the delegation status) may be wrong/different from what will happen in the actual sequential execution, so the consensus guarantee of reserve balance being sufficient to pay at least the fee do not apply directly. Fortunately, there is no problem currently because the reserve-balance design is not very aggressive: it allows only 1 emptying transaction and disregards even statically known credits, even to non-delegated accounts:

We do [validate the transactions](https://github.com/category-labs/monad/blob/fa50e08ea0ce55fc2251312841658dda31632697/category/execution/ethereum/validate_transaction.cpp#L257) before reaching this point and only reach here when validation succeeds. The validation success implies that the original balance (speculatively assumed pre-tx balance) is at least as large as the max fee (+tx.value). For non-emptying transactions, this is sufficient because consensus also checks that for non-emptying transactions max_fee is <= 10 MON, and these 2 assumptions imply the asserted condition:
```
Lemma foo (original_bal value gas_fee: N) :
  value + gas_fee <= original_bal (* condition checked by transaction validation in execution. original_bal may be a speculated value *)
  -> gas_fee <= 10 (* condition checked by consensus for non-emptying txs. gas_fee is fixed for a tx and not affected by speculation *)
  -> gas_fee <= original_bal `min` 10 (* this assert *).
Proof. lia. Qed.
```

But for emptying transactions, consensus does *not* check that `gas_fee <= 10`. Fortunately, the assert occurs only inside the non-emptying case, when `can_sender_dip_into_reserve` returns false. But one problem is that because of speculation, the `Account::code` read in `dipped_into_reserve` to computed the delegation status for `can_sender_dip_into_reserve` may  not be what consensus used its calculations. But that turns out to not be a problem. This assert only pertains to the sender and we know the sender's address cannot be an SC (cryptographic hardness).So the sender's code is either empty or has a delegaton marker. But there can be a delegation mismatch: consensus considered the sender's account delegated as it would be in a sequential execution but this account is not delegated in speculative execution, or vice versa.
But if consensus determined that the tx was allowed to empty, then execution would also make the same determination: even if it speculatively reads `Account::code` even before the previous transaction has finished or even started. The reason is as follows:
If consensus determined that the tx was allowed to empty, there must be no delegation/undelegation requests (EIP7702 authorities) for the sender in this block, at least till this transaction. Also, the account must be undelegated at the beginning of the block. Also, any sender's account cannot be a smart contract, so `Account::code` must be empty. Thus `Account::code` must be empty in the pre-block state and remains empty during the execution of all the previous transactions. So even if speculative execution reads an state that is not that from the just previous transaction, it will read the correct delegation status (not delegated): the same as what consensus used in its calculations.
*)
