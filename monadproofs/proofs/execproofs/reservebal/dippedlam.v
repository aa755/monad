Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.fiber_specs.
Import optional_specs.
Import fiber_specs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.invariants.
Require Import skylabs.auto.cpp.proof.

Require Import skylabs.auto.cpp.tactics4.
Require Import monad.asts.reserve_balance_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.execproofs.reservebal.reservebal_specs.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.evmc_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import monad.proofs.libspecs.span_specs.
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
Require Import monad.proofs.execproofs.reservebal.dippedlam_lemmas.
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

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

cpp.spec ("std::min(const monad::uint256_t&, const monad::uint256_t&)"
  .<< Atype "monad::uint256_t" >>) from reserve_balance_cpp.source inline.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : reserve_balance_cpp.source ⊧ CU}.

  #[local] Instance learn_block_state_rfrag :
    AtLearnEq3 BlockState.Rfrag :=
    ltac:(solve_learnable).

  Ltac slauto := (slautot ltac:(autorewrite with syntactic (*equiv iff slbwd *); try iExistsDef; (*try rewrite left_id; *) try autounfold with unfold; try Forward.forward_reason; try Forward.rwHyps (*; try optionSomeBig;  try instOptionR*))); try iPureIntro.
        
  Disable Notation "::wpS".
  Disable Notation "::wpL".
  Hint Rewrite map_fst_update_assum_exactness_map : syntactic.
  Hint Rewrite
    current_balance_pessimistic_model_stack_cons
    original_balance_pessimistic_model_map_check_min_original_balance_update
    original_balance_pessimistic_model_map_update_assum_exactness_at
    preTxAccountOf_map_update_assum_exactness_at
    get_original_balance_update_after_failed_check_min
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
  Disable Notation "::wpPRᵢ".
(*
  Let get_orig_wpp : spec_type val
    (tMethod "monad::State" QM "intx::uint<256u>"
      ["const monad::Address&"%cpp_type]) :=
    fun this0 : ptr =>
      \arg{addrp0 : ptr} "address" (Vptr addrp0)
      \pre{orig0 : MapModel evm.address AssumedPreTxAccountState}
        this0 |-> StateOriginalR orig0
      \prepost{(q : Qp) (addr0 : evm.address)}
        addrp0 |-> addressR q addr0
      \pre [| is_Some (mapModelLookup orig0 addr0) |]
      \post{retp : ptr}[Vptr retp]
        retp |-> bytes32R 1
          (original_balance_pessimistic_model_map orig0 addr0)
        ** this0 |-> StateOriginalR orig0.

  Let get_orig_wpp_exact : spec_type val
    (tMethod "monad::State" QM "intx::uint<256u>"
      ["const monad::Address&"%cpp_type]) :=
    fun this0 : ptr =>
      \arg{addrp : ptr} "address" (Vptr addrp)
      \pre{orig : MapModel evm.address AssumedPreTxAccountState}
        this0 |-> StateOriginalR orig
      \prepost{(q : Qp) (addr : evm.address)}
        addrp |-> addressR q addr
      \pre [| is_Some (mapModelLookup orig addr) |]
      \post{retp : ptr}[Vptr retp]
        retp |-> bytes32R 1
          (original_balance_pessimistic_model_map orig addr)
        ** this0 |-> StateOriginalR orig.
*)
Lemma prf:  verify[source] dipped_into_reserve_lam_call_spec.
Proof.
  verify_spec'.
  name_locals.
  go.
  iExists orig.
  go.
  (* std::min compares original balance with the cap. Its two arms recover
     exactly the two reserve values used by the previous threshold proof. *)
  wp_if.
  {
    intros Hsmall.
    assert (Hok : check_min_balance_ok
      (original_balance_pessimistic_model_map orig addr) DefReserve = false).
    { unfold check_min_balance_ok. apply bool_decide_false. lia. }
    go.
    wp_if.
    {
      intros ->.
      go.
      wp_if.
      {
        intros Hlt.
        go.
        erewrite reserve_violation_threshold_model_sender_false_none;
          [|exact Hok|exact Hlt].
        go.
      }
      {
        intros Hle.
        erewrite reserve_violation_threshold_model_sender_false_some;
          [|exact Hok|exact Hle].
        go.
        rewrite (u256_sub_mod_small _ _ Hle ltac:(assumption)).
        go.
      }
    }
    {
      intros Hneq.
      go.
      unfold reserve_violation_threshold_model.
      rewrite bool_decide_eq_false_2; [|exact Hneq].
      rewrite N.min_r; [|lia].
      go.
    }
  }
  {
    intros Hlarge.
    assert (Hok : check_min_balance_ok
      (original_balance_pessimistic_model_map orig addr) DefReserve = true).
    { unfold check_min_balance_ok. apply bool_decide_true. lia. }
    go.
    wp_if.
    {
      intros ->.
      go.
      wp_if.
      {
        intros Hlt.
        go.
        erewrite reserve_violation_threshold_model_sender_true_none;
          [|exact Hok|exact Hlt].
        go.
      }
      {
        intros Hle.
        go.
        erewrite reserve_violation_threshold_model_sender_true_some;
          [|exact Hok|exact Hle].
        assert (HDefLt : (DefReserve < 2 ^ 256)%N).
        { closedN. lia. }
        rewrite <- (u256_sub_mod_small DefReserve gas_fees Hle HDefLt).
        go.
      }
    }
    {
      intros Hneq.
      go.
      unfold reserve_violation_threshold_model.
      rewrite bool_decide_eq_false_2; [|exact Hneq].
      rewrite N.min_l; [|lia].
      go.
    }
  }
Qed.

End with_Sigma.
