Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.invariants.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.

Require Import monad.asts.reserve_balance_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.reservebalold.

Set Warnings "+sl-impossible-patterns".
Set Default Goal Selector "!".
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.

  Lemma map_assumed_pre_tx_state_key_ptrs
      (orig : MapModel evm.address AssumedPreTxAccountState) :
    map (λ '(a, (b, _)), (a, b)) orig =
    map
      (λ pat : evm.address * (ptr * AssumedPreTxAccountState),
         let (a1, y) := pat in let (b0, _) := y in (a1, b0))
      orig.
  Proof.
    induction orig as [| [a [b aps]] tl IH]; simpl; [reflexivity |].
    now f_equal.
  Qed.

  Lemma reserve_violation_threshold_model_sender_true_none
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (gas_fees : N) :
    check_min_balance_ok
      (original_balance_pessimistic_model_map orig addr) DefReserve = true ->
    (DefReserve < gas_fees)%N ->
    reserve_violation_threshold_model orig addr addr gas_fees = None.
  Proof.
    intros Hok Hlt.
    unfold reserve_violation_threshold_model.
    rewrite bool_decide_eq_true_2; [|reflexivity].
    unfold check_min_balance_ok in Hok.
    apply bool_decide_eq_true_1 in Hok.
    rewrite N.min_l; [|exact Hok].
    apply N.ltb_lt in Hlt.
    now rewrite Hlt.
  Qed.

  Lemma reserve_violation_threshold_model_sender_true_some
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (gas_fees : N) :
    check_min_balance_ok
      (original_balance_pessimistic_model_map orig addr) DefReserve = true ->
    (gas_fees <= DefReserve)%N ->
    reserve_violation_threshold_model orig addr addr gas_fees =
    Some (DefReserve - gas_fees).
  Proof.
    intros Hok Hle.
    unfold reserve_violation_threshold_model.
    rewrite bool_decide_eq_true_2; [|reflexivity].
    unfold check_min_balance_ok in Hok.
    apply bool_decide_eq_true_1 in Hok.
    rewrite N.min_l; [|exact Hok].
    apply N.ltb_ge in Hle.
    now rewrite Hle.
  Qed.

  Lemma reserve_violation_threshold_model_sender_false_none
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (gas_fees : N) :
    check_min_balance_ok
      (original_balance_pessimistic_model_map orig addr) DefReserve = false ->
    (original_balance_pessimistic_model_map orig addr < gas_fees)%N ->
    reserve_violation_threshold_model orig addr addr gas_fees = None.
  Proof.
    intros Hok Hlt.
    unfold reserve_violation_threshold_model.
    rewrite bool_decide_eq_true_2; [|reflexivity].
    unfold check_min_balance_ok in Hok.
    apply bool_decide_eq_false_1 in Hok.
    apply N.nle_gt in Hok.
    rewrite N.min_r; [|apply N.lt_le_incl; exact Hok].
    apply N.ltb_lt in Hlt.
    now rewrite Hlt.
  Qed.

  Lemma reserve_violation_threshold_model_sender_false_some
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) (gas_fees : N) :
    check_min_balance_ok
      (original_balance_pessimistic_model_map orig addr) DefReserve = false ->
    (gas_fees <= original_balance_pessimistic_model_map orig addr)%N ->
    reserve_violation_threshold_model orig addr addr gas_fees =
    Some (original_balance_pessimistic_model_map orig addr - gas_fees).
  Proof.
    intros Hok Hle.
    unfold reserve_violation_threshold_model.
    rewrite bool_decide_eq_true_2; [|reflexivity].
    unfold check_min_balance_ok in Hok.
    apply bool_decide_eq_false_1 in Hok.
    apply N.nle_gt in Hok.
    rewrite N.min_r; [|apply N.lt_le_incl; exact Hok].
    apply N.ltb_ge in Hle.
    now rewrite Hle.
  Qed.

  Lemma u256_sub_mod_small
      (x y : N) :
    (y <= x)%N ->
    (x < 2 ^ 256)%N ->
    Z.to_N ((Z.of_N x - Z.of_N y) mod 2 ^ 256)%Z = x - y.
  Proof.
    intros Hle Hlt.
    assert (Hinjsub :
      (Z.of_N (x - y) = Z.of_N x - Z.of_N y)%Z).
    { apply N2Z.inj_sub. exact Hle. }
    rewrite <- Hinjsub.
    rewrite Z.mod_small.
    2: { pose proof Hlt. lia. }
    rewrite N2Z.id.
    reflexivity.
  Qed.

  Lemma exact_balance_update_min_balance_update_failed
      (ex : AssumptionExactness)
      (orig cur debit : N) :
    check_min_balance_ok cur debit = false ->
    exact_balance_update (min_balance_update ex orig cur debit) =
    min_balance_update ex orig cur debit.
  Proof.
    intros Hok.
    unfold exact_balance_update, min_balance_update.
    now rewrite Hok.
  Qed.

  Lemma get_original_balance_update_after_failed_check_min
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address)
      (max_reserve : N) :
    check_min_balance_ok
      (original_balance_pessimistic_model_map orig addr) max_reserve = false ->
    update_assum_exactness_at addr exact_balance_update
      (check_min_original_balance_update orig addr max_reserve) =
    check_min_original_balance_update orig addr max_reserve.
  Proof.
    intros Hok.
    unfold check_min_original_balance_update, update_assum_exactness_at.
    rewrite map_map.
    apply map_ext.
    intros [addr' [loc aps]].
    simpl.
    destruct (decide (addr' = addr)) as [->|Hneq].
    - rewrite (bool_decide_eq_true_2 (addr = addr)); [|reflexivity].
      rewrite (bool_decide_eq_true_2 (addr = addr)); [|reflexivity].
      simpl.
      f_equal.
      f_equal.
      f_equal.
      apply exact_balance_update_min_balance_update_failed.
      exact Hok.
    - rewrite (bool_decide_eq_false_2 (addr' = addr) Hneq).
      rewrite (bool_decide_eq_false_2 (addr' = addr) Hneq).
      reflexivity.
  Qed.

  Lemma observeDippedIntoReserveLambda
      (this addrp statep senderp gas_feesp : ptr) :
    Observe (type_ptr (Tnamed dipped_into_reserve_lam) this)
      (this |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp).
  Proof.
    apply observe_intro; [exact _|].
    unfold DippedIntoReserveLambdaR.
    go.
  Qed.

  Definition observeDippedIntoReserveLambdaF
      (this addrp statep senderp gas_feesp : ptr) :=
    @observe_fwd _ _ _
      (observeDippedIntoReserveLambda this addrp statep senderp gas_feesp).

  Lemma observeDippedIntoReserveLambdaRefThis (this : ptr) :
    Observe (reference_to (Tnamed dipped_into_reserve_lam) this)
      (this |-> structR dipped_into_reserve_lam 1$m).
  Proof.
    apply observe_intro; [exact _|].
    go.
  Qed.

  Definition observeDippedIntoReserveLambdaRefThisF (this : ptr) :=
    @observe_fwd _ _ _ (observeDippedIntoReserveLambdaRefThis this).

  Definition wp_init_condition_B := [BWD] wp_init_condition.
End with_Sigma.

#[global] Hint Rewrite map_assumed_pre_tx_state_key_ptrs : syntactic.
#[global] Hint Resolve observeDippedIntoReserveLambdaF : sl_opacity.
#[global] Hint Resolve observeDippedIntoReserveLambdaRefThisF : sl_opacity.
#[global] Hint Resolve wp_init_condition_B : sl_opacity.
