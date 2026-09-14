Set Default Goal Selector "!".

(*
  Adapter between the generic Boost Outcome specifications and Monad's common
  [Result<T>] error type.  The generic Outcome layer does not know that Monad
  uses [system_error2::errored_status_code<...>].  This layer supplies an
  concrete System Error 2 representation so moves preserve the domain and
  domain-specific payload, rather than merely remembering that some error
  occurred.
*)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.lang.cpp.cpp.
Require Import monad.proofs.libspecs.outcome_specs.
Require Import monad.proofs.libspecs.result_model.
Require Import monad.proofs.libspecs.system_error2.all.

Import cQp_compat.

(** Internal logical index used by the generic Outcome layer.  Ordinary Monad
    clients use [ResultR] below and therefore do not see this representation
    record. *)
Definition outcome_status_code : Type := erased_status_code_model.

Definition outcome_error_ty : type := erased_errored_status_code_ty.

#[global] Instance outcome_error_BundledRep
    `{Sigma : cpp_logic} {CU : genv} :
  concepts.BundledRep outcome_error_ty outcome_status_code :=
  {| concepts.objR := StatusCodeR |}.

#[global] Instance status_code_failure_model
    `{Sigma : cpp_logic} {CU : genv} :
  OutcomeFailureModel outcome_error_ty outcome_status_code := {}.

(** [StatusResultError E] supplies the status-code encoding needed to construct
    and propagate [E] through [status_result].  It deliberately does not require
    that this encoding be injective: the base Outcome interface observes the
    stored status code, not the original Gallina constructor.  Thus [ResultR]
    represents errors modulo this encoding.  A client that recovers and
    distinguishes application errors must provide a separate, domain-specific
    law relating System Error 2's semantic [equivalent] operation to equality
    on [E]. *)
Class StatusResultError (E : Type) : Type := {
  status_result_error_code : E -> outcome_status_code;
  (** Every [Result.Err] value maps to a live
      [errored_status_code], never to a success-valued status code. *)
  status_result_error_is_failure error :
    status_error_failure
      (status_code_error (status_result_error_code error)) = true;
}.
#[global] Hint Mode StatusResultError - : typeclass_instances.

(** Generic logical conversion used by Outcome's converting error
    constructor.  A concrete C++ error type still supplies its own
    [BundledRep]; this adapter only reuses the application error's canonical
    status-code encoding and failure guarantee. *)
Definition status_result_error_conversion
    (input_error_ty : type) (E : Type)
    `{ErrorModel : !StatusResultError E} :
    OutcomeErrorConversion
      input_error_ty outcome_error_ty E outcome_status_code :=
  {|
    outcome_convert_error := status_result_error_code;
    outcome_error_conversion_succeeds :=
      fun error =>
        status_error_failure
          (status_code_error (status_result_error_code error)) = true;
  |}.

Definition result_to_outcome_state {A E : Type}
    `{ErrorModel : !StatusResultError E}
    (result : Result.t A E) : outcome_result_state A outcome_status_code :=
  match result with
  | Result.Ok value => OutcomeValue value
  | Result.Err error =>
      OutcomeError (@status_result_error_code E ErrorModel error)
  end.

(** Public representation of Monad's default [status_result<T>].  The
    application chooses the logical error type [E]; [StatusResultError E]
    hides its conversion to System Error 2's erased C++ error member. *)
sl.lock Definition ResultR
    `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}
    {A E : Type} (value_ty : type)
    `{!concepts.BundledRep value_ty A}
    `{!StatusResultError E}
    (q : Qp) (result : Result.t A E) : Rep :=
  OutcomeResultR
    (outcome_result_name
       value_ty outcome_error_ty
       (outcome_status_code_throw_policy_ty value_ty outcome_error_ty))
    value_ty outcome_error_ty q
    (result_to_outcome_state result).

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Lemma ResultR_unpack {A E} value_ty
      `{!concepts.BundledRep value_ty A}
      `{!StatusResultError E}
      (p : ptr) q (result : Result.t A E) :
    p |-> ResultR value_ty q result
    |--
    p |-> OutcomeResultR
      (outcome_result_name
         value_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty value_ty outcome_error_ty))
      value_ty outcome_error_ty q
      (result_to_outcome_state result).
  Proof.
    rewrite ResultR.unlock.
    reflexivity.
  Qed.

  Lemma ResultR_pack {A E} value_ty
      `{!concepts.BundledRep value_ty A}
      `{!StatusResultError E}
      (p : ptr) q (result : Result.t A E) :
    p |-> OutcomeResultR
      (outcome_result_name
         value_ty outcome_error_ty
         (outcome_status_code_throw_policy_ty value_ty outcome_error_ty))
      value_ty outcome_error_ty q
      (result_to_outcome_state result)
    |--
    p |-> ResultR value_ty q result.
  Proof.
    rewrite ResultR.unlock.
    reflexivity.
  Qed.

  Definition ResultR_unpack_F {A E} value_ty
      `{!concepts.BundledRep value_ty A}
      `{!StatusResultError E}
      p q (result : Result.t A E) :=
    [FWD] (ResultR_unpack value_ty p q result).

  Definition ResultR_pack_B {A E} value_ty
      `{!concepts.BundledRep value_ty A}
      `{!StatusResultError E}
      p q (result : Result.t A E) :=
    [BWD] (ResultR_pack value_ty p q result).

  #[global] Instance observeResultRType {A E} value_ty
      `{!concepts.BundledRep value_ty A}
      `{!StatusResultError E} q result :
    Observe
      (type_ptrR
         (Tnamed
            (outcome_result_name
               value_ty outcome_error_ty
               (outcome_status_code_throw_policy_ty
                  value_ty outcome_error_ty))))
      (ResultR value_ty q result).
  Proof.
    rewrite ResultR.unlock.
    apply _.
  Qed.

  Definition observeResultRType_F :=
    ltac:(mk_at_obs_fwd (@observeResultRType)).
End with_Sigma.

#[global] Hint Resolve observeResultRType_F : sl_opacity.
