Set Default Goal Selector "!".

(**
  Semantic and C++ adapter for Monad RLP [DecodeError].

  [DecodeError] is Monad-owned.  System Error 2 supplies the generic
  quick-enum mechanism, while this file fixes the domain UUID, messages,
  success/failure classification, generic mapping, and erased integer
  representation declared by [category/core/rlp/decode_error.*].
*)

From Stdlib Require Import List NArith Strings.Ascii Strings.String ZArith.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.elpi.cpp_enum.
Require Import skylabs.cpp.spec.concepts.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.libspecs.outcome_specs.
Require Import monad.proofs.libspecs.outcome_status_code_specs.
Require Import monad.proofs.libspecs.rlp_decode_error_model.
Require Import monad.proofs.libspecs.system_error2.all.

Import ListNotations.

(** The generated enum is kept in the C++ adapter layer.  The explicit map
    below makes its relationship to the pure logical error type auditable. *)
Module CppDecodeError.
  cpp.enum "monad::rlp::DecodeError" from storage_page_cpp.source variant.
End CppDecodeError.

Definition decode_error_ty : type :=
  "enum monad::rlp::DecodeError"%cpp_type.

Definition decode_error_to_cpp
    (error : DecodeError.DecodeError.t)
    : CppDecodeError.DecodeError.t :=
  match error with
  | DecodeError.DecodeError.TypeUnexpected =>
      CppDecodeError.DecodeError.TypeUnexpected
  | DecodeError.DecodeError.Overflow =>
      CppDecodeError.DecodeError.Overflow
  | DecodeError.DecodeError.InputTooLong =>
      CppDecodeError.DecodeError.InputTooLong
  | DecodeError.DecodeError.InputTooShort =>
      CppDecodeError.DecodeError.InputTooShort
  | DecodeError.DecodeError.ArrayLengthUnexpected =>
      CppDecodeError.DecodeError.ArrayLengthUnexpected
  | DecodeError.DecodeError.InvalidTxnType =>
      CppDecodeError.DecodeError.InvalidTxnType
  | DecodeError.DecodeError.LeadingZero =>
      CppDecodeError.DecodeError.LeadingZero
  | DecodeError.DecodeError.PathTooShort =>
      CppDecodeError.DecodeError.PathTooShort
  | DecodeError.DecodeError.PathTooLong =>
      CppDecodeError.DecodeError.PathTooLong
  | DecodeError.DecodeError.NonCanonical =>
      CppDecodeError.DecodeError.NonCanonical
  end.

Definition decode_error_to_val
    (error : DecodeError.DecodeError.t) : val :=
  CppDecodeError.DecodeError.to_val (decode_error_to_cpp error).

#[global] Instance decode_error_to_val_inj :
    Inj (=) (=) decode_error_to_val.
Proof.
  unfold Inj.
  intros lhs rhs Heq.
  unfold decode_error_to_val in Heq.
  apply CppDecodeError.DecodeError.to_val_inj in Heq.
  destruct lhs; destruct rhs;
    cbn [decode_error_to_cpp] in Heq;
    congruence.
Qed.

Fixpoint ascii_bytes (text : string) : list N :=
  match text with
  | EmptyString => []
  | String byte rest => N_of_ascii byte :: ascii_bytes rest
  end.

Definition decode_error_to_Z
    (error : DecodeError.DecodeError.t) : Z :=
  match error with
  | DecodeError.DecodeError.TypeUnexpected => 1
  | DecodeError.DecodeError.Overflow => 2
  | DecodeError.DecodeError.InputTooLong => 3
  | DecodeError.DecodeError.InputTooShort => 4
  | DecodeError.DecodeError.ArrayLengthUnexpected => 5
  | DecodeError.DecodeError.InvalidTxnType => 6
  | DecodeError.DecodeError.LeadingZero => 7
  | DecodeError.DecodeError.PathTooShort => 8
  | DecodeError.DecodeError.PathTooLong => 9
  | DecodeError.DecodeError.NonCanonical => 10
  end.

Lemma decode_error_to_Z_inj : Inj (=) (=) decode_error_to_Z.
Proof.
  intros lhs rhs Heq.
  destruct lhs; destruct rhs; cbn [decode_error_to_Z] in Heq;
    congruence.
Qed.

Definition decode_error_failure
    (_error : DecodeError.DecodeError.t) : bool := true.

Definition decode_error_message
    (error : DecodeError.DecodeError.t) : list N :=
  ascii_bytes
    (match error with
     | DecodeError.DecodeError.TypeUnexpected => "type unexpected"
     | DecodeError.DecodeError.Overflow => "overflow"
     | DecodeError.DecodeError.InputTooLong => "input too long"
     | DecodeError.DecodeError.InputTooShort => "input too short"
     | DecodeError.DecodeError.ArrayLengthUnexpected =>
         "array length unexpected"
     | DecodeError.DecodeError.InvalidTxnType => "invalid txn type"
     | DecodeError.DecodeError.LeadingZero => "leading zero"
     | DecodeError.DecodeError.PathTooShort => "path too short"
     | DecodeError.DecodeError.PathTooLong => "path too long"
     | DecodeError.DecodeError.NonCanonical => "non-canonical encoding"
     end)%string.

Definition decode_error_generic
    (_error : DecodeError.DecodeError.t) : option generic_status := None.

(** Result of System Error 2's [parse_uuid2] on
    [da6c5e8c-d6a1-101c-9cff-97a0f36ddcb9]. *)
Definition decode_error_domain_id : N := 6542829014486890852%N.

Definition decode_error_equivalence_key
    (error : DecodeError.DecodeError.t) : status_equivalence_key :=
  {|
    status_key_namespace := decode_error_domain_id;
    status_key_value := decode_error_to_Z error;
  |}.

Definition decode_error_status_domain : status_domain :=
  {|
    status_domain_payload := DecodeError.DecodeError.t;
    status_domain_id := decode_error_domain_id;
    status_domain_name := ascii_bytes "Decode Error"%string;
    status_domain_failure := decode_error_failure;
    status_domain_message := decode_error_message;
    status_domain_generic := decode_error_generic;
    status_domain_strict_keys :=
      fun error => [decode_error_equivalence_key error];
    status_domain_accepts_keys :=
      fun error => [decode_error_equivalence_key error];
  |}.

Definition decode_error_status_error
    (error : DecodeError.DecodeError.t) : status_error :=
  StatusError decode_error_status_domain error.

#[global] Instance decode_error_quick_enum_status_model :
    QuickEnumStatusModel decode_error_ty DecodeError.DecodeError.t :=
  {|
    quick_enum_status_error := decode_error_status_error;
    quick_enum_erased_value := decode_error_to_Z;
  |}.

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  #[global] Instance decode_error_BundledRep :
    concepts.BundledRep decode_error_ty DecodeError.DecodeError.t :=
    concepts.prim_BundledRep decode_error_to_val.

  Definition decode_error_status_code
      (error : DecodeError.DecodeError.t) : outcome_status_code :=
    quick_enum_erased_status_code decode_error_ty error.

  Lemma decode_error_status_code_is_failure error :
    status_error_failure
      (status_code_error (decode_error_status_code error)) = true.
  Proof.
    destruct error; reflexivity.
  Qed.

  #[global] Instance decode_error_StatusResultError :
    StatusResultError DecodeError.DecodeError.t :=
    {|
      status_result_error_code := decode_error_status_code;
      status_result_error_is_failure :=
        decode_error_status_code_is_failure;
    |}.

  #[global] Instance decode_error_to_status_code :
    OutcomeErrorConversion decode_error_ty outcome_error_ty
      DecodeError.DecodeError.t outcome_status_code :=
    status_result_error_conversion
      decode_error_ty DecodeError.DecodeError.t.
End with_cpp.
