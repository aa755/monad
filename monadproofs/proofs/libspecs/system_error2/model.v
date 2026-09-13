Set Default Goal Selector "!".

(**
  Pure model of System Error 2 status-code domains and status codes.

  A C++ [status_code<Domain>] carries a domain-specific payload.  Erasing the
  C++ template argument does not erase that semantic payload: the erased object
  retains a runtime domain pointer and a representation of the payload.  The
  dependent [status_error] type below records exactly that relationship.

  This file deliberately contains no C++ types or separation-logic predicates.
  The physical System Error 2 representation is defined separately and indexed
  by this model.
*)

From Stdlib Require Import List NArith ZArith.

Import ListNotations.

(** System Error 2's generic domain uses values analogous to [std::errc].
    Keeping the value abstractly numeric here lets domain adapters state their
    generic mapping without imposing any representation on their own payload. *)
Definition generic_status : Type := Z.

(** A strict-equivalence key is a semantic rendezvous point chosen by domain
    adapters.  The namespace prevents unrelated domains from accidentally
    equating payloads that happen to use the same numeric value. *)
Record status_equivalence_key : Type := {
  status_key_namespace : N;
  status_key_value : Z;
}.

(**
  The operations modeled here are the observable virtual interface of
  [status_code_domain].

  [status_domain_strict_keys] describes the meanings offered by the left-hand
  code to its domain's directed [_do_equivalent] implementation.
  [status_domain_accepts_keys] describes meanings accepted when that code is
  used as the right-hand argument.  Keeping the two lists separate preserves
  the fact that [_do_equivalent] need not be symmetric.
*)
Record status_domain : Type := {
  (** Semantic type carried by status codes in this domain. *)
  status_domain_payload : Type;
  (** Runtime identity returned by [status_code_domain::id()]. *)
  status_domain_id : N;
  (** Human-readable result of [status_code_domain::name()]. *)
  status_domain_name : list N;
  (** Result of the virtual [_do_failure] operation. *)
  status_domain_failure : status_domain_payload -> bool;
  (** Result of the virtual [_do_message] operation. *)
  status_domain_message : status_domain_payload -> list N;
  (** Result of the virtual [_generic_code] operation, when meaningful. *)
  status_domain_generic : status_domain_payload -> option generic_status;
  (** Meanings offered by directed strict equivalence. *)
  status_domain_strict_keys :
    status_domain_payload -> list status_equivalence_key;
  (** Meanings accepted by directed strict equivalence. *)
  status_domain_accepts_keys :
    status_domain_payload -> list status_equivalence_key;
}.

(** A status error retains both its domain and that domain's payload type.
    Pattern matching on [StatusError] therefore reveals the payload with its
    correct type; it is not reduced to a raw [long] or an untyped token. *)
Inductive status_error : Type :=
| StatusError :
    forall domain : status_domain,
      status_domain_payload domain -> status_error.

Arguments StatusError domain payload.

Definition status_error_domain (error : status_error) : status_domain :=
  match error with
  | StatusError domain _ => domain
  end.

Definition status_error_domain_id (error : status_error) : N :=
  status_domain_id (status_error_domain error).

Definition status_error_failure (error : status_error) : bool :=
  match error with
  | StatusError domain payload => status_domain_failure domain payload
  end.

Definition status_error_message (error : status_error) : list N :=
  match error with
  | StatusError domain payload => status_domain_message domain payload
  end.

Definition status_error_generic (error : status_error)
    : option generic_status :=
  match error with
  | StatusError domain payload => status_domain_generic domain payload
  end.

Definition status_error_strict_keys (error : status_error)
    : list status_equivalence_key :=
  match error with
  | StatusError domain payload =>
      status_domain_strict_keys domain payload
  end.

Definition status_error_accepts_keys (error : status_error)
    : list status_equivalence_key :=
  match error with
  | StatusError domain payload =>
      status_domain_accepts_keys domain payload
  end.

(** This is the directed result modeled by
    [lhs.domain()._do_equivalent(lhs, rhs)]. *)
Definition status_error_strictly_equivalent
    (lhs rhs : status_error) : Prop :=
  exists key,
    In key (status_error_strict_keys lhs) /\
    In key (status_error_accepts_keys rhs).

(**
  [status_code::equivalent] first invokes strict equivalence in both
  directions.  If neither direction succeeds, it compares the generic codes
  produced by both domains.
*)
Definition status_error_equivalent (lhs rhs : status_error) : Prop :=
  status_error_strictly_equivalent lhs rhs \/
  status_error_strictly_equivalent rhs lhs \/
  exists generic,
    status_error_generic lhs = Some generic /\
    status_error_generic rhs = Some generic.

(**
  A domain-specific client safely recovers a payload by proving this relation.
  Its conclusion names the exact modeled domain, so no equality of numeric
  domain IDs is used to cast between unrelated payload types.
*)
Definition status_error_has_payload
    (domain : status_domain)
    (payload : status_domain_payload domain)
    (error : status_error) : Prop :=
  error = StatusError domain payload.

Lemma status_error_has_payload_domain_id
    domain payload error :
  status_error_has_payload domain payload error ->
  status_error_domain_id error = status_domain_id domain.
Proof.
  intros ->.
  reflexivity.
Qed.

Lemma status_error_equivalent_symmetric lhs rhs :
  status_error_equivalent lhs rhs ->
  status_error_equivalent rhs lhs.
Proof.
  intros [Hstrict | [Hstrict | [generic [Hlhs Hrhs]]]].
  - right; left; exact Hstrict.
  - left; exact Hstrict.
  - right; right.
    exists generic.
    auto.
Qed.
