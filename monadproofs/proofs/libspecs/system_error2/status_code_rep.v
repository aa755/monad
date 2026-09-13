Set Default Goal Selector "!".

(**
  Locked concrete representations of System Error 2 domains and erased errors.

  [StatusCodeR] follows the inheritance and field layout recorded in
  [layout.v].  Its logical index retains the semantic [status_error], while the
  heap owns the actual domain pointer and erased [long].  Ordinary clients use
  the observations below and do not unfold the representation.

  A status code does not exclusively own its process-wide domain singleton.
  [StatusDomainWitness] instead records persistent knowledge that the stored
  pointer denotes the semantic domain and supports its virtual interface.
  [StatusPayloadOwnership] accounts for resources represented by the erased
  word.  It is empty for inline quick-enum payloads, but can own an indirect
  allocation for domains such as System Error 2's nested-status domain.
*)

From Stdlib Require Import List.

Require Import skylabs.auto.cpp.proof.
Require Import monad.proofs.libspecs.system_error2.layout.
Require Import monad.proofs.libspecs.system_error2.model.

Import ListNotations.

(** Logical contents of a live erased status-code object.

    [status_code_domain_pointer] is retained because it is part of the concrete
    object identity.  Semantic operations use [status_code_error], not pointer
    equality or the erased numeric value. *)
Record erased_status_code_model : Type := {
  (** Address of the immutable [status_code_domain] singleton. *)
  status_code_domain_pointer : ptr;
  (** Bits stored in the erased [long].  They are explicit because nested
      status codes store a bit-cast allocation pointer rather than a numeric
      encoding computable from the semantic payload alone. *)
  status_code_erased_value : Z;
  (** Domain and domain-specific payload represented by this object. *)
  status_code_error : status_error;
}.

(** Persistent knowledge attached to a runtime domain pointer.

    The intended implementation contains the domain's type information and
    persistent [virtual.vptrI] facts for the [status_code_domain] interface.
    It does not own the singleton exclusively.  This is an abstract third-party
    library boundary because different System Error 2 domains have different
    most-derived C++ classes and virtual-method implementations. *)
Parameter StatusDomainWitness :
  forall `{Sigma : cpp_logic}, ptr -> status_domain -> mpred.

(** Resources represented by one erased payload word.

    For an inline quick-enum code this is a persistent/pure relation between the
    word and enum value.  For an indirecting domain it owns the allocation whose
    pointer representation is stored in [raw_value], including the nested status
    code and allocator state needed by [_do_erased_destroy].  The resource is
    fractional so read-only Outcome objects can share it; destruction requires
    full ownership and consumes it. *)
Parameter StatusPayloadOwnership :
  forall `{Sigma : cpp_logic}, cQp.t -> Z -> status_error -> mpred.

Axiom StatusDomainWitness_persistent :
  forall `{Sigma : cpp_logic} domainp domain,
    Persistent (StatusDomainWitness domainp domain).
#[global] Existing Instance StatusDomainWitness_persistent.

Axiom StatusPayloadOwnership_cfractional :
  forall `{Sigma : cpp_logic} raw_value error,
    CFractional
      (fun q => StatusPayloadOwnership q raw_value error).
#[global] Existing Instance StatusPayloadOwnership_cfractional.

(** Concrete base-subobject representation of [status_code_domain].

    [mdc] is the most-derived-class prefix.  It is explicit because the
    domain is polymorphic and BRiCk's [derivationR] records the dynamic
    dispatch path. *)
sl.lock Definition StatusDomainR
    `{Sigma : cpp_logic} {CU : genv}
    (mdc : list name) (q : cQp.t) (domain : status_domain) : Rep :=
  derivationR status_code_domain_name
    (mdc ++ [status_code_domain_name]) q **
  _field status_domain_id_field |->
    ulonglongR q (Z.of_N (status_domain_id domain)) **
  structR status_code_domain_name q.

(** The two physical fields of [status_code<detail::erased<long>>], wrapped
    in every empty inheritance layer up to [errored_status_code]. *)
sl.lock Definition ErasedStatusCodeObjectR
    `{Sigma : cpp_logic} {CU : genv}
    (q : Qp) (domainp : ptr) (raw_value : Z) : Rep :=
  structR erased_errored_status_code_name (cQp.mut q) **
  _base erased_errored_status_code_name erased_status_code_name |->
    (structR erased_status_code_name (cQp.mut q) **
     _base erased_status_code_name erased_status_mixin_name |->
       (structR erased_status_mixin_name (cQp.mut q) **
        _base erased_status_mixin_name erased_status_storage_name |->
          (structR erased_status_storage_name (cQp.mut q) **
           _field erased_status_value_field |->
             longR (cQp.mut q) raw_value **
           _base erased_status_storage_name status_code_void_name |->
             (structR status_code_void_name (cQp.mut q) **
              _field status_code_domain_field |->
                primR (Tptr (Qconst status_code_domain_ty))
                  (cQp.mut q) (Vptr domainp))))).

(** A live [errored_status_code] always denotes a failure.  The pure
    condition matches the runtime [_check()] performed by its constructors. *)
sl.lock Definition StatusCodeR
    `{Sigma : cpp_logic} {CU : genv}
    (q : Qp) (code : erased_status_code_model) : Rep :=
  ErasedStatusCodeObjectR q
     code.(status_code_domain_pointer)
     code.(status_code_erased_value) **
  pureR
    (StatusDomainWitness
       code.(status_code_domain_pointer)
       (status_error_domain code.(status_code_error))) **
  pureR
    (StatusPayloadOwnership
       (cQp.mut q)
       code.(status_code_erased_value)
       code.(status_code_error)) **
  [| status_error_failure code.(status_code_error) = true |].

(** State left by the System Error 2 move constructor.  It preserves the
    erased bits but clears the domain pointer, so destruction performs no
    virtual call. *)
Definition MovedStatusCodeR
    `{Sigma : cpp_logic} {CU : genv}
    (q : Qp) (raw_value : Z) : Rep :=
  ErasedStatusCodeObjectR q nullptr raw_value.

(** The destructor accepts either a live error or the null-domain source left
    by a move. *)
Inductive erased_status_code_state : Type :=
| StatusCodeLive : erased_status_code_model -> erased_status_code_state
| StatusCodeMoved : Z -> erased_status_code_state.

Definition ErasedStatusCodeStateR
    `{Sigma : cpp_logic} {CU : genv}
    (q : Qp) (state : erased_status_code_state) : Rep :=
  match state with
  | StatusCodeLive code => StatusCodeR q code
  | StatusCodeMoved raw_value => MovedStatusCodeR q raw_value
  end.

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv}.

  #[global] Instance StatusDomainR_cfractional mdc domain :
    CFractional (fun q => StatusDomainR mdc q domain).
  Proof.
    rewrite StatusDomainR.unlock.
    apply _.
  Qed.

  #[global] Instance ErasedStatusCodeObjectR_cfractional domainp raw_value :
    CFractional (fun q =>
      ErasedStatusCodeObjectR q domainp raw_value).
  Proof.
    rewrite ErasedStatusCodeObjectR.unlock.
    apply _.
  Qed.

  #[global] Instance StatusCodeR_cfractional code :
    CFractional (fun q => StatusCodeR q code).
  Proof.
    rewrite StatusCodeR.unlock.
    apply _.
  Qed.

  #[global] Instance StatusCodeR_as_cfractional q code :
    AsCFractional
      (StatusCodeR (cQp.frac q) code)
      (fun q => StatusCodeR (cQp.frac q) code)
      q.
  Proof.
    solve_as_cfrac.
  Qed.

  #[global] Instance StatusCodeR_fractional code :
    Fractional (fun q : Qp => StatusCodeR q code).
  Proof.
    change
      (Fractional
         (fun q : Qp => StatusCodeR (cQp.mk false q) code)).
    apply
      (cfractional_fractional_mk_0
         (fun q : cQp.t => StatusCodeR (cQp.frac q) code)
         false).
    apply StatusCodeR_cfractional.
  Qed.

  #[global] Instance StatusCodeR_as_fractional q code :
    AsFractional
      (StatusCodeR q code)
      (fun q => StatusCodeR q code)
      q.
  Proof.
    exact
      (fractional_as_fractional
         (fun q => StatusCodeR q code)
         q
         (StatusCodeR_fractional code)).
  Qed.

  #[global] Instance MovedStatusCodeR_cfractional raw_value :
    CFractional (fun q => MovedStatusCodeR q raw_value).
  Proof.
    unfold MovedStatusCodeR.
    apply _.
  Qed.

  #[global] Instance ErasedStatusCodeStateR_cfractional state :
    CFractional (fun q => ErasedStatusCodeStateR q state).
  Proof.
    destruct state; apply _.
  Qed.

  #[global] Instance observeStatusDomainRType mdc q domain :
    Observe (type_ptrR status_code_domain_ty)
      (StatusDomainR mdc q domain).
  Proof.
    rewrite StatusDomainR.unlock.
    apply _.
  Qed.

  #[global] Instance observeStatusCodeRType q code :
    Observe (type_ptrR erased_errored_status_code_ty)
      (StatusCodeR q code).
  Proof.
    rewrite StatusCodeR.unlock ErasedStatusCodeObjectR.unlock.
    apply _.
  Qed.

  #[global] Instance observeMovedStatusCodeRType q raw_value :
    Observe (type_ptrR erased_errored_status_code_ty)
      (MovedStatusCodeR q raw_value).
  Proof.
    unfold MovedStatusCodeR.
    rewrite ErasedStatusCodeObjectR.unlock.
    apply _.
  Qed.

  #[global] Instance observeStatusCodeRFailure q code :
    Observe
      ([| status_error_failure code.(status_code_error) = true |] : Rep)
      (StatusCodeR q code).
  Proof.
    rewrite StatusCodeR.unlock.
    apply _.
  Qed.

  Definition observeStatusDomainRType_F :=
    ltac:(mk_at_obs_fwd (@observeStatusDomainRType)).

  Definition observeStatusCodeRType_F :=
    ltac:(mk_at_obs_fwd (@observeStatusCodeRType)).

  Definition observeMovedStatusCodeRType_F :=
    ltac:(mk_at_obs_fwd (@observeMovedStatusCodeRType)).

  Definition observeStatusCodeRFailure_F :=
    ltac:(mk_at_obs_fwd (@observeStatusCodeRFailure)).

  Hint Resolve
    observeStatusDomainRType_F
    observeStatusCodeRType_F
    observeMovedStatusCodeRType_F
    observeStatusCodeRFailure_F
    : sl_opacity.
End with_cpp.

#[global] Hint Resolve
  observeStatusDomainRType_F
  observeStatusCodeRType_F
  observeMovedStatusCodeRType_F
  observeStatusCodeRFailure_F
  : sl_opacity.
