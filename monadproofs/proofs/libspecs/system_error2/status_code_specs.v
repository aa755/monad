Set Default Goal Selector "!".

(**
  Generic C++ specifications for the erased System Error 2 status code used by
  Boost Outcome.

  This file stops at the third-party library boundary.  It specifies the
  quick-enum converting constructor, move constructor, destructor, and erased
  value observer in terms of [StatusCodeR].  Domain-specific adapters supply
  only [QuickEnumStatusModel]; they do not duplicate these C++ specs.
*)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.lang.cpp.cpp.
Require Import monad.proofs.libspecs.system_error2.layout.
Require Import monad.proofs.libspecs.system_error2.model.
Require Import monad.proofs.libspecs.system_error2.status_code_rep.

Import cQp_compat.

(** Semantic interpretation of one C++ quick-enum specialization. *)
Class QuickEnumStatusModel
    (enum_ty : type) (Enum : Type) : Type := {
  (** Error represented after System Error 2 converts the enum. *)
  quick_enum_status_error : Enum -> status_error;
  (** Integer bits stored by the inline quick-enum status code. *)
  quick_enum_erased_value : Enum -> Z;
}.
#[global] Hint Mode QuickEnumStatusModel + - : typeclass_instances.

Definition quick_enum_erased_status_code
    `{CU : genv} (enum_ty : type) {Enum : Type}
    `{Model : !QuickEnumStatusModel enum_ty Enum}
    (value : Enum) : erased_status_code_model :=
  {|
    status_code_domain_pointer :=
      _global (quick_enum_domain_global_name enum_ty);
    status_code_erased_value :=
      @quick_enum_erased_value enum_ty Enum Model value;
    status_code_error :=
      @quick_enum_status_error enum_ty Enum Model value;
  |}.

Definition erased_status_code_quick_enum_ctor_name
    (enum_ty : type) : name :=
  Ninst
    (Nscoped erased_errored_status_code_name
      (Nctor [Trv_ref enum_ty]))
    [Atype enum_ty; Atype (quick_enum_domain_ty enum_ty)].

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Definition erased_status_code_quick_enum_ctor_spec
      (enum_ty : type) {Enum : Type}
      `{!concepts.BundledRep enum_ty Enum}
      `{Model : !QuickEnumStatusModel enum_ty Enum} : mpred :=
    specify
      {|
        info_name := erased_status_code_quick_enum_ctor_name enum_ty;
        info_type :=
          tCtor erased_errored_status_code_name [Trv_ref enum_ty];
      |}
      (fun this : ptr =>
        \arg{valuep : ptr} "v" (Vref valuep)
        \prepost{value}
          valuep |-> concepts.objR enum_ty 1%Qp value
        \pre
          [| status_error_failure
               (@quick_enum_status_error
                  enum_ty Enum Model value) = true |]
        \post
          this |-> StatusCodeR 1%Qp
            (quick_enum_erased_status_code enum_ty value)).

  Definition erased_status_code_move_ctor_spec : mpred :=
    specify.exact.ctor erased_errored_status_code_name
      [Trv_ref erased_errored_status_code_ty]
      (fun this : ptr =>
        \arg{otherp : ptr} "" (Vref otherp)
        \pre{code}
          otherp |-> StatusCodeR 1%Qp code
        \post
          this |-> StatusCodeR 1%Qp code
          ** otherp |-> MovedStatusCodeR 1%Qp
               code.(status_code_erased_value)).

  Definition erased_status_code_dtor_spec : mpred :=
    specify.exact.dtor erased_errored_status_code_name
      (fun this : ptr =>
        \pre{state}
          this |-> ErasedStatusCodeStateR 1%Qp state
        \post emp).

  Definition erased_status_code_value_spec : mpred :=
    specify.exact.method
      (Nscoped erased_errored_status_code_name
        (Nfunction function_qualifiers.Nc "value" []))
      function_qualifiers.Nc
      Tlong
      []
      (fun this : ptr =>
        \prepost{q code}
          this |-> StatusCodeR q code
        \post
          [Vint
             code.(status_code_erased_value)] emp).

  Definition SpecFor_erased_status_code_quick_enum_ctor :=
    RegisterSpec (@erased_status_code_quick_enum_ctor_spec).

  Definition SpecFor_erased_status_code_move_ctor :=
    RegisterSpec erased_status_code_move_ctor_spec.

  Definition SpecFor_erased_status_code_dtor :=
    RegisterSpec erased_status_code_dtor_spec.

  Definition SpecFor_erased_status_code_value :=
    RegisterSpec erased_status_code_value_spec.
End with_cpp.

#[global] Existing Instance SpecFor_erased_status_code_quick_enum_ctor.
#[global] Existing Instance SpecFor_erased_status_code_move_ctor.
#[global] Existing Instance SpecFor_erased_status_code_dtor.
#[global] Existing Instance SpecFor_erased_status_code_value.

#[global] Arguments erased_status_code_quick_enum_ctor_spec : simpl never.
#[global] Arguments erased_status_code_move_ctor_spec : simpl never.
#[global] Arguments erased_status_code_dtor_spec : simpl never.
#[global] Arguments erased_status_code_value_spec : simpl never.

#[global] Hint Opaque
  erased_status_code_quick_enum_ctor_spec
  erased_status_code_move_ctor_spec
  erased_status_code_dtor_spec
  erased_status_code_value_spec
  : sl_opacity.
