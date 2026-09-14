Set Default Goal Selector "!".

(*
  Generic representation predicates and specifications for the part of Boost
  Outcome used by Monad's [Result<T>] code.

  This file owns the Boost boundary.  A concrete [basic_result] name
  structurally determines its value, error, and policy types.  Existing
  [BundledRep] instances then determine the corresponding logical models.
  Client files must not duplicate the Boost function-template specifications
  below.
*)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.lang.cpp.cpp.

Import cQp_compat.

(** A live result contains either a value or an error.  [OutcomeMoved] is the
    valid but semantically unspecified source state left by operations such as
    [try_operation_return_as], which move the active error into another object.
    Keeping it distinct prevents a move spec from duplicating the logical
    payload between source and destination. *)
Inductive outcome_result_state (A E : Type) : Type :=
| OutcomeValue (value : A) : outcome_result_state A E
| OutcomeError (error : E) : outcome_result_state A E
| OutcomeMoved : outcome_result_state A E.

Arguments OutcomeValue {A E} _.
Arguments OutcomeError {A E} _.
Arguments OutcomeMoved {A E}.

(** A [failure_type] is itself moved when it is propagated into another
    result. *)
Inductive outcome_failure_state (E : Type) : Type :=
| OutcomeFailureValue (error : E) : outcome_failure_state E
| OutcomeFailureMoved : outcome_failure_state E.

Arguments OutcomeFailureValue {E} _.
Arguments OutcomeFailureMoved {E}.

Definition outcome_result_has_value {A E}
    (result : outcome_result_state A E) : bool :=
  match result with
  | OutcomeValue _ => true
  | OutcomeError _ | OutcomeMoved => false
  end.

(** The canonical cpp2v name of [boost::outcome_v2::basic_result<T, E, P>].
    Keeping this definition transparent lets registered-spec unification
    recover all three template arguments from a concrete AST symbol. *)
Definition outcome_result_name
    (value_ty error_ty policy_ty : type) : name :=
  Ninst
    "boost::outcome_v2::basic_result"%cpp_name
    [Atype value_ty; Atype error_ty; Atype policy_ty].

(** The policy used by Monad's current Outcome aliases.  It remains a separate
    constructor from [outcome_result_name], so the generic result specs do not
    assume this particular policy. *)
Definition outcome_status_code_throw_policy_ty
    (value_ty error_ty : type) : type :=
  Tnamed
    (Ninst
       "boost::outcome_v2::experimental::policy::status_code_throw"%cpp_name
       [Atype value_ty; Atype error_ty; Atype Tvoid]).

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  (** Boost Outcome stores status and policy bookkeeping separately from the
      active union member.  This predicate abstracts that non-payload state for
      a live object. *)
  Parameter OutcomeResultStatusR : name -> Qp -> bool -> Rep.

  #[global] Declare Instance OutcomeResultStatusR_cfractional result_name :
    CFractional1 (OutcomeResultStatusR result_name).

  #[global] Instance OutcomeResultStatusR_as_cfractional result_name :
    AsCFractional1 (OutcomeResultStatusR result_name).
  Proof.
    solve_as_cfrac.
  Qed.

  (** These implementation-defined offsets locate the alternatives in Boost's
      union storage.  Clients can use a returned value reference without
      depending on Boost's inheritance layout. *)
  Parameter outcome_result_value_offset : name -> offset.
  Parameter outcome_result_error_offset : name -> offset.

  (** A moved-from result still owns a valid, destructible Boost object, but its
      former payload is no longer available.  This abstract payload owns the
      implementation fields other than the [structR] witness. *)
  Parameter OutcomeResultMovedPayloadR : name -> Qp -> Rep.

  (** Constructor tags are Boost-owned objects.  Their representation remains
      abstract because no tag method is verified. *)
  Parameter OutcomeTagR : type -> Qp -> Rep.

  Definition outcome_has_value_overload_name : name :=
    "boost::outcome_v2::detail::has_value_overload"%cpp_name.

  Definition outcome_as_failure_overload_name : name :=
    "boost::outcome_v2::detail::as_failure_overload"%cpp_name.

  Definition outcome_assume_value_overload_name : name :=
    "boost::outcome_v2::detail::assume_value_overload"%cpp_name.

  Definition outcome_has_value_overload_ty : type :=
    Tnamed outcome_has_value_overload_name.

  Definition outcome_as_failure_overload_ty : type :=
    Tnamed outcome_as_failure_overload_name.

  Definition outcome_assume_value_overload_ty : type :=
    Tnamed outcome_assume_value_overload_name.

  Definition outcome_failure_name_for (error_ty : type) : name :=
    Ninst "boost::outcome_v2::failure_type"%cpp_name
      [Atype error_ty; Atype "void"%cpp_type].

  (** The complete [failure_type<E>] object is abstract because Boost is a
      library boundary.  It is indexed by the logical error so propagation
      specs can state that the same error is transferred.  The separate type
      observation below is the only layout fact exposed to automation. *)
  Parameter OutcomeFailureR :
    forall {E : Type}, type -> Qp -> outcome_failure_state E -> Rep.

  (** Only object-valued results have value constructors and extraction
      functions returning [T&&].  [basic_result<void, E>] uses a distinct
      overload whose extraction result is [void]. *)
  Class OutcomeObjectValue (value_ty : type) : Prop := {}.
  #[global] Hint Mode OutcomeObjectValue + : typeclass_instances.

  Class OutcomeFailureModel (error_ty : type) (E : Type) : Prop := {}.
  #[global] Hint Mode OutcomeFailureModel + - : typeclass_instances.

  (** A converting error constructor may take a type different from the
      [basic_result]'s stored error type. *)
  Class OutcomeErrorConversion
      (input_error_ty result_error_ty : type)
      (InputError ResultError : Type) : Type := {
    (* Logical effect of the C++ conversion into the stored error type. *)
    outcome_convert_error : InputError -> ResultError;
    (** The C++ conversion returns normally only on these inputs.  This matters
        when the stored type is an [errored_status_code]: constructing one from
        a success-valued status code terminates instead of returning an object. *)
    outcome_error_conversion_succeeds : InputError -> Prop;
  }.
  #[global] Hint Mode OutcomeErrorConversion + + - - : typeclass_instances.

  (** Ownership left at a source object after its value has been moved. *)
  Class MoveResidualRep
      (value_ty : type) (A : Type)
      `{!concepts.BundledRep value_ty A} : Type := {
    (* The residual ownership at the source address after moving [value]. *)
    move_residualR : A -> Rep;
  }.
  #[global] Hint Mode MoveResidualRep + - - : typeclass_instances.

  (** [void] has no C++ object storage.  This is therefore a genuine model of
      the value alternative of [basic_result<void, E>], rather than a dummy
      representation for an object whose fields are being ignored. *)
  #[global] Instance void_BundledRep :
    concepts.BundledRep Tvoid unit :=
    {| concepts.objR := fun _ _ => emp |}.

  Definition OutcomeResultMemberR {A E : Type}
      (result_name : name) (value_ty error_ty : type)
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E}
      (q : Qp) (result : outcome_result_state A E) : Rep :=
    match result with
    | OutcomeValue value =>
        outcome_result_value_offset result_name
          |-> concepts.objR value_ty q value
    | OutcomeError error =>
        outcome_result_error_offset result_name
          |-> concepts.objR error_ty q error
    | OutcomeMoved => OutcomeResultMovedPayloadR result_name q
    end.

  Definition OutcomeResultR {A E : Type}
      (result_name : name) (value_ty error_ty : type)
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E}
      (q : Qp) (result : outcome_result_state A E) : Rep :=
    structR result_name (cQp.mut q) **
    match result with
    | OutcomeValue _ | OutcomeError _ =>
        OutcomeResultStatusR result_name q
          (outcome_result_has_value result) **
        OutcomeResultMemberR result_name value_ty error_ty q result
    | OutcomeMoved => OutcomeResultMovedPayloadR result_name q
    end.

  Instance observeOutcomeResultRType {A E : Type}
      result_name value_ty error_ty
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E} q result :
    Observe (type_ptrR (Tnamed result_name))
      (OutcomeResultR result_name value_ty error_ty q result).
  Proof.
    unfold OutcomeResultR.
    apply _.
  Qed.

  Definition observeOutcomeResultRType_F :=
    ltac:(mk_at_obs_fwd (@observeOutcomeResultRType)).

  Axiom observeOutcomeTagRType :
    forall tag_ty q,
      Observe (type_ptrR tag_ty) (OutcomeTagR tag_ty q).
  #[global] Existing Instance observeOutcomeTagRType.

  Definition observeOutcomeTagRType_F :=
    ltac:(mk_at_obs_fwd observeOutcomeTagRType).

  Axiom observeOutcomeFailureRType :
    forall {E} error_ty q failure,
    Observe (type_ptrR (Tnamed (outcome_failure_name_for error_ty)))
      (@OutcomeFailureR E error_ty q failure).
  #[global] Existing Instance observeOutcomeFailureRType.

  Definition observeOutcomeFailureRType_F :=
    ltac:(mk_at_obs_fwd (@observeOutcomeFailureRType)).

  Lemma OutcomeResultR_unpack {A E : Type}
      result_name value_ty error_ty
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E}
      (p : ptr) q (result : outcome_result_state A E) :
    p |-> OutcomeResultR result_name value_ty error_ty q result
    |-- p |-> structR result_name (cQp.mut q) **
        p |->
          match result with
          | OutcomeValue _ | OutcomeError _ =>
              OutcomeResultStatusR result_name q
                (outcome_result_has_value result) **
              OutcomeResultMemberR
                result_name value_ty error_ty q result
          | OutcomeMoved => OutcomeResultMovedPayloadR result_name q
          end.
  Proof.
    unfold OutcomeResultR.
    go.
  Qed.

  Lemma OutcomeResultR_pack {A E : Type}
      result_name value_ty error_ty
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E}
      (p : ptr) q (result : outcome_result_state A E) :
    p |-> structR result_name (cQp.mut q) **
    p |->
      match result with
      | OutcomeValue _ | OutcomeError _ =>
          OutcomeResultStatusR result_name q
            (outcome_result_has_value result) **
          OutcomeResultMemberR result_name value_ty error_ty q result
      | OutcomeMoved => OutcomeResultMovedPayloadR result_name q
      end
    |-- p |-> OutcomeResultR result_name value_ty error_ty q result.
  Proof.
    unfold OutcomeResultR.
    go.
  Qed.

  Definition OutcomeResultR_unpack_F {A E : Type}
      result_name value_ty error_ty
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E}
      p q (result : outcome_result_state A E) :=
    [FWD]
      (OutcomeResultR_unpack
         result_name value_ty error_ty p q result).

  Definition OutcomeResultR_pack_B {A E : Type}
      result_name value_ty error_ty
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E}
      p q (result : outcome_result_state A E) :=
    [BWD]
      (OutcomeResultR_pack
         result_name value_ty error_ty p q result).

  (** The three functions used by [BOOST_OUTCOME_TRY] are function templates.
      Their contracts depend only on the generic result/failure models. *)
  Definition outcome_try_has_value_spec
      (value_ty error_ty policy_ty : type)
      {A E : Type}
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E} : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    let result_ty := Tnamed result_name in
    specify.template.func
      "boost::outcome_v2::try_operation_has_value"%cpp_name
      [Atype (Tref result_ty); Atype Tbool]
      Tbool [Tref result_ty; outcome_has_value_overload_ty] $
      \arg{resp : ptr} "v" (Vref resp)
      \arg{tagp : ptr} "" (Vptr tagp)
      \prepost{q result}
        resp |-> OutcomeResultR result_name value_ty error_ty q result
      \post [Vbool (outcome_result_has_value result)] emp.

  Definition outcome_try_return_as_spec
      (value_ty error_ty policy_ty : type)
      {A E : Type}
      `{!OutcomeFailureModel error_ty E}
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E} : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    let result_ty := Tnamed result_name in
    specify.template.func
      "boost::outcome_v2::try_operation_return_as"%cpp_name
      [Atype result_ty; Atype Tvoid]
      (Tnamed (outcome_failure_name_for error_ty))
      [Trv_ref result_ty; outcome_as_failure_overload_ty] $
      \arg{resp : ptr} "v" (Vref resp)
      \arg{tagp : ptr} "" (Vptr tagp)
      \pre{error}
        resp |-> OutcomeResultR result_name value_ty error_ty 1%Qp
          (OutcomeError error)
      \post{retp : ptr} [Vptr retp]
        resp |-> OutcomeResultR result_name value_ty error_ty 1%Qp
          OutcomeMoved
        ** retp |-> OutcomeFailureR error_ty 1%Qp
             (OutcomeFailureValue error).

  Definition outcome_try_extract_value_spec
      (value_ty error_ty policy_ty : type)
      {A E : Type}
      `{!OutcomeObjectValue value_ty}
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E} : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    let result_ty := Tnamed result_name in
    specify.template.func
      "boost::outcome_v2::try_operation_extract_value"%cpp_name
      [Atype result_ty; Atype Tvoid]
      (Trv_ref value_ty)
      [Trv_ref result_ty; outcome_assume_value_overload_ty] $
      \arg{resp : ptr} "v" (Vref resp)
      \arg{tagp : ptr} "" (Vptr tagp)
      \prepost{q value}
        resp |-> OutcomeResultR result_name value_ty error_ty q
          (OutcomeValue value)
      \post
        [Vref (resp ,, outcome_result_value_offset result_name)] emp.

  Definition outcome_try_extract_void_spec
      (error_ty policy_ty : type)
      {E : Type}
      `{!concepts.BundledRep error_ty E} : mpred :=
    let result_name :=
      outcome_result_name Tvoid error_ty policy_ty in
    let result_ty := Tnamed result_name in
    specify.template.func
      "boost::outcome_v2::try_operation_extract_value"%cpp_name
      [Atype result_ty; Atype Tvoid]
      Tvoid
      [Trv_ref result_ty; outcome_assume_value_overload_ty] $
      \arg{resp : ptr} "v" (Vref resp)
      \arg{tagp : ptr} "" (Vptr tagp)
      \prepost{q}
        resp |-> OutcomeResultR result_name Tvoid error_ty q
          (OutcomeValue tt)
      \post [Vvoid] emp.

  Definition outcome_failure_dtor_spec
      (error_ty : type)
      {E : Type} `{!OutcomeFailureModel error_ty E} : mpred :=
    specify.template.dtor (outcome_failure_name_for error_ty) $
      fun this : ptr =>
        \pre{failure : outcome_failure_state E}
          this |-> OutcomeFailureR error_ty 1%Qp failure
        \post emp.

  Definition outcome_value_tag_name (result_name : name) : name :=
    Nscoped result_name (Nid "value_converting_constructor_tag").

  Definition outcome_error_tag_name (result_name : name) : name :=
    Nscoped result_name (Nid "error_converting_constructor_tag").

  Definition outcome_explicit_move_tag_name (result_name : name) : name :=
    Nscoped result_name (Nid "explicit_compatible_move_conversion_tag").

  Definition outcome_value_tag_ty (result_name : name) : type :=
    Tnamed (outcome_value_tag_name result_name).

  Definition outcome_error_tag_ty (result_name : name) : type :=
    Tnamed (outcome_error_tag_name result_name).

  Definition outcome_explicit_move_tag_ty (result_name : name) : type :=
    Tnamed (outcome_explicit_move_tag_name result_name).

  Definition outcome_value_tag_ctor_spec
      (value_ty error_ty policy_ty : type) : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify.template.ctor (outcome_value_tag_name result_name) [] $
      fun this : ptr =>
        \post this |-> OutcomeTagR (outcome_value_tag_ty result_name) 1%Qp.

  Definition outcome_value_tag_dtor_spec
      (value_ty error_ty policy_ty : type) : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify.template.dtor (outcome_value_tag_name result_name) $
      fun this : ptr =>
        \pre this |-> OutcomeTagR (outcome_value_tag_ty result_name) 1%Qp
        \post emp.

  Definition outcome_error_tag_ctor_spec
      (value_ty error_ty policy_ty : type) : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify.template.ctor (outcome_error_tag_name result_name) [] $
      fun this : ptr =>
        \post this |-> OutcomeTagR (outcome_error_tag_ty result_name) 1%Qp.

  Definition outcome_error_tag_dtor_spec
      (value_ty error_ty policy_ty : type) : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify.template.dtor (outcome_error_tag_name result_name) $
      fun this : ptr =>
        \pre this |-> OutcomeTagR (outcome_error_tag_ty result_name) 1%Qp
        \post emp.

  Definition outcome_explicit_move_tag_ctor_spec
      (value_ty error_ty policy_ty : type) : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify.template.ctor (outcome_explicit_move_tag_name result_name) [] $
      fun this : ptr =>
        \post this |->
          OutcomeTagR (outcome_explicit_move_tag_ty result_name) 1%Qp.

  Definition outcome_explicit_move_tag_dtor_spec
      (value_ty error_ty policy_ty : type) : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify.template.dtor (outcome_explicit_move_tag_name result_name) $
      fun this : ptr =>
        \pre this |->
          OutcomeTagR (outcome_explicit_move_tag_ty result_name) 1%Qp
        \post emp.

  Definition outcome_result_dtor_spec
      (value_ty error_ty policy_ty : type)
      {A E : Type}
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E} : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify.template.dtor result_name $
      fun this : ptr =>
        \pre{result}
          this |-> OutcomeResultR result_name value_ty error_ty 1%Qp result
        \post emp.

  Definition outcome_result_value_ctor_name
      (result_name : name) (value_ty : type) : name :=
    Ninst
      (Nscoped result_name
        (Nctor [Trv_ref value_ty; outcome_value_tag_ty result_name]))
      [Atype value_ty; Atype "void"%cpp_type].

  (** The emitted names of these nested, templated constructors are more
      precise than the patterns accepted by [specify.template.ctor].  The raw
      [specify] calls therefore construct only the function identifier; their
      contracts remain template-generic in the result, value, and error types. *)
  Definition outcome_result_value_ctor_spec
      (value_ty error_ty policy_ty : type)
      {A E : Type}
      `{!OutcomeObjectValue value_ty}
      `{BR : !concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E}
      `{MR : !MoveResidualRep value_ty A} : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify
      {|
        info_name := outcome_result_value_ctor_name result_name value_ty;
        info_type :=
          tCtor result_name
            [Trv_ref value_ty; outcome_value_tag_ty result_name]
      |}
      (fun this : ptr =>
        \arg{valuep : ptr} "" (Vref valuep)
        \arg{tagp : ptr} "" (Vptr tagp)
        \pre{value} valuep |-> concepts.objR value_ty 1%Qp value
        \prepost tagp |->
          OutcomeTagR (outcome_value_tag_ty result_name) 1%Qp
        \post
          this |-> OutcomeResultR result_name value_ty error_ty 1%Qp
            (OutcomeValue value)
          ** valuep |-> @move_residualR value_ty A BR MR value).

  Definition outcome_result_error_ctor_name
      (result_name : name) (input_error_ty : type) : name :=
    Ninst
      (Nscoped result_name
        (Nctor [Trv_ref input_error_ty; outcome_error_tag_ty result_name]))
      [Atype input_error_ty; Atype "void"%cpp_type].

  Definition outcome_result_error_ctor_spec
      (value_ty result_error_ty policy_ty input_error_ty : type)
      {A E InputError : Type}
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep result_error_ty E}
      `{InputBR : !concepts.BundledRep input_error_ty InputError}
      `{InputMR : !MoveResidualRep input_error_ty InputError}
      `{Conversion : !OutcomeErrorConversion
          input_error_ty result_error_ty InputError E} : mpred :=
    let result_name :=
      outcome_result_name value_ty result_error_ty policy_ty in
    specify
      {|
        info_name :=
          outcome_result_error_ctor_name result_name input_error_ty;
        info_type :=
          tCtor result_name
            [Trv_ref input_error_ty; outcome_error_tag_ty result_name]
      |}
      (fun this : ptr =>
        \arg{errorp : ptr} "" (Vref errorp)
        \arg{tagp : ptr} "" (Vptr tagp)
        \pre{error}
          errorp |-> concepts.objR input_error_ty 1%Qp error
        \pre
          [| @outcome_error_conversion_succeeds
               input_error_ty result_error_ty InputError E
               Conversion error |]
        \prepost tagp |->
          OutcomeTagR (outcome_error_tag_ty result_name) 1%Qp
        \post
          this |-> OutcomeResultR
            result_name value_ty result_error_ty 1%Qp
            (OutcomeError
              (@outcome_convert_error
                 input_error_ty result_error_ty InputError E
                 Conversion error))
          ** errorp |->
               @move_residualR input_error_ty InputError InputBR InputMR error).

  Definition outcome_result_failure_ctor_spec
      (value_ty error_ty policy_ty : type)
      {A E : Type}
      `{!OutcomeFailureModel error_ty E}
      `{!concepts.BundledRep value_ty A}
      `{!concepts.BundledRep error_ty E} : mpred :=
    let result_name :=
      outcome_result_name value_ty error_ty policy_ty in
    specify
      {|
        info_name :=
          Ninst
            (Nscoped result_name
              (Nctor
                [Trv_ref (Tnamed (outcome_failure_name_for error_ty));
                      outcome_explicit_move_tag_ty result_name]))
            [Atype error_ty; Atype "void"%cpp_type];
        info_type :=
          tCtor result_name
            [Trv_ref (Tnamed (outcome_failure_name_for error_ty));
             outcome_explicit_move_tag_ty result_name]
      |}
      (fun this : ptr =>
        \arg{failurep : ptr} "" (Vref failurep)
        \arg{tagp : ptr} "" (Vptr tagp)
        \pre{error}
          failurep |-> OutcomeFailureR error_ty 1%Qp
            (OutcomeFailureValue error)
        \prepost tagp |->
          OutcomeTagR (outcome_explicit_move_tag_ty result_name) 1%Qp
        \post
          this |-> OutcomeResultR result_name value_ty error_ty 1%Qp
            (OutcomeError error)
          ** failurep |-> OutcomeFailureR error_ty 1%Qp
               (@OutcomeFailureMoved E)).

  (** The overload marker classes are not templates.  Default initialization
      exposes their ordinary empty-struct witness, which their destructors
      consume directly. *)
  Definition outcome_has_value_overload_dtor_spec : mpred :=
    specify.exact.dtor outcome_has_value_overload_name $
      fun this : ptr =>
        \pre this |-> structR outcome_has_value_overload_name 1$m
        \post emp.

  Definition outcome_as_failure_overload_dtor_spec : mpred :=
    specify.exact.dtor outcome_as_failure_overload_name $
      fun this : ptr =>
        \pre this |-> structR outcome_as_failure_overload_name 1$m
        \post emp.

  Definition outcome_assume_value_overload_dtor_spec : mpred :=
    specify.exact.dtor outcome_assume_value_overload_name $
      fun this : ptr =>
        \pre this |-> structR outcome_assume_value_overload_name 1$m
        \post emp.

  Definition SpecFor_outcome_result_value_ctor :=
    RegisterSpec (@outcome_result_value_ctor_spec).
  Definition SpecFor_outcome_result_error_ctor :=
    RegisterSpec (@outcome_result_error_ctor_spec).
  Definition SpecFor_outcome_try_has_value :=
    RegisterSpec (@outcome_try_has_value_spec).
  Definition SpecFor_outcome_try_return_as :=
    RegisterSpec (@outcome_try_return_as_spec).
  Definition SpecFor_outcome_try_extract_value :=
    RegisterSpec (@outcome_try_extract_value_spec).
  Definition SpecFor_outcome_try_extract_void :=
    RegisterSpec (@outcome_try_extract_void_spec).
  Definition SpecFor_outcome_failure_dtor :=
    RegisterSpec (@outcome_failure_dtor_spec).
  Definition SpecFor_outcome_value_tag_ctor :=
    RegisterSpec (@outcome_value_tag_ctor_spec).
  Definition SpecFor_outcome_value_tag_dtor :=
    RegisterSpec (@outcome_value_tag_dtor_spec).
  Definition SpecFor_outcome_error_tag_ctor :=
    RegisterSpec (@outcome_error_tag_ctor_spec).
  Definition SpecFor_outcome_error_tag_dtor :=
    RegisterSpec (@outcome_error_tag_dtor_spec).
  Definition SpecFor_outcome_explicit_move_tag_ctor :=
    RegisterSpec (@outcome_explicit_move_tag_ctor_spec).
  Definition SpecFor_outcome_explicit_move_tag_dtor :=
    RegisterSpec (@outcome_explicit_move_tag_dtor_spec).
  Definition SpecFor_outcome_result_dtor :=
    RegisterSpec (@outcome_result_dtor_spec).
  Definition SpecFor_outcome_result_failure_ctor :=
    RegisterSpec (@outcome_result_failure_ctor_spec).
  Definition SpecFor_outcome_has_value_overload_dtor :=
    RegisterSpec outcome_has_value_overload_dtor_spec.
  Definition SpecFor_outcome_as_failure_overload_dtor :=
    RegisterSpec outcome_as_failure_overload_dtor_spec.
  Definition SpecFor_outcome_assume_value_overload_dtor :=
    RegisterSpec outcome_assume_value_overload_dtor_spec.

End with_Sigma.

#[global] Existing Instance SpecFor_outcome_result_value_ctor.
#[global] Existing Instance SpecFor_outcome_result_error_ctor.
#[global] Existing Instance SpecFor_outcome_try_has_value.
#[global] Existing Instance SpecFor_outcome_try_return_as.
#[global] Existing Instance SpecFor_outcome_try_extract_value.
#[global] Existing Instance SpecFor_outcome_try_extract_void.
#[global] Existing Instance SpecFor_outcome_failure_dtor.
#[global] Existing Instance SpecFor_outcome_value_tag_ctor.
#[global] Existing Instance SpecFor_outcome_value_tag_dtor.
#[global] Existing Instance SpecFor_outcome_error_tag_ctor.
#[global] Existing Instance SpecFor_outcome_error_tag_dtor.
#[global] Existing Instance SpecFor_outcome_explicit_move_tag_ctor.
#[global] Existing Instance SpecFor_outcome_explicit_move_tag_dtor.
#[global] Existing Instance SpecFor_outcome_result_dtor.
#[global] Existing Instance SpecFor_outcome_result_failure_ctor.
#[global] Existing Instance SpecFor_outcome_has_value_overload_dtor.
#[global] Existing Instance SpecFor_outcome_as_failure_overload_dtor.
#[global] Existing Instance SpecFor_outcome_assume_value_overload_dtor.

#[global] Arguments outcome_result_value_ctor_spec : simpl never.
#[global] Arguments outcome_result_error_ctor_spec : simpl never.
#[global] Arguments outcome_try_has_value_spec : simpl never.
#[global] Arguments outcome_try_return_as_spec : simpl never.
#[global] Arguments outcome_try_extract_value_spec : simpl never.
#[global] Arguments outcome_try_extract_void_spec : simpl never.
#[global] Arguments outcome_failure_dtor_spec : simpl never.
#[global] Arguments outcome_value_tag_ctor_spec : simpl never.
#[global] Arguments outcome_value_tag_dtor_spec : simpl never.
#[global] Arguments outcome_error_tag_ctor_spec : simpl never.
#[global] Arguments outcome_error_tag_dtor_spec : simpl never.
#[global] Arguments outcome_explicit_move_tag_ctor_spec : simpl never.
#[global] Arguments outcome_explicit_move_tag_dtor_spec : simpl never.
#[global] Arguments outcome_result_dtor_spec : simpl never.
#[global] Arguments outcome_result_failure_ctor_spec : simpl never.
#[global] Arguments outcome_has_value_overload_dtor_spec : simpl never.
#[global] Arguments outcome_as_failure_overload_dtor_spec : simpl never.
#[global] Arguments outcome_assume_value_overload_dtor_spec : simpl never.

#[global] Hint Opaque
  outcome_result_value_ctor_spec
  outcome_result_error_ctor_spec
  outcome_try_has_value_spec
  outcome_try_return_as_spec
  outcome_try_extract_value_spec
  outcome_try_extract_void_spec
  outcome_failure_dtor_spec
  outcome_value_tag_ctor_spec
  outcome_value_tag_dtor_spec
  outcome_error_tag_ctor_spec
  outcome_error_tag_dtor_spec
  outcome_explicit_move_tag_ctor_spec
  outcome_explicit_move_tag_dtor_spec
  outcome_result_dtor_spec
  outcome_result_failure_ctor_spec
  outcome_has_value_overload_dtor_spec
  outcome_as_failure_overload_dtor_spec
  outcome_assume_value_overload_dtor_spec : sl_opacity.

#[global] Hint Resolve
  observeOutcomeResultRType_F
  observeOutcomeTagRType_F
  observeOutcomeFailureRType_F
  OutcomeResultR_unpack_F
  OutcomeResultR_pack_B : sl_opacity.
