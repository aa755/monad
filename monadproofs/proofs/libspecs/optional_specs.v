Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.

Require Import monad.proofs.misc.

Set Default Goal Selector "!".

Section cp.
  Import own.
  Import frac.

  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}.

  (** The libstdc++ layout used for [std::optional<T>] when [T] is trivially
      copy constructible, copy assignable, move constructible, move assignable,
      and destructible. Unlike the former field-only representation,
      this representation retains the class, base-class, union, and field
      resource traversed by BRiCk's C++ const-conversion semantics. *)
  Definition trivial_optional_name (ty : type) : name :=
    Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional")) [Atype ty].

  Definition trivial_optional_base_name (ty : type) : name :=
    Ninst (Nscoped (Nglobal (Nid "std")) (Nid "_Optional_base"))
      [Atype ty; Avalue (Eint 1 Tbool); Avalue (Eint 1 Tbool)].

  Definition trivial_optional_enable_name (ty : type) : name :=
    Ninst (Nscoped (Nglobal (Nid "std")) (Nid "_Enable_copy_move"))
      [Avalue (Eint 1 Tbool); Avalue (Eint 1 Tbool);
       Avalue (Eint 1 Tbool); Avalue (Eint 1 Tbool);
       Atype (Tnamed (trivial_optional_name ty))].

  Definition trivial_optional_payload_name (ty : type) : name :=
    Ninst (Nscoped (Nglobal (Nid "std")) (Nid "_Optional_payload"))
      [Atype ty; Avalue (Eint 1 Tbool); Avalue (Eint 1 Tbool);
       Avalue (Eint 1 Tbool)].

  Definition trivial_optional_payload_base_name (ty : type) : name :=
    Ninst (Nscoped (Nglobal (Nid "std")) (Nid "_Optional_payload_base"))
      [Atype ty].

  Definition trivial_optional_storage_name (ty : type) : name :=
    Ninst
      (Nscoped (trivial_optional_payload_base_name ty) (Nid "_Storage"))
      [Atype ty; Avalue (Eint 1 Tbool)].

  Definition trivial_optional_empty_name (ty : type) : name :=
    Nscoped (trivial_optional_payload_base_name ty) (Nid "_Empty_byte").

  Definition trivial_optional_storageR {T : Type}
      (ty : type) (elemR : cQp.t -> T -> Rep)
      (q : cQp.t) (value : option T) : Rep :=
    match value with
    | None =>
        unionR (trivial_optional_storage_name ty) q (Some 0) **
        _field
          (Nscoped (trivial_optional_storage_name ty) (Nid "_M_empty"))
          |-> structR (trivial_optional_empty_name ty) q
    | Some element =>
        unionR (trivial_optional_storage_name ty) q (Some 1) **
        _field
          (Nscoped (trivial_optional_storage_name ty) (Nid "_M_value"))
          |-> elemR q element
    end.

  Definition trivial_optional_payload_baseR {T : Type}
      (ty : type) (elemR : cQp.t -> T -> Rep)
      (q : cQp.t) (value : option T) : Rep :=
    structR (trivial_optional_payload_base_name ty) q **
    _field
      (Nscoped (trivial_optional_payload_base_name ty) (Nid "_M_payload"))
      |-> trivial_optional_storageR ty elemR q value **
    _field
      (Nscoped (trivial_optional_payload_base_name ty) (Nid "_M_engaged"))
      |-> boolR q (bool_decide (is_Some value)).

  Definition trivial_optional_payloadR {T : Type}
      (ty : type) (elemR : cQp.t -> T -> Rep)
      (q : cQp.t) (value : option T) : Rep :=
    structR (trivial_optional_payload_name ty) q **
    _base (trivial_optional_payload_name ty)
      (trivial_optional_payload_base_name ty)
      |-> trivial_optional_payload_baseR ty elemR q value.

  Definition trivial_optional_baseR {T : Type}
      (ty : type) (elemR : cQp.t -> T -> Rep)
      (q : cQp.t) (value : option T) : Rep :=
    structR (trivial_optional_base_name ty) q **
    _field (Nscoped (trivial_optional_base_name ty) (Nid "_M_payload"))
      |-> trivial_optional_payloadR ty elemR q value.

  Definition value_offset (ty : type) : offset :=
      o_base CU (trivial_optional_name ty)
           (trivial_optional_base_name ty)
      ,, o_field CU
           (Nscoped (trivial_optional_base_name ty) (Nid "_M_payload"))
      ,, o_base CU (trivial_optional_payload_name ty)
           (trivial_optional_payload_base_name ty)
      ,, o_field CU
           (Nscoped (trivial_optional_payload_base_name ty)
             (Nid "_M_payload"))
      ,, o_field CU
           (Nscoped (trivial_optional_storage_name ty) (Nid "_M_value")).

  Definition trivial_optional_value_ptr (ty : type) (p : ptr) : ptr :=
    p ,, value_offset ty.

  (** [spineR] owns the optional's implementation, but not its contained value.
      In the engaged case its pointer parameter identifies the actual payload
      subobject; it is not an independently allocated value. Clients can split
      out the element without learning the names of libstdc++'s internal bases.

      This concrete definition currently covers the trivial-special-members
      layout described above. To extend it, inspect the instantiated optional
      in [CU]'s type table, follow its actual bases and payload fields, and own
      their [structR] and [unionR] resources. Named element types must be resolved
      through that table, not classified from their names. Nontrivial payload
      specializations have different intermediate bases. An implementation of
      [reset] must also account for a disengaged union whose value was destroyed
      without constructing [_M_empty]; it must not expose that detail to clients.

      FIXME: [dbspecs.commit_spec] temporarily uses this same spine for
      [std::optional<std::vector<monad::Withdrawal>>], despite its nontrivial
      layout. This is a known representation mismatch, not a proved layout
      equivalence. The deferred fix is to follow the actual instantiation in
      [CU]: [_Optional_base<T, false, false>], a payload with a nontrivial
      destructor inheriting through [_Optional_payload<T, true, false, false>],
      and [_Storage<T, false>]. Own all its base/field/union witnesses and derive
      the corresponding payload offset. Select this internally from the actual
      layout, not from a Withdrawal-specific test. Keep vector ownership in
      [optionR]'s element Rep and preserve the public signature and split/join
      interface. This extension is deliberately deferred; the current use must
      not be cited as verification of that nontrivial optional layout. *)
  Definition spineR (ty : type) (q : cQp.t) (payload : option ptr) : Rep :=
    structR (trivial_optional_name ty) q **
    _base (trivial_optional_name ty) (trivial_optional_base_name ty)
      |-> trivial_optional_baseR ty
        (fun _ expected => as_Rep (fun actual => [| actual = expected |]))
        q payload **
    _base (trivial_optional_name ty) (trivial_optional_enable_name ty)
      |-> structR (trivial_optional_enable_name ty) q.

  Definition optionR {T : Type}
      (ty : type) (elemR : cQp.t -> T -> Rep)
      (q : cQp.t) (value : option T) : Rep :=
    match value with
    | None => spineR ty q None
    | Some element =>
        Exists payload : ptr,
          spineR ty q (Some payload) ** pureR (payload |-> elemR q element)
    end.

  (** This expansion proves that separating the spine from the element preserves
      the former field-expanded representation exactly. It is for representation
      proofs only; clients use [optionR] and the split/join lemmas. *)
  Lemma optionR_layout {T : Type}
      ty (elemR : cQp.t -> T -> Rep) q value (p : ptr) :
    p |-> optionR ty elemR q value -|-
    p |->
      (structR (trivial_optional_name ty) q **
       _base (trivial_optional_name ty) (trivial_optional_base_name ty)
         |-> trivial_optional_baseR ty elemR q value **
       _base (trivial_optional_name ty) (trivial_optional_enable_name ty)
         |-> structR (trivial_optional_enable_name ty) q).
  Proof.
    unfold optionR, spineR,
      trivial_optional_baseR, trivial_optional_payloadR,
      trivial_optional_payload_baseR, trivial_optional_storageR.
    destruct value.
    {
      simpl. apply bi.equiv_entails. split.
      { normalize_ptrs. go. }
      { normalize_ptrs. go. }
    }
    { reflexivity. }
  Qed.

  (** Separating and rejoining the payload preserves the entire spine. No
      borrow wand is needed, and the client never handles internal base fields. *)
  Lemma trivial_optional_some_split {T : Type}
      ty (elemR : cQp.t -> T -> Rep) q value (p : ptr) :
    p |-> optionR ty elemR q (Some value)
    |--
    p |-> spineR ty q (Some (trivial_optional_value_ptr ty p)) **
    trivial_optional_value_ptr ty p |-> elemR q value.
  Proof.
    rewrite optionR_layout.
    unfold spineR, trivial_optional_baseR,
      trivial_optional_payloadR, trivial_optional_payload_baseR,
      trivial_optional_storageR,
      trivial_optional_value_ptr.
    simpl.
    normalize_ptrs.
    go.
  Qed.

  Lemma trivial_optional_some_join {T : Type}
      ty (elemR : cQp.t -> T -> Rep) q value (p : ptr) :
    p |-> spineR ty q (Some (trivial_optional_value_ptr ty p)) **
    trivial_optional_value_ptr ty p |-> elemR q value
    |--
    p |-> optionR ty elemR q (Some value).
  Proof.
    rewrite optionR_layout.
    unfold spineR, trivial_optional_baseR,
      trivial_optional_payloadR, trivial_optional_payload_baseR,
      trivial_optional_storageR,
      trivial_optional_value_ptr.
    simpl.
    normalize_ptrs.
    go.
  Qed.

  Definition trivial_optional_some_split_C :=
    [CANCEL] @trivial_optional_some_split.

  Definition trivial_optional_some_split_F :=
    [FWD] @trivial_optional_some_split.

  Definition trivial_optional_some_join_B :=
    [BWD] @trivial_optional_some_join.

  Definition trivial_optional_some_join_F :=
    [FWD] @trivial_optional_some_join.

  #[global] Instance observeSpineRType ty q payload :
    Observe (type_ptrR (Tnamed (trivial_optional_name ty)))
      (spineR ty q payload).
  Proof.
    unfold spineR.
    apply _.
  Qed.

  Definition observeSpineRType_F :=
    ltac:(mk_at_obs_fwd (@observeSpineRType)).

  #[global] Instance observeTrivialOptionalRType {T : Type}
      ty (elemR : cQp.t -> T -> Rep) q value :
    Observe (type_ptrR (Tnamed (trivial_optional_name ty)))
      (optionR ty elemR q value).
  Proof.
    unfold optionR, spineR.
    destruct value.
    { apply _. }
    apply _.
  Qed.

  Definition observeTrivialOptionalRType_F :=
    ltac:(mk_at_obs_fwd (@observeTrivialOptionalRType)).

  #[global] Instance learnTrivialOptionalR {T : Type} :
    LearnEq4 (@optionR T) := ltac:(solve_learnable).

  #[global] Instance learnOptionalModelType {A B : Type}
      ty ty' (R : cQp.t -> A -> Rep) (R' : cQp.t -> B -> Rep)
      q q' value value' (p : ptr) :
    learn_exist_interface.Learnable
      (p |-> optionR ty R q value)
      (p |-> optionR ty' R' q' value') [A = B] :=
    ltac:(solve_learnable).

  #[global] Instance learnOptionalSpine {A : Type}
      ty ty' (R : cQp.t -> A -> Rep) q q' value payload (p : ptr) :
    learn_exist_interface.Learnable
      (p |-> optionR ty R q value)
      (p |-> spineR ty' q' payload) [ty = ty'; q = q'] :=
    ltac:(solve_learnable).

  #[global] Instance learnOptionalElement {A : Type}
      ty ty' (R R' : cQp.t -> A -> Rep) q q' value element (p : ptr) :
    learn_exist_interface.Learnable
      (p |-> optionR ty R q value)
      (trivial_optional_value_ptr ty' p |-> R' q' element)
      [value = Some element; R = R'; q = q'] :=
    ltac:(solve_learnable).

  Definition optionalPrimR (q:Qp) (primty:type) (on: option N): Rep :=
    optionR primty
      (fun q' (v:N) => primR primty q' (Vint v)) (cQp.mut q) on.

  Definition opt_reconstr_spec T ty : ptr -> WpSpec mpredI val val :=
    fun this =>
      \arg{other} "other" (Vptr other)
      \prepost{(R: T -> Rep) t} other |-> R t
      \pre{prev} this |-> optionR ty (fun _ => R) 1$m prev
      \post [Vptr this] this |-> optionR ty (fun _ => R) 1$m (Some t).

  Definition opt_reconstr baseModelTy basety :=
    λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
      specify
        {|
          info_name :=
            Ninst
              (Nscoped
                (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
                  [Atype basety])
                ((Nop function_qualifiers.N OOEqual)
                  [Trv_ref basety])) [Atype basety];
          info_type :=
            tMethod
              (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
                [Atype basety])
              QM
              (Tref
                (Tnamed
                  (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
                    [Atype basety])))
              [Trv_ref basety]
        |} (opt_reconstr_spec baseModelTy basety).

  Section optional_methods.
    Context (ty: type).

    #[local] Notation opt := ("std::optional".<<Atype ty>>)%cpp_name.

    Definition optional_has_value_spec :=
      let qf := function_qualifiers.Nc in
      specify.template.method opt "has_value" qf "bool" [] $
        \this this
        \prepost{{T} (R: cQp.t -> T -> Rep) (o: option T) (q: cQp.t)} this |-> optionR ty R q o
        \post[Vbool (bool_decide (is_Some o))] emp.

    Definition optional_value_const_spec :=
      let qf := function_qualifiers.Ncl in
      specify.template.method opt "value" qf (Tref (Tconst ty)) [] $
        \this this
        \prepost{{T} (R: cQp.t -> T -> Rep) (t: T) (q: cQp.t)} this |-> optionR ty R q (Some t)
        \post[Vptr (this ,, value_offset ty)] emp.

    Definition optional_arrow_spec :=
      specify.template.op opt OOArrow function_qualifiers.N (Tptr ty) [] $
        \this this
        \prepost{{T} (R : cQp.t -> T -> Rep) (t : T) (q: cQp.t)}
          this |-> optionR ty R q (Some t)
        \post[Vptr (this ,, value_offset ty)] emp.

    Definition optional_arrow_const_spec :=
      specify.template.op opt OOArrow function_qualifiers.Nc
        (Tptr (Tconst ty)) [] $
        \this this
        \prepost{{T} (R : cQp.t -> T -> Rep) (t : T) (q: cQp.t)}
          this |-> optionR ty R q (Some t)
        \post[Vptr (this ,, value_offset ty)] emp.

    Context {T : Type}.
    Context {cb : concepts.BundledRep ty T}.

    Definition optional_dtor_spec :=
      specify.template.dtor opt $
        \this this
        \pre{o : option T} this |-> optionR ty (concepts.objR ty) 1 o
        \post emp.

    (* Library boundary restricted to the trivial-special-members layout modeled
       by [optionR]. Registration matches the symbol, not its layout: callers
       must check the instantiated CU; [BundledRep] and [MovedValue] do not
       establish layout compatibility. This is not a verified contract for
       arbitrary optional<T>. The operator itself is also a template. *)
    Definition optional_assign_value_spec
        {mv : concepts.MovedValue ty T} :=
      specify
        {| info_name :=
             Ninst (Nscoped opt
               (Nop function_qualifiers.N OOEqual [Trv_ref ty])) [Atype ty];
           info_type := tMethod opt QM (Tref (Tnamed opt)) [Trv_ref ty] |} $
        \this this
        \arg{other : ptr} "__u" (Vref other)
        \pre{value prev}
          other |-> concepts.objR ty 1$m value **
          this |-> optionR ty (concepts.objR ty) 1$m prev
        \post[Vref this]
          this |-> optionR ty (concepts.objR ty) 1$m (Some value) **
          other |-> concepts.moved_objR ty 1$m value.
  End optional_methods.

  Definition SpecFor_optional_has_value := RegisterSpec optional_has_value_spec.
  #[global] Existing Instance SpecFor_optional_has_value.
  Definition SpecFor_optional_value_const := RegisterSpec optional_value_const_spec.
  #[global] Existing Instance SpecFor_optional_value_const.
  Definition SpecFor_optional_arrow := RegisterSpec optional_arrow_spec.
  #[global] Existing Instance SpecFor_optional_arrow.
  Definition SpecFor_optional_arrow_const := RegisterSpec optional_arrow_const_spec.
  #[global] Existing Instance SpecFor_optional_arrow_const.
  Definition SpecFor_optional_dtor := RegisterSpec (@optional_dtor_spec).
  #[global] Existing Instance SpecFor_optional_dtor.
  Definition SpecFor_optional_assign_value :=
    RegisterSpec (@optional_assign_value_spec).
  #[global] Existing Instance SpecFor_optional_assign_value.

  Definition nullopt_copy_ctor_spec :=
    specify.template.ctor "std::nullopt_t"%cpp_name
      [Tref (Tconst "std::nullopt_t"%cpp_type)] $
      fun this : ptr =>
      \arg{otherp: ptr} "__tag" (Vref otherp)
      \post this |-> structR "std::nullopt_t" 1$m
    .

  Definition SpecFor_nullopt_copy_ctor := RegisterSpec nullopt_copy_ctor_spec.
  #[global] Existing Instance SpecFor_nullopt_copy_ctor.

  Definition nullopt_dtor_spec :=
    specify.template.dtor "std::nullopt_t"%cpp_name $
      fun this : ptr =>
      \pre this |-> structR "std::nullopt_t" 1$m
      \post emp
    .

  Definition SpecFor_nullopt_dtor := RegisterSpec nullopt_dtor_spec.
  #[global] Existing Instance SpecFor_nullopt_dtor.

  Definition std_nullopt_spec : mpred :=
    specify
      {| info_name := "std::nullopt"%cpp_name;
         info_type := tFunction (Tref (Tconst (Tnamed "std::nullopt_t"))) [] |}
      (\post [Vptr (_global "std::nullopt")] emp).

  Definition SpecFor_std_nullopt := RegisterSpec std_nullopt_spec.
  #[global] Existing Instance SpecFor_std_nullopt.
End cp.

#[global] Opaque trivial_optional_storageR trivial_optional_payload_baseR
  trivial_optional_payloadR trivial_optional_baseR spineR optionR.
#[global] Hint Opaque optionR : sl_opacity.
#[global] Hint Opaque optional_dtor_spec : sl_opacity.
#[global] Hint Opaque optional_assign_value_spec : sl_opacity.
#[global] Hint Opaque optional_has_value_spec : sl_opacity.
#[global] Hint Opaque optional_value_const_spec : sl_opacity.
#[global] Hint Opaque optional_arrow_spec : sl_opacity.
#[global] Hint Opaque optional_arrow_const_spec : sl_opacity.

#[global] Hint Resolve observeSpineRType_F observeTrivialOptionalRType_F
  : sl_opacity.
#[global] Hint Resolve trivial_optional_some_split_C
  trivial_optional_some_join_B : sl_opacity.

#[global] Arguments optional_value_const_spec : simpl never.
#[global] Arguments optional_has_value_spec : simpl never.
#[global] Arguments optional_arrow_spec : simpl never.
#[global] Arguments optional_arrow_const_spec : simpl never.
