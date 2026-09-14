Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.spec.

Set Default Goal Selector "!".

(** libstdc++ span stores a pointer and an extent-storage subobject. For a
    static extent that subobject is empty; for dynamic_extent it owns the
    runtime size. The span owns neither the elements nor their allocation.
    These specs use the 64-bit size_t layout of the supported Linux target. *)
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}.

  Definition SpanRbase (cppType : type) (q : cQp.t) (base : ptr)
      (size : N) (sizeStatic : bool) : Rep :=
    let extent := if sizeStatic then Z.of_N size else 18446744073709551615 in
    let span := ("std::span".<< Atype cppType,
      Avalue (Eint extent "unsigned long") >>)%cpp_name in
    let storage := ("std::__detail::__extent_storage".<<
      Avalue (Eint extent "unsigned long") >>)%cpp_name in
    [| if sizeStatic then (size < 18446744073709551615)%N
       else (size <= 18446744073709551615)%N |] **
    structR span q **
    _field (span .:: field_name.Id "_M_ptr") |->
      primR (Tptr (erase_qualifiers cppType)) q (Vptr base) **
    _field (span .:: field_name.Id "_M_extent") |->
      (structR storage q **
       if sizeStatic then emp else
       _field (storage .:: field_name.Id "_M_extent_value") |->
         primR Tulong q (Vn size)).

  Definition SpanR' {ElemType} (cppType : type) (elemRep : ElemType -> Rep)
      (base : ptr) (q : Qp) (lt : list ElemType) (sizeStatic : bool) : Rep :=
    SpanRbase cppType (cQp.mut q) base (lengthN lt) sizeStatic
      ** pureR (base |-> arrayR cppType elemRep lt).

  Definition SpanR {ElemType} (cppType : type) (elemRep : ElemType -> Rep)
      (q : Qp) (lt : list ElemType) (sizeStatic : bool) : Rep :=
    Exists base,
      SpanRbase cppType (cQp.mut q) base (lengthN lt) sizeStatic
        ** pureR (base |-> arrayR cppType elemRep lt).

  #[global] Instance : LearnEq5 SpanRbase := ltac:(solve_learnable).

  #[global] Instance observeSpanRbaseType ty q base size (sizeStatic : bool) :
    Observe (type_ptrR (Tnamed ("std::span".<< Atype ty,
      Avalue (Eint (if sizeStatic then Z.of_N size else 18446744073709551615)
        "unsigned long") >>)%cpp_name))
      (SpanRbase ty q base size sizeStatic).
  Proof.
    unfold SpanRbase. apply _.
  Qed.

  Definition observeSpanRbaseType_F :=
    ltac:(mk_at_obs_fwd observeSpanRbaseType).

  Section span_specs.
    Context (ety: type) (extent: Z).

    #[local] Notation span :=
      ("std::span".<< Atype ety, Avalue (Eint extent "unsigned long") >>)%cpp_name.

    Definition span_size_spec :=
      let qf := function_qualifiers.Nc in
      specify.template.method span "size" qf Tulong [] $
        \this this
        \prepost{q base size sizeStaticallyKnown} this |-> SpanRbase ety q base size sizeStaticallyKnown
        \pre [| if sizeStaticallyKnown then extent = Z.of_N size else extent = 2^64-1 |]
        \post[Vn size] emp.

    Definition span_ctor_spec :=
      specify.template.ctor span [Tptr ety; Tulong] $
        \this this
        \arg{base: ptr} "ptr" (Vptr base)
        \arg{size: N} "count" (Vn size)
        \pre [| if bool_decide (extent = 2^64-1) then (True : Prop) else Z.of_N size = extent |]
        \post this |-> SpanRbase ety 1$m base size (negb (bool_decide (extent = 2^64-1))).
    
    Definition span_dtor_spec :=
      specify.template.dtor span $
        \this this
        \pre{base size sizeStaticallyKnown} this |-> SpanRbase ety 1$m base size sizeStaticallyKnown
        \pre [| if sizeStaticallyKnown then extent = Z.of_N size else extent = 2^64-1 |]
        \post emp.

    (** Indexing only returns a reference. The persistent typed range supports
        its pointer arithmetic; clients keep and split element ownership
        separately. In particular, this contract does not give a const span
        ownership of, or write access to, the elements. *)
    Definition span_index_spec :=
      specify.template.op span OOSubscript function_qualifiers.Nc
        (Tref ety) [Tulong] $
        \this this
        \arg{index : N} "__idx" (Vn index)
        \prepost{q base size sizeStatic}
          this |-> SpanRbase ety q base size sizeStatic
        \pre [| if sizeStatic then extent = Z.of_N size else extent = 2^64-1 |]
        \pre [| (index < size)%N |]
        \pre base |-> typed_sliceR (erase_qualifiers ety) 0 (Z.of_N size)
        \post [Vref (base .[ erase_qualifiers ety ! Z.of_N index ])] emp.
    
  End span_specs.

  Definition SpecFor_span_size := RegisterSpec span_size_spec.
  #[global] Existing Instance SpecFor_span_size.
  
  Definition SpecFor_span_ctor := RegisterSpec span_ctor_spec.
  #[global] Existing Instance SpecFor_span_ctor.

  Definition SpecFor_span_dtor := RegisterSpec span_dtor_spec.
  #[global] Existing Instance SpecFor_span_dtor.

  Definition SpecFor_span_index := RegisterSpec span_index_spec.
  #[global] Existing Instance SpecFor_span_index.

End with_Sigma.

#[global] Hint Resolve observeSpanRbaseType_F : sl_opacity.
#[global] Hint Opaque SpanRbase : sl_opacity typeclass_instances.
#[global] Hint Opaque span_size_spec span_index_spec : sl_opacity.
#[global] Arguments span_size_spec : simpl never.
