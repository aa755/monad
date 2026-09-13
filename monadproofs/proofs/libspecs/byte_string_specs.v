Set Default Goal Selector "!".

(*
  Specs for byte strings and byte string views.

  The owning [byte_string] remains an abstract libstdc++ boundary.  In
  contrast, [byte_string_view] is modeled by its actual two-field spine: a
  pointer and a length.  A view does not own the bytes it names, so clients
  carry the backing [array_sliceR] separately.
*)

From Stdlib Require Import List NArith ZArith.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.lang.cpp.cpp.
Require Import monad.asts.storage_page_cpp.

Import cQp_compat.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition byte_string_name : name :=
    "std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>"%cpp_name.

  Definition byte_string_ty : type := Tnamed byte_string_name.

  Definition byte_string_view_name : name :=
    "std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>"%cpp_name.

  Definition byte_string_view_ty : type :=
    Tnamed byte_string_view_name.

  (** A real definition of the libstdc++ string representation would own its
      size/capacity spine and either its small-string buffer or allocated
      backing store.  Its move operations must additionally describe all valid
      moved-from states.  The storage-page proof treats those implementation
      details as a third-party-library boundary. *)
  Parameter ByteStringPayloadR : cQp.t -> list Z -> Rep.

  Definition ByteStringR (q : cQp.t) (bytes : list Z) : Rep :=
    type_ptrR byte_string_ty ** ByteStringPayloadR q bytes.

  (** [basic_string] is a third-party abstraction boundary.  This law states
      that BRiCk's temporary constification traverses the hidden libstdc++
      object representation while preserving the modeled byte sequence.  A
      concrete replacement for [ByteStringPayloadR] must prove this law from
      the string's fields and allocation ownership. *)
  Axiom ByteStringR_const :
    const.CONST1 storage_page_cpp.source byte_string_name ByteStringR.

  Definition ByteStringR_const_C := [CANCEL] ByteStringR_const.

  Definition byte_string_view_len_field : offset :=
    o_field CU
      (Field'' byte_string_view_ty (field_name.Id "_M_len")).

  Definition byte_string_view_data_field : offset :=
    o_field CU
      (Field'' byte_string_view_ty (field_name.Id "_M_str")).

  (** [ByteStringViewSpineR] owns exactly the two words stored in a
      libstdc++ [basic_string_view] object.  [view_data] points at the first
      visible byte and [view_length] is the number of visible bytes.  The
      pointed-to bytes are deliberately not part of this Rep. *)
  Definition ByteStringViewSpineR
      (q : Qp) (view_data : ptr) (view_length : N) : Rep :=
    byte_string_view_len_field
      |-> primR Tulong (cQp.mut q) (Vn view_length)
    ** byte_string_view_data_field
      |-> primR (Tptr (Qconst Tuchar)) (cQp.mut q) (Vptr view_data)
    ** structR byte_string_view_name (cQp.mut q).

  (** [byte_string_view_window] is the pure relation used when a view names an
      arbitrary contiguous subrange of a separately owned byte array. *)
  Definition byte_string_view_window
      (backing_base : ptr) (backing : list Z)
      (view_data : ptr) (visible : list Z) : Prop :=
    exists prefix suffix,
      backing = prefix ++ visible ++ suffix /\
      view_data =
        backing_base .[ Tuchar ! Z.of_nat (length prefix) ].

  (** A decoder advances its input only from the front, so its current view is
      always a suffix of the original backing array. *)
  Definition byte_string_view_suffix
      (backing_base : ptr) (backing : list Z)
      (view_data : ptr) (visible : list Z) : Prop :=
    exists consumed,
      backing = consumed ++ visible /\
      view_data =
        backing_base .[ Tuchar ! Z.of_nat (length consumed) ].

  (** The postcondition form records the concrete view length while retaining
      the exact visible suffix as a pure witness. *)
  Definition byte_string_view_suffix_length
      (backing_base : ptr) (backing : list Z)
      (view_data : ptr) (view_length : N) : Prop :=
    exists visible,
      view_length = N.of_nat (length visible) /\
      byte_string_view_suffix
        backing_base backing view_data visible.

  Lemma byte_string_view_suffix_length_intro
      backing_base backing view_data visible :
    byte_string_view_suffix backing_base backing view_data visible ->
    byte_string_view_suffix_length
      backing_base backing view_data
      (N.of_nat (length visible)).
  Proof.
    intro Hsuffix.
    exists visible.
    split; [reflexivity | exact Hsuffix].
  Qed.

  #[global] Instance byte_string_view_BundledRep :
    concepts.BundledRep byte_string_view_ty (ptr * N) :=
    {| concepts.objR :=
         fun q value => ByteStringViewSpineR q value.1 value.2 |}.

  Instance observeByteStringRType q bytes :
    Observe (type_ptrR byte_string_ty) (ByteStringR q bytes).
  Proof.
    unfold ByteStringR.
    apply _.
  Qed.

  Instance observeByteStringViewSpineRType q data length :
    Observe (type_ptrR byte_string_view_ty)
      (ByteStringViewSpineR q data length).
  Proof.
    unfold ByteStringViewSpineR.
    apply _.
  Qed.

  Definition observeByteStringRType_F :=
    ltac:(mk_at_obs_fwd observeByteStringRType).

  Definition observeByteStringViewSpineRType_F :=
    ltac:(mk_at_obs_fwd observeByteStringViewSpineRType).

  Lemma ByteStringR_unpack (p : ptr) q bytes :
    p |-> ByteStringR q bytes
    |-- p |-> type_ptrR byte_string_ty **
        p |-> ByteStringPayloadR q bytes.
  Proof.
    unfold ByteStringR.
    go.
  Qed.

  Lemma ByteStringR_pack (p : ptr) q bytes :
    p |-> type_ptrR byte_string_ty **
    p |-> ByteStringPayloadR q bytes
    |-- p |-> ByteStringR q bytes.
  Proof.
    unfold ByteStringR.
    go.
  Qed.

  Definition ByteStringR_unpack_F p q bytes :=
    [FWD] (ByteStringR_unpack p q bytes).

  Definition ByteStringR_pack_B p q bytes :=
    [BWD] (ByteStringR_pack p q bytes).

  (** A view's two fields alone do not justify pointer arithmetic: they can
      outlive the backing allocation.  Accessors require a typed range, which
      clients obtain from their separately owned backing bytes.  Observing it
      does not consume or borrow those bytes. *)
  Lemma observe_byte_string_view_suffix_range
      backing_base q backing view_data visible :
    byte_string_view_suffix backing_base backing view_data visible ->
    Observe
      (view_data |-> typed_sliceR Tuchar 0 (Z.of_nat (length visible)))
      (backing_base |-> array_sliceR Tuchar 0
        (Z.of_nat (length backing))
        (fun value => ucharR (cQp.const q) value) backing).
  Proof.
    intros [consumed [-> ->]].
    apply observe_intro.
    { exact _. }
    rewrite length_app Nat2Z.inj_add.
    rewrite (array_sliceR_app'
      backing_base 0 (Z.of_nat (length consumed))
      (Z.of_nat (length consumed) + Z.of_nat (length visible))
      (fun value => ucharR (cQp.const q) value) consumed visible
      ltac:(change (N.of_nat (length consumed) =
        Z.to_N (Z.of_nat (length consumed) - 0)); lia)
      ltac:(lia) ltac:(lia)).
    pose proof (_at_sub_array_sliceR (ty := Tuchar) backing_base
      (fun value => ucharR (cQp.const q) value)
      (Z.of_nat (length consumed)) 0 (Z.of_nat (length visible)) visible)
      as Hshift.
    rewrite Z.add_0_r in Hshift.
    rewrite <- Hshift.
    rewrite <- bi.sep_assoc.
    apply bi.sep_mono_r.
    apply observe_elim.
    exact _.
  Qed.

  Definition byte_string_view_suffix_range_C
      (backing_base : ptr) (q : Qp) (backing : list Z)
      (view_data : ptr) (visible : list Z)
      (Hsuffix : byte_string_view_suffix
        backing_base backing view_data visible) :=
    [CANCEL] (observe_elim _ _
      (O := observe_byte_string_view_suffix_range
        backing_base q backing view_data visible Hsuffix)).

  (** Reversible decomposition of the backing array at the first byte of a
      suffix view.  Unlike a borrow-and-return wand, the right-hand side
      exposes ordinary prefix, cell, and suffix resources; clients may split
      further before joining the same equivalence in reverse. *)
  Lemma byte_string_view_suffix_head_split
      (backing_base : ptr) (q : Qp) (backing : list Z)
      (view_data : ptr) (consumed : list Z)
      (byte : Z) (rest : list Z) :
    backing = consumed ++ byte :: rest ->
    view_data =
      backing_base .[ Tuchar ! Z.of_nat (length consumed) ] ->
    backing_base |-> array_sliceR Tuchar 0
      (Z.of_nat (length backing))
      (fun value => ucharR (cQp.const q) value) backing
    -|-
    backing_base |-> array_sliceR Tuchar 0
      (Z.of_nat (length consumed))
      (fun value => ucharR (cQp.const q) value) consumed
    ** type_ptr Tuchar view_data
    ** view_data |-> ucharR (cQp.const q) byte
    ** backing_base |-> array_sliceR Tuchar
         (Z.of_nat (length consumed) + 1)
         (Z.of_nat (length backing))
         (fun value => ucharR (cQp.const q) value) rest.
  Proof.
    intros Hbacking Hdata.
    subst backing view_data.
    rewrite (array_sliceR_app'
      backing_base 0 (Z.of_nat (length consumed))
      (Z.of_nat (length (consumed ++ byte :: rest)))
      (fun value => ucharR (cQp.const q) value)
      consumed (byte :: rest)
      ltac:(
        change
          (N.of_nat (length consumed) =
           Z.to_N (Z.of_nat (length consumed) - 0));
        rewrite Z.sub_0_r;
        lia)
      ltac:(lia)
      ltac:(rewrite length_app; simpl; lia)).
    rewrite array_sliceR_cons.
    rewrite !assoc.
    reflexivity.
  Qed.

  Lemma byte_string_view_suffix_head_extract
      (backing_base : ptr) (q : Qp) (backing : list Z)
      (view_data : ptr) (consumed : list Z) (byte : Z) (rest : list Z)
      (Hbacking : backing = consumed ++ byte :: rest)
      (Hdata :
         view_data =
           backing_base .[ Tuchar ! Z.of_nat (length consumed) ]) :
    backing_base |-> array_sliceR Tuchar 0
      (Z.of_nat (length backing))
      (fun value => ucharR (cQp.const q) value) backing
    |--
    backing_base |-> array_sliceR Tuchar 0
      (Z.of_nat (length consumed))
      (fun value => ucharR (cQp.const q) value) consumed
    ** type_ptr Tuchar view_data
    ** view_data |-> ucharR (cQp.const q) byte
    ** backing_base |-> array_sliceR Tuchar
         (Z.of_nat (length consumed) + 1)
         (Z.of_nat (length backing))
         (fun value => ucharR (cQp.const q) value) rest.
  Proof.
    apply bi.equiv_entails_1_1.
    exact
      (byte_string_view_suffix_head_split
         backing_base q backing view_data consumed byte rest
         Hbacking Hdata).
  Qed.

  Lemma byte_string_view_suffix_head_join
      (backing_base : ptr) (q : Qp) (backing : list Z)
      (view_data : ptr) (consumed : list Z) (byte : Z) (rest : list Z)
      (Hbacking : backing = consumed ++ byte :: rest)
      (Hdata :
         view_data =
           backing_base .[ Tuchar ! Z.of_nat (length consumed) ]) :
    backing_base |-> array_sliceR Tuchar 0
      (Z.of_nat (length consumed))
      (fun value => ucharR (cQp.const q) value) consumed
    ** view_data |-> ucharR (cQp.const q) byte
    ** backing_base |-> array_sliceR Tuchar
         (Z.of_nat (length consumed) + 1)
         (Z.of_nat (length backing))
         (fun value => ucharR (cQp.const q) value) rest
    |--
    backing_base |-> array_sliceR Tuchar 0
      (Z.of_nat (length backing))
      (fun value => ucharR (cQp.const q) value) backing.
  Proof.
    etransitivity.
    {
      rewrite
        (observe_elim
           (type_ptr Tuchar view_data)
           (view_data |-> ucharR (cQp.const q) byte)).
      rewrite (comm bi_sep
        (view_data |-> ucharR (cQp.const q) byte)
        (type_ptr Tuchar view_data)).
      rewrite -assoc.
      reflexivity.
    }
    apply bi.equiv_entails_1_2.
    exact
      (byte_string_view_suffix_head_split
         backing_base q backing view_data consumed byte rest
         Hbacking Hdata).
  Qed.

  Definition byte_string_view_suffix_head_extract_F
      backing_base q backing view_data consumed byte rest
      Hbacking Hdata :=
    [FWD]
      (byte_string_view_suffix_head_extract
         backing_base q backing view_data consumed byte rest
         Hbacking Hdata).

  Definition byte_string_view_suffix_head_join_F
      backing_base q backing view_data consumed byte rest
      Hbacking Hdata :=
    [FWD]
      (byte_string_view_suffix_head_join
         backing_base q backing view_data consumed byte rest
         Hbacking Hdata).

  Lemma byte_string_view_suffix_tail
      backing_base backing view_data byte rest :
    byte_string_view_suffix
      backing_base backing view_data (byte :: rest) ->
    byte_string_view_suffix
      backing_base backing
      (view_data .[ Tuchar ! 1 ]) rest.
  Proof.
    intros [consumed [Hbacking Hdata]].
    exists (consumed ++ [byte]).
    split.
    {
      rewrite Hbacking.
      rewrite -app_assoc.
      reflexivity.
    }
    {
      rewrite Hdata o_sub_sub length_app.
      simpl.
      replace (Z.of_nat (length consumed + 1))
        with (Z.of_nat (length consumed) + 1)%Z by lia.
      reflexivity.
    }
  Qed.

  Hint Resolve
    observeByteStringRType_F
    observeByteStringViewSpineRType_F : sl_opacity.

  #[local] Hint Resolve
    byte_string_view_suffix_length_intro : pure.

  cpp.spec
    "std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>::basic_string()"
    from storage_page_cpp.source as byte_string_ctor_spec
    with (
      fun this : ptr =>
        \post this |-> ByteStringR 1$m []
    ).

  cpp.spec
    "std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>::basic_string(std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>&&)"
    from storage_page_cpp.source as byte_string_move_ctor_spec
    with (
      fun this : ptr =>
        \arg{otherp : ptr} "" (Vref otherp)
        \pre{bytes} otherp |-> ByteStringR 1$m bytes
        \post
          Exists moved_from_bytes : list Z,
          this |-> ByteStringR 1$m bytes **
          otherp |-> ByteStringR 1$m moved_from_bytes
    ).

  cpp.spec
    "std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>::~basic_string()"
    from storage_page_cpp.source as byte_string_dtor_spec
    with (
      fun this : ptr =>
        \pre{bytes} this |-> ByteStringR 1$m bytes
        \post emp
    ).

  cpp.spec
    "std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>::reserve(unsigned long)"
    from storage_page_cpp.source as byte_string_reserve_spec
    with (
      fun this : ptr =>
        \arg{capacity : N} "__res_arg" (Vn capacity)
        \pre{bytes} this |-> ByteStringR 1$m bytes
        \post this |-> ByteStringR 1$m bytes
    ).

  cpp.spec
    "std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>::push_back(unsigned char)"
    from storage_page_cpp.source as byte_string_push_back_spec
    with (
      fun this : ptr =>
        \arg{byte : Z} "__c" (Vint byte)
        \pre [| 0 <= byte < 256 |]%Z
        \pre{bytes} this |-> ByteStringR 1$m bytes
        \post this |-> ByteStringR 1$m (bytes ++ [byte])
    ).

  cpp.spec
    "std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>::operator+=(const std::__cxx11::basic_string<unsigned char, evmc::byte_traits<unsigned char>, std::allocator<unsigned char>>&)"
    from storage_page_cpp.source as byte_string_append_spec
    with (
      fun this : ptr =>
        \arg{otherp : ptr} "__str" (Vref otherp)
        \pre{bytes} this |-> ByteStringR 1$m bytes
        \prepost{(q : Qp) other} otherp |-> ByteStringR q$c other
        \post [Vref this]
          this |-> ByteStringR 1$m (bytes ++ other)
    ).

  cpp.spec
    "std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>::empty() const"
    from storage_page_cpp.source as string_view_empty_spec
    with (
      fun this : ptr =>
        \prepost{q data length}
          this |-> ByteStringViewSpineR q data length
        \post [Vbool (N.eqb length 0)] emp
    ).

  cpp.spec
    "std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>::remove_prefix(unsigned long)"
    from storage_page_cpp.source as string_view_remove_prefix_spec
    with (
      fun this : ptr =>
        \arg{n : N} "__n" (Vn n)
        \pre{data length} this |-> ByteStringViewSpineR 1 data length
        \pre [| (n <= length)%N |]
        \prepost data |-> typed_sliceR Tuchar 0 (Z.of_N length)
        \post this |-> ByteStringViewSpineR 1
          (data .[ Tuchar ! Z.of_N n ])
          (length - n)
    ).

  cpp.spec
    "std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>::operator[](unsigned long) const"
    from storage_page_cpp.source as string_view_index_spec
    with (
      fun this : ptr =>
        \arg{index : N} "__pos" (Vn index)
        \prepost{q data length}
          this |-> ByteStringViewSpineR q data length
        \pre [| (index < length)%N |]
        \prepost data |-> typed_sliceR Tuchar 0 (Z.of_N length)
        \post [Vref (data .[ Tuchar ! Z.of_N index ])] emp
    ).

  cpp.spec
    "std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>::basic_string_view(const std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>&)"
    from storage_page_cpp.source as string_view_copy_ctor_spec
    with (
      fun this : ptr =>
        \arg{otherp : ptr} "" (Vref otherp)
        \prepost{q data length}
          otherp |-> ByteStringViewSpineR q data length
        \post this |-> ByteStringViewSpineR 1 data length
    ).

  cpp.spec
    "std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>::~basic_string_view()"
    from storage_page_cpp.source as string_view_dtor_spec
    with (
      fun this : ptr =>
        \pre{data length} this |-> ByteStringViewSpineR 1 data length
        \post emp
    ).

End with_Sigma.

#[global] Hint Resolve
  byte_string_view_suffix_length_intro : pure.

#[global] Hint Resolve
  observeByteStringRType_F
  observeByteStringViewSpineRType_F
  ByteStringR_const_C : sl_opacity.

#[global] Hint Opaque
  ByteStringR ByteStringViewSpineR : sl_opacity.

Opaque ByteStringR ByteStringViewSpineR.
