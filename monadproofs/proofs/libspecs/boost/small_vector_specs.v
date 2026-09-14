Set Default Goal Selector "!".

(*
  Narrow specs for the Boost small_vector/vector shape used by storage_page_t.

  [SmallVectorR] is a view of the Boost vector base subobject, not a full
  verification of Boost.  The spine owns the holder fields that client proofs
  read directly, plus an abstract backing-storage token for allocator/spare
  capacity details.  The live payload remains explicit as an [arrayLR], so
  storage-page proofs can reason about indexed elements without exposing
  Boost's spare-capacity and allocator internals.
*)

From Stdlib Require Import List NArith ZArith.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.cpp.

Import cQp_compat.

Module boost_small_vector.
Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition vector_holder_field (vector_base_ty : type) : offset :=
    o_field CU (Field'' vector_base_ty (field_name.Id "m_holder")).

  Definition holder_start_field (holder_ty : type) : offset :=
    o_field CU (Field'' holder_ty (field_name.Id "m_start")).

  Definition holder_size_field (holder_ty : type) : offset :=
    o_field CU (Field'' holder_ty (field_name.Id "m_size")).

  Definition holder_capacity_field (holder_ty : type) : offset :=
    o_field CU (Field'' holder_ty (field_name.Id "m_capacity")).

  Record SmallVectorState : Type := {
    small_vector_base : ptr;
    small_vector_capacity : N;
  }.

  Parameter SmallVectorStorageR :
    forall (elem_ty : type) (q : Qp)
      (size : N) (state : SmallVectorState), Rep.

  Definition SmallVectorHolderR
      (holder_ty elem_ty : type)
      (q : Qp) (base : ptr) (size capacity : N) : Rep :=
    holder_start_field holder_ty
      |-> primR (Tptr elem_ty) q (Vptr base)
    ** holder_size_field holder_ty
      |-> primR Tulong q (Vn size)
    ** holder_capacity_field holder_ty
      |-> primR Tulong q (Vn capacity)
    ** SmallVectorStorageR elem_ty q size
      {|
        small_vector_base := base;
        small_vector_capacity := capacity;
      |}
    ** structR (Ndependent' holder_ty) q.

  Definition SmallVectorSpineR
      (vector_base_ty holder_ty elem_ty : type)
      (q : Qp) (size : N) (state : SmallVectorState) : Rep :=
    vector_holder_field vector_base_ty
      |-> SmallVectorHolderR holder_ty elem_ty q
        state.(small_vector_base) size state.(small_vector_capacity)
    ** structR (Ndependent' vector_base_ty) q.

  #[global] Instance observeSmallVectorSpineType
      vector_base_ty holder_ty elem_ty q size state :
    Observe (type_ptrR (Tnamed (Ndependent' vector_base_ty)))
      (SmallVectorSpineR vector_base_ty holder_ty elem_ty q size state).
  Proof.
    unfold SmallVectorSpineR.
    apply _.
  Qed.

  Definition SmallVectorPayloadR
      (elem_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep)
      (q : Qp) (state : SmallVectorState) (values : list A) : Rep :=
    pureR
      (state.(small_vector_base)
        |-> arrayLR elem_ty 0 (Z.of_nat (length values))
          (elemR (cQp.mut q)) values).

  Definition SmallVectorCapR
      (_small_vector_ty vector_base_ty holder_ty elem_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep)
      (q : Qp) (state : SmallVectorState) (values : list A) : Rep :=
    [| (N.of_nat (length values) <=
          state.(small_vector_capacity))%N |]
    ** SmallVectorSpineR vector_base_ty holder_ty elem_ty q
         (N.of_nat (length values)) state
    ** SmallVectorPayloadR elem_ty elemR q state values.

  Definition SmallVectorR
      (_small_vector_ty vector_base_ty holder_ty elem_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep)
      (q : Qp) (values : list A) : Rep :=
    Exists (base : ptr) (capacity : N),
      SmallVectorCapR
        _small_vector_ty vector_base_ty holder_ty elem_ty elemR q
        {|
          small_vector_base := base;
          small_vector_capacity := capacity;
        |}
        values.

  Definition small_vector_base_offset
      (small_vector_name small_vector_base_name vector_base_name : name)
      : offset :=
    o_base CU small_vector_name small_vector_base_name ,,
    o_base CU small_vector_base_name vector_base_name.

  Definition SmallVectorObjectR
      (small_vector_name small_vector_base_name vector_base_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep)
      (q : Qp) (values : list A) : Rep :=
    small_vector_base_offset
      small_vector_name small_vector_base_name vector_base_name
      |-> SmallVectorR
        small_vector_ty vector_base_ty holder_ty elem_ty elemR q values.

  Definition small_vector_insert_at {A : Type}
      (offset : nat) (value : A) (values : list A) : list A :=
    firstn offset values ++ value :: skipn offset values.

  Definition small_vector_erase_at {A : Type}
      (offset : nat) (values : list A) : list A :=
    firstn offset values ++ skipn (S offset) values.

  Definition small_vector_replace_at {A : Type}
      (offset : nat) (value : A) (values : list A) : list A :=
    firstn offset values ++ value :: skipn (S offset) values.

  Definition small_vector_iterator_ptr_field
      (iterator_ty : type) : offset :=
    o_field CU (Field'' iterator_ty (field_name.Id "m_ptr")).

  Definition SmallVectorIteratorR
      (iterator_ty elem_ty : type) (q : cQp.t)
      (base : ptr) (index : Z) : Rep :=
    small_vector_iterator_ptr_field iterator_ty
      |-> primR (Tptr elem_ty) q (Vptr (base .[ elem_ty ! index ]))
    ** structR (Ndependent' iterator_ty) q.

  Definition holder_start_const_name (holder_name : name) : name :=
    Nscoped holder_name
      (Nfunction function_qualifiers.Nc "start" []).

  Definition holder_start_const_spec
      (holder_name : name) (holder_ty elem_ty : type) : mpred :=
    specify.exact.method
      (holder_start_const_name holder_name)
      function_qualifiers.Nc
      (Tptr elem_ty)
      []
      (fun this : ptr =>
        \pre{q base size capacity}
          this |-> SmallVectorHolderR
            holder_ty elem_ty q base size capacity
        \post [Vptr base]
          this |-> SmallVectorHolderR
            holder_ty elem_ty q base size capacity).

  Definition begin_spec
      (vector_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty iterator_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep) : mpred :=
    specify.exact.method
      (Nscoped vector_name
        (Nfunction function_qualifiers.N "begin" []))
      function_qualifiers.N
      iterator_ty
      []
      (fun this : ptr =>
        \pre{values base capacity}
          this |-> SmallVectorCapR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR
            1%Qp
            {|
              small_vector_base := base;
              small_vector_capacity := capacity;
            |}
            values
        \post{itp : ptr} [Vptr itp]
          this |-> SmallVectorCapR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR
            1%Qp
            {|
              small_vector_base := base;
              small_vector_capacity := capacity;
            |}
            values
          ** itp |-> SmallVectorIteratorR iterator_ty elem_ty 1$m base 0).

  Definition iterator_plus_spec
      (iterator_ty elem_ty : type) : mpred :=
    specify.template.static_op
      "boost::container"
      OOPlus
      []
      iterator_ty
      [Tref (Qconst iterator_ty); Tlong]
      (
        \arg{iterp : ptr} "x" (Vref iterp)
        \arg{offset : N} "off" (Vn offset)
        \prepost{q base index}
          iterp |-> SmallVectorIteratorR iterator_ty elem_ty q base index
        \pre
          valid_ptr (base .[ elem_ty ! (index + Z.of_N offset) ])
        \post{retp : ptr} [Vptr retp]
          retp |-> SmallVectorIteratorR
            iterator_ty elem_ty 1$m base (index + Z.of_N offset)
      ).

  Definition const_iterator_from_iterator_ctor_spec
      (const_iterator_name : name)
      (iterator_ty const_iterator_ty elem_ty : type) : mpred :=
    specify.exact.ctor const_iterator_name
      [Tref (Qconst iterator_ty)]
      (fun this : ptr =>
        \arg{otherp : ptr} "other" (Vref otherp)
        \prepost{q base index}
          otherp |-> SmallVectorIteratorR iterator_ty elem_ty q base index
        \post
          this |-> SmallVectorIteratorR
            const_iterator_ty elem_ty 1$m base index
      ).

  Definition iterator_dtor_spec
      (iterator_name : name) (iterator_ty elem_ty : type) : mpred :=
    specify.exact.dtor iterator_name (fun this : ptr =>
      \pre{base index}
        this |-> SmallVectorIteratorR iterator_ty elem_ty 1$m base index
      \post emp).

  Definition index_mut_spec
      (vector_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty : type)
      {A : Type} (default : A) (elemR : cQp.t -> A -> Rep) : mpred :=
    specify.exact.method
      (Nscoped vector_name
        (Nop function_qualifiers.N OOSubscript [Tulong]))
      function_qualifiers.N
      (Tref elem_ty)
      [Tulong]
      (fun this : ptr =>
        \arg{index : N} "n" (Vn index)
        \pre{values base capacity}
          this |-> SmallVectorCapR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR
            1%Qp
            {|
              small_vector_base := base;
              small_vector_capacity := capacity;
            |}
            values
        \pre [| (index < N.of_nat (length values))%N |]
        \post{retp : ptr} [Vref retp]
          retp |-> elemR (cQp.mut 1) (nth (N.to_nat index) values default)
          ** Forall new_value : A,
              retp |-> elemR (cQp.mut 1) new_value -*
              this |-> SmallVectorCapR
                small_vector_ty vector_base_ty holder_ty elem_ty elemR
                1%Qp
                {|
                  small_vector_base := base;
                  small_vector_capacity := capacity;
                |}
                (small_vector_replace_at
                   (N.to_nat index) new_value values)).

  Definition insert_spec
      (vector_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty
         iterator_ty const_iterator_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep) : mpred :=
    specify.exact.method
      (Nscoped vector_name
        (Nfunction function_qualifiers.N
          "insert" [const_iterator_ty; Tref (Qconst elem_ty)]))
      function_qualifiers.N
      iterator_ty
      [const_iterator_ty; Tref (Qconst elem_ty)]
      (fun this : ptr =>
        \arg{positionp : ptr} "arg1" (Vptr positionp)
        \arg{valuep : ptr} "x" (Vref valuep)
        \pre{values base capacity index value}
          this |-> SmallVectorCapR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR
            1%Qp
            {|
              small_vector_base := base;
              small_vector_capacity := capacity;
            |}
            values
        \prepost
          positionp |->
          SmallVectorIteratorR const_iterator_ty elem_ty 1$m base index
        \prepost{qvalue}
          valuep |-> elemR qvalue value
        \pre [| (0 <= index <= Z.of_nat (length values))%Z |]
        \post{(retp new_base : ptr) (new_capacity : N)} [Vptr retp]
          this |-> SmallVectorCapR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR
            1%Qp
            {|
              small_vector_base := new_base;
              small_vector_capacity := new_capacity;
            |}
            (small_vector_insert_at (Z.to_nat index) value values)
          ** retp |-> SmallVectorIteratorR
            iterator_ty elem_ty 1$m new_base index
      ).

  Definition erase_spec
      (vector_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty
         iterator_ty const_iterator_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep) : mpred :=
    specify.exact.method
      (Nscoped vector_name
        (Nfunction function_qualifiers.N
          "erase" [const_iterator_ty]))
      function_qualifiers.N
      iterator_ty
      [const_iterator_ty]
      (fun this : ptr =>
        \arg{positionp : ptr} "position" (Vptr positionp)
        \pre{values base capacity index}
          this |-> SmallVectorCapR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR
            1%Qp
            {|
              small_vector_base := base;
              small_vector_capacity := capacity;
            |}
            values
        \prepost
          positionp |->
          SmallVectorIteratorR const_iterator_ty elem_ty 1$m base index
        \pre [| (0 <= index < Z.of_nat (length values))%Z |]
        \post{(retp new_base : ptr) (new_capacity : N)} [Vptr retp]
          this |-> SmallVectorCapR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR
            1%Qp
            {|
              small_vector_base := new_base;
              small_vector_capacity := new_capacity;
            |}
            (small_vector_erase_at (Z.to_nat index) values)
          ** retp |-> SmallVectorIteratorR
            iterator_ty elem_ty 1$m new_base index
      ).

  Definition size_const_name (vector_base_name : name) : name :=
    Nscoped vector_base_name
      (Nfunction function_qualifiers.Nc "size" []).

  Definition size_const_spec
      (vector_base_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep) : mpred :=
    specify.exact.method
      (size_const_name vector_base_name)
      function_qualifiers.Nc
      Tulong
      []
      (fun this : ptr =>
        \prepost{q values}
          this |-> SmallVectorR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR q values
        \post [Vn (N.of_nat (length values))] emp).

  Definition default_ctor_spec
      (small_vector_name : name)
      (small_vector_base_name vector_base_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep) : mpred :=
    specify.exact.ctor small_vector_name [] (fun this : ptr =>
      \post
        this |-> SmallVectorObjectR
          small_vector_name small_vector_base_name vector_base_name
          small_vector_ty vector_base_ty holder_ty elem_ty elemR 1%Qp []).

  Definition dtor_spec
      (small_vector_name : name)
      (small_vector_base_name vector_base_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty : type)
      {A : Type} (elemR : cQp.t -> A -> Rep) : mpred :=
    specify.exact.dtor small_vector_name (fun this : ptr =>
      \pre{values}
        this |-> SmallVectorObjectR
          small_vector_name small_vector_base_name vector_base_name
          small_vector_ty vector_base_ty holder_ty elem_ty elemR 1%Qp values
      \post emp).

  #[global] Instance observeSmallVectorBaseType
      small_vector_ty vector_base_ty holder_ty elem_ty {A : Type}
      (elemR : cQp.t -> A -> Rep) q values :
    Observe (type_ptrR (Tnamed (Ndependent' vector_base_ty)))
      (SmallVectorR small_vector_ty vector_base_ty holder_ty elem_ty elemR
         q values).
  Proof.
    unfold SmallVectorR, SmallVectorCapR.
    apply _.
  Qed.

  Definition observeSmallVectorBaseType_F :=
    ltac:(mk_at_obs_fwd observeSmallVectorBaseType).

  #[global] Instance observeSmallVectorCapType
      small_vector_ty vector_base_ty holder_ty elem_ty {A : Type}
      (elemR : cQp.t -> A -> Rep) q state values :
    Observe (type_ptrR (Tnamed (Ndependent' vector_base_ty)))
      (SmallVectorCapR small_vector_ty vector_base_ty holder_ty elem_ty
         elemR q state values).
  Proof.
    unfold SmallVectorCapR.
    apply _.
  Qed.

  Definition observeSmallVectorCapType_F :=
    ltac:(mk_at_obs_fwd observeSmallVectorCapType).

  #[global] Instance observeSmallVectorIteratorType
      iterator_ty elem_ty q base index :
    Observe (type_ptrR (Tnamed (Ndependent' iterator_ty)))
      (SmallVectorIteratorR iterator_ty elem_ty q base index).
  Proof.
    apply observe_intro.
    { exact _. }
    unfold SmallVectorIteratorR.
    go.
  Qed.

  Definition observeSmallVectorIteratorType_F :=
    ltac:(mk_at_obs_fwd observeSmallVectorIteratorType).

  Lemma SmallVectorCapR_pack
      small_vector_ty vector_base_ty holder_ty elem_ty
      {A : Type} (elemR : cQp.t -> A -> Rep) q base capacity values :
    SmallVectorCapR
      small_vector_ty vector_base_ty holder_ty elem_ty elemR q
      {|
        small_vector_base := base;
        small_vector_capacity := capacity;
      |}
      values
    |--
    SmallVectorR
      small_vector_ty vector_base_ty holder_ty elem_ty elemR q values.
  Proof.
    unfold SmallVectorR.
    rewrite <- (bi.exist_intro base).
    rewrite <- (bi.exist_intro capacity).
    go.
  Qed.

  Definition SmallVectorCapR_pack_F
      small_vector_ty vector_base_ty holder_ty elem_ty
      {A : Type} (elemR : cQp.t -> A -> Rep) q base capacity values :=
    [FWD]
      (SmallVectorCapR_pack
         small_vector_ty vector_base_ty holder_ty elem_ty
         elemR q base capacity values).

  Lemma SmallVectorCapR_at_pack
      small_vector_ty vector_base_ty holder_ty elem_ty
      {A : Type} (elemR : cQp.t -> A -> Rep) q (p : ptr)
      base capacity values :
    p |-> SmallVectorCapR
      small_vector_ty vector_base_ty holder_ty elem_ty elemR q
      {|
        small_vector_base := base;
        small_vector_capacity := capacity;
      |}
      values
    |--
    p |-> SmallVectorR
      small_vector_ty vector_base_ty holder_ty elem_ty elemR q values.
  Proof.
    apply _at_mono.
    apply SmallVectorCapR_pack.
  Qed.

  Definition SmallVectorCapR_at_pack_F
      small_vector_ty vector_base_ty holder_ty elem_ty
      {A : Type} (elemR : cQp.t -> A -> Rep) q p base capacity values :=
    [FWD]
      (SmallVectorCapR_at_pack
         small_vector_ty vector_base_ty holder_ty elem_ty
         elemR q p base capacity values).

  #[global] Instance learnSmallVectorSpineR
      vector_base_ty holder_ty elem_ty :
    LearnEq3
      (SmallVectorSpineR vector_base_ty holder_ty elem_ty) :=
    ltac:(solve_learnable).

  #[global] Instance learnSmallVectorStorageR elem_ty :
    LearnEq3 (SmallVectorStorageR elem_ty) :=
    ltac:(solve_learnable).

  #[global] Instance learnSmallVectorPayloadR elem_ty {A : Type}
      (elemR : cQp.t -> A -> Rep) :
    LearnEq3 (SmallVectorPayloadR elem_ty elemR) :=
    ltac:(solve_learnable).

  #[global] Instance learnSmallVectorCapR
      small_vector_ty vector_base_ty holder_ty elem_ty {A : Type}
      (elemR : cQp.t -> A -> Rep) :
    LearnEq3
      (SmallVectorCapR
         small_vector_ty vector_base_ty holder_ty elem_ty elemR) :=
    ltac:(solve_learnable).

  #[global] Instance learnSmallVectorR
      small_vector_ty vector_base_ty holder_ty elem_ty {A : Type}
      (elemR : cQp.t -> A -> Rep) :
    LearnEq2
      (SmallVectorR small_vector_ty vector_base_ty holder_ty elem_ty elemR) :=
    ltac:(solve_learnable).

  #[global] Instance learnSmallVectorObjectR
      small_vector_name small_vector_base_name vector_base_name
      small_vector_ty vector_base_ty holder_ty elem_ty {A : Type}
      (elemR : cQp.t -> A -> Rep) :
    LearnEq2
      (SmallVectorObjectR
         small_vector_name small_vector_base_name vector_base_name
         small_vector_ty vector_base_ty holder_ty elem_ty elemR) :=
    ltac:(solve_learnable).

  #[global] Instance learnSmallVectorIteratorR
      iterator_ty elem_ty :
    LearnEq3 (SmallVectorIteratorR iterator_ty elem_ty) :=
    ltac:(solve_learnable).

  Definition index_const_name (vector_base_name : name) : name :=
    Nscoped vector_base_name
      (Nop function_qualifiers.Nc OOSubscript [Tulong]).

  Definition index_const_spec
      (vector_base_name : name)
      (small_vector_ty vector_base_ty holder_ty elem_ty : type)
      {A : Type} (default : A) (elemR : cQp.t -> A -> Rep) : mpred :=
    specify.exact.method
      (index_const_name vector_base_name)
      function_qualifiers.Nc
      (Tref (Qconst elem_ty))
      [Tulong]
      (fun this : ptr =>
        \arg{index : N} "n" (Vn index)
        \pre{q values}
          this |-> SmallVectorR
            small_vector_ty vector_base_ty holder_ty elem_ty elemR q values
        \pre [| (index < N.of_nat (length values))%N |]
        \post{retp : ptr} [Vref retp]
          retp |-> elemR (cQp.mut q) (nth (N.to_nat index) values default)
          ** (retp |-> elemR (cQp.mut q)
                (nth (N.to_nat index) values default) -*
              this |-> SmallVectorR
                small_vector_ty vector_base_ty holder_ty elem_ty elemR
                q values)).

End with_Sigma.
End boost_small_vector.

#[global] Hint Resolve
  boost_small_vector.observeSmallVectorBaseType_F
  boost_small_vector.observeSmallVectorCapType_F
  boost_small_vector.observeSmallVectorIteratorType_F : sl_opacity.

#[global] Arguments boost_small_vector.SmallVectorR : simpl never.
#[global] Arguments boost_small_vector.SmallVectorCapR : simpl never.
#[global] Arguments boost_small_vector.SmallVectorPayloadR : simpl never.
#[global] Arguments boost_small_vector.SmallVectorHolderR : simpl never.
#[global] Arguments boost_small_vector.SmallVectorStorageR : simpl never.
#[global] Arguments boost_small_vector.SmallVectorSpineR : simpl never.
#[global] Arguments boost_small_vector.SmallVectorObjectR : simpl never.
#[global] Arguments boost_small_vector.SmallVectorIteratorR : simpl never.
#[global] Arguments boost_small_vector.index_const_spec : simpl never.
#[global] Arguments boost_small_vector.index_mut_spec : simpl never.
#[global] Arguments boost_small_vector.size_const_spec : simpl never.
#[global] Arguments boost_small_vector.default_ctor_spec : simpl never.
#[global] Arguments boost_small_vector.dtor_spec : simpl never.
#[global] Arguments boost_small_vector.begin_spec : simpl never.
#[global] Arguments boost_small_vector.iterator_plus_spec : simpl never.
#[global] Arguments boost_small_vector.const_iterator_from_iterator_ctor_spec
  : simpl never.
#[global] Arguments boost_small_vector.iterator_dtor_spec : simpl never.
#[global] Arguments boost_small_vector.insert_spec : simpl never.
#[global] Arguments boost_small_vector.erase_spec : simpl never.
#[global] Hint Opaque
  boost_small_vector.SmallVectorSpineR
  boost_small_vector.SmallVectorStorageR
  boost_small_vector.SmallVectorHolderR
  boost_small_vector.SmallVectorPayloadR
  boost_small_vector.SmallVectorCapR
  boost_small_vector.SmallVectorR
  boost_small_vector.SmallVectorObjectR
  boost_small_vector.SmallVectorIteratorR
  boost_small_vector.index_const_spec
  boost_small_vector.index_mut_spec
  boost_small_vector.size_const_spec
  boost_small_vector.default_ctor_spec
  boost_small_vector.dtor_spec
  boost_small_vector.begin_spec
  boost_small_vector.iterator_plus_spec
  boost_small_vector.const_iterator_from_iterator_ctor_spec
  boost_small_vector.iterator_dtor_spec
  boost_small_vector.insert_spec
  boost_small_vector.erase_spec : sl_opacity.
