Require Import skylabs.auto.cpp.proof.
Require Import stdpp.gmap.
Require Import monad.proofs.libspecs.pair_specs.

Set Default Goal Selector "!".

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Definition templated_method
      (name class : name) (qs : function_qualifiers.t)
      (ret : type) (args : list type)
      (spec : ptr -> WpSpec_cpp_val) : mpred :=
    _global name |-> unmaterialized_specR
      (tMethod class (function_qualifiers.to_type_qualifiers qs) ret args)
      spec.

  Definition immer_map_name
      (key_ty value_ty hash_ty equal_ty memory_policy_ty : type)
      (bits : Z) : name :=
    ("immer::map".<<
      Atype key_ty,
      Atype value_ty,
      Atype hash_ty,
      Atype equal_ty,
      Atype memory_policy_ty,
      Avalue (Eint bits Tuint)
    >>)%cpp_name.

  Definition immer_map_ty
      (key_ty value_ty hash_ty equal_ty memory_policy_ty : type)
      (bits : Z) : type :=
    Tnamed (immer_map_name key_ty value_ty hash_ty equal_ty
      memory_policy_ty bits).

  Fixpoint immer_map_lookup {K V : Type} `{!EqDecision K}
      (m : list (K * V)) (key : K) : option V :=
    match m with
    | [] => None
    | (key0, value0) :: tl =>
        if decide (key0 = key)
        then Some value0
        else immer_map_lookup tl key
    end.

  Definition immer_map_insert {K V : Type} `{!EqDecision K}
      (key : K) (value : V) (m : list (K * V)) : list (K * V) :=
    (key, value) ::
      filter (fun kv => negb (bool_decide (kv.1 = key))) m.

  Definition ImmerMapR {K V : Type}
      (map_ty : type) (_keyR : cQp.t -> K -> Rep)
      (_valueR : Qp -> V -> Rep) (_q : Qp)
      (_m : list (K * V)) : Rep.
  Proof using.
    Admitted.

  Instance observe_ImmerMapR_type_ptr {K V : Type}
      (map_ty : type) keyR valueR q (m : list (K * V)) :
    Observe (type_ptrR map_ty)
      (ImmerMapR map_ty keyR valueR q m).
  Proof using.
    Admitted.

  Definition observe_ImmerMapR_type_ptr_F {K V : Type}
      (map_ty : type) (keyR : cQp.t -> K -> Rep)
      (valueR : Qp -> V -> Rep) (q : Qp)
      (m : list (K * V)) :=
    ltac:(mk_at_obs_fwd (@observe_ImmerMapR_type_ptr
      K V map_ty keyR valueR q m)).
  Section map_methods.
    Context (key_ty value_ty hash_ty equal_ty memory_policy_ty : type)
      (bits : Z).

    #[local] Notation map_name :=
      (immer_map_name key_ty value_ty hash_ty equal_ty
        memory_policy_ty bits).
    #[local] Notation map_ty :=
      (immer_map_ty key_ty value_ty hash_ty equal_ty
        memory_policy_ty bits).

    Definition immer_map_find_spec :=
      templated_method
        (Nscoped map_name
          (Nfunction function_qualifiers.Nc "find"
            [Tref (Tconst key_ty)]))
        map_name function_qualifiers.Nc
        (Tptr (Tconst value_ty)) [Tref (Tconst key_ty)] $
        \this this
        \arg{keyp : ptr} "k" (Vref keyp)
        \pre{{K V} (eqd : EqDecision K)
            (keyR : cQp.t -> K -> Rep) (valueR : Qp -> V -> Rep)
            (q : Qp) (m : list (K * V))}
          this |-> ImmerMapR map_ty keyR valueR q m
        \prepost{qkey key} keyp |-> keyR qkey key
        \post{retp : ptr} [Vptr retp]
          if bool_decide (retp = nullptr)
          then
              this |-> ImmerMapR map_ty keyR valueR q m
          else
              Exists value,
                retp |-> valueR q value
                ** (retp |-> valueR q value -*
                    this |-> ImmerMapR map_ty keyR valueR q m).

    Definition immer_map_insert_spec :=
      let pair_ty :=
        Tnamed ("std::pair".<< Atype key_ty, Atype value_ty >>)%cpp_name in
      specify.template.method
        map_name "insert" function_qualifiers.Ncl map_ty [pair_ty] $
        \this this
        \arg{valuep : ptr} "value" (Vptr valuep)
        \prepost{{K V} (eqd : EqDecision K)
            (keyR : cQp.t -> K -> Rep) (valueR : Qp -> V -> Rep)
            (kv : K * V)}
          valuep |-> pairR key_ty value_ty
            (fun q => keyR (cQp.mut q)) valueR 1%Qp 1%Qp kv
        \prepost{q m} this |-> ImmerMapR map_ty keyR valueR q m
        \post{retp : ptr} [Vptr retp]
          retp |-> ImmerMapR map_ty keyR valueR 1%Qp
            (@immer_map_insert K V eqd kv.1 kv.2 m).

    Definition immer_map_move_assign_spec :=
      specify.template.op map_name OOEqual function_qualifiers.N
        (Tref map_ty) [Trv_ref map_ty] $
        \this this
        \arg{otherp : ptr} "" (Vref otherp)
        \pre{{K V} (keyR : cQp.t -> K -> Rep) (valueR : Qp -> V -> Rep)
            (old m : list (K * V))}
          this |-> ImmerMapR map_ty keyR valueR 1%Qp old
          ** otherp |-> ImmerMapR map_ty keyR valueR 1%Qp m
        \post[Vref this]
          this |-> ImmerMapR map_ty keyR valueR 1%Qp m
          ** otherp |-> ImmerMapR map_ty keyR valueR 1%Qp m.

    Definition immer_map_dtor_spec :=
      specify.template.dtor map_name $
        \this this
        \pre{{K V} (keyR : cQp.t -> K -> Rep) (valueR : Qp -> V -> Rep)
            (q : Qp) (m : list (K * V))}
          this |-> ImmerMapR map_ty keyR valueR q m
        \post emp.
  End map_methods.

  Definition SpecFor_immer_map_find :=
    RegisterSpec (@immer_map_find_spec).
  #[global] Existing Instance SpecFor_immer_map_find.

  Definition SpecFor_immer_map_insert :=
    RegisterSpec (@immer_map_insert_spec).
  #[global] Existing Instance SpecFor_immer_map_insert.

  Definition SpecFor_immer_map_move_assign :=
    RegisterSpec (@immer_map_move_assign_spec).
  #[global] Existing Instance SpecFor_immer_map_move_assign.

  Definition SpecFor_immer_map_dtor :=
    RegisterSpec (@immer_map_dtor_spec).
  #[global] Existing Instance SpecFor_immer_map_dtor.
End with_Sigma.

#[global] Hint Resolve observe_ImmerMapR_type_ptr_F : sl_opacity.
#[global] Opaque ImmerMapR.
#[global] Hint Opaque
  ImmerMapR
  immer_map_find_spec
  immer_map_insert_spec
  immer_map_move_assign_spec
  immer_map_dtor_spec : sl_opacity.

#[global] Arguments immer_map_find_spec : simpl never.
#[global] Arguments immer_map_insert_spec : simpl never.
#[global] Arguments immer_map_move_assign_spec : simpl never.
#[global] Arguments immer_map_dtor_spec : simpl never.
