Require Import skylabs.auto.cpp.proof.

Set Default Goal Selector "!".
Import linearity.

Module scalar_array.
  Definition array_name (ty : type) (extent : Z) : name :=
    ("std::array".<< Atype ty, Avalue (Eint extent Tulong) >>)%cpp_name.

  Section with_Sigma.
    Context `{Sigma : cpp_logic} {CU : genv}.

    (* libstdc++ uses _M_elems for nonempty arrays. *)
    Definition R (ty : type) (extent : Z) (q : cQp.t)
        (values : list val) : Rep :=
      _field (Field (array_name ty extent) (field_name.Id "_M_elems"))
        |-> (type_ptrR (Tarray ty (Z.to_N extent))
             ** arrayR ty (primR ty q) values)
      ** structR (array_name ty extent) q
      ** pureR [| Z.of_nat (length values) = extent |].

    #[global] Instance R_learn ty extent : LearnEq2 (R ty extent) :=
      ltac:(solve_learnable).

    #[global] Instance R_type_ptr ty extent q values :
      Observe (type_ptrR (Tnamed (array_name ty extent)))
        (R ty extent q values).
    Proof.
      unfold R. apply _.
    Qed.

    Definition R_type_ptr_F := ltac:(mk_at_obs_fwd R_type_ptr).

    (* These are library-boundary specs, not proofs of the compiler-generated
       __builtin_memcpy body. Integer assignment leaves the source unchanged;
       non-integer, qualified-element, and zero-sized arrays are excluded. *)
    Definition assign_spec (move : bool) (ty : type) (extent : Z) : mpred :=
      let arr := array_name ty extent in
      let argty := if move then Trv_ref (Tnamed arr)
                   else Tref (Tconst (Tnamed arr)) in
      specify.template.op arr OOEqual function_qualifiers.N
        (Tref (Tnamed arr)) [argty] $
        \this this
        \arg{other : ptr} "other" (Vref other)
        \pre [| (match ty with Tnum _ _ => true | _ => false end) = true
                /\ (0 < extent < 2 ^ 64)%Z |]
        \pre{(q : cQp.t) (old values : list val)}
          this |-> R ty extent 1$m old
          ** other |-> R ty extent q values
        \post[Vref this]
          this |-> R ty extent 1$m values
          ** other |-> R ty extent q values.

    Definition SpecFor_copy_assign := RegisterSpec (assign_spec false).
    #[global] Existing Instance SpecFor_copy_assign.
    Definition SpecFor_move_assign := RegisterSpec (assign_spec true).
    #[global] Existing Instance SpecFor_move_assign.
  End with_Sigma.

  #[global] Hint Opaque R assign_spec : sl_opacity.
  #[global] Hint Resolve R_type_ptr_F : sl_opacity.
End scalar_array.
