Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.disableIPMtacs_use_go_instead.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma nth_of_lookupN_local {A : Type}
      (xs : list A) (index : N) (value default : A) :
    xs !! index = Some value ->
    nth (N.to_nat index) xs default = value.
  Proof using.
    intro Hlookup.
    rewrite lookupN_nth_error in Hlookup.
    exact (@nth_error_nth A xs (N.to_nat index) value default Hlookup).
  Qed.

  Lemma nth_of_lookupZ_of_N_local {A : Type}
      (xs : list A) (index : N) (value default : A) :
    xs !! Z.of_N index = Some value ->
    nth (N.to_nat index) xs default = value.
  Proof using.
    intro HlookupZ.
    pose proof
      (proj1 (lookupZ_Some_to_N xs (Z.of_N index) value) HlookupZ)
      as [_ HlookupN].
    replace (Z.to_N (Z.of_N index)) with index in HlookupN by lia.
    exact (nth_of_lookupN_local xs index value default HlookupN).
  Qed.

  Lemma arrayLR_combine_middle_lookup_local {A : Type}
      (ty : type) (p : ptr) (i j k : Z) (f : A -> Rep) (xs : list A)
      (Hijk : SolveArith (i <= j /\ j < k)%Z) :
    type_ptr ty (p .[ ty ! (j)%Z ]) **
    (Exists x : A,
      p .[ ty ! (j)%Z ] |-> f x **
      p |-> arrayLR ty i j f (sliceZ i i j xs) **
      p |-> arrayLR ty (j + 1)%Z k f (sliceZ i (j + 1)%Z k xs) **
      [| lengthN xs = Z.to_N (k - i) |] **
      [| xs !! (j - i)%Z = Some x |]) |--
    p |-> arrayLR ty i k f xs.
  Proof using CU MODd Sigma.
    pose proof
      (@instances.list_split_middle_forall_var_sliceZ
         A i j k xs _ (j + 1)%Z eq_refl (j - i)%Z eq_refl)
      as Hsplit.
    pose proof
      (@classes.extract _ _ _ _ _ _
         (@array.array_sliceR_extractable_middle _ _ _ _ A ty p i j (j + 1)%Z
            k f xs Hijk _ _ _ _ _ Hsplit eq_refl))
      as Hextract.
    rewrite Hextract.
    go.
  Qed.

  Definition arrayLR_combine_middle_lookup_local_B {A : Type}
      ty p i j k f xs Hijk :=
    [BWD]
      (@arrayLR_combine_middle_lookup_local
         A ty p i j k f xs Hijk).

  Lemma prf_storage_page_values_holder_start_const :
    verify[source] storage_page_values_holder_start_const_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    unfold boost_small_vector.SmallVectorHolderR.
    go.
  Qed.

  Lemma prf_storage_page_values_index_const :
    verify[source] storage_page_values_index_const_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    unfold boost_small_vector.SmallVectorR,
      boost_small_vector.SmallVectorCapR,
      boost_small_vector.SmallVectorSpineR,
      boost_small_vector.SmallVectorPayloadR,
      boost_small_vector.vector_holder_field,
      storage_page_values_vector_ty.
    unfold Field'', Ndependent'.
    change
      ("boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>"%cpp_name
       .:: field_name.Id "m_holder")
      with
      "boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>::m_holder"%cpp_name.
    go.
    rewrite <- (bi.exist_intro (A := Qp) q).
    iExists base, (N.of_nat (length values)), capacity.
    go.
    lazymatch goal with
    | Hlookup : values !! _ = Some ?t |- _ =>
        rewrite (nth_of_lookupZ_of_N_local values index t 0%N Hlookup)
    end.
    assert
      (Hijk :
        SolveArith
          (0 <= Z.of_N index /\
           Z.of_N index < Z.of_nat (length values))%Z).
    {
      constructor.
      lia.
    }
    rewrite <- (bi.exist_intro (A := ptr) base).
    rewrite <- (bi.exist_intro (A := N) capacity).
    go using
      (arrayLR_combine_middle_lookup_local_B
         bytes32_ty base 0 (Z.of_N index) (Z.of_nat (length values))
         (bytes32R (cQp.mut q)) values Hijk).
  Qed.
End with_Sigma.
