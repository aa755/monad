Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.blake3specs.
Require Import monad.proofs.libspecs.blake3.blake3_impl_h_specs.
Require monad.proofs.libspecs.blake3.model.
Require Import skylabs.lang.cpp.logic.object_repr.

Import linearity.

Set Warnings "+sl-impossible-patterns".

Transparent
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R.

Opaque init_leaf_scratch_model.

Definition leaf_clear_lowbit (word : N) : N :=
  N.land word (word - 1).

Fixpoint leaf_loop_indices (fuel : nat) (word : N) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if N.eqb word 0
      then []
      else
        let idx := N.to_nat (countr_zero64 word) in
        idx :: leaf_loop_indices fuel' (leaf_clear_lowbit word)
  end.

Definition leaf_indices (w : N) : list nat :=
  leaf_loop_indices page_pair_count w.

Definition leaf_loop_state
  (x : N) (y : list nat) (z : N) : Prop :=
  let fuel := (page_pair_count - length y)%nat in
  leaf_indices x = List.app y (leaf_loop_indices fuel z) /\
  List.Forall (fun idx => Nat.lt idx page_pair_count) y /\
  Nat.le ((length y + N.to_nat (popcount64 z))%nat) page_pair_count /\
  N.lt x (2 ^ 64) /\
  N.lt z (2 ^ 64).

Definition leaf_pair_hash
    (page : list N) (pair_index : nat) : N :=
  blake3model.bytes32_to_N
    (blake3model.H64
       blake3model.leaf_mode (page_pair_leaf_model page pair_index)).

Fixpoint apply_leaf_hashes_to_scratch
    (page : list N) (scratch : list N) (indices : list nat) : list N :=
  match indices with
  | [] => scratch
  | index :: rest =>
      apply_leaf_hashes_to_scratch
        page (<[ index := leaf_pair_hash page index ]> scratch) rest
  end.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Definition leaf_pair_block_ty : type :=
    Tarray Tuchar 64%N.

  Inductive leaf_pair_block_row : Type :=
  | LeafPairBlockUninit
  | LeafPairBlockLeft : blake3model.digest -> leaf_pair_block_row
  | LeafPairBlockFull : blake3model.bytes64 -> leaf_pair_block_row.

  Definition leaf_pair_block_rowR (row : leaf_pair_block_row) : Rep :=
    match row with
    | LeafPairBlockUninit =>
        arrayLR Tuchar 0 64
          (fun _ : unit => anyR Tuchar 1$m)
          (replicateN 64 ())
    | LeafPairBlockLeft lhs =>
        arrayLR Tuchar 0 32
          (fun byte : val => primR Tuchar 1$m byte)
          (blake3specs.bytes32_byte_values lhs)
        ** arrayLR Tuchar 32 64
          (fun _ : unit => anyR Tuchar 1$m)
          (replicateN 32 ())
    | LeafPairBlockFull block =>
        blake3specs.Blake3BlockR 1 block
    end.

  Definition leaf_pair_bytesp (pairsp : ptr) (row : nat) : ptr :=
    pairsp .[ leaf_pair_block_ty ! Z.of_nat row ].

  Definition uninitR_anyR_F ty q :=
    [FWD] (uninitR_anyR ty q).

  Definition leaf_pair_block_rows
      (page : list N) (indices : list nat) : list leaf_pair_block_row :=
    map
      (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
      indices ++
    replicateN
      (Z.to_N (64 - Z.of_nat (length indices))) LeafPairBlockUninit.

  Lemma leaf_pair_block_any_rows_init (p : ptr) :
    p |-> arrayLR leaf_pair_block_ty 0 64
          (fun _ : unit =>
             arrayLR Tuchar 0 64
               (fun _ : unit => anyR Tuchar 1$m)
               (replicateN 64 ()))
          (replicateN 64 ())
    |--
    p |-> arrayLR leaf_pair_block_ty 0 64
          leaf_pair_block_rowR (replicateN 64 LeafPairBlockUninit).
  Proof using CU MODd Sigma.
    assert
      (Hrows :
        replicateN 64 LeafPairBlockUninit =
        map (fun _ : unit => LeafPairBlockUninit)
          (replicateN 64 ())).
    { vm_compute. reflexivity. }
    rewrite Hrows.
    rewrite
      (array_sliceR_fmap
         (ty := leaf_pair_block_ty)
         0 64 (replicateN 64 ())
         leaf_pair_block_rowR
         (fun _ : unit => LeafPairBlockUninit)).
    simpl.
    go.
  Qed.

  Definition leaf_pair_block_any_rows_init_F (p : ptr) :=
    [FWD] (leaf_pair_block_any_rows_init p).

  Lemma leaf_pair_block_uninit_rows_forget (p : ptr) :
    p |-> arrayLR leaf_pair_block_ty 0 64
          leaf_pair_block_rowR (replicateN 64 LeafPairBlockUninit)
    |--
    p |-> arrayLR leaf_pair_block_ty 0 64
          (fun _ : unit =>
             arrayLR Tuchar 0 64
               (fun _ : unit => anyR Tuchar 1$m)
               (replicateN 64 ()))
          (replicateN 64 ()).
  Proof using CU MODd Sigma.
    assert
      (Hrows :
        replicateN 64 LeafPairBlockUninit =
        map (fun _ : unit => LeafPairBlockUninit)
          (replicateN 64 ())).
    { vm_compute. reflexivity. }
    rewrite Hrows.
    rewrite
      (array_sliceR_fmap
         (ty := leaf_pair_block_ty)
         0 64 (replicateN 64 ())
         leaf_pair_block_rowR
         (fun _ : unit => LeafPairBlockUninit)).
    cbn [leaf_pair_block_rowR].
    go using uninitR_anyR_F.
  Qed.

  Definition leaf_pair_block_uninit_rows_forget_F (p : ptr) :=
    [FWD] (leaf_pair_block_uninit_rows_forget p).

  Fixpoint leaf_input_blocks_from
      (pairsp : ptr) (row : nat) (page : list N) (indices : list nat)
      : list blake3specs.blake3_input_block :=
    match indices with
    | [] => []
    | idx :: rest =>
        blake3specs.mk_blake3_input_block
          (leaf_pair_bytesp pairsp row)
          (page_pair_leaf_model page idx) ::
        leaf_input_blocks_from pairsp (S row) page rest
    end.

  Definition leaf_input_blocks
      (pairsp : ptr) (page : list N) (indices : list nat)
      : list blake3specs.blake3_input_block :=
    leaf_input_blocks_from pairsp 0 page indices.

  Definition leaf_input_ptrs (pairsp : ptr) (indices : list nat)
      : list ptr :=
    map (leaf_pair_bytesp pairsp) (seq 0 (length indices)).

  Lemma leaf_input_blocks_length pairsp row page indices :
    length (leaf_input_blocks_from pairsp row page indices) =
    length indices.
  Proof using.
    revert row.
    induction indices as [| idx rest IH]; intro row.
    { reflexivity. }
    simpl.
    rewrite IH.
    reflexivity.
  Qed.

  Lemma leaf_input_blocks_ptrs_from pairsp row page indices :
    map blake3specs.blake3_input_block_ptr
      (leaf_input_blocks_from pairsp row page indices) =
    map (leaf_pair_bytesp pairsp) (seq row (length indices)).
  Proof using.
    revert row.
    induction indices as [| idx rest IH]; intro row.
    { reflexivity. }
    simpl.
    rewrite IH.
    reflexivity.
  Qed.

  Lemma leaf_input_blocks_ptrs pairsp page indices :
    map blake3specs.blake3_input_block_ptr
      (leaf_input_blocks pairsp page indices) =
    leaf_input_ptrs pairsp indices.
  Proof using.
    unfold leaf_input_blocks, leaf_input_ptrs.
    apply leaf_input_blocks_ptrs_from.
  Qed.

  Lemma leaf_input_blocks_data
      pairsp page indices :
    map blake3specs.blake3_input_block_data
      (leaf_input_blocks pairsp page indices) =
    map (page_pair_leaf_model page) indices.
  Proof using.
    unfold leaf_input_blocks.
    generalize 0%nat.
    induction indices as [| idx rest IH]; intro row.
    { reflexivity. }
    simpl.
    rewrite IH.
    reflexivity.
  Qed.

  Definition leaf_index_arrayR (indices : list nat) : Rep :=
    as_Rep
      (fun base =>
         base |-> arrayLR Tuchar (Z.of_nat (length indices)) 64
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN
              (Z.to_N (64 - Z.of_nat (length indices))) ())
         ** base |-> arrayLR Tuchar 0 (Z.of_nat (length indices))
           (fun index : nat => ucharR 1$m (Z.of_nat index)) indices).

  Definition leaf_inputs_arrayR
      (pairsp : ptr) (indices : list nat) : Rep :=
    as_Rep
      (fun base =>
         base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
           (Z.of_nat (length indices)) 64
           (fun _ : unit =>
              anyR blake3specs.blake3_input_ptr_store_ty 1$m)
           (replicateN
              (Z.to_N (64 - Z.of_nat (length indices))) ())
         ** base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
           0 (Z.of_nat (length indices))
           (fun row : nat =>
              primR blake3specs.blake3_input_ptr_value_ty 1$m
                (Vptr (leaf_pair_bytesp pairsp row)))
           (seq 0 (length indices))).

  Definition primR_anyR_F ty q v :=
    [FWD] (primR_anyR ty q v).

  Lemma anyR_input_ptr_store_value q :
    anyR blake3specs.blake3_input_ptr_store_ty q -|-
    anyR blake3specs.blake3_input_ptr_value_ty q.
  Proof using.
    reflexivity.
  Qed.

  Lemma primR_input_ptr_anyR_store q inputp :
    primR blake3specs.blake3_input_ptr_value_ty q (Vptr inputp)
    |--
    anyR blake3specs.blake3_input_ptr_store_ty q.
  Proof using MODd.
    go using primR_anyR_F.
  Qed.

  Definition primR_input_ptr_anyR_store_F q inputp :=
    [FWD] (primR_input_ptr_anyR_store q inputp).

  Lemma input_ptr_arrayR_forget_store (input_ptrs : list ptr) :
    arrayR blake3specs.blake3_input_ptr_store_ty
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty
           1$m (Vptr inputp))
      input_ptrs
    |--
    arrayR blake3specs.blake3_input_ptr_store_ty
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN (lengthN input_ptrs) ()).
  Proof using MODd.
    induction input_ptrs as [| inputp input_ptrs IH].
    {
      rewrite lengthN_nil replicateN_0 !arrayR_nil.
      go.
    }
    {
      rewrite lengthN_cons N.add_1_r replicateN_S !arrayR_cons.
      assert (IH_at :
        .[ blake3specs.blake3_input_ptr_store_ty ! 1 ]
          |-> arrayR blake3specs.blake3_input_ptr_store_ty
                (fun inputp : ptr =>
                   primR blake3specs.blake3_input_ptr_value_ty
                     1$m (Vptr inputp))
                input_ptrs
        |--
        .[ blake3specs.blake3_input_ptr_store_ty ! 1 ]
          |-> arrayR blake3specs.blake3_input_ptr_store_ty
                (fun _ : unit =>
                   anyR blake3specs.blake3_input_ptr_store_ty 1$m)
                (replicateN (lengthN input_ptrs) ())).
      {
        apply _offsetR_mono.
        exact IH.
      }
      pose (IH_F := [FWD] IH_at).
      go using primR_input_ptr_anyR_store_F, IH_F.
    }
  Qed.

  Definition input_ptr_arrayR_forget_store_F input_ptrs :=
    [FWD] (input_ptr_arrayR_forget_store input_ptrs).

  Lemma input_ptr_null_arrayR_forget_store
      (len : N) :
    arrayR blake3specs.blake3_input_ptr_store_ty
      (primR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN len (Vptr nullptr))
    |--
    arrayR blake3specs.blake3_input_ptr_store_ty
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN len ()).
  Proof using MODd.
    induction len using N.peano_ind.
    {
      rewrite !replicateN_0 !arrayR_nil.
      go.
    }
    {
      rewrite !replicateN_S !arrayR_cons.
      assert (IH_at :
        .[ blake3specs.blake3_input_ptr_store_ty ! 1 ]
          |-> arrayR blake3specs.blake3_input_ptr_store_ty
                (primR blake3specs.blake3_input_ptr_store_ty 1$m)
                (replicateN len (Vptr nullptr))
        |--
        .[ blake3specs.blake3_input_ptr_store_ty ! 1 ]
          |-> arrayR blake3specs.blake3_input_ptr_store_ty
                (fun _ : unit =>
                   anyR blake3specs.blake3_input_ptr_store_ty 1$m)
                (replicateN len ())).
      {
        apply _offsetR_mono.
        exact IHlen.
      }
      pose (IH_F := [FWD] IH_at).
      go using primR_anyR_F, IH_F.
    }
  Qed.

  Lemma input_ptr_null_arrayR_forget_store_at
      (base : ptr) (len : N) :
    base |-> arrayR blake3specs.blake3_input_ptr_store_ty
      (primR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN len (Vptr nullptr))
    |--
    base |-> arrayR blake3specs.blake3_input_ptr_store_ty
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN len ()).
  Proof using MODd.
    apply _at_mono.
    exact (input_ptr_null_arrayR_forget_store len).
  Qed.

  Definition input_ptr_null_arrayR_forget_store_at_F base len :=
    [FWD] (input_ptr_null_arrayR_forget_store_at base len).

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).

  Lemma use_wand_local_r (P Q : mpred) :
    P ** (P -* Q) |-- Q.
  Proof using.
    go.
  Qed.

  Definition use_wand_local_r_F P Q :=
    [FWD] (use_wand_local_r P Q).

  Definition const_input_ptr_array_type_ptr_erase_F p :=
    [FWD->]
      (type_ptr_erase (Tarray (Tptr (Qconst Tuchar)) 64%N) p).

  Definition at_sep_F p P Q :=
    [FWD->] (_at_sep p P Q).

  Definition offsetR_sep_F o P Q :=
    [FWD->] (_offsetR_sep o P Q).

  Definition at_offsetR_F p o R :=
    [FWD->] (_at_offsetR p o R).

  Lemma arrayLR_extract_middle_lookup_local {A : Type}
      (ty : type) (p : ptr) (i j k : Z) (f : A -> Rep) (xs : list A)
      (Hijk : SolveArith (i <= j /\ j < k)%Z) :
    p |-> arrayLR ty i k f xs |--
    type_ptr ty (p .[ ty ! (j)%Z ]) **
    Exists x : A,
      p .[ ty ! (j)%Z ] |-> f x **
      p |-> arrayLR ty i j f (sliceZ i i j xs) **
      p |-> arrayLR ty (j + 1)%Z k f (sliceZ i (j + 1)%Z k xs) **
      [| lengthN xs = Z.to_N (k - i) |] **
      [| xs !! (j - i)%Z = Some x |].
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
    go1.
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

  Lemma arrayLR_extract_middle_lookup_equiv_local {A : Type}
      (ty : type) (p : ptr) (i j k : Z) (f : A -> Rep) (xs : list A)
      (Hijk : SolveArith (i <= j /\ j < k)%Z) :
    p |-> arrayLR ty i k f xs -|-
    type_ptr ty (p .[ ty ! (j)%Z ]) **
    Exists x : A,
      p .[ ty ! (j)%Z ] |-> f x **
      p |-> arrayLR ty i j f (sliceZ i i j xs) **
      p |-> arrayLR ty (j + 1)%Z k f (sliceZ i (j + 1)%Z k xs) **
      [| lengthN xs = Z.to_N (k - i) |] **
      [| xs !! (j - i)%Z = Some x |].
  Proof using CU MODd Sigma.
    split'.
    { exact (arrayLR_extract_middle_lookup_local ty p i j k f xs Hijk). }
    { exact (arrayLR_combine_middle_lookup_local ty p i j k f xs Hijk). }
  Qed.

  Definition leaf_index_tail_head_F base (seen : list nat) xs
      (Hijk :
        SolveArith
          (Z.of_nat (length seen) <= Z.of_nat (length seen) /\
           Z.of_nat (length seen) < 64)%Z) :=
    [FWD->]
      (arrayLR_extract_middle_lookup_equiv_local
         Tuchar base
         (Z.of_nat (length seen)) (Z.of_nat (length seen)) 64
         (fun _ : unit => anyR Tuchar 1$m) xs Hijk).

  Definition leaf_inputs_tail_head_F base (seen : list nat) xs
      (Hijk :
        SolveArith
          (Z.of_nat (length seen) <= Z.of_nat (length seen) /\
           Z.of_nat (length seen) < 64)%Z) :=
    [FWD->]
      (arrayLR_extract_middle_lookup_equiv_local
         blake3specs.blake3_input_ptr_store_ty base
         (Z.of_nat (length seen)) (Z.of_nat (length seen)) 64
         (fun _ : unit =>
            anyR blake3specs.blake3_input_ptr_store_ty 1$m) xs Hijk).

  Definition leaf_inputs_uninit_tail_head_F base (seen : list nat) xs
      (Hijk :
        SolveArith
          (Z.of_nat (length seen) <= Z.of_nat (length seen) /\
           Z.of_nat (length seen) < 64)%Z) :=
    [FWD->]
      (arrayLR_extract_middle_lookup_equiv_local
         blake3specs.blake3_input_ptr_store_ty base
         (Z.of_nat (length seen)) (Z.of_nat (length seen)) 64
         (fun _ : unit =>
            uninitR (Tptr Tuchar) 1$m) xs Hijk).

	  Lemma ptr_o_sub_N_of_nat (ty : type) (base : ptr) (n : nat) :
	    base .[ ty ! N.of_nat n ] = base .[ ty ! Z.of_nat n ].
	  Proof using CU.
	    rewrite nat_N_Z.
	    reflexivity.
	  Qed.

  Lemma bytes32_to_N_bytes32_of_N_range_local word :
    (word < 2 ^ 256)%N ->
    blake3model.bytes32_to_N (blake3model.bytes32_of_N word) = word.
  Proof using.
    intro Hword.
    unfold blake3model.bytes32_of_N,
      blake3model.bytes32_to_N,
      model.bytes32_to_N, model.bytes32_of_N.
    rewrite N.mod_small.
    {
      exact (fin.to_of_N' (model.pow2N_pos 256) word Hword).
    }
    {
      change (word < 2 ^ 256)%N.
      exact Hword.
    }
  Qed.

  Lemma bytes32_byte_values_of_N_range_local word :
    (word < 2 ^ 256)%N ->
    blake3specs.bytes32_byte_values (blake3model.bytes32_of_N word) =
    exec_specs.bytes32_be_values word.
	  Proof using.
	    intro Hword.
	    unfold blake3specs.bytes32_byte_values,
	      blake3_impl_h_specs.bytes32_byte_values.
    change (model.bytes32_to_N (blake3model.bytes32_of_N word))
      with
        (blake3model.bytes32_to_N
           (blake3model.bytes32_of_N word)).
	    rewrite bytes32_to_N_bytes32_of_N_range_local.
    {
      reflexivity.
    }
    exact Hword.
  Qed.

  Lemma arrayLR_app_combine_local {A : Type}
      (ty : type) (Hty : @HasSize CU ty)
      (p : ptr) (i j k : Z)
      (f : A -> Rep) (xs ys : list A) :
    lengthZ xs = j - i ->
    lengthZ ys = k - j ->
    p |-> arrayLR ty i j f xs
    ** p |-> arrayLR ty j k f ys
    |--
    p |-> arrayLR ty i k f (xs ++ ys).
  Proof using CU MODd Sigma.
    intros Hxs Hys.
    rewrite !array_sliceR.unlock.
    rewrite !_at_sep !_at_only_provable.
    rewrite arrayR_app__N.
    rewrite Hxs Hys.
    repeat rewrite _at_offsetR.
    rewrite
      (_at_sep
         (p .[ ty ! i ])
         (arrayR ty f xs)
         (.[ ty ! j - i ] |-> arrayR ty f ys)).
    repeat rewrite _at_offsetR.
    rewrite o_sub_sub.
    replace (i + (j - i))%Z with j by lia.
    go.
  Qed.

  Definition arrayLR_app_combine_local_F {A : Type}
      ty (Hty : @HasSize CU ty) p i j k f (xs ys : list A) Hxs Hys :=
    [FWD] (@arrayLR_app_combine_local
             A ty Hty p i j k f xs ys Hxs Hys).

  Lemma any_unit_arrayLR32_to_val_arrayLR32_local (base : ptr) :
    base |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ())
    |--
    base |-> arrayLR Tuchar 0 32
      (fun _ : val => anyR Tuchar 1$m) (replicateN 32 (Vint 0)).
  Proof using CU MODd Sigma.
    change (replicateN 32 (Vint 0))
      with ((fun _ : unit => Vint 0) <$> replicateN 32 ()).
    rewrite array_sliceR_fmap.
    go.
  Qed.

  Definition any_unit_arrayLR32_to_val_arrayLR32_local_F (base : ptr) :=
    [FWD] (any_unit_arrayLR32_to_val_arrayLR32_local base).

  Lemma leaf_pair_block_uninit_split_first
      (base : ptr) :
    base |-> leaf_pair_block_rowR LeafPairBlockUninit
    |--
    base |-> arrayLR Tuchar 0 32
      (fun _ : val => anyR Tuchar 1$m) (replicateN 32 (Vint 0))
    ** base |-> arrayLR Tuchar 32 64
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ()).
  Proof using CU MODd Sigma.
    unfold leaf_pair_block_rowR.
    change (replicateN 64 ())
      with (List.app (replicateN 32 ()) (replicateN 32 ())).
    assert (Hprefix :
      lengthN (replicateN 32 ()) = Z.to_N (32 - 0)).
    {
      rewrite lengthN_simpl.
      reflexivity.
    }
    assert (Hlo : (0 <= 32)%Z) by lia.
    assert (Hhi : (32 <= 64)%Z) by lia.
    pose proof
      (@array_sliceR_app'
         _ _ _ _ unit Tuchar base
         0 32 64
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateN 32 ())
         (replicateN 32 ())
         Hprefix Hlo Hhi) as Happ.
    rewrite Happ.
    go using any_unit_arrayLR32_to_val_arrayLR32_local_F.
  Qed.

  Definition leaf_pair_block_uninit_split_first_F base :=
    [FWD] (leaf_pair_block_uninit_split_first base).

  Lemma arrayLR_32_64_shift_zero_local {A : Type}
      (base : ptr) (R : A -> Rep) xs :
    lengthZ xs = 32 ->
    base |-> arrayLR Tuchar 32 64 R xs
    |--
    base .[ Tuchar ! 32 ] |-> arrayLR Tuchar 0 32 R xs.
  Proof using CU MODd Sigma.
    intro Hlen.
    rewrite !array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite
      (_at_sep
         (base .[ Tuchar ! 32 ])
         [| lengthZ xs = 32 - 0 |]
         (.[ Tuchar ! 0 ] |-> arrayR Tuchar R xs)).
    rewrite _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite Hlen.
    go.
  Qed.

  Definition arrayLR_32_64_shift_zero_local_F {A : Type}
      base R (xs : list A) Hlen :=
    [FWD] (@arrayLR_32_64_shift_zero_local
             A base R xs Hlen).

  Lemma any_unit_arrayLR32_64_to_val_arrayLR0_32_local (base : ptr) :
    base |-> arrayLR Tuchar 32 64
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ())
    |--
    base .[ Tuchar ! 32 ] |-> arrayLR Tuchar 0 32
      (fun _ : val => anyR Tuchar 1$m) (replicateN 32 (Vint 0)).
  Proof using CU MODd Sigma.
    etransitivity.
    {
      apply arrayLR_32_64_shift_zero_local.
      vm_compute.
      reflexivity.
    }
    apply any_unit_arrayLR32_to_val_arrayLR32_local.
  Qed.

  Definition any_unit_arrayLR32_64_to_val_arrayLR0_32_local_F (base : ptr) :=
    [FWD] (any_unit_arrayLR32_64_to_val_arrayLR0_32_local base).

  Lemma memcpy_dst_any_val32_witness_local (base : ptr) Q :
    base |-> arrayLR Tuchar 0 32
      (fun _ : val => anyR Tuchar 1$m) (replicateN 32 (Vint 0))
    ** Q
    |--
    Exists A : Type, Exists old_bytes : list A,
      base |-> arrayLR Tuchar 0 32
        (fun _ : A => anyR Tuchar 1$m) old_bytes
      ** Q.
  Proof using CU MODd Sigma.
    rewrite <- (bi.exist_intro (A := Type) val).
    rewrite <-
      (bi.exist_intro
         (A := list val) (replicateN 32 (Vint 0))).
    go.
  Qed.

  Definition memcpy_dst_any_val32_witness_local_F (base : ptr) Q :=
    [FWD] (memcpy_dst_any_val32_witness_local base Q).

  Definition bytes32R_to_bytes_field_F base word :=
    [FWD] (bytes32R_to_bytes_field base word).

  Definition bytes_field_to_bytes32R_B base word Hrange :=
    [BWD] (bytes_field_to_bytes32R base word Hrange).

  Lemma leaf_pair_block_rows_replicate_tail (seen : list nat) :
    (length seen < page_pair_count)%nat ->
    replicateN (Z.to_N (64 - Z.of_nat (length seen)))
      LeafPairBlockUninit =
    LeafPairBlockUninit ::
    replicateN (Z.to_N (64 - Z.of_nat (length seen) - 1))
      LeafPairBlockUninit.
  Proof using.
    intro Hseen.
    unfold replicateN.
    replace (N.to_nat (Z.to_N (64 - Z.of_nat (length seen))))
      with
        (S
           (N.to_nat
              (Z.to_N (64 - Z.of_nat (length seen) - 1)))).
    {
      reflexivity.
    }
    unfold page_pair_count in Hseen.
    lia.
  Qed.

  Lemma leaf_pair_block_rows_current_split
      (base : ptr) page seen :
    (length seen < page_pair_count)%nat ->
    base |-> arrayLR leaf_pair_block_ty 0 64 leaf_pair_block_rowR
      (leaf_pair_block_rows page seen)
    |--
    base |-> arrayLR leaf_pair_block_ty 0 (Z.of_nat (length seen))
      leaf_pair_block_rowR
      (map (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
         seen)
    ** type_ptr leaf_pair_block_ty
         (leaf_pair_bytesp base (length seen))
    ** leaf_pair_bytesp base (length seen)
       |-> leaf_pair_block_rowR LeafPairBlockUninit
    ** base |-> arrayLR leaf_pair_block_ty
         (Z.of_nat (length seen) + 1) 64 leaf_pair_block_rowR
         (replicateN
            (Z.to_N (64 - Z.of_nat (length seen) - 1))
            LeafPairBlockUninit).
  Proof using CU MODd Sigma.
    intro Hseen.
    unfold leaf_pair_block_rows, leaf_pair_bytesp.
    pose proof (leaf_pair_block_rows_replicate_tail seen Hseen)
      as Htail.
    rewrite Htail.
    assert
      (Hprefix :
        lengthN
          (map
             (fun idx =>
                LeafPairBlockFull (page_pair_leaf_model page idx))
             seen) =
        Z.to_N (Z.of_nat (length seen) - 0)).
    {
      rewrite lengthN_length length_map.
      lia.
    }
    assert
      (Hlo : (0 <= Z.of_nat (length seen))%Z) by lia.
    assert
      (Hhi : (Z.of_nat (length seen) <= 64)%Z).
    {
      unfold page_pair_count in Hseen.
      lia.
    }
    pose proof
      (@array_sliceR_app'
         _ _ _ _ leaf_pair_block_row leaf_pair_block_ty base
         0 (Z.of_nat (length seen)) 64
         leaf_pair_block_rowR
         (map
            (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
            seen)
         (LeafPairBlockUninit ::
          replicateN
            (Z.to_N (64 - Z.of_nat (length seen) - 1))
            LeafPairBlockUninit)
         Hprefix Hlo Hhi) as Happ.
    rewrite Happ.
    rewrite array_sliceR_cons.
    go.
  Qed.

  Definition leaf_pair_block_rows_current_split_F
      (base : ptr) page seen Hseen :=
    [FWD] (leaf_pair_block_rows_current_split base page seen Hseen).

  Lemma leaf_pair_block_left_from_first_copy
      (base : ptr) word :
    (word < 2 ^ 256)%N ->
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values word)
    ** base |-> arrayLR Tuchar 32 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 32 ())
    |--
    base |-> leaf_pair_block_rowR
      (LeafPairBlockLeft (blake3model.bytes32_of_N word)).
  Proof using CU MODd Sigma.
    intro Hword.
    unfold leaf_pair_block_rowR.
    pose proof (bytes32_byte_values_of_N_range_local word Hword)
      as Hbytes.
    rewrite Hbytes.
    go.
  Qed.

  Definition leaf_pair_block_left_from_first_copy_F (base : ptr) word Hword :=
    [FWD] (leaf_pair_block_left_from_first_copy base word Hword).

  Lemma leaf_pair_block_left_split_second
      (base : ptr) lhs :
    base |-> leaf_pair_block_rowR (LeafPairBlockLeft lhs)
    |--
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      (blake3specs.bytes32_byte_values lhs)
    ** base .[ Tuchar ! 32 ] |-> arrayLR Tuchar 0 32
      (fun _ : val => anyR Tuchar 1$m)
      (replicateN 32 (Vint 0)).
  Proof using CU MODd Sigma.
    unfold leaf_pair_block_rowR.
    go using any_unit_arrayLR32_64_to_val_arrayLR0_32_local_F.
  Qed.

  Definition leaf_pair_block_left_split_second_F (base : ptr) lhs :=
    [FWD] (leaf_pair_block_left_split_second base lhs).

  Lemma byte_arrayLR0_to_arrayR64_local
      (base : ptr) bytes :
    length bytes = 64%nat ->
    base |-> arrayLR Tuchar 0 64
      (fun byte : val => primR Tuchar 1$m byte) bytes
    |--
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar 1$m byte) bytes.
  Proof using CU MODd Sigma.
    intro Hlen.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite lengthZ_correct Hlen.
    go.
  Qed.

  Definition byte_arrayLR0_to_arrayR64_local_F (base : ptr) bytes Hlen :=
    [FWD] (byte_arrayLR0_to_arrayR64_local base bytes Hlen).

  Lemma leaf_pair_block_full_from_offset_halves
      (base : ptr) lhs rhs :
    (lhs < 2 ^ 256)%N ->
    (rhs < 2 ^ 256)%N ->
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values lhs)
    ** base |-> arrayLR Tuchar 32 64
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values rhs)
    |--
    base |-> leaf_pair_block_rowR
      (LeafPairBlockFull (blake3model.bytes32_of_N lhs, blake3model.bytes32_of_N rhs)).
  Proof using CU MODd Sigma.
    intros Hlhs Hrhs.
    unfold leaf_pair_block_rowR, blake3specs.Blake3BlockR,
      blake3_impl_h_specs.Blake3BlockR,
      blake3specs.BlockR,
      blake3_impl_h_specs.BlockR,
      blake3specs.bytes64_byte_values,
      blake3_impl_h_specs.bytes64_byte_values.
    cbn [fst snd].
    pose proof (bytes32_byte_values_of_N_range_local lhs Hlhs)
      as Hlhs_bytes.
    pose proof (bytes32_byte_values_of_N_range_local rhs Hrhs)
      as Hrhs_bytes.
    unfold blake3specs.bytes32_byte_values in Hlhs_bytes, Hrhs_bytes.
    rewrite Hlhs_bytes Hrhs_bytes.
    change (32 + 32)%Z with 64%Z.
    etransitivity.
    {
      apply (arrayLR_app_combine_local
        Tuchar ltac:(apply has_size; exact _)
        base 0 32 64
        (fun byte : val => primR Tuchar 1$m byte)
        (exec_specs.bytes32_be_values lhs)
        (exec_specs.bytes32_be_values rhs)).
      {
        rewrite lengthZ_correct.
        reflexivity.
      }
      {
        rewrite lengthZ_correct.
        reflexivity.
      }
    }
    apply byte_arrayLR0_to_arrayR64_local.
    rewrite app_length.
    reflexivity.
  Qed.

  Definition leaf_pair_block_full_from_offset_halves_F
      (base : ptr) lhs rhs Hlhs Hrhs :=
    [FWD] (leaf_pair_block_full_from_offset_halves
             base lhs rhs Hlhs Hrhs).

  Lemma leaf_pair_block_full_from_digest_lhs
      (base : ptr) lhs rhs :
    (lhs < 2 ^ 256)%N ->
    (rhs < 2 ^ 256)%N ->
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      (blake3specs.bytes32_byte_values
         (blake3model.bytes32_of_N lhs))
    ** base |-> arrayLR Tuchar 32 64
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values rhs)
    |--
    base |-> leaf_pair_block_rowR
      (LeafPairBlockFull
         (blake3model.bytes32_of_N lhs,
          blake3model.bytes32_of_N rhs)).
  Proof using CU MODd Sigma.
    intros Hlhs Hrhs.
    pose proof (bytes32_byte_values_of_N_range_local lhs Hlhs)
      as Hlhs_bytes.
    rewrite Hlhs_bytes.
    apply leaf_pair_block_full_from_offset_halves; assumption.
  Qed.

  Definition leaf_pair_block_full_from_digest_lhs_F
      (base : ptr) lhs rhs Hlhs Hrhs :=
    [FWD] (leaf_pair_block_full_from_digest_lhs
             base lhs rhs Hlhs Hrhs).

  Lemma page_pair_leaf_model_countr_zero page bits :
    page_pair_leaf_model page (N.to_nat (countr_zero64 bits)) =
    (blake3model.bytes32_of_N
       (nth (Z.to_nat (2 * countr_zero64 bits)) page 0%N),
     blake3model.bytes32_of_N
       (nth (Z.to_nat (2 * countr_zero64 bits + 1)) page 0%N)).
  Proof using.
    unfold page_pair_leaf_model.
    replace (Z.to_nat (2 * countr_zero64 bits))
      with (2 * N.to_nat (countr_zero64 bits))%nat.
    2: {
      rewrite Z2Nat.inj_mul.
      2: { lia. }
      2: { lia. }
      rewrite !N2Z2Nat.
      reflexivity.
    }
    replace (Z.to_nat (2 * countr_zero64 bits + 1))
      with (2 * N.to_nat (countr_zero64 bits) + 1)%nat.
    2: {
      rewrite Z2Nat.inj_add.
      2: { lia. }
      2: { lia. }
      rewrite Z2Nat.inj_mul.
      2: { lia. }
      2: { lia. }
      rewrite !N2Z2Nat.
      reflexivity.
    }
    reflexivity.
  Qed.

  Lemma leaf_pair_block_full_from_countr_zero
      (base : ptr) page bits :
    (nth (Z.to_nat (2 * countr_zero64 bits)) page 0 < 2 ^ 256)%N ->
    (nth (Z.to_nat (2 * countr_zero64 bits + 1)) page 0 < 2 ^ 256)%N ->
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      (blake3specs.bytes32_byte_values
         (blake3model.bytes32_of_N
            (nth (Z.to_nat (2 * countr_zero64 bits)) page 0%N)))
    ** base |-> arrayLR Tuchar 32 64
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values
         (nth (Z.to_nat (2 * countr_zero64 bits + 1)) page 0%N))
    |--
    base |-> leaf_pair_block_rowR
      (LeafPairBlockFull
         (page_pair_leaf_model page (N.to_nat (countr_zero64 bits)))).
  Proof using CU MODd Sigma.
    intros Hlhs Hrhs.
    rewrite page_pair_leaf_model_countr_zero.
    apply leaf_pair_block_full_from_digest_lhs; assumption.
  Qed.

  Definition leaf_pair_block_full_from_countr_zero_F
      (base : ptr) page bits Hlhs Hrhs :=
    [FWD] (leaf_pair_block_full_from_countr_zero
             base page bits Hlhs Hrhs).

  Lemma leaf_pair_block_full_fold
      (base : ptr) block :
    base |-> blake3specs.Blake3BlockR 1 block
    |--
    base |-> leaf_pair_block_rowR (LeafPairBlockFull block).
  Proof using CU MODd Sigma.
    reflexivity.
  Qed.

  Definition leaf_pair_block_full_fold_F base block :=
    [FWD] (leaf_pair_block_full_fold base block).

  Lemma arrayLR_cons_combine_local {A : Type}
      (ty : type) (p : ptr) (m n : Z)
      (R : A -> Rep) (x : A) (xs : list A) :
    type_ptr ty (p .[ ty ! m ])
    ** p .[ ty ! m ] |-> R x
    ** p |-> arrayLR ty (m + 1) n R xs
    |--
    p |-> arrayLR ty m n R (x :: xs).
  Proof using CU MODd Sigma.
    etransitivity.
    {
      apply ChargeCompat.sepSPA2.
    }
    rewrite <- (@array_sliceR_cons _ _ _ _ A ty p m n R x xs).
    go.
  Qed.

  Definition arrayLR_cons_combine_local_F {A : Type}
      ty p m n R (x : A) xs :=
    [FWD] (@arrayLR_cons_combine_local A ty p m n R x xs).

  Lemma leaf_pair_block_rows_current_pack
      (base : ptr) page seen idx :
    (length seen < page_pair_count)%nat ->
    base |-> arrayLR leaf_pair_block_ty 0 (Z.of_nat (length seen))
      leaf_pair_block_rowR
      (map (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
         seen)
    ** type_ptr leaf_pair_block_ty
         (leaf_pair_bytesp base (length seen))
    ** leaf_pair_bytesp base (length seen)
       |-> leaf_pair_block_rowR
             (LeafPairBlockFull (page_pair_leaf_model page idx))
    ** base |-> arrayLR leaf_pair_block_ty
         (Z.of_nat (length seen) + 1) 64 leaf_pair_block_rowR
         (replicateN
            (Z.to_N (64 - Z.of_nat (length seen) - 1))
            LeafPairBlockUninit)
    |--
    base |-> arrayLR leaf_pair_block_ty 0 64 leaf_pair_block_rowR
      (leaf_pair_block_rows page (seen ++ [idx])).
  Proof using CU MODd Sigma.
    intro Hseen.
    unfold leaf_pair_block_rows, leaf_pair_bytesp.
    rewrite map_app.
    simpl.
    rewrite <- app_assoc.
    replace
      (replicateN
         (Z.to_N
            (64 - Z.of_nat (length (seen ++ [idx]))))
         LeafPairBlockUninit)
      with
      (replicateN
         (Z.to_N (64 - Z.of_nat (length seen) - 1))
         LeafPairBlockUninit).
    2: {
      rewrite List.length_app.
      cbn [length].
      f_equal.
      lia.
    }
    change (blake3specs.Blake3BlockR 1
              (page_pair_leaf_model page idx))
      with (leaf_pair_block_rowR
              (LeafPairBlockFull (page_pair_leaf_model page idx))).
    go using
      (arrayLR_cons_combine_local_F
         leaf_pair_block_ty base
         (Z.of_nat (length seen)) 64 leaf_pair_block_rowR
         (LeafPairBlockFull (page_pair_leaf_model page idx))
         (replicateN
            (Z.to_N (64 - Z.of_nat (length seen) - 1))
            LeafPairBlockUninit)).
  Qed.

  Definition leaf_pair_block_rows_current_pack_F
      (base : ptr) page seen idx Hseen :=
    [FWD] (leaf_pair_block_rows_current_pack
             base page seen idx Hseen).

  Lemma leaf_pair_block_rows_current_pack_block
      (base : ptr) page seen idx :
    (length seen < page_pair_count)%nat ->
    base |-> arrayLR leaf_pair_block_ty 0 (Z.of_nat (length seen))
      leaf_pair_block_rowR
      (map (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
         seen)
    ** type_ptr leaf_pair_block_ty
         (leaf_pair_bytesp base (length seen))
    ** leaf_pair_bytesp base (length seen)
       |-> blake3specs.Blake3BlockR 1 (page_pair_leaf_model page idx)
    ** base |-> arrayLR leaf_pair_block_ty
         (Z.of_nat (length seen) + 1) 64 leaf_pair_block_rowR
         (replicateN
            (Z.to_N (64 - (Z.of_nat (length seen) + 1)))
            LeafPairBlockUninit)
    |--
    base |-> arrayLR leaf_pair_block_ty 0 64 leaf_pair_block_rowR
      (leaf_pair_block_rows page (seen ++ [idx])).
  Proof using CU MODd Sigma.
    intro Hseen.
    change (blake3specs.Blake3BlockR 1
              (page_pair_leaf_model page idx))
      with (leaf_pair_block_rowR
              (LeafPairBlockFull (page_pair_leaf_model page idx))).
    replace (64 - (Z.of_nat (length seen) + 1))%Z
      with (64 - Z.of_nat (length seen) - 1)%Z by lia.
    apply leaf_pair_block_rows_current_pack.
    exact Hseen.
  Qed.

  Definition leaf_pair_block_rows_current_pack_block_F
      (base : ptr) page seen idx Hseen :=
    [FWD] (leaf_pair_block_rows_current_pack_block
             base page seen idx Hseen).

  Lemma leaf_pair_block_rows_current_pack_block_direct
      (base : ptr) page seen idx :
    (length seen < page_pair_count)%nat ->
    base |-> arrayLR leaf_pair_block_ty 0 (Z.of_nat (length seen))
      leaf_pair_block_rowR
      (map (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
         seen)
    ** type_ptr leaf_pair_block_ty
         (base .[ leaf_pair_block_ty ! Z.of_nat (length seen) ])
    ** base .[ leaf_pair_block_ty ! Z.of_nat (length seen) ]
       |-> blake3specs.Blake3BlockR 1 (page_pair_leaf_model page idx)
    ** base |-> arrayLR leaf_pair_block_ty
         (Z.of_nat (length seen) + 1) 64 leaf_pair_block_rowR
         (replicateN
            (Z.to_N (64 - (Z.of_nat (length seen) + 1)))
            LeafPairBlockUninit)
    |--
    base |-> arrayLR leaf_pair_block_ty 0 64 leaf_pair_block_rowR
      (leaf_pair_block_rows page (seen ++ [idx])).
  Proof using CU MODd Sigma.
    intro Hseen.
    unfold leaf_pair_block_rows.
    rewrite map_app.
    simpl.
    rewrite <- app_assoc.
    replace
      (replicateN
         (Z.to_N
            (64 - Z.of_nat (length (seen ++ [idx]))))
         LeafPairBlockUninit)
      with
      (replicateN
         (Z.to_N (64 - (Z.of_nat (length seen) + 1)))
         LeafPairBlockUninit).
    2: {
      rewrite List.length_app.
      cbn [length].
      f_equal.
      lia.
    }
    change (blake3specs.Blake3BlockR 1
              (page_pair_leaf_model page idx))
      with (leaf_pair_block_rowR
              (LeafPairBlockFull (page_pair_leaf_model page idx))).
    replace (64 - (Z.of_nat (length seen) + 1))%Z
      with (64 - Z.of_nat (length seen) - 1)%Z by lia.
    go using
      (arrayLR_cons_combine_local_F
         leaf_pair_block_ty base
         (Z.of_nat (length seen)) 64 leaf_pair_block_rowR
         (LeafPairBlockFull (page_pair_leaf_model page idx))
         (replicateN
            (Z.to_N (64 - Z.of_nat (length seen) - 1))
            LeafPairBlockUninit)).
  Qed.

  Definition leaf_pair_block_rows_current_pack_block_direct_F
      (base : ptr) page seen idx Hseen :=
    [FWD] (leaf_pair_block_rows_current_pack_block_direct
             base page seen idx Hseen).

  Lemma leaf_pair_block_rows_current_pack_block_from_slice
      (base : ptr) page seen idx :
    (length seen < page_pair_count)%nat ->
    base |-> typed_sliceR leaf_pair_block_ty 0 64
    ** base |-> arrayLR leaf_pair_block_ty 0 (Z.of_nat (length seen))
      leaf_pair_block_rowR
      (map (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
         seen)
    ** leaf_pair_bytesp base (length seen)
       |-> blake3specs.Blake3BlockR 1 (page_pair_leaf_model page idx)
    ** base |-> arrayLR leaf_pair_block_ty
         (Z.of_nat (length seen) + 1) 64 leaf_pair_block_rowR
         (replicateN
            (Z.to_N (64 - (Z.of_nat (length seen) + 1)))
            LeafPairBlockUninit)
    |--
    base |-> typed_sliceR leaf_pair_block_ty 0 64
    ** base |-> arrayLR leaf_pair_block_ty 0 64 leaf_pair_block_rowR
      (leaf_pair_block_rows page (seen ++ [idx])).
  Proof using CU MODd Sigma.
    intro Hseen.
    unfold leaf_pair_bytesp.
    pose
      (pack_current :=
         [BWD] (leaf_pair_block_rows_current_pack_block_direct
                  base page seen idx Hseen)).
    assert
      (Hcurrent_range :
        SolveArith (0 <= Z.of_nat (length seen) < 64)%Z).
    {
      constructor.
      unfold page_pair_count in Hseen.
      lia.
    }
    pose
      (current_pair_type :=
         @typed_sliceR_elim_type_ptr_C
           thread_info _Σ Sigma CU
           leaf_pair_block_ty 0 64 base
           (Z.of_nat (length seen)) leaf_pair_block_ty
           (base .[ leaf_pair_block_ty ! Z.of_nat (length seen) ])
           (TypePtrImplies_id
              leaf_pair_block_ty
              (base .[ leaf_pair_block_ty ! Z.of_nat (length seen) ]))
           Hcurrent_range).
    go using current_pair_type, pack_current.
  Qed.

  Definition leaf_pair_block_rows_current_pack_block_from_slice_F
      (base : ptr) page seen idx Hseen :=
    [FWD] (leaf_pair_block_rows_current_pack_block_from_slice
             base page seen idx Hseen).

  Lemma arrayR_read_cell_with_wand {A : Type}
      (ty : type) (R : A -> Rep)
      (base : ptr) (xs : list A) (i : nat) (x : A) :
    xs !! i = Some x ->
    base |-> arrayR ty R xs |--
    base .[ ty ! Z.of_nat i ] |-> R x
    ** (base .[ ty ! Z.of_nat i ] |-> R x -*
        base |-> arrayR ty R xs).
  Proof using MODd.
    go.
    match goal with
    | Hlookup : xs !! i = Some x |- _ =>
        rewrite
          (@arrayR_cell
             thread_info _Σ Sigma CU A R ty xs i x
             (Z.of_nat i) eq_refl Hlookup)
    end.
    go.
  Qed.

  Definition arrayR_read_cell_with_wand_F
      {A : Type} ty R base xs i x Hlookup :=
    [FWD] (@arrayR_read_cell_with_wand
             A ty R base xs i x Hlookup).

  Lemma arrayR_update_cell_with_wand {A : Type}
      (ty : type) (R : A -> Rep)
      (base : ptr) (xs : list A) (i : nat) (old new : A) :
    xs !! i = Some old ->
    base |-> arrayR ty R xs |--
    base .[ ty ! Z.of_nat i ] |-> R old
    ** (base .[ ty ! Z.of_nat i ] |-> R new -*
        base |-> arrayR ty R (<[i := new]> xs)).
  Proof.
    go.
    match goal with
    | Hlookup : xs !! i = Some old |- _ =>
        pose proof (lookup_lt_Some _ _ _ Hlookup) as Hlt;
        rewrite
          (@arrayR_cell
             thread_info _Σ Sigma CU A R ty xs i old
             (Z.of_nat i) eq_refl Hlookup);
        rewrite
          (@arrayR_cell
             thread_info _Σ Sigma CU A R ty
             (<[i := new]> xs) i new (Z.of_nat i) eq_refl)
    end.
    2: {
      apply list_lookup_insert_eq.
      exact Hlt.
    }
    assert
      (Htake :
        take i (<[i := new]> xs) = take i xs).
    {
      apply take_insert_ge.
      lia.
    }
    assert
      (Hdrop :
        drop (S i) (<[i := new]> xs) = drop (S i) xs).
    {
      apply drop_insert_lt.
      lia.
    }
    rewrite Htake Hdrop.
    go.
  Qed.

  Definition arrayR_update_cell_with_wand_F
      {A : Type} ty R base xs i old new Hlookup :=
    [FWD] (@arrayR_update_cell_with_wand
             A ty R base xs i old new Hlookup).

  Lemma leaf_loop_state_lookup_bound pair_bitmap indices bits i idx :
    leaf_loop_state pair_bitmap indices bits ->
    indices !! i = Some idx ->
    (idx < page_pair_count)%nat.
  Proof.
    intros [_ [Hindices _]] Hlookup.
    rewrite Forall_forall in Hindices.
    apply Hindices.
    eapply list_elem_of_lookup_2.
    exact Hlookup.
  Qed.

  Lemma lookup_nat_of_lookupZ_of_N_local {A : Type}
      (xs : list A) (j : N) (x : A) :
    xs !! Z.of_N j = Some x ->
    xs !! N.to_nat j = Some x.
  Proof.
    intro Hlookup.
    destruct (proj1 (lookupZ_Some_to_nat xs (Z.of_N j) x) Hlookup)
      as [_ Hlookup_nat].
    replace (Z.to_nat (Z.of_N j)) with (N.to_nat j) in Hlookup_nat by lia.
    exact Hlookup_nat.
  Qed.

  Lemma leaf_hash_outputs_lookup page indices i idx :
    indices !! i = Some idx ->
    List.app
      (blake3specs.blake3_hash_many_outputs
         blake3model.leaf_mode
         (map (page_pair_leaf_model page) indices))
      (drop (length indices) (replicateN 64 0%N)) !! i =
    Some (leaf_pair_hash page idx).
  Proof.
    intro Hlookup.
    apply lookup_app_l_Some.
    unfold blake3specs.blake3_hash_many_outputs, leaf_pair_hash.
    rewrite !list_lookup_fmap.
    rewrite Hlookup.
    reflexivity.
  Qed.

  Lemma apply_leaf_hashes_to_scratch_app page scratch lhs rhs :
    apply_leaf_hashes_to_scratch page scratch (lhs ++ rhs) =
    apply_leaf_hashes_to_scratch
      page (apply_leaf_hashes_to_scratch page scratch lhs) rhs.
  Proof.
    revert scratch.
    induction lhs as [| idx rest IH]; intro scratch.
    {
      reflexivity.
    }
    {
      simpl.
      exact (IH (<[idx := leaf_pair_hash page idx]> scratch)).
    }
  Qed.

  Lemma apply_leaf_hashes_to_scratch_take_succ
      page scratch indices i idx :
    indices !! i = Some idx ->
    apply_leaf_hashes_to_scratch page scratch (take (S i) indices) =
    <[idx := leaf_pair_hash page idx]>
      (apply_leaf_hashes_to_scratch page scratch (take i indices)).
  Proof.
    intro Hlookup.
    rewrite (take_S_r indices i idx Hlookup).
    rewrite apply_leaf_hashes_to_scratch_app.
    reflexivity.
  Qed.

  Lemma leaf_hash_outputs_replicate64_length page indices :
    (length indices <= page_pair_count)%nat ->
    length
      (blake3specs.blake3_hash_many_outputs
         blake3model.leaf_mode
         (map (page_pair_leaf_model page) indices) ++
       drop (length indices) (replicateN 64 0%N)) =
    N.to_nat 64.
  Proof.
    intro Hindices.
    unfold blake3specs.blake3_hash_many_outputs.
    rewrite List.length_app.
    repeat rewrite length_map.
    rewrite length_drop.
    change (length (replicateN 64 0%N)) with 64%nat.
    change (N.to_nat 64) with 64%nat.
    unfold page_pair_count in Hindices.
    lia.
  Qed.

  Lemma Forall_range_zero_replicateN len :
    List.Forall (fun x => (x < 2 ^ 256)%N)
      (replicateN len 0%N).
  Proof.
    induction len as [| len IH] using N.peano_ind.
    {
      cbn.
      constructor.
    }
    {
      replace (N.succ len) with (len + 1)%N by lia.
      rewrite replicateN_succ.
      constructor.
      {
        lia.
      }
      exact IH.
    }
  Qed.

  Lemma Forall_skipn_local {A : Type} (P : A -> Prop) n xs :
    List.Forall P xs -> List.Forall P (skipn n xs).
  Proof.
    revert xs.
    induction n as [| n IH]; intros xs Hxs.
    {
      exact Hxs.
    }
    {
      destruct xs as [| x rest].
      {
        constructor.
      }
      {
        inversion Hxs; subst.
        apply IH.
        assumption.
      }
    }
  Qed.

  Lemma leaf_hash_outputs_replicate64_range page indices :
    List.Forall (fun x => (x < 2 ^ 256)%N)
      (blake3specs.blake3_hash_many_outputs
         blake3model.leaf_mode
         (map (page_pair_leaf_model page) indices) ++
       drop (length indices) (replicateN 64 0%N)).
  Proof.
    apply Forall_app.
    split.
    {
      apply blake3specs.blake3_hash_many_outputs_range.
    }
    {
      apply Forall_drop.
      apply Forall_range_zero_replicateN.
    }
  Qed.

  Lemma wp_destroy_leaf_hash_outputs64
      (tu : translation_unit) (flat_outp : ptr)
      page indices (Q : epred) :
    (length indices <= page_pair_count)%nat ->
    □ exec_specs.bytes32_dtor_spec
    ** flat_outp |-> blake3specs.Blake3OutputWordsR 1
      (blake3specs.blake3_hash_many_outputs
         blake3model.leaf_mode
         (map (page_pair_leaf_model page) indices) ++
       drop (length indices) (replicateN 64 0%N))
    ** Q
    |-- wp_destroy_array tu QM bytes32_ty 64%N flat_outp Q.
  Proof.
    intro Hindices.
    unfold blake3specs.Blake3OutputWordsR.
    exact
      (evmc_specs.wp_destroy_bytes32_array
         tu flat_outp 64%N
         (blake3specs.blake3_hash_many_outputs
            blake3model.leaf_mode
            (map (page_pair_leaf_model page) indices) ++
          drop (length indices) (replicateN 64 0%N))
         Q
         (leaf_hash_outputs_replicate64_length
            page indices Hindices)).
  Qed.

  Definition wp_destroy_leaf_hash_outputs64_B
      tu flat_outp page indices Q Hindices :=
    [BWD] (wp_destroy_leaf_hash_outputs64
             tu flat_outp page indices Q Hindices).

  Fixpoint bytes32_zero_cells_from
      (base : ptr) (start count : nat) : mpred :=
    match count with
    | O => □ valid_ptr (base .[ bytes32_ty ! Z.of_nat start ])
    | S count' =>
        base .[ bytes32_ty ! Z.of_nat start ]
          |-> exec_specs.bytes32R 1 0
        ** bytes32_zero_cells_from base (S start) count'
    end.

  Lemma bytes32_zero_cells_from_pack base start count :
    bytes32_zero_cells_from base start count |--
    base .[ bytes32_ty ! Z.of_nat start ]
      |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
            (replicate count 0%N).
  Proof using CU MODd Sigma.
    revert base start.
    induction count as [| count IH]; intros base start.
    {
      cbn [bytes32_zero_cells_from replicate].
      go using _at_arrayR_nil_B.
    }
    cbn [bytes32_zero_cells_from replicate].
    pose (IH_F := [FWD] (IH base (S start))).
    go using _at_arrayR_cons_B, IH_F.
    repeat rewrite o_sub_sub.
    replace (Z.of_nat start + 1)%Z
      with (Z.of_nat (S start)) by lia.
    go using IH_F.
  Qed.

  Lemma leaf_output_words64_zero_pack base :
    bytes32_zero_cells_from base 0 64 |--
    base |-> blake3specs.Blake3OutputWordsR 1 (replicateN 64 0%N).
  Proof using CU MODd Sigma.
    unfold blake3specs.Blake3OutputWordsR.
    change (replicateN 64 0%N) with (replicate 64 0%N).
    rewrite -{2}(offset_ptr_sub_0 base bytes32_ty).
    2: {
      apply has_size.
      exact _.
    }
    exact (bytes32_zero_cells_from_pack base 0 64).
  Qed.

  Definition leaf_output_words64_zero_pack_F base :=
    [FWD] (leaf_output_words64_zero_pack base).

  Lemma leaf_output_words64_zero_pack_cells base :
    type_ptr bytes32_ty (base .[ bytes32_ty ! 63 ])
    ** base .[ bytes32_ty ! 0 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 1 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 2 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 3 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 4 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 5 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 6 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 7 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 8 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 9 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 10 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 11 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 12 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 13 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 14 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 15 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 16 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 17 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 18 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 19 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 20 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 21 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 22 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 23 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 24 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 25 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 26 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 27 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 28 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 29 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 30 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 31 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 32 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 33 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 34 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 35 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 36 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 37 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 38 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 39 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 40 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 41 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 42 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 43 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 44 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 45 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 46 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 47 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 48 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 49 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 50 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 51 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 52 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 53 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 54 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 55 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 56 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 57 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 58 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 59 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 60 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 61 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 62 ]
      |-> exec_specs.bytes32R 1 0
    ** base .[ bytes32_ty ! 63 ]
      |-> exec_specs.bytes32R 1 0
    |--
    base |-> blake3specs.Blake3OutputWordsR 1 (replicateN 64 0%N).
  Proof using CU MODd Sigma.
    etrans.
    2: {
      exact (leaf_output_words64_zero_pack base).
    }
    cbn [bytes32_zero_cells_from].
    go using type_ptr_valid_plus_one_C.
  Qed.

  Definition leaf_output_words64_zero_pack_cells_F base :=
    [FWD] (leaf_output_words64_zero_pack_cells base).

		  Lemma repeat_app_local {A : Type} (n m : nat) (x : A) :
		    replicate (n + m) x = (replicate n x ++ replicate m x)%list.
		  Proof.
    induction n as [| n IH].
    {
      reflexivity.
    }
    {
      cbn.
      rewrite IH.
	      reflexivity.
	    }
	  Qed.

	  Lemma bytes32_be_values_from_length len z :
	    length (exec_specs.bytes32_be_values_from len z) = len.
	  Proof.
	    induction len as [| len IH].
	    {
	      reflexivity.
	    }
	    {
	      simpl.
	      congruence.
	    }
	  Qed.

	  Lemma bytes32_be_values_length z :
	    length (exec_specs.bytes32_be_values z) = 32%nat.
	  Proof.
	    unfold exec_specs.bytes32_be_values.
	    apply bytes32_be_values_from_length.
	  Qed.

	  Lemma bytes64_byte_values_length block :
	    length (blake3specs.bytes64_byte_values block) = 64%nat.
	  Proof.
	    unfold blake3specs.bytes64_byte_values,
	      blake3_impl_h_specs.bytes64_byte_values,
	      blake3specs.bytes32_byte_values,
	      blake3_impl_h_specs.bytes32_byte_values.
	    rewrite length_app.
	    rewrite !bytes32_be_values_length.
	    reflexivity.
	  Qed.

	  Lemma uchar_arrayR_values_forget (base : ptr) values :
	    base |-> arrayR Tuchar (primR Tuchar 1$m) values |--
	    base |-> arrayLR Tuchar 0 (Z.of_nat (length values))
	      (fun _ : unit => anyR Tuchar 1$m)
	      (replicateN (N.of_nat (length values)) ()).
	  Proof using CU MODd Sigma.
	    revert base.
	    induction values as [| value rest IH]; intro base.
	    {
	      go using _at_arrayR_nil_F.
	    }
	    {
	      cbn [length].
	      rewrite Nat2Z.inj_succ.
	      rewrite Nat2N.inj_succ.
	      replace (N.succ (N.of_nat (length rest)))
	        with (N.of_nat (length rest) + 1)%N by lia.
	      rewrite replicateN_succ.
	      pose (IH_F := [FWD] (IH (base .[ Tuchar ! 1 ]))).
	      rewrite array_sliceR_cons.
	      go using _at_arrayR_cons_F, IH_F.
	      rewrite (offset_ptr_sub_0 base Tuchar); [ | vm_compute; eauto ].
	      go using primR_anyR_F.
	    }
	  Qed.

	  Definition uchar_arrayR_values_forget_F base values :=
	    [FWD] (uchar_arrayR_values_forget base values).

	  Lemma leaf_pair_block_rowR_forget (base : ptr) row :
	    base |-> leaf_pair_block_rowR row |--
	    base |-> arrayLR Tuchar 0 64
	      (fun _ : unit => anyR Tuchar 1$m)
	      (replicateN 64 ()).
	  Proof using CU MODd Sigma.
	    destruct row as [| lhs | block].
	    {
	      go.
	    }
	    {
	      cbn [leaf_pair_block_rowR].
	      replace (replicateN 64 ()) with
	        ((replicateN 32 ()) ++ (replicateN 32 ()))%list.
	      2: {
	        unfold replicateN.
	        change (N.to_nat 64) with 64%nat.
	        change (N.to_nat 32) with 32%nat.
	        rewrite <- repeat_app_local.
	        reflexivity.
	      }
	      rewrite
	        (@array_sliceR_app'
	           _ _ _ _ unit Tuchar base
	           0 32 64
	           (fun _ : unit => anyR Tuchar 1$m)
	           (replicateN 32 ())
	           (replicateN 32 ()));
	        try solve [rewrite lengthN_replicateN; lia | lia].
	      go using primR_anyR_F, uninitR_anyR_F.
	    }
	    {
	      unfold leaf_pair_block_rowR, blake3specs.Blake3BlockR,
	        blake3_impl_h_specs.Blake3BlockR,
	        blake3specs.BlockR,
	        blake3_impl_h_specs.BlockR.
	      change
	        (base |-> arrayR Tuchar (primR Tuchar 1$m)
	                  (blake3specs.bytes64_byte_values block)
	         |--
	         base |-> arrayLR Tuchar 0 64
	                   (fun _ : unit => anyR Tuchar 1$m)
	                   (replicateN 64 ())).
	      replace 64%Z with
	        (Z.of_nat (length (blake3specs.bytes64_byte_values block))).
	      2: {
	        rewrite bytes64_byte_values_length.
	        reflexivity.
	      }
	      replace (replicateN 64 ()) with
	        (replicateN
	           (N.of_nat (length (blake3specs.bytes64_byte_values block)))
	           ()).
	      2: {
	        rewrite bytes64_byte_values_length.
	        reflexivity.
	      }
	      apply uchar_arrayR_values_forget.
	    }
	  Qed.

	  Definition leaf_pair_block_rowR_forget_F base row :=
	    [FWD] (leaf_pair_block_rowR_forget base row).

	  Lemma replicate_length_unit_map {A : Type} (xs : list A) :
	    replicate (length xs) () =
	    map (fun _ : A => ()) xs.
	  Proof.
	    induction xs as [| x rest IH].
	    {
	      reflexivity.
	    }
	    {
	      simpl.
	      congruence.
	    }
	  Qed.

	  Lemma leaf_pair_block_rows_prefix_forget
	      (base : ptr) rows :
	    base |-> arrayLR leaf_pair_block_ty 0 (Z.of_nat (length rows))
	      leaf_pair_block_rowR rows |--
	    base |-> arrayLR leaf_pair_block_ty 0 (Z.of_nat (length rows))
	      (fun _ : unit =>
	         arrayLR Tuchar 0 64
	           (fun _ : unit => anyR Tuchar 1$m)
	           (replicateN 64 ()))
	      (replicate (length rows) ()).
	  Proof using CU MODd Sigma.
	    rewrite replicate_length_unit_map.
	    rewrite
	      (array_sliceR_fmap
	         (ty := leaf_pair_block_ty)
	         0 (Z.of_nat (length rows)) rows
	         (fun _ : unit =>
	            arrayLR Tuchar 0 64
	              (fun _ : unit => anyR Tuchar 1$m)
	              (replicateN 64 ()))
	         (fun _ : leaf_pair_block_row => ()))
	      /=.
	    apply _at_mono.
	    f_equiv.
	    intro row.
	    apply Rep_entails_at => rowp.
	    apply leaf_pair_block_rowR_forget.
	  Qed.

	  Definition leaf_pair_block_rows_prefix_forget_F base rows :=
	    [FWD] (leaf_pair_block_rows_prefix_forget base rows).

	  Definition leaf_pair_block_rows_prefix_forget_C base rows :=
	    [CANCEL] (leaf_pair_block_rows_prefix_forget base rows).

	  Lemma leaf_pair_block_rows_forget_64
	      (base : ptr) page indices :
	    (length indices <= 64)%nat ->
	    base |-> arrayLR leaf_pair_block_ty 0 64
	      leaf_pair_block_rowR (leaf_pair_block_rows page indices) |--
	    base |-> arrayLR leaf_pair_block_ty 0 64
	      (fun _ : unit =>
	         arrayLR Tuchar 0 64
	           (fun _ : unit => anyR Tuchar 1$m)
	           (replicateN 64 ()))
	      (replicateN 64 ()).
	  Proof using CU MODd Sigma.
	    intro Hlen.
	    unfold leaf_pair_block_rows.
	    replace
	      (base |-> arrayLR leaf_pair_block_ty 0 64
	        (fun _ : unit =>
	           arrayLR Tuchar 0 64
	             (fun _ : unit => anyR Tuchar 1$m)
	             (replicateN 64 ()))
	        (replicateN 64 ()))
	      with
	      (base |-> arrayLR leaf_pair_block_ty 0 64
	        (fun _ : unit =>
	           arrayLR Tuchar 0 64
	             (fun _ : unit => anyR Tuchar 1$m)
	             (replicateN 64 ()))
	        ((replicateN (N.of_nat (length indices)) ()) ++
	         (replicateZ (64 - Z.of_nat (length indices)) ()))%list).
	    2: {
	      f_equal.
	      unfold replicateZ, replicateN.
	      rewrite <- repeat_app_local.
	      f_equal.
	      rewrite Nat2N.id.
	      rewrite Z_N_nat.
	      replace (Z.to_nat (64 - Z.of_nat (length indices)))
	        with (64 - length indices)%nat by lia.
	      change (N.to_nat 64) with 64%nat.
	      f_equal.
	      lia.
	    }
	    rewrite
	      (@array_sliceR_app'
	         _ _ _ _ unit leaf_pair_block_ty base
	         0 (Z.of_nat (length indices)) 64
	         (fun _ : unit =>
	            arrayLR Tuchar 0 64
	              (fun _ : unit => anyR Tuchar 1$m)
	              (replicateN 64 ()))
	         (replicateN (N.of_nat (length indices)) ())
	         (replicateZ (64 - Z.of_nat (length indices)) ()));
	      try solve [rewrite lengthN_replicateN; lia | lia].
	    rewrite
	      (@array_sliceR_app'
	         _ _ _ _ leaf_pair_block_row leaf_pair_block_ty base
	         0 (Z.of_nat (length indices)) 64
	         leaf_pair_block_rowR
	         (map
	            (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
	            indices)
	         (replicateZ
	            (64 - Z.of_nat (length indices)) LeafPairBlockUninit));
	      try solve [rewrite lengthN_map; rewrite lengthN_length; lia | lia].
	    unfold replicateZ.
	    replace
	      (replicateN (Z.to_N (64 - Z.of_nat (length indices)))
	         LeafPairBlockUninit)
	      with
	      (map (fun _ : unit => LeafPairBlockUninit)
	         (replicateN (Z.to_N (64 - Z.of_nat (length indices))) ())).
	    2: {
	      unfold replicateN.
	      induction
	        (N.to_nat (Z.to_N (64 - Z.of_nat (length indices)))).
	      {
	        reflexivity.
	      }
	      {
	        simpl.
	        congruence.
	      }
	    }
	    rewrite
	      (array_sliceR_fmap
	         (ty := leaf_pair_block_ty)
	         (Z.of_nat (length indices)) 64
	         (replicateN (Z.to_N (64 - Z.of_nat (length indices))) ())
	         leaf_pair_block_rowR
	         (fun _ : unit => LeafPairBlockUninit)).
	    cbn [leaf_pair_block_rowR].
	    replace (replicateN (N.of_nat (length indices)) ()) with
	      (replicate (length indices) ()).
	    2: {
	      unfold replicateN.
	      rewrite Nat2N.id.
	      reflexivity.
	    }
	    replace (Z.of_nat (length indices)) with
	      (Z.of_nat
	         (length
	            (map
	               (fun idx : nat =>
	                  LeafPairBlockFull (page_pair_leaf_model page idx))
	               indices))).
	    2: {
	      rewrite length_map.
	      reflexivity.
	    }
	    replace (replicate (length indices) ()) with
	      (replicate
	         (length
	            (map
	               (fun idx : nat =>
	                  LeafPairBlockFull (page_pair_leaf_model page idx))
	               indices)) ()).
	    2: {
	      rewrite length_map.
	      reflexivity.
	    }
	    go using
	      (leaf_pair_block_rows_prefix_forget_C base
	         (map
	            (fun idx : nat =>
	               LeafPairBlockFull (page_pair_leaf_model page idx))
	            indices)).
	  Qed.

	  Definition leaf_pair_block_rows_forget_64_F
	      base page indices Hlen :=
	    [FWD] (leaf_pair_block_rows_forget_64
	             base page indices Hlen).

	  Lemma leaf_pair_block_row_cleanup_anyR (base : ptr) :
	    base |-> arrayLR Tuchar 0 64
	      (fun _ : unit => anyR Tuchar 1$m)
	      (replicateN 64 ())
	    |--
	    base |-> anyR leaf_pair_block_ty 1$m.
	  Proof using MODd.
	    unfold leaf_pair_block_ty.
	    rewrite array.arrayR_anyR_eqv.
	    change (replicateZ 64 ()) with (replicateN 64 ()).
	    go.
	  Qed.

	  Definition leaf_pair_block_row_cleanup_anyR_F base :=
	    [FWD] (leaf_pair_block_row_cleanup_anyR base).

	  Lemma wp_destroy_leaf_pair_block_row_anyR_cell_local :
	    forall (tu : translation_unit) (base : ptr) (Q : epred),
	    type_ptr leaf_pair_block_ty base
	    ** base |-> anyR leaf_pair_block_ty 1$m
	    ** Q
	    |-- wp_destroy_val tu QM leaf_pair_block_ty base Q.
	  Proof.
	    intros tu base Q.
	    unfold leaf_pair_block_ty.
	    rewrite -destroy.wp_destroy_val_array.
	    cbn.
	    go.
	  Qed.

	  Lemma wp_destroy_leaf_pair_block_row_bytes_cell_local :
	    forall (tu : translation_unit) (base : ptr) (Q : epred),
	    type_ptr leaf_pair_block_ty base
	    ** base |-> arrayLR Tuchar 0 64
	         (fun _ : unit => anyR Tuchar 1$m)
	         (replicateN 64 ())
	    ** Q
	    |-- wp_destroy_val tu QM leaf_pair_block_ty base Q.
	  Proof using CU MODd Sigma.
	    intros tu base Q.
	    go using
	      (leaf_pair_block_row_cleanup_anyR_F base),
	      wp_destroy_leaf_pair_block_row_anyR_cell_local.
	  Qed.

	  Lemma leaf_inputs_prefix_forget
	      (base : ptr) (indices : list nat) (input_ptrs : list ptr) :
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty
           1$m (Vptr inputp))
      input_ptrs |--
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN (N.of_nat (length indices)) ()).
  Proof using MODd.
    rewrite !array_sliceR.unlock.
    go.
    assert (Hn : N.of_nat (length indices) = lengthN input_ptrs) by lia.
    replace (replicateN (N.of_nat (length indices)) ())
      with (replicateN (lengthN input_ptrs) ()) by
      (rewrite Hn; reflexivity).
    replace (lengthZ (replicateN (lengthN input_ptrs) ()))
      with (lengthZ input_ptrs).
    2: {
      rewrite lengthN_replicateN.
      lia.
    }
    assert (Hforget_at :
      base .[ blake3specs.blake3_input_ptr_store_ty ! 0 ]
        |-> arrayR blake3specs.blake3_input_ptr_store_ty
              (fun inputp : ptr =>
                 primR blake3specs.blake3_input_ptr_value_ty
                   1$m (Vptr inputp))
              input_ptrs
      |--
      base .[ blake3specs.blake3_input_ptr_store_ty ! 0 ]
        |-> arrayR blake3specs.blake3_input_ptr_store_ty
              (fun _ : unit =>
                 anyR blake3specs.blake3_input_ptr_store_ty 1$m)
              (replicateN (lengthN input_ptrs) ())).
    {
      apply _at_mono.
      exact (input_ptr_arrayR_forget_store input_ptrs).
    }
    pose (Hforget_F := [FWD] Hforget_at).
    go using Hforget_F.
  Qed.

  Definition leaf_inputs_prefix_forget_F
      base (indices : list nat) (input_ptrs : list ptr) :=
    [FWD] (leaf_inputs_prefix_forget base indices input_ptrs).

  Lemma leaf_inputs_split_anyR_array
      (base : ptr) (indices : list nat) (input_ptrs : list ptr) :
    (length indices <= page_pair_count)%nat ->
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty
           1$m (Vptr inputp))
      input_ptrs
    ** base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      (Z.of_nat (length indices)) 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateZ (64 - Z.of_nat (length indices)) ())
    |--
    base |-> anyR
      (Tarray blake3specs.blake3_input_ptr_store_ty 64%N) 1$m.
  Proof using MODd.
    intro Hindices.
    rewrite array.arrayR_anyR_eqv.
    replace (replicateZ 64%N ())
      with
        ((replicateN (N.of_nat (length indices)) ()) ++
         (replicateZ (64 - Z.of_nat (length indices)) ()))%list.
    2: {
      unfold replicateZ, replicateN.
      rewrite <- repeat_app_local.
      f_equal.
      unfold page_pair_count in Hindices.
      lia.
    }
    rewrite
      (@array_sliceR_app'
         _ _ _ _ unit blake3specs.blake3_input_ptr_store_ty base
         0 (Z.of_nat (length indices)) 64
         (fun _ : unit =>
            anyR blake3specs.blake3_input_ptr_store_ty 1$m)
         (replicateN (N.of_nat (length indices)) ())
         (replicateZ (64 - Z.of_nat (length indices)) ()));
      try solve [rewrite lengthN_replicateN; lia
                | unfold page_pair_count in Hindices; lia].
    go using leaf_inputs_prefix_forget_F.
  Qed.

  Definition leaf_inputs_split_anyR_array_F
      base (indices : list nat) (input_ptrs : list ptr) Hindices :=
    [FWD] (leaf_inputs_split_anyR_array
             base indices input_ptrs Hindices).

  Lemma input_ptr_typed_slice_cell_type
      (base : ptr) (n : nat) :
    (n < 64)%nat ->
    base |-> typed_sliceR blake3specs.blake3_input_ptr_store_ty 0 64
    |--
    type_ptr blake3specs.blake3_input_ptr_store_ty
      (base .[ blake3specs.blake3_input_ptr_store_ty ! Z.of_nat n ]).
  Proof using.
    intro Hn.
    go.
  Qed.

  Definition input_ptr_typed_slice_cell_type_F base n Hn :=
    [FWD] (input_ptr_typed_slice_cell_type base n Hn).

  Definition input_ptr_typed_slice_cell_type_C base n Hn :=
    [CANCEL] (input_ptr_typed_slice_cell_type base n Hn).

  Lemma wp_destroy_leaf_inputs_array_split_cleanup_local :
    forall (tu : translation_unit) (base : ptr)
      (indices : list nat) (input_ptrs : list ptr) (Q : epred),
    (length indices <= page_pair_count)%nat ->
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty
           1$m (Vptr inputp))
      input_ptrs
    ** base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      (Z.of_nat (length indices)) 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateZ (64 - Z.of_nat (length indices)) ())
    ** Q
    |-- wp_destroy_val tu QM
          (Tarray (Tptr (Qconst Tuchar)) 64%N) base Q.
  Proof using MODd.
    intros tu base indices input_ptrs Q Hindices.
    go using
      destroy.wp_destroy_val_array_B,
      (leaf_inputs_split_anyR_array_F
         base indices input_ptrs Hindices).
  Qed.

  Definition wp_destroy_leaf_inputs_array_split_cleanup_local_B
      tu base indices input_ptrs Q Hindices :=
    [BWD] (wp_destroy_leaf_inputs_array_split_cleanup_local
             tu base indices input_ptrs Q Hindices).

  Lemma anyR_arrayLR_destroy_run_local
      (tu : translation_unit) (base : ptr) (n : nat) (Q : epred) :
    base |-> arrayLR Tuchar 0 (Z.of_nat n)
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN (N.of_nat n) ())
    ** Q
    |-- destroy.run_array tu QM Tuchar base n Q.
  Proof using MODd.
    induction n as [| n IH].
    {
      go.
    }
    {
      rewrite Nat2Z.inj_succ.
      rewrite Nat2N.inj_succ.
      replace (N.succ (N.of_nat n))
        with (N.of_nat n + 1)%N by lia.
      replace (replicateN (N.of_nat n + 1) ())
        with (replicateN (N.of_nat n) () ++ [()])%list.
      2: {
        unfold replicateN.
        change (N.to_nat 1) with 1%nat.
        rewrite N2Nat.inj_add.
        rewrite repeat_app_local.
        reflexivity.
      }
      cbn [destroy.run_array].
      pose (IH_F := [FWD] IH).
      rewrite array_sliceR_snoc.
      replace (Z.succ (Z.of_nat n) - 1)%Z
        with (Z.of_nat n) by lia.
      go using destroy.wp_destroy_val_char_B, IH_F.
    }
  Qed.

  Definition anyR_arrayLR_destroy_run_local_B tu base n Q :=
    [BWD] (anyR_arrayLR_destroy_run_local tu base n Q).

  Lemma leaf_index_prefix_forget (base : ptr) indices :
    base |-> arrayLR Tuchar 0 (Z.of_nat (length indices))
      (fun index : nat => ucharR 1$m (Z.of_nat index)) indices |--
    base |-> arrayLR Tuchar 0 (Z.of_nat (length indices))
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN (N.of_nat (length indices)) ()).
  Proof using MODd.
    revert base.
    induction indices as [| index rest IH]; intro base.
    {
      go.
    }
    cbn [length replicateN].
    rewrite Nat2Z.inj_succ.
    rewrite Nat2N.inj_succ.
    replace (N.succ (N.of_nat (length rest)))
      with (N.of_nat (length rest) + 1)%N by lia.
    rewrite replicateN_succ.
    pose (IH_F := [FWD] (IH (base .[ Tuchar ! 1 ]))).
    rewrite !array_sliceR_cons.
    go using
      _at_sub_array_sliceR_F,
      _at_sub_array_sliceR_B,
      IH_F.
    rewrite (offset_ptr_sub_0 base Tuchar); [ | vm_compute; eauto ].
    go using primR_anyR_F.
    rewrite lengthN_replicateN.
    go.
  Qed.

  Definition leaf_index_prefix_forget_F base indices :=
    [FWD] (leaf_index_prefix_forget base indices).

  Lemma leaf_index_arrayR_forget (base : ptr) (indices : list nat) :
    (length indices <= page_pair_count)%nat ->
    base |-> leaf_index_arrayR indices |--
    base |-> arrayLR Tuchar 0 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 64 ()).
  Proof using MODd.
    intro Hindices.
    unfold leaf_index_arrayR.
    rewrite _at_as_Rep.
    replace (replicateN 64 ())
      with
        ((replicateN (N.of_nat (length indices)) ()) ++
         (replicateZ (64 - Z.of_nat (length indices)) ()))%list.
    2: {
      unfold replicateZ, replicateN.
      rewrite <- repeat_app_local.
      f_equal.
      unfold page_pair_count in Hindices.
      lia.
    }
    rewrite
      (@array_sliceR_app'
         _ _ _ _ unit Tuchar base
         0 (Z.of_nat (length indices)) 64
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateN (N.of_nat (length indices)) ())
         (replicateZ (64 - Z.of_nat (length indices)) ()));
      try solve [rewrite lengthN_replicateN; lia
                | unfold page_pair_count in Hindices; lia].
    go using (leaf_index_prefix_forget_F base indices).
  Qed.

  Definition leaf_index_arrayR_forget_F
      base (indices : list nat) Hindices :=
    [FWD] (leaf_index_arrayR_forget base indices Hindices).

  Lemma destroy_run_leaf_index_array_cleanup_local :
    forall (tu : translation_unit) (base : ptr)
      (indices : list nat) (Q : epred),
    (length indices <= page_pair_count)%nat ->
    base |-> leaf_index_arrayR indices
    ** Q
    |-- destroy.run_array tu QM Tuchar base (N.to_nat 64%N) Q.
  Proof using MODd.
    intros tu base indices Q Hindices.
    change (N.to_nat 64%N) with 64%nat.
    go using
      (leaf_index_arrayR_forget_F base indices Hindices),
      (anyR_arrayLR_destroy_run_local_B tu base 64 Q).
  Qed.

  Definition destroy_run_leaf_index_array_cleanup_local_B
      tu base indices Q Hindices :=
    [BWD] (destroy_run_leaf_index_array_cleanup_local
             tu base indices Q Hindices).

  Lemma Z_to_N_land_N (lhs rhs : N) :
    Z.to_N (Z.land lhs rhs) = N.land lhs rhs.
  Proof.
    rewrite <- N2Z.inj_land.
    rewrite N2Z.id.
    reflexivity.
  Qed.

  Lemma leaf_clear_lowbit_machine (bits : N) :
    Z.to_N (Z.land bits (bits - 1)) = leaf_clear_lowbit bits.
  Proof.
    unfold leaf_clear_lowbit.
    destruct (N.eq_dec bits 0%N) as [-> | Hbits].
    {
      reflexivity.
    }
    replace (Z.of_N bits - 1)%Z with (Z.of_N (bits - 1)) by lia.
    apply Z_to_N_land_N.
  Qed.

  Lemma sliceZ_replicateZ_drop_one {A : Type}
      (base limit : Z) (x : A) :
    base < limit ->
    sliceZ base (base + 1) limit
      (replicateZ (limit - base) x) =
    replicateZ (limit - (base + 1)) x.
  Proof.
    intro Hbase.
    unfold sliceZ.
    replace (base + 1 - base)%Z with 1%Z by lia.
    change (Z.to_N 1) with 1%N.
    rewrite takeN_replicateN.
    rewrite N.min_l.
    2: {
      lia.
    }
    rewrite dropN_replicateN.
    f_equal.
    unfold replicateZ.
    f_equal.
    apply N2Z.inj.
    rewrite N2Z.inj_sub.
    2: { lia. }
    rewrite !Z2N.id; lia.
  Qed.

  Lemma observeStoragePageTypePtr (p : ptr) q page :
    Observe (type_ptr storage_page_ty p) (p |-> StoragePageR q page).
  Proof using MODd.
    apply observe_intro.
    { exact _. }
    unfold StoragePageR.
    rewrite !_at_sep.
    go.
  Qed.

  Definition observeStoragePageTypePtr_F p q page :=
    @observe_fwd _ _ _ (observeStoragePageTypePtr p q page).

  Lemma type_ptr_leaf_pair_block_valid
      (pairsp : ptr) (idx : nat) :
    (idx < page_pair_count)%nat ->
    type_ptr (Tarray leaf_pair_block_ty 64%N) pairsp |--
    valid_ptr (leaf_pair_bytesp pairsp idx).
  Proof using MODd.
    intro Hidx.
    unfold leaf_pair_bytesp.
    assert (Hrange : SolveArith (0 <= Z.of_nat idx < 64)%Z).
    { constructor; unfold page_pair_count in Hidx; lia. }
    rewrite (type_ptr_o_sub_impl
               (Z.of_nat idx) 64
               (Tarray leaf_pair_block_ty 64%N)
               leaf_pair_block_ty pairsp pairsp
               (TypePtrImplies_id
                  (Tarray leaf_pair_block_ty 64%N) pairsp)
               Hrange).
    go using type_ptr_valid.
  Qed.

  Definition type_ptr_leaf_pair_block_valid_F pairsp idx Hidx :=
    [FWD] (type_ptr_leaf_pair_block_valid pairsp idx Hidx).

  Lemma observeLeafPairBlockValid pairsp idx :
	    (idx < page_pair_count)%nat ->
	    Observe
	      (valid_ptr (leaf_pair_bytesp pairsp idx))
	      (type_ptr (Tarray leaf_pair_block_ty 64%N) pairsp).
	  Proof using MODd.
	    intro Hidx.
	    apply observe_intro.
	    { exact _. }
	    rewrite {1}(bi.persistent_sep_dup
                      (type_ptr (Tarray leaf_pair_block_ty 64%N) pairsp)).
	    apply bi.sep_mono_r.
	    exact (type_ptr_leaf_pair_block_valid pairsp idx Hidx).
	  Qed.

	  Definition observeLeafPairBlockValid_F pairsp idx Hidx :=
	    @observe_fwd _ _ _
	      (observeLeafPairBlockValid pairsp idx Hidx).

  Lemma StoragePageR_unpack (p : ptr) q page :
    p |-> StoragePageR q page
    |--
    p |-> StoragePageR q page.
  Proof using MODd.
    reflexivity.
  Qed.

  Definition StoragePageR_unpack_F p q page :=
    [FWD] (StoragePageR_unpack p q page).

  Lemma StoragePageR_pack (p : ptr) q page :
    p |-> StoragePageR q page |--
    p |-> StoragePageR q page.
  Proof using MODd.
    reflexivity.
  Qed.

  Definition StoragePageR_pack_B p q page :=
    [BWD] (StoragePageR_pack p q page).

  Lemma observeScratchRLength (p : ptr) q scratch :
    Observe
      ([| length scratch = page_pair_count |] : mpred)
      (p |-> ScratchR q scratch).
  Proof using MODd.
    apply observe_intro.
    { exact _. }
    unfold ScratchR.
    rewrite _at_sep.
    go.
  Qed.

  Definition observeScratchRLength_F p q scratch :=
    @observe_fwd _ _ _ (observeScratchRLength p q scratch).

  Lemma leaf_index_arrayR_empty_pack (base : ptr) :
    base |-> arrayLR Tuchar 0 64
      (fun _ : unit => uninitR Tuchar 1$m)
      (replicateN 64 ())
    |-- base |-> leaf_index_arrayR [].
  Proof.
    unfold leaf_index_arrayR.
    go using uninitR_anyR_F.
  Qed.

  Definition leaf_index_arrayR_empty_pack_F base :=
    [FWD] (leaf_index_arrayR_empty_pack base).

  Lemma leaf_inputs_arrayR_empty_pack (base pagep : ptr) :
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty 0 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN 64 ())
    |-- base |-> leaf_inputs_arrayR pagep [].
  Proof.
    unfold leaf_inputs_arrayR.
    go using uninitR_anyR_F.
  Qed.

	  Definition leaf_inputs_arrayR_empty_pack_F base pagep :=
	    [FWD] (leaf_inputs_arrayR_empty_pack base pagep).

	  Lemma leaf_inputs_arrayR_zero_pack (base pagep : ptr) :
	    base |-> arrayR blake3specs.blake3_input_ptr_store_ty
	      (primR blake3specs.blake3_input_ptr_store_ty 1$m)
	      (replicateN 64 (Vptr nullptr))
	    |-- base |-> leaf_inputs_arrayR pagep [].
	  Proof using MODd.
	    unfold leaf_inputs_arrayR.
	    rewrite _at_as_Rep.
	    rewrite array_sliceR.unlock arrayR_nil.
	    rewrite _at_sep _at_only_provable _at_offsetR.
	    rewrite offset_ptr_sub_0;
	      [|unfold blake3specs.blake3_input_ptr_store_ty,
	          blake3_impl_h_specs.blake3_input_ptr_store_ty,
	          blake3_impl_h_specs.blake3_input_ptr_store_ty_for;
	        cbn; eexists; reflexivity].
	    cbn [length].
	    rewrite Z.sub_0_r.
	    replace (Z.to_N (64 - 0%nat)) with 64%N by reflexivity.
	    go using (input_ptr_null_arrayR_forget_store_at_F base 64%N).
	  Qed.

	  Definition leaf_inputs_arrayR_zero_pack_F base pagep :=
	    [FWD] (leaf_inputs_arrayR_zero_pack base pagep).

	  Lemma leaf_inputs_arrayR_blake3_unpack
      (base pagep : ptr) (indices : list nat) :
    base |-> leaf_inputs_arrayR pagep indices |--
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      (Z.of_nat (length indices)) 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN
         (Z.to_N (64 - Z.of_nat (length indices))) ())
    ** base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr inputp))
      (leaf_input_ptrs pagep indices).
  Proof.
    go.
    unfold leaf_inputs_arrayR.
    rewrite
      (array_sliceR_fmap
         (ty := blake3specs.blake3_input_ptr_store_ty)
         0 (Z.of_nat (length indices)) (seq 0 (length indices))
         (fun inputp : ptr =>
            primR blake3specs.blake3_input_ptr_value_ty 1$m
              (Vptr inputp))
         (leaf_pair_bytesp pagep)).
    go.
  Qed.

  Definition leaf_inputs_arrayR_blake3_unpack_F base pagep indices :=
    [FWD] (leaf_inputs_arrayR_blake3_unpack base pagep indices).

  Lemma leaf_inputs_arrayR_blake3_pack
      (base pagep : ptr) (indices : list nat) :
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      (Z.of_nat (length indices)) 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN
         (Z.to_N (64 - Z.of_nat (length indices))) ())
    ** base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr inputp))
      (leaf_input_ptrs pagep indices)
    |-- base |-> leaf_inputs_arrayR pagep indices.
  Proof.
    go.
    unfold leaf_inputs_arrayR.
    rewrite
      (array_sliceR_fmap
         (ty := blake3specs.blake3_input_ptr_store_ty)
         0 (Z.of_nat (length indices)) (seq 0 (length indices))
         (fun inputp : ptr =>
            primR blake3specs.blake3_input_ptr_value_ty 1$m
              (Vptr inputp))
         (leaf_pair_bytesp pagep)).
    go.
  Qed.

  Definition leaf_inputs_arrayR_blake3_pack_B base pagep indices :=
    [BWD] (leaf_inputs_arrayR_blake3_pack base pagep indices).

  Lemma leaf_inputs_arrayR_blake3_inputs_pack
      (base pagep : ptr) q page indices :
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr inputp))
      (leaf_input_ptrs pagep indices)
    ** blake3specs.Blake3InputBlocksDataR q
      (leaf_input_blocks pagep page indices)
    |--
    base |-> blake3specs.Blake3InputBlocksR
      true 1 q
      (leaf_input_blocks pagep page indices).
  Proof using CU MODd Sigma.
    unfold blake3specs.Blake3InputBlocksR,
      blake3_impl_h_specs.Blake3InputBlocksR.
    rewrite _at_as_Rep.
    rewrite leaf_input_blocks_length.
    rewrite <- (leaf_input_blocks_ptrs pagep page indices).
    rewrite
      (array_sliceR_fmap
         (ty := blake3specs.blake3_input_ptr_store_ty)
         0 (Z.of_nat (length indices))
         (leaf_input_blocks pagep page indices)
         (fun inputp : ptr =>
            primR blake3specs.blake3_input_ptr_value_ty 1$m
              (Vptr inputp))
         blake3specs.blake3_input_block_ptr).
    go.
  Qed.

  Definition leaf_inputs_arrayR_blake3_inputs_pack_F
      base pagep q page indices :=
    [FWD] (leaf_inputs_arrayR_blake3_inputs_pack
             base pagep q page indices).

  Lemma leaf_inputs_arrayR_blake3_inputs_unpack
      (base pagep : ptr) q page indices :
    base |-> blake3specs.Blake3InputBlocksR
      true 1 q
      (leaf_input_blocks pagep page indices)
    |--
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr inputp))
      (leaf_input_ptrs pagep indices)
    ** blake3specs.Blake3InputBlocksDataR q
      (leaf_input_blocks pagep page indices).
  Proof using CU MODd Sigma.
    unfold blake3specs.Blake3InputBlocksR,
      blake3_impl_h_specs.Blake3InputBlocksR.
    rewrite _at_as_Rep.
    rewrite leaf_input_blocks_length.
    rewrite <- (leaf_input_blocks_ptrs pagep page indices).
    rewrite
      (array_sliceR_fmap
         (ty := blake3specs.blake3_input_ptr_store_ty)
         0 (Z.of_nat (length indices))
         (leaf_input_blocks pagep page indices)
         (fun inputp : ptr =>
            primR blake3specs.blake3_input_ptr_value_ty 1$m
              (Vptr inputp))
         blake3specs.blake3_input_block_ptr).
    go.
  Qed.

  Definition leaf_inputs_arrayR_blake3_inputs_unpack_F
      base pagep q page indices :=
    [FWD] (leaf_inputs_arrayR_blake3_inputs_unpack
             base pagep q page indices).

  Lemma leaf_input_blocks_ptr_array_to_input_ptrs
      (base pagep : ptr) page indices :
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length (leaf_input_blocks pagep page indices)))
      (fun input : blake3specs.blake3_input_block =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr (blake3specs.blake3_input_block_ptr input)))
      (leaf_input_blocks pagep page indices)
    |--
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr inputp))
      (leaf_input_ptrs pagep indices).
  Proof using CU MODd Sigma.
    rewrite leaf_input_blocks_length.
    rewrite <- (leaf_input_blocks_ptrs pagep page indices).
    rewrite
      (array_sliceR_fmap
         (ty := blake3specs.blake3_input_ptr_store_ty)
         0 (Z.of_nat (length indices))
         (leaf_input_blocks pagep page indices)
         (fun inputp : ptr =>
            primR blake3specs.blake3_input_ptr_value_ty 1$m
              (Vptr inputp))
         blake3specs.blake3_input_block_ptr).
    go.
  Qed.

  Definition leaf_input_blocks_ptr_array_to_input_ptrs_F
      base pagep page indices :=
    [FWD] (leaf_input_blocks_ptr_array_to_input_ptrs
             base pagep page indices).

  Lemma leaf_inputs_prefix_arrayR_blake3_pack
      (base pagep : ptr) (indices : list nat) :
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr inputp))
      (leaf_input_ptrs pagep indices)
    |--
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun row : nat =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr (leaf_pair_bytesp pagep row)))
      (seq 0 (length indices)).
  Proof.
    unfold leaf_input_ptrs.
    rewrite <-
      (array_sliceR_fmap
         (ty := blake3specs.blake3_input_ptr_store_ty)
         0 (Z.of_nat (length indices)) (seq 0 (length indices))
         (fun inputp : ptr =>
            primR blake3specs.blake3_input_ptr_value_ty 1$m
              (Vptr inputp))
         (leaf_pair_bytesp pagep)).
    go.
  Qed.

  Definition leaf_inputs_prefix_arrayR_blake3_pack_F
      base pagep indices :=
    [FWD] (leaf_inputs_prefix_arrayR_blake3_pack base pagep indices).

  Lemma leaf_inputs_prefix_arrayR_blake3_pack_for_page
      (base pagep : ptr) page (indices : list nat) :
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length (map (page_pair_leaf_model page) indices)))
      (fun inputp : ptr =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr inputp))
      (leaf_input_ptrs pagep indices)
    |--
    base |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length indices))
      (fun row : nat =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr (leaf_pair_bytesp pagep row)))
      (seq 0 (length indices)).
  Proof.
    rewrite !List.length_map.
    go using leaf_inputs_prefix_arrayR_blake3_pack_F.
  Qed.

  Definition leaf_inputs_prefix_arrayR_blake3_pack_for_page_F
      base pagep page indices :=
    [FWD] (leaf_inputs_prefix_arrayR_blake3_pack_for_page
             base pagep page indices).

  Lemma leaf_hash_outputs_from_call_params page indices :
    blake3_hash_many_outputs_from_params
      (blake3_hash_many_call_params
         blake3model.mip8_leaf_iv_words 0 false 64 0 0)
      (map (page_pair_leaf_model page) indices) =
    blake3specs.blake3_hash_many_outputs
      blake3model.leaf_mode
      (map (page_pair_leaf_model page) indices).
  Proof.
    unfold blake3specs.blake3_hash_many_outputs,
      blake3_hash_many_outputs.
    rewrite blake3_hash_many_call_params_leaf.
    reflexivity.
  Qed.

  Lemma leaf_hash_outputs_length page indices :
    length
      (blake3specs.blake3_hash_many_outputs
         blake3model.leaf_mode
         (map (page_pair_leaf_model page) indices)) =
    length indices.
  Proof.
    unfold blake3specs.blake3_hash_many_outputs,
      blake3_hash_many_outputs,
      blake3_hash_many_outputs_from_params.
    rewrite !List.length_map.
    reflexivity.
  Qed.

  (* Retain slice validity before automation consumes an empty slice. *)
  #[local] Hint Resolve obs_typed_slice_array_sliceR_F | 0 : sl_opacity.

  Lemma leaf_pair_block_prefix_blake3_blocks_from
      (base : ptr) start page indices :
    base |-> arrayLR leaf_pair_block_ty
      (Z.of_nat start)
      (Z.of_nat (start + length indices))
      (fun idx => blake3specs.Blake3BlockR 1
        (page_pair_leaf_model page idx))
      indices
    |--
    base |-> typed_sliceR leaf_pair_block_ty
      (Z.of_nat start) (Z.of_nat (start + length indices))
    **
    blake3specs.Blake3InputBlocksDataR 1
      (leaf_input_blocks_from base start page indices).
  Proof using CU MODd Sigma.
    revert start base.
    induction indices as [| idx rest IH]; intros start base.
    {
      cbn.
      go using _at_arrayR_nil_F.
    }
    cbn [length map seq leaf_input_blocks_from].
    replace (start + S (length rest))%nat
      with (S start + length rest)%nat by lia.
    pose (IH_F := [FWD] (IH (S start) base)).
    cbn [blake3specs.Blake3InputBlocksDataR
         blake3_impl_h_specs.Blake3InputBlocksDataR].
    go using obs_typed_slice_array_sliceR_F.
    replace (Z.of_nat start + 1)%Z
      with (Z.of_nat (S start)) by lia.
    go using IH_F, type_ptr_valid.
    all: replace (Z.of_nat start + 1)%Z
      with (Z.of_nat (S start)) by lia.
    all: replace (Z.of_nat (S (start + length rest)))
      with (Z.of_nat (S start + length rest)) by lia.
    all: go using IH_F, type_ptr_valid.
  Qed.

  Definition leaf_pair_block_prefix_blake3_blocks_F base page indices :=
    [FWD] (leaf_pair_block_prefix_blake3_blocks_from base 0 page indices).

  Lemma leaf_pair_block_prefix_blake3_blocks_pack_from
      (base : ptr) slice_start slice_end start page indices :
    (slice_start <= Z.of_nat start /\
     Z.of_nat (start + length indices) <= slice_end)%Z ->
    base |-> typed_sliceR leaf_pair_block_ty slice_start slice_end
    **
    blake3specs.Blake3InputBlocksDataR 1
      (leaf_input_blocks_from base start page indices)
    |--
    base |-> arrayLR leaf_pair_block_ty
      (Z.of_nat start)
      (Z.of_nat (start + length indices))
      (fun idx => blake3specs.Blake3BlockR 1
        (page_pair_leaf_model page idx))
      indices.
  Proof using CU MODd Sigma.
    revert start base.
    induction indices as [| idx rest IH]; intros start base Hslice.
    {
      cbn.
      go using _at_arrayR_nil_B.
    }
    cbn [length map seq leaf_input_blocks_from].
    replace (start + S (length rest))%nat
      with (S start + length rest)%nat by lia.
    destruct Hslice as [Hslice_lo Hslice_hi].
    assert
      (Htail :
        (slice_start <= Z.of_nat (S start) /\
         Z.of_nat (S start + length rest) <= slice_end)%Z).
    {
      split.
      { lia. }
      {
        cbn in Hslice_hi.
        lia.
      }
    }
    pose (IH_F := [FWD] (IH (S start) base Htail)).
    cbn [blake3specs.Blake3InputBlocksDataR
         blake3_impl_h_specs.Blake3InputBlocksDataR].
    replace (Z.of_nat start + 1)%Z
      with (Z.of_nat (S start)) by lia.
    go using arrayLR_cons_B, IH_F,
      typed_sliceR_elim_type_ptr_C, type_ptr_valid.
    all: replace (Z.of_nat start + 1)%Z
      with (Z.of_nat (S start)) by lia.
    all: replace (Z.of_nat (S (start + length rest)))
      with (Z.of_nat (S start + length rest)) by lia.
    all: go using arrayLR_cons_B, IH_F,
      typed_sliceR_elim_type_ptr_C, type_ptr_valid.
    all: rewrite array_sliceR_cons.
    all: go using IH_F,
      typed_sliceR_elim_type_ptr_C, type_ptr_valid.
  Qed.

  Definition leaf_pair_block_prefix_blake3_blocks_pack_F
      base page indices (Hindices : (length indices <= 64)%nat) :=
    [FWD] (leaf_pair_block_prefix_blake3_blocks_pack_from
             base 0 64 0 page indices ltac:(lia)).

  Lemma leaf_pair_block_rows_blake3_unpack
      (base : ptr) page indices :
    (length indices <= 64)%nat ->
    base |-> arrayLR leaf_pair_block_ty 0 64 leaf_pair_block_rowR
      (leaf_pair_block_rows page indices)
    |--
    base |-> typed_sliceR leaf_pair_block_ty 0 64
    **
    blake3specs.Blake3InputBlocksDataR 1
      (leaf_input_blocks base page indices)
    ** base |-> arrayLR leaf_pair_block_ty
      (Z.of_nat (length indices)) 64 leaf_pair_block_rowR
      (replicateN
         (Z.to_N (64 - Z.of_nat (length indices))) LeafPairBlockUninit).
  Proof using CU MODd Sigma.
    intro Hindices.
    unfold leaf_input_blocks, leaf_pair_block_rows.
    rewrite
      (@array_sliceR_app'
         _ _ _ _ leaf_pair_block_row leaf_pair_block_ty base
         0 (Z.of_nat (length indices)) 64
         leaf_pair_block_rowR
         (map
            (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
            indices)
         (replicateN
            (Z.to_N (64 - Z.of_nat (length indices)))
            LeafPairBlockUninit)).
    all: try rewrite lengthN_map.
    all: try rewrite lengthN_replicateN.
    all: try unfold lengthN.
    all: try lia.
    rewrite
      (array_sliceR_fmap
         (ty := leaf_pair_block_ty)
         0 (Z.of_nat (length indices)) indices
         leaf_pair_block_rowR
         (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))).
    cbn [leaf_pair_block_rowR].
    go using leaf_pair_block_prefix_blake3_blocks_F.
  Qed.

  Definition leaf_pair_block_rows_blake3_unpack_F base page indices Hindices :=
    [FWD] (leaf_pair_block_rows_blake3_unpack
             base page indices Hindices).

  Lemma leaf_pair_block_rows_blake3_pack
      (base : ptr) page indices :
    (length indices <= 64)%nat ->
    base |-> typed_sliceR leaf_pair_block_ty 0 64
    **
    blake3specs.Blake3InputBlocksDataR 1
      (leaf_input_blocks base page indices)
    ** base |-> arrayLR leaf_pair_block_ty
      (Z.of_nat (length indices)) 64 leaf_pair_block_rowR
      (replicateN
         (Z.to_N (64 - Z.of_nat (length indices))) LeafPairBlockUninit)
    |--
    base |-> arrayLR leaf_pair_block_ty 0 64 leaf_pair_block_rowR
      (leaf_pair_block_rows page indices).
  Proof using CU MODd Sigma.
    intro Hindices.
    unfold leaf_input_blocks, leaf_pair_block_rows.
    rewrite
      (@array_sliceR_app'
         _ _ _ _ leaf_pair_block_row leaf_pair_block_ty base
         0 (Z.of_nat (length indices)) 64
         leaf_pair_block_rowR
         (map
            (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))
            indices)
         (replicateN
            (Z.to_N (64 - Z.of_nat (length indices)))
            LeafPairBlockUninit)).
    all: try rewrite lengthN_map.
    all: try rewrite lengthN_replicateN.
    all: try unfold lengthN.
    all: try lia.
    rewrite
      (array_sliceR_fmap
         (ty := leaf_pair_block_ty)
         0 (Z.of_nat (length indices)) indices
         leaf_pair_block_rowR
         (fun idx => LeafPairBlockFull (page_pair_leaf_model page idx))).
    cbn [leaf_pair_block_rowR].
    go using
      (leaf_pair_block_prefix_blake3_blocks_pack_F
         base page indices Hindices).
  Qed.

	  Definition leaf_pair_block_rows_blake3_pack_F base page indices Hindices :=
	    [FWD] (leaf_pair_block_rows_blake3_pack
	             base page indices Hindices).

	  Lemma leaf_pair_block_data_rows_forget_64
	      (base : ptr) page indices :
	    (length indices <= 64)%nat ->
	    base |-> typed_sliceR leaf_pair_block_ty 0 64
	    **
	    blake3specs.Blake3InputBlocksDataR 1
	      (leaf_input_blocks base page indices)
	    ** base |-> arrayLR leaf_pair_block_ty
	         (Z.of_nat (length indices)) 64 leaf_pair_block_rowR
	         (replicateN
	            (Z.to_N (64 - Z.of_nat (length indices)))
	            LeafPairBlockUninit)
	    |--
	    base |-> arrayLR leaf_pair_block_ty 0 64
	      (fun _ : unit =>
	         arrayLR Tuchar 0 64
	           (fun _ : unit => anyR Tuchar 1$m)
	           (replicateN 64 ()))
	      (replicateN 64 ()).
	  Proof using CU MODd Sigma.
	    intro Hlen.
	    transitivity
	      (base |-> arrayLR leaf_pair_block_ty 0 64
	         leaf_pair_block_rowR (leaf_pair_block_rows page indices)).
	    {
	      apply leaf_pair_block_rows_blake3_pack.
	      exact Hlen.
	    }
	    apply leaf_pair_block_rows_forget_64.
	    exact Hlen.
	  Qed.

	  Definition leaf_pair_block_data_rows_forget_64_F
	      base page indices Hlen :=
	    [FWD] (leaf_pair_block_data_rows_forget_64
	             base page indices Hlen).

	  Lemma wp_destroy_leaf_pair_blocks_array_cleanup_local :
	    forall (tu : translation_unit) (base : ptr)
	      page indices (Q : epred),
	    (length indices <= 64)%nat ->
	    base |-> typed_sliceR leaf_pair_block_ty 0 64
	    ** blake3specs.Blake3InputBlocksDataR 1
	         (leaf_input_blocks base page indices)
	    ** base |-> arrayLR leaf_pair_block_ty
	         (Z.of_nat (length indices)) 64 leaf_pair_block_rowR
	         (replicateN
	            (Z.to_N (64 - Z.of_nat (length indices)))
	            LeafPairBlockUninit)
	    ** Q
	    |-- wp_destroy_val tu QM
	          (Tarray leaf_pair_block_ty 64%N) base Q.
	  Proof using CU MODd Sigma.
	    intros tu base page indices Q Hindices.
	    transitivity
	      ((base |-> arrayLR leaf_pair_block_ty 0 64
	         (fun _ : unit =>
	            arrayLR Tuchar 0 64
	              (fun _ : unit => anyR Tuchar 1$m)
	              (replicateN 64 ()))
	         (replicateN 64 ())
	       ** Q)%I).
	    {
	      go using
	        (leaf_pair_block_data_rows_forget_64_F
	           base page indices Hindices).
	    }
	    rewrite -destroy.wp_destroy_val_array.
	    cbn.
	    etrans.
	    {
	      exact
	        (brick_upstream.destroy_run_array_from_arrayLR
	           unit tu QM leaf_pair_block_ty 64%nat base
	           (fun _ : unit =>
	              arrayLR Tuchar 0 64
	                (fun _ : unit => anyR Tuchar 1$m)
	                (replicateN 64 ()))
	           (replicateN 64 ()) Q
	           ltac:(change (length (replicateN 64 ())) with 64%nat;
	                 reflexivity)
	           eq_refl
	           (fun cellp _ Qcell =>
	              wp_destroy_leaf_pair_block_row_bytes_cell_local
	                tu cellp Qcell)).
	    }
	    exact (destroy.run_array_ok tu 64%N QM
	             leaf_pair_block_ty base Q).
	  Qed.

	  Definition wp_destroy_leaf_pair_blocks_array_cleanup_local_B
	      tu base page indices Q Hindices :=
	    [BWD] (wp_destroy_leaf_pair_blocks_array_cleanup_local
	             tu base page indices Q Hindices).

	  Lemma leaf_hash_many_post_pack
      key_q (keyp inputs_addr flat_outp pairsp : ptr)
      page indices old_outputs :
    (length indices <= 64)%nat ->
    List.Forall (fun x => (x < 2 ^ 256)%N) old_outputs ->
    pairsp |-> typed_sliceR leaf_pair_block_ty 0 64
    ** pairsp |-> arrayLR leaf_pair_block_ty
         (Z.of_nat (length indices)) 64 leaf_pair_block_rowR
         (replicateN
            (Z.to_N (64 - Z.of_nat (length indices))) LeafPairBlockUninit)
    ** keyp |-> blake3specs.Blake3ConstKeyWordsR
         key_q blake3model.mip8_leaf_iv_words
    ** inputs_addr |-> blake3specs.Blake3InputBlocksR
         true 1 1
         (leaf_input_blocks pairsp page indices)
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
         (Z.of_nat (length indices)) 64
         (fun _ : unit =>
            anyR blake3specs.blake3_input_ptr_store_ty 1$m)
         (replicateZ (64 - Z.of_nat (length indices)) ())
    ** flat_outp |-> storage_page_byte_bridges.evmc_bytes32_array_spineR
         1$m (length indices)
    ** flat_outp |-> blake3specs.Blake3OutputBytesR 1
         (blake3_hash_many_outputs_from_params
            (blake3_hash_many_call_params
               blake3model.mip8_leaf_iv_words 0 false 64 0 0)
            (map blake3specs.blake3_input_block_data
               (leaf_input_blocks pairsp page indices)))
    ** flat_outp .[ blake3specs.bytes32_ty ! Z.of_nat (length indices) ]
       |-> blake3specs.Blake3OutputWordsR 1
             (skipn (length indices) old_outputs)
    |--
    pairsp |-> arrayLR leaf_pair_block_ty 0 64 leaf_pair_block_rowR
      (leaf_pair_block_rows page indices)
    ** keyp |-> blake3specs.Blake3ConstKeyWordsR
         key_q blake3model.mip8_leaf_iv_words
    ** inputs_addr |-> leaf_inputs_arrayR pairsp indices
    ** flat_outp |-> blake3specs.Blake3OutputWordsR 1
         (List.app
            (blake3specs.blake3_hash_many_outputs
               blake3model.leaf_mode
               (map (page_pair_leaf_model page) indices))
            (skipn (length indices) old_outputs)).
  Proof using CU MODd Sigma.
	    intros Hindices Hrange_old.
	    rewrite leaf_input_blocks_data.
	    rewrite leaf_hash_outputs_from_call_params.
	    assert
      (Houtput_range :
        List.Forall (fun x => (x < 2 ^ 256)%N)
          (blake3specs.blake3_hash_many_outputs
             blake3model.leaf_mode
             (map (page_pair_leaf_model page) indices))).
    {
      apply blake3specs.blake3_hash_many_outputs_range.
    }
    go using
      (leaf_pair_block_rows_blake3_pack_F
         pairsp page indices Hindices),
      leaf_inputs_arrayR_blake3_pack_B,
      leaf_inputs_arrayR_blake3_inputs_unpack_F,
      (blake3_output_bytes_prefix_tail_to_words_F
         flat_outp
         (blake3specs.blake3_hash_many_outputs
            blake3model.leaf_mode
            (map (page_pair_leaf_model page) indices))
         (skipn (length indices) old_outputs)
         (length indices)
         Houtput_range
         (eq_sym (leaf_hash_outputs_length page indices))),
      leaf_inputs_prefix_arrayR_blake3_pack_F,
      leaf_inputs_prefix_arrayR_blake3_pack_for_page_F.
  Qed.

  Definition leaf_hash_many_post_pack_F
      key_q keyp inputs_addr flat_outp pairsp page indices old_outputs
      Hindices Hrange :=
    [FWD] (leaf_hash_many_post_pack
             key_q keyp inputs_addr flat_outp pairsp page indices
             old_outputs Hindices Hrange).

  Lemma leaf_arrays_step_pack
      (pairsp inputs_addr indices_addr : ptr)
      (seen : list nat) (idx : N) :
    inputs_addr |-> typed_sliceR blake3specs.blake3_input_ptr_store_ty 0 64
	    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
	      0 (Z.of_nat (length seen))
	      (fun row : nat =>
	         primR blake3specs.blake3_input_ptr_value_ty 1$m
	           (Vptr (leaf_pair_bytesp pairsp row)))
	      (seq 0 (length seen))
	    ** indices_addr |-> arrayLR Tuchar
	      0 (Z.of_nat (length seen))
	      (fun index : nat => ucharR 1$m (Z.of_nat index))
	      seen
	    ** indices_addr |-> arrayLR Tuchar
	      (Z.of_nat (length seen) + 1) 64
	      (fun _ : unit => anyR Tuchar 1$m)
	      (replicateZ (64 - Z.of_nat (length seen) - 1) ())
    ** indices_addr .[ Tuchar ! Z.of_nat (length seen) ]
      |-> ucharR 1$m (Z.of_N idx)
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      (Z.of_nat (length seen) + 1) 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateZ (64 - Z.of_nat (length seen) - 1) ())
    ** inputs_addr .[ blake3specs.blake3_input_ptr_store_ty !
                      Z.of_nat (length seen) ]
      |-> primR blake3specs.blake3_input_ptr_value_ty 1$m
            (Vptr (leaf_pair_bytesp pairsp (length seen)))
    |--
    (indices_addr |-> arrayLR Tuchar
       (Z.of_nat (length (seen ++ [N.to_nat idx]))) 64
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateZ
          (64 - Z.of_nat (length (seen ++ [N.to_nat idx]))) ())
     ** indices_addr |-> arrayLR Tuchar
       0 (Z.of_nat (length (seen ++ [N.to_nat idx])))
       (fun index : nat => ucharR 1$m (Z.of_nat index))
       (seen ++ [N.to_nat idx]))
    ** (inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
       (Z.of_nat (length (seen ++ [N.to_nat idx]))) 64
       (fun _ : unit =>
          anyR blake3specs.blake3_input_ptr_store_ty 1$m)
       (replicateZ
          (64 - Z.of_nat (length (seen ++ [N.to_nat idx]))) ())
     ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
       0 (Z.of_nat (length (seen ++ [N.to_nat idx])))
       (fun row : nat =>
          primR blake3specs.blake3_input_ptr_value_ty 1$m
            (Vptr (leaf_pair_bytesp pairsp row)))
       (seq 0 (length (seen ++ [N.to_nat idx])))).
  Proof.
    go.
    rewrite !List.length_app.
    cbn [List.length].
    replace (Z.of_nat (length seen + 1) - 1)%Z
      with (Z.of_nat (length seen)) by lia.
    rewrite !array_sliceR_singleton'.
    rewrite N_nat_Z.
    replace (64 - Z.of_nat (length seen) - 1)%Z
      with (64 - Z.of_nat (length seen + 1))%Z by lia.
    clear H.
    assert (Hseen_lt : (length seen < 64)%nat) by lia.
    replace (seq 0 (length seen + 1))
      with (seq 0 (length seen) ++ [length seen])%list.
    2: {
      rewrite (seq_app (length seen) 1 0).
      simpl.
      reflexivity.
    }
    go using input_ptr_typed_slice_cell_type_C.
    Unshelve.
    all: try solve [lia | eauto | typeclasses eauto | go].
  Qed.

  Definition leaf_arrays_step_pack_F
      pairsp inputs_addr indices_addr seen idx :=
    [FWD] (leaf_arrays_step_pack
             pairsp inputs_addr indices_addr seen idx).

  Lemma leaf_arrays_step_pack_current_tail
      (pairsp inputs_addr indices_addr : ptr)
      (seen : list nat) (idx : N) :
    inputs_addr |-> typed_sliceR blake3specs.blake3_input_ptr_store_ty 0 64
	    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
	      0 (Z.of_nat (length seen))
	      (fun row : nat =>
	         primR blake3specs.blake3_input_ptr_value_ty 1$m
	           (Vptr (leaf_pair_bytesp pairsp row)))
	      (seq 0 (length seen))
	    ** indices_addr |-> arrayLR Tuchar
	      (Z.of_nat (length seen) + 1) 64
	      (fun _ : unit => anyR Tuchar 1$m)
      (replicateZ (64 - Z.of_nat (length seen) - 1) ())
    ** indices_addr .[ Tuchar ! Z.of_nat (length seen) ]
      |-> ucharR 1$m (Z.of_N idx)
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      (Z.of_nat (length seen) + 1) 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateZ (64 - Z.of_nat (length seen) - 1) ())
    ** inputs_addr .[ blake3specs.blake3_input_ptr_store_ty !
                      Z.of_nat (length seen) ]
      |-> primR blake3specs.blake3_input_ptr_value_ty 1$m
            (Vptr (leaf_pair_bytesp pairsp (length seen)))
    |--
    indices_addr |-> arrayLR Tuchar
      (Z.of_nat (length seen))
      (Z.of_nat (length (seen ++ [N.to_nat idx])))
      (fun index : nat => ucharR 1$m (Z.of_nat index))
      [N.to_nat idx]
    ** indices_addr |-> arrayLR Tuchar
      (Z.of_nat (length (seen ++ [N.to_nat idx]))) 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN
         (Z.to_N (64 - Z.of_nat (length (seen ++ [N.to_nat idx]))))
         ())
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      (Z.of_nat (length (seen ++ [N.to_nat idx]))) 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateN
         (Z.to_N (64 - Z.of_nat (length (seen ++ [N.to_nat idx]))))
         ())
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length (seen ++ [N.to_nat idx])))
      (fun row : nat =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr (leaf_pair_bytesp pairsp row)))
      (seq 0 (length (seen ++ [N.to_nat idx]))).
  Proof.
    go.
    rewrite !List.length_app.
    cbn [List.length].
    replace (Z.of_nat (length seen + 1) - 1)%Z
      with (Z.of_nat (length seen)) by lia.
    rewrite !array_sliceR_singleton'.
    rewrite N_nat_Z.
    replace (64 - Z.of_nat (length seen) - 1)%Z
      with (64 - Z.of_nat (length seen + 1))%Z by lia.
    replace (seq 0 (length seen + 1))
      with (seq 0 (length seen) ++ [length seen])%list.
    2: {
      rewrite (seq_app (length seen) 1 0).
      simpl.
      reflexivity.
    }
    go using input_ptr_typed_slice_cell_type_C.
    Unshelve.
    all: try solve [lia | eauto | typeclasses eauto | go].
  Qed.

  Definition leaf_arrays_step_pack_current_tail_F
      pairsp inputs_addr indices_addr seen idx :=
    [FWD] (leaf_arrays_step_pack_current_tail
             pairsp inputs_addr indices_addr seen idx).

  Lemma leaf_arrays_step_pack_split_index
      (pairsp inputs_addr indices_addr : ptr)
      (seen : list nat) (idx : N) :
    inputs_addr |-> typed_sliceR blake3specs.blake3_input_ptr_store_ty 0 64
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      0 (Z.of_nat (length seen))
      (fun row : nat =>
         primR blake3specs.blake3_input_ptr_value_ty 1$m
           (Vptr (leaf_pair_bytesp pairsp row)))
      (seq 0 (length seen))
    ** indices_addr |-> arrayLR Tuchar
      0 (Z.of_nat (length seen))
      (fun index : nat => ucharR 1$m (Z.of_nat index))
      seen
    ** indices_addr |-> arrayLR Tuchar
      (Z.of_nat (length seen) + 1) 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateZ (64 - Z.of_nat (length seen) - 1) ())
    ** indices_addr .[ Tuchar ! Z.of_nat (length seen) ]
      |-> ucharR 1$m (Z.of_N idx)
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
      (Z.of_nat (length seen) + 1) 64
      (fun _ : unit =>
         anyR blake3specs.blake3_input_ptr_store_ty 1$m)
      (replicateZ (64 - Z.of_nat (length seen) - 1) ())
    ** inputs_addr .[ blake3specs.blake3_input_ptr_store_ty !
                      Z.of_nat (length seen) ]
      |-> primR blake3specs.blake3_input_ptr_value_ty 1$m
            (Vptr (leaf_pair_bytesp pairsp (length seen)))
    |--
    (type_ptr Tuchar
       (indices_addr .[ Tuchar !
         Z.of_nat (length (seen ++ [N.to_nat idx])) - 1 ])
     ** indices_addr .[ Tuchar !
          Z.of_nat (length (seen ++ [N.to_nat idx])) - 1 ]
        |-> ucharR 1$m (Z.of_nat (N.to_nat idx))
     ** indices_addr |-> arrayLR Tuchar
          0 (Z.of_nat (length (seen ++ [N.to_nat idx])) - 1)
          (fun index : nat => ucharR 1$m (Z.of_nat index))
          seen)
    ** indices_addr |-> arrayLR Tuchar
       (Z.of_nat (length (seen ++ [N.to_nat idx]))) 64
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateZ
          (64 - Z.of_nat (length (seen ++ [N.to_nat idx]))) ())
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
       (Z.of_nat (length (seen ++ [N.to_nat idx]))) 64
       (fun _ : unit =>
          anyR blake3specs.blake3_input_ptr_store_ty 1$m)
       (replicateZ
          (64 - Z.of_nat (length (seen ++ [N.to_nat idx]))) ())
    ** inputs_addr |-> arrayLR blake3specs.blake3_input_ptr_store_ty
       0 (Z.of_nat (length (seen ++ [N.to_nat idx])))
       (fun row : nat =>
          primR blake3specs.blake3_input_ptr_value_ty 1$m
            (Vptr (leaf_pair_bytesp pairsp row)))
       (seq 0 (length (seen ++ [N.to_nat idx]))).
  Proof.
    go.
    rewrite !List.length_app.
    cbn [List.length].
    replace (Z.of_nat (length seen + 1) - 1)%Z
      with (Z.of_nat (length seen)) by lia.
    rewrite N_nat_Z.
    replace (64 - Z.of_nat (length seen) - 1)%Z
      with (64 - Z.of_nat (length seen + 1))%Z by lia.
    clear H.
    replace (seq 0 (length seen + 1))
      with (seq 0 (length seen) ++ [length seen])%list.
    2: {
      rewrite (seq_app (length seen) 1 0).
      simpl.
      reflexivity.
    }
    go using input_ptr_typed_slice_cell_type_C.
  Qed.

  Definition leaf_arrays_step_pack_split_index_F
      pairsp inputs_addr indices_addr seen idx :=
    [FWD] (leaf_arrays_step_pack_split_index
             pairsp inputs_addr indices_addr seen idx).

  Lemma popcount_fuel_bound fuel word :
    (popcount_fuel fuel word <= N.of_nat fuel)%N.
  Proof.
    revert word.
    induction fuel as [| fuel IH]; intro word.
    {
      cbn.
      lia.
    }
    {
      cbn.
      destruct (N.odd word); pose proof (IH (word ≫ 1)%N); lia.
    }
  Qed.

  Lemma popcount64_bound word :
    (popcount64 word <= 64)%N.
  Proof.
    unfold popcount64.
    change 64%N with (N.of_nat 64).
    apply popcount_fuel_bound.
  Qed.

  Lemma leaf_loop_state_init pair_bitmap :
    (pair_bitmap < 2 ^ 64)%N ->
    leaf_loop_state pair_bitmap [] pair_bitmap.
  Proof.
    intro Hbitmap.
    unfold leaf_loop_state.
    split.
    {
      reflexivity.
    }
    split.
    {
      apply List.Forall_nil.
    }
    split.
    {
      unfold page_pair_count.
      pose proof (popcount64_bound pair_bitmap) as Hpop.
      apply N2Nat_inj_le in Hpop.
      exact Hpop.
    }
    split.
    {
      exact Hbitmap.
    }
    {
      exact Hbitmap.
    }
  Qed.

  Lemma shiftr_one_even_nonzero word :
    word <> 0%N ->
    N.odd word = false ->
    (word ≫ 1)%N <> 0%N.
  Proof.
    intros Hword Hodd Hshift.
    apply Hword.
    rewrite (N.shiftr_succ_r word 0) in Hshift.
    rewrite N.shiftr_0_r in Hshift.
    rewrite (N.div2_odd word).
    rewrite Hshift.
    rewrite Hodd.
    reflexivity.
  Qed.

  Lemma shiftr_one_lt_pow fuel word :
    (word < 2 ^ N.of_nat (S fuel))%N ->
    (word ≫ 1 < 2 ^ N.of_nat fuel)%N.
  Proof.
    intro Hword.
    rewrite N.shiftr_div_pow2.
    apply N.div_lt_upper_bound.
    {
      discriminate.
    }
    rewrite Nat2N.inj_succ in Hword.
    rewrite N.pow_succ_r' in Hword.
    {
      change (2 ^ 1)%N with 2%N.
      exact Hword.
    }
  Qed.

  Lemma countr_zero_fuel_nonzero_lt fuel word :
    word <> 0%N ->
    (word < 2 ^ N.of_nat fuel)%N ->
    (countr_zero_fuel fuel word < N.of_nat fuel)%N.
  Proof.
    revert word.
    induction fuel as [| fuel IH]; intros word Hword Hbound.
    {
      simpl in Hbound.
      nia.
    }
    simpl.
    destruct (word =? 0)%N eqn:Hword_eq.
    {
      apply N.eqb_eq in Hword_eq.
      contradiction.
    }
    destruct (N.odd word) eqn:Hodd.
    {
      nia.
    }
    change (N.pos (Pos.of_succ_nat fuel)) with (N.of_nat (S fuel)).
    rewrite Nat2N.inj_succ.
    change
      ((1 + countr_zero_fuel fuel (word ≫ 1) <
        N.succ (N.of_nat fuel))%N).
    pose proof
      (IH (word ≫ 1)%N
         (shiftr_one_even_nonzero word Hword Hodd)
         (shiftr_one_lt_pow fuel word Hbound))
      as Hcz.
    {
      nia.
    }
  Qed.

  Lemma countr_zero64_nonzero_lt word :
    word <> 0%N ->
    (word < 2 ^ 64)%N ->
    (countr_zero64 word < 64)%N.
  Proof.
    intros Hword Hbound.
    unfold countr_zero64.
    change 64%N with (N.of_nat 64).
    apply countr_zero_fuel_nonzero_lt.
    {
      exact Hword.
    }
    {
      exact Hbound.
    }
  Qed.

  Lemma trim8_countr_zero64 word :
    word <> 0%N ->
    (word < 2 ^ 64)%N ->
    trim 8 (countr_zero64 word) = Z.of_N (countr_zero64 word).
  Proof.
    intros Hword Hbound.
    unfold trim.
    apply Z.mod_small.
    pose proof (countr_zero64_nonzero_lt word Hword Hbound) as Hcz.
    lia.
  Qed.

  Lemma popcount_fuel_zero fuel :
    popcount_fuel fuel 0 = 0%N.
  Proof.
    induction fuel as [| fuel IH].
    {
      reflexivity.
    }
    {
      cbn.
      rewrite N.shiftr_0_l.
      exact IH.
    }
  Qed.

  Lemma shiftr_one_twice (a : N) :
    ((2 * a) ≫ 1 = a)%N.
  Proof.
    change 1%N with (N.succ 0%N).
    rewrite N.shiftr_succ_r.
    rewrite N.shiftr_0_r.
    apply N.div2_even.
  Qed.

  Lemma shiftr_one_twice_plus_one (a : N) :
    (((2 * a + 1) ≫ 1) = a)%N.
  Proof.
    change 1%N with (N.succ 0%N).
    rewrite N.shiftr_succ_r.
    rewrite N.shiftr_0_r.
    apply N.div2_odd'.
  Qed.

  Lemma popcount_fuel_even fuel a :
    popcount_fuel (S fuel) (2 * a) =
    popcount_fuel fuel a.
  Proof.
    cbn.
    rewrite N.odd_even.
    rewrite shiftr_one_twice.
    reflexivity.
  Qed.

  Lemma popcount_fuel_odd fuel a :
    popcount_fuel (S fuel) (2 * a + 1) =
    (1 + popcount_fuel fuel a)%N.
  Proof.
    cbn.
    rewrite N.odd_odd.
    rewrite shiftr_one_twice_plus_one.
    reflexivity.
  Qed.

  Lemma leaf_clear_lowbit_odd word :
    N.odd word = true ->
    leaf_clear_lowbit word = (word - 1)%N.
  Proof.
    intro Hodd.
    unfold leaf_clear_lowbit.
    pose proof (N.div2_odd word) as Hword_eq.
    rewrite Hodd in Hword_eq.
    rewrite Hword_eq.
    change (N.b2n true) with 1%N.
    replace (2 * N.div2 word + 1 - 1)%N
      with (2 * N.div2 word)%N.
    2: {
      symmetry.
      apply N.add_sub.
    }
    rewrite N.land_odd_even.
    rewrite N.land_diag.
    reflexivity.
  Qed.

  Lemma leaf_clear_lowbit_even word :
    N.odd word = false ->
    leaf_clear_lowbit word =
      (2 * leaf_clear_lowbit (word ≫ 1))%N.
  Proof.
    intro Hodd.
    unfold leaf_clear_lowbit at 1.
    destruct (N.eq_dec word 0%N) as [-> | Hword].
    {
      reflexivity.
    }
    pose proof (N.div2_odd word) as Hword_eq.
    rewrite Hodd in Hword_eq.
    rewrite Hword_eq.
    change (N.b2n false) with 0%N.
    replace (2 * N.div2 word + 0 - 1)%N
      with (2 * (N.div2 word - 1) + 1)%N.
    2: {
      assert (N.div2 word <> 0%N).
      {
        intro Hdiv.
        apply Hword.
        rewrite Hword_eq Hdiv.
        reflexivity.
      }
      destruct (N.div2 word) as [| p].
      {
        contradiction.
      }
      {
        nia.
      }
    }
    rewrite N.add_0_r.
    rewrite N.land_even_odd.
    rewrite shiftr_one_twice.
    reflexivity.
  Qed.

  Lemma popcount_fuel_clear_lowbit fuel word :
    word <> 0%N ->
    (word < 2 ^ N.of_nat fuel)%N ->
    (popcount_fuel fuel (leaf_clear_lowbit word) + 1 =
     popcount_fuel fuel word)%N.
  Proof.
    revert word.
    induction fuel as [| fuel IH]; intros word Hword Hbound.
    {
      cbn in Hbound.
      nia.
    }
    cbn [popcount_fuel].
    destruct (N.odd word) eqn:Hodd.
    {
      pose proof (N.div2_odd word) as Hword_eq.
      rewrite Hodd in Hword_eq.
      rewrite Hword_eq.
      change (N.b2n true) with 1%N.
      rewrite (leaf_clear_lowbit_odd (2 * N.div2 word + 1)).
      2: {
        rewrite N.odd_odd.
        reflexivity.
      }
      replace (2 * N.div2 word + 1 - 1)%N
        with (2 * N.div2 word)%N.
      2: {
        symmetry.
        apply N.add_sub.
      }
      rewrite N.odd_even.
      rewrite shiftr_one_twice.
      rewrite shiftr_one_twice_plus_one.
      lia.
    }
    {
      rewrite (leaf_clear_lowbit_even word Hodd).
      rewrite N.odd_even.
      rewrite shiftr_one_twice.
      rewrite (IH ((word ≫ 1)%N)).
      {
        reflexivity.
      }
      {
        apply shiftr_one_even_nonzero; assumption.
      }
      {
        apply shiftr_one_lt_pow.
        exact Hbound.
      }
    }
  Qed.

  Lemma popcount64_clear_lowbit word :
    word <> 0%N ->
    (word < 2 ^ 64)%N ->
    (popcount64 (leaf_clear_lowbit word) + 1 =
     popcount64 word)%N.
  Proof.
    intros Hword Hbound.
    unfold popcount64.
    change 64%N with (N.of_nat 64).
    apply popcount_fuel_clear_lowbit; assumption.
  Qed.

  Lemma popcount_fuel_nonzero fuel word :
    word <> 0%N ->
    (word < 2 ^ N.of_nat fuel)%N ->
    (0 < popcount_fuel fuel word)%N.
  Proof.
    revert word.
    induction fuel as [| fuel IH]; intros word Hword Hbound.
    {
      cbn in Hbound.
      nia.
    }
    cbn.
    destruct (N.odd word) eqn:Hodd.
    {
      lia.
    }
    {
      pose proof
        (IH (word ≫ 1)%N
           (shiftr_one_even_nonzero word Hword Hodd)
           (shiftr_one_lt_pow fuel word Hbound)).
      lia.
    }
  Qed.

  Lemma popcount64_nonzero word :
    word <> 0%N ->
    (word < 2 ^ 64)%N ->
    (0 < popcount64 word)%N.
  Proof.
    intros Hword Hbound.
    unfold popcount64.
    change 64%N with (N.of_nat 64).
    apply popcount_fuel_nonzero; assumption.
  Qed.

  Lemma countr_zero_fuel_bit_true fuel word :
    word <> 0%N ->
    (word < 2 ^ N.of_nat fuel)%N ->
    N.testbit word (countr_zero_fuel fuel word) = true.
  Proof.
    revert word.
    induction fuel as [| fuel IH]; intros word Hword Hbound.
    {
      cbn in Hbound.
      nia.
    }
    cbn [countr_zero_fuel].
    destruct (word =? 0)%N eqn:Hword_eq.
    {
      apply N.eqb_eq in Hword_eq.
      contradiction.
    }
    destruct (N.odd word) eqn:Hodd.
    {
      rewrite N.bit0_odd.
      exact Hodd.
    }
    {
      replace (1 + countr_zero_fuel fuel (word ≫ 1))%N
        with (N.succ (countr_zero_fuel fuel (word ≫ 1)%N)) by lia.
      rewrite N.testbit_succ_r_div2.
      2: {
        lia.
      }
      apply IH.
      {
        apply shiftr_one_even_nonzero; assumption.
      }
      {
        apply shiftr_one_lt_pow.
        exact Hbound.
      }
    }
  Qed.

  Lemma countr_zero64_bit_true word :
    word <> 0%N ->
    (word < 2 ^ 64)%N ->
    N.testbit word (countr_zero64 word) = true.
  Proof.
    intros Hword Hbound.
    unfold countr_zero64.
    change 64%N with (N.of_nat 64).
    apply countr_zero_fuel_bit_true; assumption.
  Qed.

  Lemma leaf_clear_lowbit_testbit_fuel fuel word j :
    word <> 0%N ->
    (word < 2 ^ N.of_nat fuel)%N ->
    N.testbit (leaf_clear_lowbit word) j =
    if (j =? countr_zero_fuel fuel word)%N
    then false
    else N.testbit word j.
  Proof.
    revert word j.
    induction fuel as [| fuel IH]; intros word j Hword Hbound.
    {
      cbn in Hbound.
      nia.
    }
    cbn [countr_zero_fuel].
    destruct (word =? 0)%N eqn:Hword_eq.
    {
      apply N.eqb_eq in Hword_eq.
      contradiction.
    }
    destruct (N.odd word) eqn:Hodd.
    {
      pose proof (N.div2_odd word) as Hword_shape.
      rewrite Hodd in Hword_shape.
      rewrite Hword_shape.
      change (N.b2n true) with 1%N.
      rewrite (leaf_clear_lowbit_odd (2 * N.div2 word + 1)).
      2: {
        rewrite N.odd_odd.
        reflexivity.
      }
      replace (2 * N.div2 word + 1 - 1)%N
        with (2 * N.div2 word)%N.
      2: {
        symmetry.
        apply N.add_sub.
      }
      destruct j as [| j'] using N.peano_ind.
      {
        rewrite N.eqb_refl.
        rewrite N.bit0_odd.
        rewrite N.odd_even.
        reflexivity.
      }
      {
        replace ((N.succ j' =? 0)%N) with false.
        2: {
          symmetry.
          apply N.eqb_neq.
          lia.
        }
        rewrite N.testbit_succ_r_div2.
        2: {
          lia.
        }
        rewrite N.testbit_succ_r_div2.
        2: {
          lia.
        }
        rewrite N.div2_even.
        rewrite N.div2_odd'.
        reflexivity.
      }
    }
    {
      rewrite (leaf_clear_lowbit_even word Hodd).
      destruct j as [| j'] using N.peano_ind.
      {
        replace ((0 =? 1 + countr_zero_fuel fuel (word ≫ 1))%N)
          with false.
        2: {
          symmetry.
          apply N.eqb_neq.
          lia.
        }
        rewrite N.bit0_odd.
        rewrite N.odd_even.
        symmetry.
        rewrite N.bit0_odd.
        exact Hodd.
      }
      {
        rewrite N.testbit_succ_r_div2.
        2: {
          lia.
        }
        rewrite N.testbit_succ_r_div2.
        2: {
          lia.
        }
        rewrite N.div2_even.
        rewrite N.div2_spec.
        destruct (N.eq_dec j' (countr_zero_fuel fuel (word ≫ 1)%N))
          as [-> | Hneq].
        {
          replace
            (1 + countr_zero_fuel fuel (word ≫ 1))%N
            with (N.succ (countr_zero_fuel fuel (word ≫ 1)%N)) by lia.
          rewrite N.eqb_refl.
          rewrite
            (IH ((word ≫ 1)%N)
               (countr_zero_fuel fuel (word ≫ 1)%N)).
          {
            rewrite N.eqb_refl.
            reflexivity.
          }
          {
            apply shiftr_one_even_nonzero; assumption.
          }
          {
            apply shiftr_one_lt_pow.
            exact Hbound.
          }
        }
        {
          replace ((N.succ j' =?
                    1 + countr_zero_fuel fuel (word ≫ 1))%N)
            with false.
          2: {
            symmetry.
            apply N.eqb_neq.
            lia.
          }
          rewrite (IH ((word ≫ 1)%N) j').
          {
            replace
              ((j' =? countr_zero_fuel fuel (word ≫ 1))%N)
              with false.
            2: {
              symmetry.
              apply N.eqb_neq.
              exact Hneq.
            }
            reflexivity.
          }
          {
            apply shiftr_one_even_nonzero; assumption.
          }
          {
            apply shiftr_one_lt_pow.
            exact Hbound.
          }
        }
      }
    }
  Qed.

  Lemma leaf_clear_lowbit_testbit64 word j :
    word <> 0%N ->
    (word < 2 ^ 64)%N ->
    N.testbit (leaf_clear_lowbit word) j =
    if (j =? countr_zero64 word)%N
    then false
    else N.testbit word j.
  Proof.
    intros Hword Hbound.
    unfold countr_zero64.
    change 64%N with (N.of_nat 64).
    apply leaf_clear_lowbit_testbit_fuel; assumption.
  Qed.

  Lemma bitmap_word_bit_testbit word index :
    bitmap_word_bit word index =
    N.testbit word (N.of_nat index).
  Proof.
    unfold bitmap_word_bit.
    destruct (N_land_bit (N.of_nat index) word) as [Hland | Hland].
    {
      assert
        (Hbit : N.testbit word (N.of_nat index) = true).
      {
        pose proof
          (f_equal
             (fun x => N.testbit x (N.of_nat index)) Hland)
          as Htest.
        rewrite N.land_spec in Htest.
        rewrite !N.pow2_bits_true in Htest.
        destruct (N.testbit word (N.of_nat index)); cbn in Htest;
          congruence.
      }
      rewrite Hland.
      rewrite Hbit.
      replace ((2 ^ N.of_nat index =? 0)%N) with false.
      {
        reflexivity.
      }
      {
        symmetry.
        apply N.eqb_neq.
        nia.
      }
    }
    {
      assert
        (Hbit : N.testbit word (N.of_nat index) = false).
      {
        pose proof
          (f_equal
             (fun x => N.testbit x (N.of_nat index)) Hland)
          as Htest.
        rewrite N.land_spec in Htest.
        rewrite N.pow2_bits_true in Htest.
        rewrite N.bits_0 in Htest.
        destruct (N.testbit word (N.of_nat index)); cbn in Htest;
          congruence.
      }
      rewrite Hland.
      rewrite N.eqb_refl.
      rewrite Hbit.
      reflexivity.
    }
  Qed.

  Lemma bitmap_word_bit_countr_zero64 word :
    word <> 0%N ->
    (word < 2 ^ 64)%N ->
    bitmap_word_bit word (N.to_nat (countr_zero64 word)) = true.
  Proof.
    intros Hword Hbound.
    rewrite bitmap_word_bit_testbit.
    rewrite N2Nat.id.
    apply countr_zero64_bit_true; assumption.
  Qed.

  Lemma bitmap_word_bit_clear_lowbit64 word index :
    word <> 0%N ->
    (word < 2 ^ 64)%N ->
    bitmap_word_bit (leaf_clear_lowbit word) index =
    if (N.of_nat index =? countr_zero64 word)%N
    then false
    else bitmap_word_bit word index.
  Proof.
    intros Hword Hbound.
    rewrite !bitmap_word_bit_testbit.
    apply leaf_clear_lowbit_testbit64; assumption.
  Qed.

  Lemma leaf_clear_lowbit_bound64 word :
    (word < 2 ^ 64)%N ->
    (leaf_clear_lowbit word < 2 ^ 64)%N.
  Proof.
    intro Hword.
    unfold leaf_clear_lowbit.
    eapply N.le_lt_trans.
    {
      apply N.land_le_l.
    }
    {
      exact Hword.
    }
  Qed.

  Lemma leaf_loop_indices_bit_true fuel word index :
    (word < 2 ^ 64)%N ->
    In index (leaf_loop_indices fuel word) ->
    bitmap_word_bit word index = true.
  Proof.
    revert word index.
    induction fuel as [| fuel IH]; intros word index Hbound Hin.
    {
      cbn in Hin.
      contradiction.
    }
    cbn [leaf_loop_indices] in Hin.
    destruct (N.eqb word 0) eqn:Hword_eq.
    {
      contradiction.
    }
    apply N.eqb_neq in Hword_eq.
    destruct Hin as [Hhead | Hin].
    {
      subst index.
      apply bitmap_word_bit_countr_zero64; assumption.
    }
    {
      pose proof
        (IH (leaf_clear_lowbit word) index
           (leaf_clear_lowbit_bound64 word Hbound) Hin)
        as Htail.
      rewrite
        (bitmap_word_bit_clear_lowbit64 word index Hword_eq Hbound)
        in Htail.
      destruct ((N.of_nat index =? countr_zero64 word)%N);
        try discriminate.
      exact Htail.
    }
  Qed.

  Lemma leaf_loop_indices_NoDup fuel word :
    (word < 2 ^ 64)%N ->
    List.NoDup (leaf_loop_indices fuel word).
  Proof.
    revert word.
    induction fuel as [| fuel IH]; intro word.
    {
      cbn [leaf_loop_indices].
      constructor.
    }
    {
      intro Hbound.
      cbn [leaf_loop_indices].
      destruct (N.eqb word 0) eqn:Hword_eq.
      {
        constructor.
      }
      apply N.eqb_neq in Hword_eq.
      constructor.
      {
        intro Hin.
        pose proof
          (leaf_loop_indices_bit_true
             fuel (leaf_clear_lowbit word)
             (N.to_nat (countr_zero64 word))
             (leaf_clear_lowbit_bound64 word Hbound) Hin)
          as Htail.
        rewrite
          (bitmap_word_bit_clear_lowbit64
             word (N.to_nat (countr_zero64 word))
             Hword_eq Hbound)
          in Htail.
        rewrite N2Nat.id in Htail.
        rewrite N.eqb_refl in Htail.
        discriminate.
      }
      {
        apply IH.
        apply leaf_clear_lowbit_bound64.
        exact Hbound.
      }
    }
  Qed.

  Lemma leaf_indices_NoDup word :
    (word < 2 ^ 64)%N ->
    List.NoDup (leaf_indices word).
  Proof.
    unfold leaf_indices.
    apply leaf_loop_indices_NoDup.
  Qed.

  Transparent init_leaf_scratch_model.

  Lemma init_leaf_scratch_model_length page pair_bitmap old_scratch :
    length (init_leaf_scratch_model page pair_bitmap old_scratch) =
    page_pair_count.
  Proof.
    unfold init_leaf_scratch_model.
    rewrite length_map.
    apply length_seq.
  Qed.

  Lemma init_leaf_scratch_model_lookup
      page pair_bitmap old_scratch i :
    (i < page_pair_count)%nat ->
    init_leaf_scratch_model page pair_bitmap old_scratch !! i =
    Some
       (if bitmap_word_bit pair_bitmap i
       then leaf_pair_hash page i
       else nth i old_scratch 0%N).
  Proof.
    intro Hi.
    unfold init_leaf_scratch_model, leaf_pair_hash.
    set
      (f :=
         fun pair_index : nat =>
           if bitmap_word_bit pair_bitmap pair_index
           then
             blake3model.bytes32_to_N
               (blake3model.H64 blake3model.leaf_mode
                  (page_pair_leaf_model page pair_index))
           else nth pair_index old_scratch 0%N).
    change ((f <$> seq 0 page_pair_count) !! i = Some (f i)).
    rewrite list_lookup_fmap.
    rewrite lookup_seq_lt.
    2: {
      exact Hi.
    }
    replace (0 + i)%nat with i by lia.
    reflexivity.
  Qed.

  Lemma init_leaf_scratch_model_zero page old_scratch :
    length old_scratch = page_pair_count ->
    init_leaf_scratch_model page 0 old_scratch = old_scratch.
  Proof.
    intro Hscratch.
    apply list_eq.
    intro i.
    destruct (lt_dec i page_pair_count) as [Hi | Hi].
    {
      rewrite init_leaf_scratch_model_lookup.
      2: {
        exact Hi.
      }
      rewrite bitmap_word_bit_testbit.
      rewrite N.bits_0.
      destruct
        (nth_lookup_or_length old_scratch i 0%N) as [Hlookup | Hlen].
      {
        rewrite Hlookup.
        reflexivity.
      }
      {
        lia.
      }
    }
    {
      rewrite (lookup_ge_None_2 old_scratch i).
      2: {
        lia.
      }
      rewrite
        (lookup_ge_None_2
           (init_leaf_scratch_model page 0 old_scratch) i).
      2: {
        rewrite init_leaf_scratch_model_length.
        lia.
      }
      reflexivity.
    }
  Qed.

  Lemma init_leaf_scratch_model_clear_lowbit_insert
      page bits scratch :
    bits <> 0%N ->
    (bits < 2 ^ 64)%N ->
    length scratch = page_pair_count ->
    init_leaf_scratch_model
      page (leaf_clear_lowbit bits)
      (<[ N.to_nat (countr_zero64 bits) :=
          leaf_pair_hash page (N.to_nat (countr_zero64 bits)) ]>
       scratch) =
    init_leaf_scratch_model page bits scratch.
  Proof.
    intros Hbits Hbits_bound Hscratch.
    pose proof
      (countr_zero64_nonzero_lt bits Hbits Hbits_bound) as Hidx_bound_N.
    assert
      (Hidx_bound :
        (N.to_nat (countr_zero64 bits) < page_pair_count)%nat).
    {
      unfold page_pair_count.
      lia.
    }
    apply list_eq.
    intro i.
    destruct (lt_dec i page_pair_count) as [Hi | Hi].
    {
      rewrite !init_leaf_scratch_model_lookup.
      2: {
        exact Hi.
      }
      2: {
        exact Hi.
      }
      rewrite bitmap_word_bit_clear_lowbit64.
      2: {
        exact Hbits.
      }
      2: {
        exact Hbits_bound.
      }
      destruct
        (N.eq_dec (N.of_nat i) (countr_zero64 bits))
        as [Heq | Hneq].
      {
        replace ((N.of_nat i =? countr_zero64 bits)%N) with true.
        2: {
          symmetry.
          apply N.eqb_eq.
          exact Heq.
        }
        assert (Hi_eq : i = N.to_nat (countr_zero64 bits)).
        {
          apply Nat2N.inj.
          rewrite N2Nat.id.
          exact Heq.
        }
        subst i.
        rewrite bitmap_word_bit_countr_zero64.
        2: {
          exact Hbits.
        }
        2: {
          exact Hbits_bound.
        }
        rewrite
          (nth_lookup_Some
             (<[ N.to_nat (countr_zero64 bits) :=
                 leaf_pair_hash
                   page (N.to_nat (countr_zero64 bits)) ]>
              scratch)
             (N.to_nat (countr_zero64 bits)) 0%N
             (leaf_pair_hash
                page (N.to_nat (countr_zero64 bits)))).
        {
          reflexivity.
        }
        {
          apply list_lookup_insert_eq.
          rewrite Hscratch.
          exact Hidx_bound.
        }
      }
      {
        replace ((N.of_nat i =? countr_zero64 bits)%N) with false.
        2: {
          symmetry.
          apply N.eqb_neq.
          exact Hneq.
        }
        destruct (bitmap_word_bit bits i).
        {
          reflexivity.
        }
        {
          rewrite !nth_lookup.
          rewrite list_lookup_insert_ne.
          {
            reflexivity.
          }
          {
            intro Hi_eq.
            apply Hneq.
            rewrite <- Hi_eq.
            rewrite N2Nat.id.
            reflexivity.
          }
        }
      }
    }
    {
      rewrite
        (lookup_ge_None_2
           (init_leaf_scratch_model
              page (leaf_clear_lowbit bits)
              (<[ N.to_nat (countr_zero64 bits) :=
                  leaf_pair_hash
                    page (N.to_nat (countr_zero64 bits)) ]>
               scratch)) i).
      2: {
        rewrite init_leaf_scratch_model_length.
        lia.
      }
      rewrite
        (lookup_ge_None_2
           (init_leaf_scratch_model page bits scratch) i).
      2: {
        rewrite init_leaf_scratch_model_length.
        lia.
      }
      reflexivity.
    }
  Qed.

  Lemma apply_leaf_hashes_to_scratch_loop_model
      page bits scratch fuel :
    (bits < 2 ^ 64)%N ->
    (N.to_nat (popcount64 bits) <= fuel)%nat ->
    length scratch = page_pair_count ->
    apply_leaf_hashes_to_scratch
      page scratch (leaf_loop_indices fuel bits) =
    init_leaf_scratch_model page bits scratch.
  Proof.
    revert bits scratch.
    induction fuel as [| fuel IH]; intros bits scratch Hbits_bound Hfuel Hscratch.
    {
      destruct (N.eq_dec bits 0%N) as [-> | Hbits].
      {
        cbn [leaf_loop_indices apply_leaf_hashes_to_scratch].
        symmetry.
        apply init_leaf_scratch_model_zero.
        exact Hscratch.
      }
      {
        pose proof
          (popcount64_nonzero bits Hbits Hbits_bound) as Hpop.
        lia.
      }
    }
    {
      cbn [leaf_loop_indices].
      destruct (N.eq_dec bits 0%N) as [-> | Hbits].
      {
        rewrite N.eqb_refl.
        cbn [apply_leaf_hashes_to_scratch].
        symmetry.
        apply init_leaf_scratch_model_zero.
        exact Hscratch.
      }
      {
        replace ((bits =? 0)%N) with false.
        2: {
          symmetry.
          apply N.eqb_neq.
          exact Hbits.
        }
        cbn [apply_leaf_hashes_to_scratch].
        rewrite IH.
        {
          apply init_leaf_scratch_model_clear_lowbit_insert;
            assumption.
        }
        {
          apply leaf_clear_lowbit_bound64.
          exact Hbits_bound.
        }
        {
          pose proof
            (popcount64_clear_lowbit bits Hbits Hbits_bound)
            as Hclear.
          pose proof (f_equal N.to_nat Hclear) as Hclear_nat.
          rewrite N2Nat.inj_add in Hclear_nat.
          change (N.to_nat 1) with 1%nat in Hclear_nat.
          lia.
        }
        {
          rewrite length_insert.
          exact Hscratch.
        }
      }
    }
  Qed.

  Lemma apply_leaf_hashes_to_scratch_done_model :
    forall page pair_bitmap old_scratch indices,
    (pair_bitmap < 2 ^ 64)%N ->
    leaf_indices pair_bitmap = indices ->
    length old_scratch = page_pair_count ->
    apply_leaf_hashes_to_scratch page old_scratch indices =
      init_leaf_scratch_model page pair_bitmap old_scratch.
  Proof.
    intros page pair_bitmap old_scratch indices Hbitmap Hindices Hscratch.
    subst indices.
    unfold leaf_indices.
    apply apply_leaf_hashes_to_scratch_loop_model.
    {
      exact Hbitmap.
    }
    {
      unfold page_pair_count.
      pose proof (popcount64_bound pair_bitmap) as Hpop.
      lia.
    }
    {
      exact Hscratch.
    }
  Qed.

  Opaque init_leaf_scratch_model.

  Lemma leaf_loop_state_bits_bound pair_bitmap seen bits :
    leaf_loop_state pair_bitmap seen bits ->
    (bits < 2 ^ 64)%N.
  Proof.
    intros [_ [_ [_ [_ Hbits]]]].
    exact Hbits.
  Qed.

  Lemma leaf_loop_state_bitmap_bound pair_bitmap seen bits :
    leaf_loop_state pair_bitmap seen bits ->
    (pair_bitmap < 2 ^ 64)%N.
  Proof.
    intros [_ [_ [_ [Hbitmap _]]]].
    exact Hbitmap.
  Qed.

  Opaque countr_zero64.

  Lemma leaf_loop_state_step pair_bitmap seen bits :
    leaf_loop_state pair_bitmap seen bits ->
    bits <> 0%N ->
    leaf_loop_state
      pair_bitmap
      (List.app seen [N.to_nat (countr_zero64 bits)])
      (leaf_clear_lowbit bits).
  Proof.
    intros [Hindices [Hseen_forall [Hpop [Hbitmap_bound Hbits_bound]]]]
      Hbits.
    pose proof
      (popcount64_nonzero bits Hbits Hbits_bound) as Hpop_pos.
    assert (Hpop_pos_nat : (0 < N.to_nat (popcount64 bits))%nat).
    {
      destruct (N.to_nat (popcount64 bits)) eqn:Hnat.
      {
        exfalso.
        rewrite <- N2Nat.inj_0 in Hnat.
        pose proof (N2Nat.inj _ _ Hnat) as Hzero.
        lia.
      }
      {
        lia.
      }
    }
    assert (Hseen_lt : (length seen < page_pair_count)%nat) by lia.
    set (fuel := (page_pair_count - length seen)%nat) in *.
    assert (Hfuel_pos : (0 < fuel)%nat).
    {
      subst fuel.
      lia.
    }
    destruct fuel as [| fuel'] eqn:Hfuel.
    {
      lia.
    }
    cbn [leaf_loop_indices] in Hindices.
    destruct (N.eqb bits 0) eqn:Hbits_eq.
    {
      apply N.eqb_eq in Hbits_eq.
      contradiction.
    }
    unfold leaf_loop_state.
    split.
    {
      rewrite Hindices.
      rewrite <- List.app_assoc.
      cbn [List.app].
      assert
        (Hfuel' :
          (page_pair_count -
           length (seen ++ [N.to_nat (countr_zero64 bits)]))%nat =
          fuel').
      {
        subst fuel.
        rewrite List.length_app.
        cbn [List.length].
        lia.
      }
      rewrite Hfuel'.
      reflexivity.
    }
    split.
    {
      apply List.Forall_app.
      split.
      {
        exact Hseen_forall.
      }
      {
        constructor.
        {
          pose proof
            (countr_zero64_nonzero_lt bits Hbits Hbits_bound) as Hcz.
          unfold page_pair_count.
          lia.
        }
        {
          constructor.
        }
      }
    }
    split.
    {
      pose proof
        (popcount64_clear_lowbit bits Hbits Hbits_bound)
        as Hclear_pop.
      pose proof (f_equal N.to_nat Hclear_pop) as Hclear_pop_nat.
      rewrite N2Nat.inj_add in Hclear_pop_nat.
      change (N.to_nat 1) with 1%nat in Hclear_pop_nat.
      rewrite List.length_app.
      cbn [List.length].
      lia.
    }
    split.
    {
      exact Hbitmap_bound.
    }
    {
      eapply N.le_lt_trans.
      {
        apply N.land_le_l.
      }
      {
        exact Hbits_bound.
      }
    }
  Qed.

  Lemma leaf_loop_indices_zero fuel :
    leaf_loop_indices fuel 0 = [].
  Proof.
    destruct fuel; reflexivity.
  Qed.

  Lemma leaf_loop_state_done pair_bitmap seen :
    leaf_loop_state pair_bitmap seen 0 ->
    leaf_indices pair_bitmap = seen.
  Proof.
    intros [Hseen _].
    unfold leaf_indices in Hseen.
    rewrite leaf_loop_indices_zero in Hseen.
    rewrite app_nil_r in Hseen.
    exact Hseen.
  Qed.

  Lemma leaf_loop_state_active_length_lt pair_bitmap seen bits :
    leaf_loop_state pair_bitmap seen bits ->
    bits <> 0%N ->
    (length seen < page_pair_count)%nat.
  Proof.
    intros [_ [_ [Hpop [_ Hbits_bound]]]] Hbits.
    pose proof
      (popcount64_nonzero bits Hbits Hbits_bound) as Hpop_pos.
    assert (Hpop_pos_nat : (0 < N.to_nat (popcount64 bits))%nat).
    {
      destruct (N.to_nat (popcount64 bits)) eqn:Hnat.
      {
        exfalso.
        rewrite <- N2Nat.inj_0 in Hnat.
        pose proof (N2Nat.inj _ _ Hnat) as Hzero.
        lia.
      }
      {
        lia.
      }
    }
    lia.
  Qed.

  #[local] Hint Resolve leaf_loop_state_init leaf_loop_state_step : pure.

  #[local] Hint Resolve
    wp_init_implicit_B_local
    wp.wp_init_initlist_struct_B
    wp_operand_initlist_default_B
    wp_init_default_array_B
    wp_init_bytes32_array_zero_local_B
    observeStoragePageLength_F
    observeStoragePageTypePtr_F
    leaf_index_arrayR_empty_pack_F
    type_ptr_reference_to_B_local
    type_ptr_elim_type_ptr_C
    type_ptr_elim_reference_to_C
    typed_sliceR_elim_type_ptr_C
    typed_sliceR_elim_reference_to_C
    UNSAFE_read_prim_cancel : sl_opacity.
  #[local] Hint Opaque
    StoragePageR ScratchR init_leaf_scratch_model
    leaf_index_arrayR leaf_inputs_arrayR
    leaf_indices leaf_loop_indices leaf_clear_lowbit
    leaf_loop_state : sl_opacity.
  Opaque
    exec_specs.bytes32_be_values_from
    exec_specs.bytes32_be_values
    exec_specs.evmc_bytes32_wordR
    exec_specs.bytes32R
    exec_specs.evmc_bytes32R.
  #[local] Hint Opaque
    exec_specs.bytes32_be_values_from
    exec_specs.bytes32_be_values
    exec_specs.evmc_bytes32_wordR
    exec_specs.bytes32R
    exec_specs.evmc_bytes32R : sl_opacity.
  Opaque
    uninitR_anyR_F
    primR_anyR_F
    primR_input_ptr_anyR_store_F
    input_ptr_arrayR_forget_store_F
    input_ptr_null_arrayR_forget_store_at_F
    use_wand_local_r_F
    const_input_ptr_array_type_ptr_erase_F
    at_sep_F
    offsetR_sep_F
    at_offsetR_F
    leaf_index_tail_head_F
    leaf_inputs_tail_head_F
    leaf_inputs_uninit_tail_head_F
    arrayR_read_cell_with_wand_F
    arrayR_update_cell_with_wand_F
    wp_destroy_leaf_hash_outputs64_B
    leaf_inputs_prefix_forget_F
    leaf_inputs_split_anyR_array_F
    input_ptr_typed_slice_cell_type_F
    wp_destroy_leaf_inputs_array_split_cleanup_local_B
    anyR_arrayLR_destroy_run_local_B
    leaf_index_prefix_forget_F
    leaf_index_arrayR_forget_F
    destroy_run_leaf_index_array_cleanup_local_B
    observeStoragePageTypePtr_F
    type_ptr_leaf_pair_block_valid_F
    observeLeafPairBlockValid_F
    StoragePageR_unpack_F
    StoragePageR_pack_B
    observeScratchRLength_F
    leaf_index_arrayR_empty_pack_F
    leaf_inputs_arrayR_empty_pack_F
    leaf_inputs_arrayR_zero_pack_F
    leaf_inputs_arrayR_blake3_unpack_F
    leaf_inputs_arrayR_blake3_pack_B
    leaf_inputs_arrayR_blake3_inputs_pack_F
    leaf_inputs_arrayR_blake3_inputs_unpack_F
    leaf_input_blocks_ptr_array_to_input_ptrs_F
    leaf_inputs_prefix_arrayR_blake3_pack_F
    leaf_inputs_prefix_arrayR_blake3_pack_for_page_F
    leaf_pair_block_rows_blake3_unpack_F
    leaf_pair_block_rows_blake3_pack_F
    leaf_hash_many_post_pack_F
    leaf_arrays_step_pack_F.

End with_Sigma.

#[global] Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R
  countr_zero64
  countr_zero_fuel
  popcount64
  popcount_fuel.

#[global] Hint Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R
  countr_zero64
  countr_zero_fuel
  popcount64
  popcount_fuel : sl_opacity.
