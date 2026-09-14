Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_specs.
Require Import monad.proofs.execproofs.mip8.blake3specs.
Require Import monad.proofs.libspecs.blake3.blake3_impl_h_specs.
Require monad.proofs.libspecs.blake3.model.

Import linearity.

#[local] Set Warnings "-non-reference-hint-using".

Local Transparent
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Definition uninitR_anyR_F ty q :=
    [FWD] (uninitR_anyR ty q).

  Lemma merge_block_any_rows_init (p : ptr) :
    p |-> arrayLR merge_block_row_ty 0 32
          (fun _ : unit =>
             arrayLR Tuchar 0 64
               (fun _ : unit => anyR Tuchar 1$m)
               (replicateN 64 ()))
          (replicateN 32 ())
    |--
    p |-> arrayLR merge_block_row_ty 0 32
          merge_block_rowR (replicateN 32 MergeBlockUninit).
  Proof using CU MODd Sigma.
    assert
      (Hrows :
        replicateN 32 MergeBlockUninit =
        map (fun _ : unit => MergeBlockUninit)
          (replicateN 32 ())).
    { vm_compute. reflexivity. }
    rewrite Hrows.
    rewrite
      (array_sliceR_fmap
         (ty := merge_block_row_ty)
         0 32 (replicateN 32 ())
         merge_block_rowR
         (fun _ : unit => MergeBlockUninit)).
    simpl.
    go.
  Qed.

  Definition merge_block_any_rows_init_F (p : ptr) :=
    [FWD] (merge_block_any_rows_init p).

  Lemma merge_block_uninit_rows_forget (p : ptr) :
    p |-> arrayLR merge_block_row_ty 0 32
          merge_block_rowR (replicateN 32 MergeBlockUninit)
    |--
    p |-> arrayLR merge_block_row_ty 0 32
          (fun _ : unit =>
             arrayLR Tuchar 0 64
               (fun _ : unit => anyR Tuchar 1$m)
               (replicateN 64 ()))
          (replicateN 32 ()).
  Proof using CU MODd Sigma.
    assert
      (Hrows :
        replicateN 32 MergeBlockUninit =
        map (fun _ : unit => MergeBlockUninit)
          (replicateN 32 ())).
    { vm_compute. reflexivity. }
    rewrite Hrows.
    rewrite
      (array_sliceR_fmap
         (ty := merge_block_row_ty)
         0 32 (replicateN 32 ())
         merge_block_rowR
         (fun _ : unit => MergeBlockUninit)).
    cbn [merge_block_rowR].
    go using uninitR_anyR_F.
  Qed.

  Definition merge_block_uninit_rows_forget_F (p : ptr) :=
    [FWD] (merge_block_uninit_rows_forget p).

  Lemma wp_destroy_uchar_anyR_cell_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    type_ptr Tuchar base
    ** base |-> anyR Tuchar 1$m
    ** Q
    |-- wp_destroy_val tu QM Tuchar base Q.
  Proof.
    intros tu base Q.
    go using destroy.anyR_wp_destroy_val_val.
  Qed.

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).

  Lemma ptr_o_sub_N_of_nat (ty : type) (base : ptr) (n : nat) :
    base .[ ty ! N.of_nat n ] = base .[ ty ! Z.of_nat n ].
  Proof using CU MODd Sigma.
    rewrite nat_N_Z.
    reflexivity.
  Qed.

  Lemma merge_index_arrayR_pack (base : ptr) indexes :
    (match indexes with
     | [] =>
         base |-> arrayLR Tuchar 0 32
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 32 ())
     | _ :: _ =>
         base |-> arrayLR Tuchar 0 (Z.of_nat (length indexes))
           (fun index : nat => ucharR 1$m (Z.of_nat index)) indexes
         ** base |-> arrayLR Tuchar (Z.of_nat (length indexes)) 32
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN
              (Z.to_N (32 - Z.of_nat (length indexes))) ())
     end)
    |-- base |-> merge_index_arrayR indexes.
  Proof using CU MODd Sigma.
    unfold merge_index_arrayR.
    go.
  Qed.

  Definition merge_index_arrayR_pack_F base indexes :=
    [FWD] (merge_index_arrayR_pack base indexes).

  Definition merge_index_arrayR_pack_B base indexes :=
    [BWD] (merge_index_arrayR_pack base indexes).

  Lemma merge_inputs_arrayR_pack
      (base blocksp : ptr) jobs :
    (match jobs with
     | [] =>
         base |-> arrayLR merge_input_ptr_ty 0 32
           (fun _ : unit => anyR merge_input_ptr_ty 1$m)
           (replicateN 32 ())
     | _ :: _ =>
         base |-> arrayLR merge_input_ptr_ty
           0 (Z.of_nat (length jobs))
           (fun job_index : nat =>
              primR merge_input_ptr_ty 1$m
                (Vptr (blocksp .[ merge_block_row_ty ! Z.of_nat job_index ])))
           (seq 0 (length jobs))
         ** base |-> arrayLR merge_input_ptr_ty
           (Z.of_nat (length jobs)) 32
           (fun _ : unit => anyR merge_input_ptr_ty 1$m)
           (replicateN
              (Z.to_N (32 - Z.of_nat (length jobs))) ())
     end)
    |-- base |-> merge_inputs_arrayR blocksp jobs.
  Proof using CU MODd Sigma.
    unfold merge_inputs_arrayR.
    go.
  Qed.

  Definition merge_inputs_arrayR_pack_F base blocksp jobs :=
    [FWD] (merge_inputs_arrayR_pack base blocksp jobs).

  Lemma merge_inputs_arrayR_null_pack
      (base blocksp : ptr) :
    base |-> arrayR merge_input_ptr_ty
      (primR merge_input_ptr_ty 1$m)
      (replicateN 32 (Vptr nullptr))
    |-- base |-> merge_inputs_arrayR blocksp [].
  Proof using CU MODd Sigma.
    unfold merge_inputs_arrayR.
    rewrite _at_as_Rep.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable _at_offsetR.
    rewrite (offset_ptr_sub_0 base merge_input_ptr_ty).
    {
      rewrite
        (array.arrayR_anyR_f
           (fun x : val => x) base 32
           merge_input_ptr_ty (replicateN 32 (Vptr nullptr)) 1$m
           ltac:(rewrite rwdb.length_replicateN; reflexivity)).
      go.
    }
    {
      vm_compute.
      eauto.
    }
  Qed.

  Definition merge_inputs_arrayR_null_pack_F base blocksp :=
    [FWD] (merge_inputs_arrayR_null_pack base blocksp).

  Definition merge_input_ptrs
      (blocksp : ptr) (jobs : list merge_job) : list ptr :=
    map
      (fun job_index : nat =>
         blocksp .[ merge_block_row_ty ! Z.of_nat job_index ])
      (seq 0 (length jobs)).

  Definition merge_input_blocks_from
      (blocksp : ptr) (start : nat) (jobs : list merge_job)
      : list blake3specs.blake3_input_block :=
    map
      (fun '(job_index, job) =>
         blake3specs.mk_blake3_input_block
           (blocksp .[ merge_block_row_ty ! Z.of_nat job_index ])
           (merge_job_input job))
      (combine (seq start (length jobs)) jobs).

  Definition merge_input_blocks
      (blocksp : ptr) (jobs : list merge_job)
      : list blake3specs.blake3_input_block :=
    merge_input_blocks_from blocksp 0 jobs.

  Lemma merge_input_ptrs_length blocksp jobs :
    length (merge_input_ptrs blocksp jobs) = length jobs.
  Proof using CU MODd Sigma.
    unfold merge_input_ptrs.
    rewrite length_map.
    apply List.length_seq.
  Qed.

  Lemma merge_input_blocks_from_ptrs blocksp start jobs :
    map blake3specs.blake3_input_block_ptr
      (merge_input_blocks_from blocksp start jobs) =
    map
      (fun job_index : nat =>
         blocksp .[ merge_block_row_ty ! Z.of_nat job_index ])
      (seq start (length jobs)).
  Proof using CU MODd Sigma.
    revert start.
    induction jobs as [| job rest IH]; intro start.
    {
      reflexivity.
    }
    {
      simpl.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma merge_input_blocks_from_length blocksp start jobs :
    length (merge_input_blocks_from blocksp start jobs) =
    length jobs.
  Proof using CU MODd Sigma.
    revert start.
    induction jobs as [| job rest IH]; intro start.
    {
      reflexivity.
    }
    {
      simpl.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma merge_input_blocks_length blocksp jobs :
    length (merge_input_blocks blocksp jobs) = length jobs.
  Proof using CU MODd Sigma.
    unfold merge_input_blocks.
    apply merge_input_blocks_from_length.
  Qed.

  Lemma combine_seq_jobs_length start (jobs : list merge_job) :
    length (combine (seq start (length jobs)) jobs) =
    length jobs.
  Proof using CU MODd Sigma.
    revert start.
    induction jobs as [| job rest IH]; intro start.
    {
      reflexivity.
    }
    {
      simpl.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma merge_input_blocks_ptrs blocksp jobs :
    map blake3specs.blake3_input_block_ptr
      (merge_input_blocks blocksp jobs) =
    merge_input_ptrs blocksp jobs.
  Proof using CU MODd Sigma.
    unfold merge_input_blocks, merge_input_ptrs.
    apply merge_input_blocks_from_ptrs.
  Qed.

  Lemma merge_input_blocks_from_data blocksp start jobs :
    map blake3specs.blake3_input_block_data
      (merge_input_blocks_from blocksp start jobs) =
    map merge_job_input jobs.
  Proof using CU MODd Sigma.
    revert start.
    induction jobs as [| job rest IH]; intro start.
    {
      reflexivity.
    }
    {
      simpl.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma merge_input_blocks_data blocksp jobs :
    map blake3specs.blake3_input_block_data
      (merge_input_blocks blocksp jobs) =
    map merge_job_input jobs.
  Proof using CU MODd Sigma.
    unfold merge_input_blocks.
    apply merge_input_blocks_from_data.
  Qed.

  Lemma merge_input_ptr_tail_from
      (base : ptr) (start n : nat) :
    map
      (fun job_index : nat =>
         base .[ merge_block_row_ty ! Z.of_nat (start + job_index) ])
      (seq 1 n) =
    map
      (fun job_index : nat =>
         base .[ merge_block_row_ty ! Z.of_nat (S start + job_index) ])
      (seq 0 n).
  Proof using CU MODd Sigma.
    rewrite <- (seq_shift n 0).
    rewrite List.map_map.
    apply List.map_ext.
    intro index.
    replace (start + S index)%nat
      with (S start + index)%nat by lia.
    reflexivity.
  Qed.

  Lemma merge_inputs_arrayR_blake3_unpack
      (base blocksp : ptr) (jobs : list merge_job) :
    base |-> merge_inputs_arrayR blocksp jobs |--
    base |-> arrayLR merge_input_ptr_ty
      (Z.of_nat (length jobs)) 32
      (fun _ : unit => anyR merge_input_ptr_ty 1$m)
      (replicateN
         (Z.to_N (32 - Z.of_nat (length jobs))) ())
    ** base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun inputp : ptr =>
         primR merge_input_ptr_ty 1$m (Vptr inputp))
      (merge_input_ptrs blocksp jobs).
  Proof using CU MODd Sigma.
    unfold merge_inputs_arrayR, merge_input_ptrs.
    destruct jobs as [| job rest].
    {
      simpl.
      go.
    }
    {
      simpl length.
      rewrite
        (array_sliceR_fmap
           (ty := merge_input_ptr_ty)
           0 (Z.of_nat (S (length rest))) (seq 0 (S (length rest)))
           (fun inputp : ptr =>
              primR merge_input_ptr_ty 1$m (Vptr inputp))
           (fun job_index : nat =>
              blocksp .[ merge_block_row_ty ! Z.of_nat job_index ])).
      go.
    }
  Qed.

  Definition merge_inputs_arrayR_blake3_unpack_F base blocksp jobs :=
    [FWD] (merge_inputs_arrayR_blake3_unpack base blocksp jobs).

  Lemma merge_inputs_arrayR_blake3_pack
      (base blocksp : ptr) (jobs : list merge_job) :
    base |-> arrayLR merge_input_ptr_ty
      (Z.of_nat (length jobs)) 32
      (fun _ : unit => anyR merge_input_ptr_ty 1$m)
      (replicateN
         (Z.to_N (32 - Z.of_nat (length jobs))) ())
    ** base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun inputp : ptr =>
         primR merge_input_ptr_ty 1$m (Vptr inputp))
      (merge_input_ptrs blocksp jobs)
    |-- base |-> merge_inputs_arrayR blocksp jobs.
  Proof using CU MODd Sigma.
    unfold merge_inputs_arrayR, merge_input_ptrs.
    destruct jobs as [| job rest].
    {
      simpl.
      go.
    }
    {
      simpl length.
      rewrite
        (array_sliceR_fmap
           (ty := merge_input_ptr_ty)
           0 (Z.of_nat (S (length rest))) (seq 0 (S (length rest)))
           (fun inputp : ptr =>
              primR merge_input_ptr_ty 1$m (Vptr inputp))
           (fun job_index : nat =>
              blocksp .[ merge_block_row_ty ! Z.of_nat job_index ])).
      go.
    }
  Qed.

  Definition merge_inputs_arrayR_blake3_pack_B base blocksp jobs :=
    [BWD] (merge_inputs_arrayR_blake3_pack base blocksp jobs).

  Definition merge_inputs_arrayR_blake3_pack_F base blocksp jobs :=
    [FWD] (merge_inputs_arrayR_blake3_pack base blocksp jobs).

  Lemma merge_inputs_arrayR_ptr_pack
      (base blocksp : ptr) (jobs : list merge_job) :
    base |-> arrayLR merge_input_ptr_ty
      (Z.of_nat (length jobs)) 32
      (fun _ : unit => anyR merge_input_ptr_ty 1$m)
      (replicateN
         (Z.to_N (32 - Z.of_nat (length jobs))) ())
    ** base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun inputp : ptr =>
         ptrR<"unsigned char"> 1$m inputp)
      (merge_input_ptrs blocksp jobs)
    |-- base |-> merge_inputs_arrayR blocksp jobs.
  Proof using CU MODd Sigma.
    unfold merge_inputs_arrayR, merge_input_ptrs.
    destruct jobs as [| job rest].
    {
      simpl.
      go.
    }
    simpl length.
    rewrite
      (array_sliceR_fmap
         (ty := merge_input_ptr_ty)
         0 (Z.of_nat (S (length rest))) (seq 0 (S (length rest)))
         (fun inputp : ptr =>
            ptrR<"unsigned char"> 1$m inputp)
         (fun job_index : nat =>
            blocksp .[ merge_block_row_ty ! Z.of_nat job_index ])).
    go.
  Qed.

  Definition merge_inputs_arrayR_ptr_pack_F base blocksp jobs :=
    [FWD] (merge_inputs_arrayR_ptr_pack base blocksp jobs).

  Lemma merge_inputs_arrayR_blake3_inputs_pack
      (base blocksp : ptr) (jobs : list merge_job) :
    base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun inputp : ptr =>
         primR merge_input_ptr_ty 1$m (Vptr inputp))
      (merge_input_ptrs blocksp jobs)
    ** blake3specs.Blake3InputBlocksDataR 1
      (merge_input_blocks blocksp jobs)
    |-- base |-> blake3specs.Blake3InputBlocksR
         false 1 1
         (merge_input_blocks blocksp jobs).
  Proof using CU MODd Sigma.
    unfold blake3specs.Blake3InputBlocksR,
      blake3_impl_h_specs.Blake3InputBlocksR.
    rewrite _at_as_Rep.
    rewrite merge_input_blocks_length.
    rewrite <- merge_input_blocks_ptrs.
    rewrite <-
      (array_sliceR_fmap
         (ty := merge_input_ptr_ty)
         0 (Z.of_nat (length jobs))
         (merge_input_blocks blocksp jobs)
         (fun inputp : ptr =>
            primR merge_input_ptr_ty 1$m (Vptr inputp))
         blake3specs.blake3_input_block_ptr).
    go.
  Qed.

  Definition merge_inputs_arrayR_blake3_inputs_pack_F
      base blocksp jobs :=
    [FWD] (merge_inputs_arrayR_blake3_inputs_pack
             base blocksp jobs).

  Lemma merge_inputs_arrayR_blake3_inputs_unpack
      (base blocksp : ptr) (jobs : list merge_job) :
    base |-> blake3specs.Blake3InputBlocksR
         false 1 1
         (merge_input_blocks blocksp jobs)
    |--
    base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun inputp : ptr =>
         primR merge_input_ptr_ty 1$m (Vptr inputp))
      (merge_input_ptrs blocksp jobs)
    ** blake3specs.Blake3InputBlocksDataR 1
      (merge_input_blocks blocksp jobs).
  Proof using CU MODd Sigma.
    unfold blake3specs.Blake3InputBlocksR,
      blake3_impl_h_specs.Blake3InputBlocksR.
    rewrite _at_as_Rep.
    rewrite merge_input_blocks_length.
    rewrite <- merge_input_blocks_ptrs.
    rewrite <-
      (array_sliceR_fmap
         (ty := merge_input_ptr_ty)
         0 (Z.of_nat (length jobs))
         (merge_input_blocks blocksp jobs)
         (fun inputp : ptr =>
            primR merge_input_ptr_ty 1$m (Vptr inputp))
         blake3specs.blake3_input_block_ptr).
    go.
  Qed.

  Definition merge_inputs_arrayR_blake3_inputs_unpack_F
      base blocksp jobs :=
    [FWD] (merge_inputs_arrayR_blake3_inputs_unpack
             base blocksp jobs).

  Lemma merge_input_blocks_ptr_array_to_input_ptrs
      (base blocksp : ptr) (jobs : list merge_job) :
    base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun input : blake3specs.blake3_input_block =>
         ptrR<"unsigned char"> 1$m
           (blake3specs.blake3_input_block_ptr input))
      (merge_input_blocks blocksp jobs)
    |--
    base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun inputp : ptr =>
         ptrR<"unsigned char"> 1$m inputp)
      (merge_input_ptrs blocksp jobs).
  Proof using CU MODd Sigma.
    rewrite <- merge_input_blocks_ptrs.
    rewrite <-
      (array_sliceR_fmap
         (ty := merge_input_ptr_ty)
         0 (Z.of_nat (length jobs))
         (merge_input_blocks blocksp jobs)
         (fun inputp : ptr =>
            ptrR<"unsigned char"> 1$m inputp)
         blake3specs.blake3_input_block_ptr).
    go.
  Qed.

  Definition merge_input_blocks_ptr_array_to_input_ptrs_F
      base blocksp jobs :=
    [FWD] (merge_input_blocks_ptr_array_to_input_ptrs
             base blocksp jobs).

  (* Retain slice validity before automation consumes an empty slice. *)
  #[local] Hint Resolve obs_typed_slice_array_sliceR_F | 0 : sl_opacity.

  Lemma merge_block_prefix_blake3_blocks_from
      (base : ptr) start jobs :
    base |-> arrayLR merge_block_row_ty
      (Z.of_nat start)
      (Z.of_nat (start + length jobs))
      (fun job => blake3specs.Blake3BlockR 1
        (merge_job_input job))
      jobs
    |--
    base |-> typed_sliceR merge_block_row_ty
      (Z.of_nat start) (Z.of_nat (start + length jobs))
    **
    blake3specs.Blake3InputBlocksDataR 1
      (merge_input_blocks_from base start jobs).
  Proof using CU MODd Sigma.
    revert start base.
    induction jobs as [| job rest IH]; intros start base.
    {
      cbn.
      go using _at_arrayR_nil_F.
    }
    {
      cbn [length map seq].
      replace (start + S (length rest))%nat
        with (S start + length rest)%nat by lia.
      pose (IH_F :=
        [FWD] (IH (S start) base)).
      cbn [blake3specs.Blake3InputBlocksDataR
           blake3_impl_h_specs.Blake3InputBlocksDataR
           merge_input_blocks_from].
      go using obs_typed_slice_array_sliceR_F.
      replace (Z.of_nat start + 1)%Z
        with (Z.of_nat (S start)) by lia.
      go using IH_F, type_ptr_valid.
      all: replace (Z.of_nat start + 1)%Z
        with (Z.of_nat (S start)) by lia.
      all: replace (Z.of_nat (S (start + length rest)))
        with (Z.of_nat (S start + length rest)) by lia.
      all: go using IH_F, type_ptr_valid.
    }
  Qed.

  Definition merge_block_prefix_blake3_blocks_F base jobs :=
    [FWD] (merge_block_prefix_blake3_blocks_from base 0 jobs).

  Lemma merge_block_prefix_blake3_blocks_pack_from
      (base : ptr) slice_start slice_end start jobs :
    (slice_start <= Z.of_nat start /\
     Z.of_nat (start + length jobs) <= slice_end)%Z ->
    base |-> typed_sliceR merge_block_row_ty slice_start slice_end
    **
    blake3specs.Blake3InputBlocksDataR 1
      (merge_input_blocks_from base start jobs)
    |--
    base |-> arrayLR merge_block_row_ty
      (Z.of_nat start)
      (Z.of_nat (start + length jobs))
      (fun job => blake3specs.Blake3BlockR 1
        (merge_job_input job))
      jobs.
  Proof using CU MODd Sigma.
    revert start base.
    induction jobs as [| job rest IH]; intros start base Hslice.
    {
      cbn.
      go using _at_arrayR_nil_B.
    }
    {
      cbn [length map seq].
      replace (start + S (length rest))%nat
        with (S start + length rest)%nat by lia.
      destruct Hslice as [Hslice_lo Hslice_hi].
      assert
        (Htail :
          (slice_start <= Z.of_nat (S start) /\
           Z.of_nat (S start + length rest) <= slice_end)%Z).
      {
        split.
        {
          lia.
        }
        {
          cbn in Hslice_hi.
          lia.
        }
      }
      pose (IH_F :=
        [FWD] (IH (S start) base Htail)).
      cbn [blake3specs.Blake3InputBlocksDataR
           blake3_impl_h_specs.Blake3InputBlocksDataR
           merge_input_blocks_from].
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
    }
  Qed.

  Definition merge_block_prefix_blake3_blocks_pack_F base jobs
      (Hjobs : (length jobs <= 32)%nat) :=
    [FWD] (merge_block_prefix_blake3_blocks_pack_from
             base 0 32 0 jobs ltac:(lia)).

  Lemma merge_block_rows_blake3_unpack
      (base : ptr) jobs :
    (length jobs <= 32)%nat ->
    base |-> arrayLR merge_block_row_ty 0 32 merge_block_rowR
      (map (fun job => MergeBlockFull (merge_job_input job)) jobs ++
       replicateN
         (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit)
    |--
    base |-> typed_sliceR merge_block_row_ty 0 32
    **
    blake3specs.Blake3InputBlocksDataR 1
      (merge_input_blocks base jobs)
    ** base |-> arrayLR merge_block_row_ty
      (Z.of_nat (length jobs)) 32 merge_block_rowR
      (replicateN
         (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit).
  Proof using CU MODd Sigma.
    intro Hjobs.
    unfold merge_input_blocks.
    rewrite
      (@array_sliceR_app'
         _ _ _ _ merge_block_row merge_block_row_ty base
         0 (Z.of_nat (length jobs)) 32
         merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs)
         (replicateN
            (Z.to_N (32 - Z.of_nat (length jobs)))
            MergeBlockUninit)).
    all: try rewrite lengthN_map.
    all: try rewrite lengthN_replicateN.
    all: try unfold lengthN.
    all: try lia.
    rewrite
      (array_sliceR_fmap
         (ty := merge_block_row_ty)
         0 (Z.of_nat (length jobs)) jobs
         merge_block_rowR
         (fun job => MergeBlockFull (merge_job_input job))).
    cbn [merge_block_rowR].
    go using merge_block_prefix_blake3_blocks_F.
  Qed.

  Definition merge_block_rows_blake3_unpack_F base jobs :=
    [FWD] (merge_block_rows_blake3_unpack base jobs).

  Lemma merge_block_rows_blake3_pack
      (base : ptr) jobs :
    (length jobs <= 32)%nat ->
    base |-> typed_sliceR merge_block_row_ty 0 32
    **
    blake3specs.Blake3InputBlocksDataR 1
      (merge_input_blocks base jobs)
    ** base |-> arrayLR merge_block_row_ty
      (Z.of_nat (length jobs)) 32 merge_block_rowR
      (replicateN
         (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit)
    |--
    base |-> arrayLR merge_block_row_ty 0 32 merge_block_rowR
      (map (fun job => MergeBlockFull (merge_job_input job)) jobs ++
       replicateN
         (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit).
  Proof using CU MODd Sigma.
    intro Hjobs.
    unfold merge_input_blocks.
    rewrite
      (@array_sliceR_app'
         _ _ _ _ merge_block_row merge_block_row_ty base
         0 (Z.of_nat (length jobs)) 32
         merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs)
         (replicateN
            (Z.to_N (32 - Z.of_nat (length jobs)))
            MergeBlockUninit)).
    all: try rewrite lengthN_map.
    all: try rewrite lengthN_replicateN.
    all: try unfold lengthN.
    all: try lia.
    rewrite
      (array_sliceR_fmap
         (ty := merge_block_row_ty)
         0 (Z.of_nat (length jobs)) jobs
         merge_block_rowR
         (fun job => MergeBlockFull (merge_job_input job))).
    cbn [merge_block_rowR].
    go using
      (merge_block_prefix_blake3_blocks_pack_F base jobs Hjobs).
  Qed.

  Definition merge_block_rows_blake3_pack_F base jobs :=
    [FWD] (merge_block_rows_blake3_pack base jobs).

  Lemma merge_block_rows_pack (base : ptr) jobs :
    base |-> arrayLR merge_block_row_ty 0 32 merge_block_rowR
      (map (fun job => MergeBlockFull (merge_job_input job)) jobs ++
       replicateN
         (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit)
    |--
    base |-> arrayLR merge_block_row_ty 0 32 merge_block_rowR
      (merge_block_rows jobs).
  Proof using CU MODd Sigma.
    unfold merge_block_rows.
    go.
  Qed.

  Definition merge_block_rows_pack_F base jobs :=
    [FWD] (merge_block_rows_pack base jobs).

  Lemma merge_plan_arraysR_pack
      leftsp rightsp blocksp inputsp jobs :
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** leftsp |-> merge_index_arrayR (map merge_job_left_index jobs)
    ** rightsp |-> merge_index_arrayR (map merge_job_right_index jobs)
    ** blocksp |-> arrayLR merge_block_row_ty 0 32
         merge_block_rowR (merge_block_rows jobs)
    ** inputsp |-> merge_inputs_arrayR blocksp jobs
    |--
    merge_plan_arraysR leftsp rightsp blocksp inputsp jobs.
  Proof using CU MODd Sigma.
    unfold merge_plan_arraysR.
    go.
  Qed.

  Definition merge_plan_arraysR_pack_F
      leftsp rightsp blocksp inputsp jobs :=
    [FWD] (merge_plan_arraysR_pack
             leftsp rightsp blocksp inputsp jobs).

  Definition merge_plan_arraysR_pack_B
      leftsp rightsp blocksp inputsp jobs :=
    [BWD] (merge_plan_arraysR_pack
             leftsp rightsp blocksp inputsp jobs).

  Lemma merge_plan_arraysR_expanded_pack
      leftsp rightsp blocksp inputsp jobs :
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** (match map merge_job_left_index jobs with
        | [] =>
            leftsp |-> arrayLR Tuchar 0 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            leftsp |-> arrayLR Tuchar
              0 (Z.of_nat (length (map merge_job_left_index jobs)))
              (fun index : nat => ucharR 1$m (Z.of_nat index))
              (map merge_job_left_index jobs)
            ** leftsp |-> arrayLR Tuchar
              (Z.of_nat (length (map merge_job_left_index jobs))) 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN
                 (Z.to_N
                    (32 - Z.of_nat
                       (length (map merge_job_left_index jobs)))) ())
        end)
    ** (match map merge_job_right_index jobs with
        | [] =>
            rightsp |-> arrayLR Tuchar 0 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            rightsp |-> arrayLR Tuchar
              0 (Z.of_nat (length (map merge_job_right_index jobs)))
              (fun index : nat => ucharR 1$m (Z.of_nat index))
              (map merge_job_right_index jobs)
            ** rightsp |-> arrayLR Tuchar
              (Z.of_nat (length (map merge_job_right_index jobs))) 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN
                 (Z.to_N
                    (32 - Z.of_nat
                       (length (map merge_job_right_index jobs)))) ())
        end)
    ** blocksp |-> arrayLR merge_block_row_ty 0 32
         merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs ++
          replicateN
            (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit)
    ** (match jobs with
        | [] =>
            inputsp |-> arrayLR merge_input_ptr_ty 0 32
              (fun _ : unit => anyR merge_input_ptr_ty 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            inputsp |-> arrayLR merge_input_ptr_ty
              0 (Z.of_nat (length jobs))
              (fun job_index : nat =>
                 primR merge_input_ptr_ty 1$m
                   (Vptr
                      (blocksp .[ merge_block_row_ty !
                                  Z.of_nat job_index ])))
              (seq 0 (length jobs))
            ** inputsp |-> arrayLR merge_input_ptr_ty
              (Z.of_nat (length jobs)) 32
              (fun _ : unit => anyR merge_input_ptr_ty 1$m)
              (replicateN
                 (Z.to_N (32 - Z.of_nat (length jobs))) ())
        end)
    |--
    merge_plan_arraysR leftsp rightsp blocksp inputsp jobs.
  Proof using CU MODd Sigma.
    unfold merge_plan_arraysR, merge_index_arrayR, merge_inputs_arrayR,
      merge_block_rows.
    go.
  Qed.

  Definition merge_plan_arraysR_expanded_pack_F
      leftsp rightsp blocksp inputsp jobs :=
    [FWD] (merge_plan_arraysR_expanded_pack
             leftsp rightsp blocksp inputsp jobs).

  Lemma merge_plan_arraysR_empty_pack
      leftsp rightsp blocksp inputsp :
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** leftsp |-> arrayLR Tuchar 0 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateN 32 ())
    ** rightsp |-> arrayLR Tuchar 0 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateN 32 ())
    ** blocksp |-> arrayLR merge_block_row_ty 0 32
         merge_block_rowR
         (replicateN 32 MergeBlockUninit)
    ** inputsp |-> arrayLR merge_input_ptr_ty 0 32
         (fun _ : unit => anyR merge_input_ptr_ty 1$m)
         (replicateN 32 ())
    |--
    merge_plan_arraysR leftsp rightsp blocksp inputsp [].
  Proof using CU MODd Sigma.
    unfold merge_plan_arraysR, merge_index_arrayR, merge_inputs_arrayR,
      merge_block_rows.
    go.
  Qed.

  Definition merge_plan_arraysR_empty_pack_F
      leftsp rightsp blocksp inputsp :=
    [FWD] (merge_plan_arraysR_empty_pack
             leftsp rightsp blocksp inputsp).

  Lemma merge_plan_arraysR_length_map_pack
      leftsp rightsp blocksp inputsp jobs :
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** (match map merge_job_left_index jobs with
        | [] =>
            leftsp |-> arrayLR Tuchar 0 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            leftsp |-> arrayLR Tuchar
              0 (Z.of_nat (length jobs))
              (fun index : nat => ucharR 1$m (Z.of_nat index))
              (map merge_job_left_index jobs)
            ** leftsp |-> arrayLR Tuchar
              (Z.of_nat (length jobs)) 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN
                 (Z.to_N (32 - Z.of_nat (length jobs))) ())
        end)
    ** (match map merge_job_right_index jobs with
        | [] =>
            rightsp |-> arrayLR Tuchar 0 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            rightsp |-> arrayLR Tuchar
              0 (Z.of_nat (length jobs))
              (fun index : nat => ucharR 1$m (Z.of_nat index))
              (map merge_job_right_index jobs)
            ** rightsp |-> arrayLR Tuchar
              (Z.of_nat (length jobs)) 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN
                 (Z.to_N (32 - Z.of_nat (length jobs))) ())
        end)
    ** blocksp |-> arrayLR merge_block_row_ty 0 32
         merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs ++
          replicateN
            (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit)
    ** inputsp |-> merge_inputs_arrayR blocksp jobs
    |--
    merge_plan_arraysR leftsp rightsp blocksp inputsp jobs.
  Proof.
    unfold merge_plan_arraysR, merge_index_arrayR, merge_block_rows.
    rewrite !List.length_map.
    go.
  Qed.

  Definition merge_plan_arraysR_length_map_pack_F
      leftsp rightsp blocksp inputsp jobs :=
    [FWD] (merge_plan_arraysR_length_map_pack
             leftsp rightsp blocksp inputsp jobs).

  Lemma merge_plan_arraysR_expanded_unpack
      leftsp rightsp blocksp inputsp jobs :
    merge_plan_arraysR leftsp rightsp blocksp inputsp jobs
    |--
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** (match map merge_job_left_index jobs with
        | [] =>
            leftsp |-> arrayLR Tuchar 0 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            leftsp |-> arrayLR Tuchar
              0 (Z.of_nat (length (map merge_job_left_index jobs)))
              (fun index : nat => ucharR 1$m (Z.of_nat index))
              (map merge_job_left_index jobs)
            ** leftsp |-> arrayLR Tuchar
              (Z.of_nat (length (map merge_job_left_index jobs))) 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN
                 (Z.to_N
                    (32 - Z.of_nat
                       (length (map merge_job_left_index jobs)))) ())
        end)
    ** (match map merge_job_right_index jobs with
        | [] =>
            rightsp |-> arrayLR Tuchar 0 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            rightsp |-> arrayLR Tuchar
              0 (Z.of_nat (length (map merge_job_right_index jobs)))
              (fun index : nat => ucharR 1$m (Z.of_nat index))
              (map merge_job_right_index jobs)
            ** rightsp |-> arrayLR Tuchar
              (Z.of_nat (length (map merge_job_right_index jobs))) 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN
                 (Z.to_N
                    (32 - Z.of_nat
                       (length (map merge_job_right_index jobs)))) ())
        end)
    ** blocksp |-> arrayLR merge_block_row_ty 0 32
         merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs ++
          replicateN
            (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit)
    ** (match jobs with
        | [] =>
            inputsp |-> arrayLR merge_input_ptr_ty 0 32
              (fun _ : unit => anyR merge_input_ptr_ty 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            inputsp |-> arrayLR merge_input_ptr_ty
              0 (Z.of_nat (length jobs))
              (fun job_index : nat =>
                 primR merge_input_ptr_ty 1$m
                   (Vptr
                      (blocksp .[ merge_block_row_ty !
                                  Z.of_nat job_index ])))
              (seq 0 (length jobs))
            ** inputsp |-> arrayLR merge_input_ptr_ty
              (Z.of_nat (length jobs)) 32
              (fun _ : unit => anyR merge_input_ptr_ty 1$m)
              (replicateN
                 (Z.to_N (32 - Z.of_nat (length jobs))) ())
        end).
  Proof.
    unfold merge_plan_arraysR, merge_index_arrayR, merge_inputs_arrayR,
      merge_block_rows.
    go.
  Qed.

  Definition merge_plan_arraysR_expanded_unpack_F
      leftsp rightsp blocksp inputsp jobs :=
    [FWD] (merge_plan_arraysR_expanded_unpack
             leftsp rightsp blocksp inputsp jobs).

  Lemma merge_hash_outputs_replicate32_length jobs :
    (length jobs <= 32)%nat ->
    length
      (merge_hash_outputs jobs (replicateN 32 0%N)) =
    N.to_nat 32.
  Proof.
    intros Hjobs.
    unfold merge_hash_outputs, blake3_hash_many_outputs.
    rewrite List.length_app.
    repeat rewrite length_map.
    rewrite length_skipn.
    change (length (replicateN 32 0%N)) with 32%nat.
    change (N.to_nat 32) with 32%nat.
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

  Fixpoint merge_bytes32_zero_cells_from
      (base : ptr) (start count : nat) : mpred :=
    match count with
    | O => □ valid_ptr (base .[ bytes32_ty ! Z.of_nat start ])
    | S count' =>
        base .[ bytes32_ty ! Z.of_nat start ]
          |-> exec_specs.bytes32R 1 0
        ** merge_bytes32_zero_cells_from base (S start) count'
    end.

  Lemma merge_bytes32_zero_cells_from_pack base start count :
    merge_bytes32_zero_cells_from base start count |--
    base .[ bytes32_ty ! Z.of_nat start ]
      |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
            (replicate count 0%N).
  Proof using CU MODd Sigma.
    revert base start.
    induction count as [| count IH]; intros base start.
    {
      cbn [merge_bytes32_zero_cells_from replicate].
      go using _at_arrayR_nil_B.
    }
    cbn [merge_bytes32_zero_cells_from replicate].
    pose (IH_F := [FWD] (IH base (S start))).
    go using _at_arrayR_cons_B, IH_F.
    repeat rewrite o_sub_sub.
    replace (Z.of_nat start + 1)%Z
      with (Z.of_nat (S start)) by lia.
    go using IH_F.
  Qed.

  Lemma merge_output_words32_zero_pack base :
    merge_bytes32_zero_cells_from base 0 32 |--
    base |-> blake3specs.Blake3OutputWordsR 1 (replicateN 32 0%N).
  Proof using CU MODd Sigma.
    unfold blake3specs.Blake3OutputWordsR.
    change (replicateN 32 0%N) with (replicate 32 0%N).
    rewrite -{2}(offset_ptr_sub_0 base bytes32_ty).
    2: {
      apply has_size.
      exact _.
    }
    exact (merge_bytes32_zero_cells_from_pack base 0 32).
  Qed.

  Lemma merge_output_words32_zero_pack_cells base :
    type_ptr bytes32_ty (base .[ bytes32_ty ! 31 ])
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
    |--
    base |-> blake3specs.Blake3OutputWordsR 1 (replicateN 32 0%N).
  Proof using CU MODd Sigma.
    etrans.
    2: {
      exact (merge_output_words32_zero_pack base).
    }
    cbn [merge_bytes32_zero_cells_from].
    go using type_ptr_valid_plus_one_C.
  Qed.

  Definition merge_output_words32_zero_pack_cells_F base :=
    [FWD] (merge_output_words32_zero_pack_cells base).

  Lemma merge_hash_outputs_from_call_params jobs :
    blake3_hash_many_outputs_from_params
      (blake3_hash_many_call_params
         model.blake3_iv_words 0 false 0 1 2)
      (map merge_job_input jobs) =
    blake3_hash_many_outputs blake3model.merge_mode
      (map merge_job_input jobs).
  Proof.
    unfold blake3specs.blake3_hash_many_outputs,
      blake3_hash_many_outputs.
    rewrite blake3_hash_many_call_params_merge.
    reflexivity.
  Qed.

  Lemma merge_hash_outputs_length jobs :
    length
      (blake3_hash_many_outputs blake3model.merge_mode
         (map merge_job_input jobs)) =
    length jobs.
  Proof.
    unfold blake3_hash_many_outputs,
      blake3_hash_many_outputs_from_params.
    rewrite !List.length_map.
    reflexivity.
  Qed.

  Definition Blake3ConstKeyWordsR_pack_iv_F p q :=
    [FWD]
      (blake3_impl_h_specs.Blake3ConstKeyWordsR_pack
         p q model.blake3_iv_words ltac:(vm_compute; reflexivity)).

  Lemma merge_hash_many_post_pack
      qiv (leftsp rightsp blocksp inputsp flat_outp : ptr)
      jobs old_outputs :
    (length jobs <= 32)%nat ->
    List.Forall (fun x => (x < 2 ^ 256)%N) old_outputs ->
    _global "IV"
      |-> blake3specs.Blake3ConstKeyWordsR
            qiv model.blake3_iv_words
    ** type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** (match map merge_job_left_index jobs with
        | [] =>
            leftsp |-> arrayLR Tuchar 0 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            leftsp |-> arrayLR Tuchar
              0 (Z.of_nat (length jobs))
              (fun index : nat => ucharR 1$m (Z.of_nat index))
              (map merge_job_left_index jobs)
            ** leftsp |-> arrayLR Tuchar
              (Z.of_nat (length jobs)) 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN
                 (Z.to_N (32 - Z.of_nat (length jobs))) ())
        end)
    ** (match map merge_job_right_index jobs with
        | [] =>
            rightsp |-> arrayLR Tuchar 0 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 32 ())
        | _ :: _ =>
            rightsp |-> arrayLR Tuchar
              0 (Z.of_nat (length jobs))
              (fun index : nat => ucharR 1$m (Z.of_nat index))
              (map merge_job_right_index jobs)
            ** rightsp |-> arrayLR Tuchar
              (Z.of_nat (length jobs)) 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN
                 (Z.to_N (32 - Z.of_nat (length jobs))) ())
        end)
    ** blocksp |-> arrayLR merge_block_row_ty 0 32
         merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs ++
          replicateN
            (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit)
    ** inputsp |-> arrayLR merge_input_ptr_ty
         0 (Z.of_nat (length (map merge_job_input jobs)))
         (fun inputp : ptr =>
            primR merge_input_ptr_ty 1$m (Vptr inputp))
         (merge_input_ptrs blocksp jobs)
    ** inputsp |-> arrayLR merge_input_ptr_ty
         (Z.of_nat (length jobs)) 32
         (fun _ : unit => anyR merge_input_ptr_ty 1$m)
         (replicateN
            (Z.to_N (32 - Z.of_nat (length jobs))) ())
    ** flat_outp |-> storage_page_byte_bridges.evmc_bytes32_array_spineR
         1$m (length jobs)
    ** flat_outp |-> blake3specs.Blake3OutputBytesR 1
         (blake3_hash_many_outputs_from_params
            (blake3_hash_many_call_params
               model.blake3_iv_words 0 false 0 1 2)
            (map merge_job_input jobs))
    ** flat_outp .[ blake3specs.bytes32_ty ! Z.of_nat (length jobs) ]
       |-> blake3specs.Blake3OutputWordsR 1
             (skipn (length jobs) old_outputs)
    |--
    _global "IV"
      |-> blake3specs.Blake3ConstKeyWordsR
            qiv model.blake3_iv_words
    ** merge_plan_arraysR leftsp rightsp blocksp inputsp jobs
    ** flat_outp |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
         (merge_hash_outputs jobs old_outputs).
  Proof using CU MODd Sigma.
    intros Hjobs Hrange_old.
    rewrite (merge_hash_outputs_from_call_params jobs).
    assert
      (Houtput_range :
        List.Forall (fun x => (x < 2 ^ 256)%N)
          (blake3_hash_many_outputs blake3model.merge_mode
             (map merge_job_input jobs))).
    {
      apply blake3specs.blake3_hash_many_outputs_range.
    }
    rewrite !List.length_map.
    change
      (flat_outp |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
         (merge_hash_outputs jobs old_outputs))
      with
      (flat_outp |-> blake3specs.Blake3OutputWordsR 1
         (merge_hash_outputs jobs old_outputs)).
    go using
      (blake3_output_bytes_prefix_tail_to_words_F
         flat_outp
         (blake3_hash_many_outputs blake3model.merge_mode
            (map merge_job_input jobs))
         (skipn (length jobs) old_outputs)
         (length jobs)
         Houtput_range
         (eq_sym (merge_hash_outputs_length jobs))),
      merge_inputs_arrayR_blake3_pack_F,
      merge_plan_arraysR_length_map_pack_F.
  Qed.

  Definition merge_hash_many_post_pack_F
      qiv leftsp rightsp blocksp inputsp flat_outp jobs
      old_outputs Hjobs Hrange :=
    [FWD] (merge_hash_many_post_pack
             qiv leftsp rightsp blocksp inputsp flat_outp jobs
             old_outputs Hjobs Hrange).

  Lemma wp_destroy_merge_hash_outputs32
      (tu : translation_unit) (flat_outp : ptr)
      (jobs : list merge_job) (Q : epred) :
    (length jobs <= 32)%nat ->
    □ exec_specs.bytes32_dtor_spec
    ** flat_outp |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
      (merge_hash_outputs jobs (replicateN 32 0%N))
    ** Q
    |-- wp_destroy_array tu QM bytes32_ty 32%N flat_outp Q.
  Proof using CU MODd Sigma.
    intros Hjobs.
    exact
      (evmc_specs.wp_destroy_bytes32_array
         tu flat_outp 32%N
         (merge_hash_outputs jobs (replicateN 32 0%N))
         Q
         (merge_hash_outputs_replicate32_length jobs Hjobs)).
  Qed.

  Definition wp_destroy_merge_hash_outputs32_B
      tu flat_outp jobs Q Hjobs :=
    [BWD] (wp_destroy_merge_hash_outputs32
             tu flat_outp jobs Q Hjobs).

  Lemma wp_destroy_merge_inputs_array_cleanup_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    base |-> arrayLR merge_input_ptr_ty 0 32
      (fun _ : unit => anyR merge_input_ptr_ty 1$m)
      (replicateN 32 ())
    ** Q
    |-- wp_destroy_val tu QM merge_inputs_array_ty base Q.
  Proof.
    intros tu base Q.
    unfold merge_inputs_array_ty, merge_input_ptr_ty.
    rewrite -destroy.wp_destroy_val_array.
    cbn.
    go.
  Qed.

  Definition wp_destroy_merge_inputs_array_cleanup_local_B
      tu base Q :=
    [BWD] (wp_destroy_merge_inputs_array_cleanup_local
             tu base Q).

  Lemma wp_destroy_merge_block_row_anyR_cell_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    type_ptr merge_block_row_ty base
    ** base |-> anyR merge_block_row_ty 1$m
    ** Q
    |-- wp_destroy_val tu QM merge_block_row_ty base Q.
  Proof.
    intros tu base Q.
    unfold merge_block_row_ty.
    rewrite -destroy.wp_destroy_val_array.
    cbn.
    go.
  Qed.

  Lemma merge_block_row_cleanup_anyR (base : ptr) :
    base |-> arrayLR Tuchar 0 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 64 ())
    |--
    base |-> anyR merge_block_row_ty 1$m.
  Proof using MODd.
    unfold merge_block_row_ty.
    rewrite array.arrayR_anyR_eqv.
    change (replicateZ 64 ()) with (replicateN 64 ()).
    go.
  Qed.

  Definition merge_block_row_cleanup_anyR_F base :=
    [FWD] (merge_block_row_cleanup_anyR base).

  Lemma wp_destroy_merge_block_row_bytes_cell_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    type_ptr merge_block_row_ty base
    ** base |-> arrayLR Tuchar 0 64
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateN 64 ())
    ** Q
    |-- wp_destroy_val tu QM merge_block_row_ty base Q.
  Proof using CU MODd Sigma.
    intros tu base Q.
    go using
      (merge_block_row_cleanup_anyR_F base),
      wp_destroy_merge_block_row_anyR_cell_local.
  Qed.

  Lemma merge_blocks_array_cleanup_rows_anyR (base : ptr) :
    base |-> arrayLR merge_block_row_ty 0 32
      (fun _ : unit =>
         arrayLR Tuchar 0 64
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 64 ()))
      (replicateN 32 ())
    |--
    base |-> arrayLR merge_block_row_ty 0 32
      (fun _ : unit => anyR merge_block_row_ty 1$m)
      (replicateN 32 ()).
  Proof using CU MODd Sigma.
    rewrite
      (array_sliceR_fmap
         (ty := merge_block_row_ty)
         0 32 (replicateN 32 ())
         (fun _ : unit => anyR merge_block_row_ty 1$m)
         (fun _ : unit => ()))
      /=.
    apply _at_mono.
    f_equiv.
    intros [].
    apply Rep_entails_at.
    intro rowp.
    apply merge_block_row_cleanup_anyR.
  Qed.

  Definition merge_blocks_array_cleanup_rows_anyR_F base :=
    [FWD] (merge_blocks_array_cleanup_rows_anyR base).

  Lemma wp_destroy_merge_blocks_array_cleanup_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    base |-> arrayLR merge_block_row_ty 0 32
      (fun _ : unit =>
         arrayLR Tuchar 0 64
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 64 ()))
      (replicateN 32 ())
    ** Q
    |-- wp_destroy_val tu QM merge_blocks_array_ty base Q.
  Proof using CU MODd Sigma.
    intros tu base Q.
    etrans.
    {
      apply bi.sep_mono_l.
      apply merge_blocks_array_cleanup_rows_anyR.
    }
    unfold merge_blocks_array_ty, merge_block_row_ty.
    rewrite -destroy.wp_destroy_val_array.
    cbn.
    etrans.
    {
      exact
        (brick_upstream.destroy_run_array_from_arrayLR
           unit tu QM (Tarray Tuchar 64%N) 32%nat base
           (fun _ : unit => anyR (Tarray Tuchar 64%N) 1$m)
           (replicateN 32 tt) Q eq_refl eq_refl
           (fun cellp _ Qcell =>
              wp_destroy_merge_block_row_anyR_cell_local
                tu cellp Qcell)).
    }
    exact (destroy.run_array_ok tu 32%N QM
             (Tarray Tuchar 64%N) base Q).
  Qed.

  Definition wp_destroy_merge_blocks_array_cleanup_local_B
      tu base Q :=
    [BWD] (wp_destroy_merge_blocks_array_cleanup_local
             tu base Q).

  Lemma destroy_run_merge_blocks_array_cleanup_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    base |-> arrayLR merge_block_row_ty 0 32
      (fun _ : unit =>
         arrayLR Tuchar 0 64
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 64 ()))
      (replicateN 32 ())
    ** Q
    |-- destroy.run_array
          tu QM merge_block_row_ty base (N.to_nat 32%N) Q.
  Proof using CU MODd Sigma.
    intros tu base Q.
    change (N.to_nat 32%N) with 32%nat.
    exact
      (brick_upstream.destroy_run_array_from_arrayLR
         unit tu QM merge_block_row_ty 32%nat base
         (fun _ : unit =>
            arrayLR Tuchar 0 64
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 64 ()))
         (replicateN 32 ()) Q
         ltac:(change (length (replicateN 32 ())) with 32%nat;
               reflexivity)
         eq_refl
         (fun cellp _ Qcell =>
            wp_destroy_merge_block_row_bytes_cell_local
              tu cellp Qcell)).
  Qed.

  Definition destroy_run_merge_blocks_array_cleanup_local_B
      tu base Q :=
    [BWD] (destroy_run_merge_blocks_array_cleanup_local
             tu base Q).

  Lemma destroy_run_merge_block_rows_uninit_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    base |-> arrayLR merge_block_row_ty 0 32 merge_block_rowR
      (replicateN 32 MergeBlockUninit)
    ** Q
    |-- destroy.run_array
          tu QM merge_block_row_ty base (N.to_nat 32%N) Q.
  Proof using CU MODd Sigma.
    intros tu base Q.
    change (N.to_nat 32%N) with 32%nat.
    etrans.
    {
      apply bi.sep_mono_l.
      apply merge_block_uninit_rows_forget.
    }
    exact
      (brick_upstream.destroy_run_array_from_arrayLR
         unit tu QM merge_block_row_ty 32%nat base
         (fun _ : unit =>
            arrayLR Tuchar 0 64
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 64 ()))
         (replicateN 32 ()) Q
         ltac:(change (length (replicateN 32 ())) with 32%nat;
               reflexivity)
         eq_refl
         (fun cellp _ Qcell =>
            wp_destroy_merge_block_row_bytes_cell_local
              tu cellp Qcell)).
  Qed.

  Definition destroy_run_merge_block_rows_uninit_local_B
      tu base Q :=
    [BWD] (destroy_run_merge_block_rows_uninit_local
             tu base Q).

  Lemma destroy_run_merge_index_array_cleanup_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    base |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 32 ())
    ** Q
    |-- destroy.run_array tu QM Tuchar base (N.to_nat 32%N) Q.
  Proof.
    intros tu base Q.
    change (N.to_nat 32%N) with 32%nat.
    exact
      (brick_upstream.destroy_run_array_from_arrayLR
         unit tu QM Tuchar 32%nat base
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateN 32 ()) Q
         ltac:(change (length (replicateN 32 ())) with 32%nat;
               reflexivity)
         eq_refl
         (fun cellp _ Qcell =>
            wp_destroy_uchar_anyR_cell_local
              tu cellp Qcell)).
  Qed.

  Definition destroy_run_merge_index_array_cleanup_local_B
      tu base Q :=
    [BWD] (destroy_run_merge_index_array_cleanup_local
             tu base Q).


  (* Support copied from the former split helper proofs.  These lemmas are
     kept here while porting [merge_scratch_level] to verify the helper bodies
     inline at their old call sites. *)

  #[local] Hint Resolve
    type_ptr_elim_type_ptr_C
    typed_sliceR_elim_type_ptr_C
    UNSAFE_read_prim_cancel : sl_opacity.
  #[local] Hint Opaque
    merge_plan_arraysR merge_index_arrayR merge_inputs_arrayR
    merge_block_rows : sl_opacity.
  Remove Hints
    _at_pick_cfrac_and_split_C
    _at_pick_frac_and_split_C
    _at_split_specific_cfrac_C
    _at_split_specific_frac_C
    : db_skylabs_syntactic.

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
  Proof.
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

  Definition arrayLR_extract_middle_lookup_local_F
      {A : Type} ty p i j k f xs Hijk :=
    [FWD] (@arrayLR_extract_middle_lookup_local
             A ty p i j k f xs Hijk).

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
  Proof.
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

  Definition arrayLR_combine_middle_lookup_local_B
      {A : Type} ty p i j k f xs Hijk :=
    [BWD] (@arrayLR_combine_middle_lookup_local
             A ty p i j k f xs Hijk).

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

  Lemma arrayR_read_cell_with_wand {A : Type}
      (ty : type) (R : A -> Rep)
      (base : ptr) (xs : list A) (i : nat) (x : A) :
    xs !! i = Some x ->
    base |-> arrayR ty R xs |--
    base .[ ty ! Z.of_nat i ] |-> R x
    ** (base .[ ty ! Z.of_nat i ] |-> R x -*
        base |-> arrayR ty R xs).
  Proof.
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

  Definition primR_anyR_F ty q v :=
    [FWD] (primR_anyR ty q v).

  Lemma arrayLR_uninit_anyR {A : Type}
      (ty : type) (base : ptr) i j q (xs : list A) :
    base |-> arrayLR ty i j (fun _ : A => uninitR ty q) xs |--
    base |-> arrayLR ty i j (fun _ : A => anyR ty q) xs.
  Proof.
    go using uninitR_anyR_F.
  Qed.

  Definition arrayLR_uninit_anyR_F {A : Type} ty base i j q (xs : list A) :=
    [FWD] (@arrayLR_uninit_anyR A ty base i j q xs).

  Lemma arrayLR_app_local {A : Type}
      (ty : type) (p : ptr) (i j k : Z)
      (f : A -> Rep) (xs ys : list A) :
    lengthZ xs = j - i ->
    lengthZ ys = k - j ->
    p |-> arrayLR ty i k f (xs ++ ys) |--
    p |-> arrayLR ty i j f xs **
    p |-> arrayLR ty j k f ys.
  Proof using CU MODd Sigma.
    intros Hxs Hys.
    rewrite !array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite arrayR_app__N.
    rewrite _at_offsetR.
    rewrite Hxs Hys.
    rewrite
      (_at_sep
         (p .[ ty ! i ])
         (arrayR ty f xs)
         (.[ ty ! j - i ] |-> arrayR ty f ys)).
    rewrite
      (_at_sep
         p [| j - i = j - i |]
         (.[ ty ! i ] |-> arrayR ty f xs)).
    rewrite
      (_at_sep
         p [| k - j = k - j |]
         (.[ ty ! j ] |-> arrayR ty f ys)).
    rewrite !_at_only_provable.
    repeat rewrite _at_offsetR.
    rewrite o_sub_sub.
    replace (i + (j - i)) with j by lia.
    go.
  Qed.

  Definition arrayLR_app_local_F {A : Type}
      ty p i j k f (xs ys : list A) Hxs Hys :=
    [FWD] (@arrayLR_app_local
             A ty p i j k f xs ys Hxs Hys).

  Lemma arrayLR_singleton_cell_local {A : Type}
      (ty : type) (Hty : @HasSize CU ty)
      (p : ptr) (j : Z) (f : A -> Rep) x :
    type_ptr ty (p .[ ty ! j ])
    ** p .[ ty ! j ] |-> f x
    |--
    p |-> arrayLR ty j (j + 1) f [x].
  Proof using CU MODd Sigma.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    change (lengthZ [x]) with 1%Z.
    rewrite _at_offsetR.
    rewrite arrDecompose.
    simpl.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact Hty.
    }
    repeat rewrite o_sub_0; auto.
    repeat rewrite _offsetR_id.
    normalize_ptrs.
    go.
  Qed.

  Definition arrayLR_singleton_cell_local_F {A : Type}
      ty (Hty : @HasSize CU ty) p j f (x : A) :=
    [FWD] (@arrayLR_singleton_cell_local
             A ty Hty p j f x).

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
    replace (i + (j - i)) with j by lia.
    go.
  Qed.

  Definition arrayLR_app_combine_local_F {A : Type}
      ty (Hty : @HasSize CU ty) p i j k f (xs ys : list A) Hxs Hys :=
    [FWD] (@arrayLR_app_combine_local
             A ty Hty p i j k f xs ys Hxs Hys).

  Lemma merge_block_uninit_row_split_first_local (base : ptr) :
    base |-> arrayLR Tuchar 0 64
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 64 ())
    |--
    base |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ())
    ** base |-> arrayLR Tuchar 32 64
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ()).
  Proof using CU MODd Sigma.
    change (replicateN 64 ())
      with (replicateN 32 () ++ replicateN 32 ()).
    go using
      (arrayLR_app_local_F
         Tuchar base 0 32 64
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateN 32 ()) (replicateN 32 ())
         ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity)).
  Qed.

  Definition merge_block_uninit_row_split_first_local_F base :=
    [FWD] (merge_block_uninit_row_split_first_local base).

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

  Definition any_unit_arrayLR32_to_val_arrayLR32_local_F base :=
    [FWD] (any_unit_arrayLR32_to_val_arrayLR32_local base).

  Lemma any_unit_arrayR32_to_val_arrayLR32_local (base : ptr) :
    base |-> arrayR Tuchar
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ())
    |--
    base |-> arrayLR Tuchar 0 32
      (fun _ : val => anyR Tuchar 1$m) (replicateN 32 (Vint 0)).
  Proof using CU MODd Sigma.
    change (replicateN 32 (Vint 0))
      with ((fun _ : unit => Vint 0) <$> replicateN 32 ()).
    rewrite array_sliceR_fmap.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    go.
  Qed.

  Definition any_unit_arrayR32_to_val_arrayLR32_local_F base :=
    [FWD] (any_unit_arrayR32_to_val_arrayLR32_local base).

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

  Definition any_unit_arrayLR32_64_to_val_arrayLR0_32_local_F base :=
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
    rewrite <- (bi.exist_intro
                   (A := list val)
                   (replicateN 32 (Vint 0))).
    go.
  Qed.

  Definition memcpy_dst_any_val32_witness_local_F base Q :=
    [FWD] (memcpy_dst_any_val32_witness_local base Q).

  Lemma scratchR_unfold_local (base : ptr) q scratch :
    base |-> ScratchR q scratch -|-
    base |-> arrayR bytes32_ty (exec_specs.bytes32R (cQp.mut q)) scratch
    ** [| length scratch = page_pair_count |].
  Proof using CU MODd Sigma.
    unfold ScratchR.
    split'; go.
  Qed.

  Lemma scratchR_unfold_entails_local (base : ptr) q scratch :
    base |-> ScratchR q scratch |--
    base |-> arrayR bytes32_ty (exec_specs.bytes32R (cQp.mut q)) scratch
    ** [| length scratch = page_pair_count |].
  Proof using CU MODd Sigma.
    rewrite scratchR_unfold_local.
    go.
  Qed.

  Definition scratchR_unfold_entails_local_F base q scratch :=
    [FWD] (scratchR_unfold_entails_local base q scratch).

  Lemma bytes32_array_cellN_recombine_with_type_ptr_local
      (i : N) (l : list N) (base : ptr) (v : N)
      (Hnth : nth_error l (N.to_nat i) = Some v) :
    base |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
             (take (N.to_nat i) l)
    ** □ type_ptr bytes32_ty (base .[ bytes32_ty ! i])
    ** base .[ bytes32_ty ! i]
         |-> exec_specs.bytes32R 1 v
    ** base .[ bytes32_ty ! i + 1]
         |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
              (drop (N.to_nat (i + 1)) l)
    |-- base |-> arrayR bytes32_ty (exec_specs.bytes32R 1) l.
  Proof using CU MODd Sigma.
    rewrite -(_at_arrayR_cellN
                i l bytes32_ty (exec_specs.bytes32R 1)
                base v Hnth).
    go.
  Qed.

  Definition bytes32_array_cellN_recombine_with_type_ptr_local_F
      i l base v Hnth :=
    [FWD]
      (bytes32_array_cellN_recombine_with_type_ptr_local
         i l base v Hnth).

  Lemma bytes32_array_suffix_recombine_local
      (base : ptr) (previous current : nat) scratch v
      (Hprevious_before_current : (previous < current)%nat)
      (Hnth :
        nth_error
          (drop
             (N.to_nat (N.of_nat previous + 1))
             scratch)
          (N.to_nat (N.of_nat (current - S previous))) = Some v) :
    base .[ bytes32_ty ! previous + 1 ]
      |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
            (take
               (N.to_nat (N.of_nat (current - S previous)))
               (drop
                  (N.to_nat (N.of_nat previous + 1))
                  scratch))
    ** base .[ bytes32_ty ! current]
         |-> exec_specs.bytes32R 1 v
    ** base .[ bytes32_ty !
          previous + 1 + ((current - S previous)%nat + 1)]
         |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
              (drop
                 (N.to_nat
                    (N.of_nat (current - S previous) + 1))
                 (drop
                    (N.to_nat (N.of_nat previous + 1))
                    scratch))
    |-- base .[ bytes32_ty ! previous + 1 ]
          |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
                (drop
                   (N.to_nat (N.of_nat previous + 1))
                   scratch).
  Proof using CU MODd Sigma.
    rewrite (_at_arrayR_cellN
                (N.of_nat (current - S previous))
                (drop
                   (N.to_nat (N.of_nat previous + 1))
                   scratch)
                bytes32_ty (exec_specs.bytes32R 1)
                (base .[ bytes32_ty ! previous + 1 ])
                v Hnth).
    repeat rewrite o_sub_sub.
    repeat rewrite N2Z.inj_add.
    change (Z.of_N 1) with 1%Z.
    rewrite nat_N_Z.
    replace
      (Z.of_nat previous + 1 +
       Z.of_nat (current - S previous))%Z
      with (Z.of_nat current) by lia.
    go.
  Qed.

  Definition bytes32_array_suffix_recombine_local_F
      base previous current scratch v Hprevious_before_current Hnth :=
    [FWD]
      (bytes32_array_suffix_recombine_local
         base previous current scratch v Hprevious_before_current Hnth).

  Lemma bytes32_current_suffix_as_offset_local
      (base : ptr) previous current scratch v
      (Hprevious_before_current : (previous < current)%nat) :
    □ type_ptr bytes32_ty (base .[ bytes32_ty ! current])
    ** base .[ bytes32_ty ! current]
         |-> exec_specs.bytes32R 1 v
    ** base .[ bytes32_ty !
          previous + 1 + ((current - S previous)%nat + 1)]
         |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
              (drop
                 (N.to_nat
                    (N.of_nat (current - S previous) + 1))
                 (drop
                    (N.to_nat (N.of_nat previous + 1))
                    scratch))
    |--
    □ type_ptr bytes32_ty
      (base .[ bytes32_ty !
        previous + 1 + N.of_nat (current - S previous)])
    ** base .[ bytes32_ty !
          previous + 1 + N.of_nat (current - S previous)]
         |-> exec_specs.bytes32R 1 v
    ** base .[ bytes32_ty !
          previous + 1 +
          (N.of_nat (current - S previous) + 1)]
         |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
              (drop
                 (N.to_nat
                    (N.of_nat (current - S previous) + 1))
                 (drop
                    (N.to_nat (N.of_nat previous + 1))
                    scratch)).
  Proof using CU MODd Sigma.
    repeat rewrite o_sub_sub.
    repeat rewrite N2Z.inj_add.
    change (Z.of_N 1) with 1%Z.
    rewrite nat_N_Z.
    replace
      (Z.of_nat previous + 1 +
       Z.of_nat (current - S previous))%Z
      with (Z.of_nat current) by lia.
    replace
      (Z.of_nat previous + 1 +
       (Z.of_nat (current - S previous) + 1))%Z
      with (Z.of_nat current + 1)%Z by lia.
    go.
  Qed.

  Definition bytes32_current_suffix_as_offset_local_F
      base previous current scratch v Hprevious_before_current :=
    [FWD]
      (bytes32_current_suffix_as_offset_local
         base previous current scratch v Hprevious_before_current).

  Lemma bytes32_array_previous_recombine_local
      (base : ptr) previous scratch v
      (Hnth :
        nth_error scratch (N.to_nat (N.of_nat previous)) = Some v) :
    base |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
             (take (N.to_nat (N.of_nat previous)) scratch)
    ** base .[ bytes32_ty ! previous]
         |-> exec_specs.bytes32R 1 v
    ** base .[ bytes32_ty ! previous + 1]
         |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
              (drop (N.to_nat (N.of_nat previous + 1)) scratch)
    |-- base |-> arrayR bytes32_ty (exec_specs.bytes32R 1) scratch.
  Proof using CU MODd Sigma.
    rewrite (_at_arrayR_cellN
                (N.of_nat previous) scratch bytes32_ty
                (exec_specs.bytes32R 1) base v Hnth).
    rewrite nat_N_Z.
    go.
  Qed.

  Definition bytes32_array_previous_recombine_local_F
      base previous scratch v Hnth :=
    [FWD]
      (bytes32_array_previous_recombine_local
         base previous scratch v Hnth).

  Lemma byte_arrayR_to_arrayLR_local
      (base : ptr) q bytes :
    length bytes = 32%nat ->
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes
    |--
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes.
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

  Definition byte_arrayR_to_arrayLR_local_F base q bytes Hlen :=
    [FWD] (byte_arrayR_to_arrayLR_local base q bytes Hlen).

  Lemma bytes32_be_values_length_local word :
    length (exec_specs.bytes32_be_values word) = 32%nat.
  Proof.
    reflexivity.
  Qed.

  Lemma bytes32R_to_byte_arrayLR_local
      (base : ptr) word :
    base |-> exec_specs.bytes32R 1 word
    |--
    base |-> structR "monad::bytes32_t" 1$m
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
       |-> structR "evmc_bytes32" 1$m
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
       o_field CU "evmc_bytes32::bytes"
       |-> type_ptrR (Tarray Tuchar 32)
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
       o_field CU "evmc_bytes32::bytes"
       |-> arrayLR Tuchar 0 32
            (fun byte : val => primR Tuchar 1$m byte)
            (exec_specs.bytes32_be_values word)
    ** [| (word < 2 ^ 256)%N |].
  Proof using CU MODd Sigma.
    Transparent exec_specs.evmc_bytes32_bytesR.
    rewrite /exec_specs.bytes32R /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR.
    Opaque exec_specs.evmc_bytes32_bytesR.
    rewrite !_at_sep.
    repeat rewrite _at_offsetR.
    rewrite !_at_sep.
    repeat rewrite _at_offsetR.
    rewrite !_at_sep.
    rewrite !_at_pureR.
    go1 using
      (byte_arrayR_to_arrayLR_local_F
         (base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
         o_field CU "evmc_bytes32::bytes")
         1
         (exec_specs.bytes32_be_values word)
         (bytes32_be_values_length_local word)).
  Qed.

  Definition bytes32R_to_byte_arrayLR_local_F base word :=
    [FWD] (bytes32R_to_byte_arrayLR_local base word).

  Lemma unpacked_bytes32R_to_byte_arrayLR_local
      (base : ptr) word :
    base |->
      (structR "monad::bytes32_t" 1$m
       ** o_base CU "monad::bytes32_t" "evmc_bytes32"
          |->
          (o_field CU "evmc_bytes32::bytes"
           |->
           (type_ptrR (Tarray Tuchar 32)
            ** arrayR Tuchar
                 (fun byte : val => primR Tuchar 1$m byte)
                 (exec_specs.bytes32_be_values word))
           ** structR "evmc_bytes32" 1$m)
       ** pureR [| (word < 2 ^ 256)%N |])
    |--
    base |-> structR "monad::bytes32_t" 1$m
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
       |-> structR "evmc_bytes32" 1$m
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
       o_field CU "evmc_bytes32::bytes"
       |-> type_ptrR (Tarray Tuchar 32)
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
       o_field CU "evmc_bytes32::bytes"
       |-> arrayLR Tuchar 0 32
            (fun byte : val => primR Tuchar 1$m byte)
            (exec_specs.bytes32_be_values word)
    ** [| (word < 2 ^ 256)%N |].
  Proof using CU MODd Sigma.
    rewrite !_at_sep.
    repeat rewrite _at_offsetR.
    rewrite !_at_sep.
    repeat rewrite _at_offsetR.
    rewrite !_at_sep.
    rewrite !_at_pureR.
    go1 using
      (byte_arrayR_to_arrayLR_local_F
         (base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
          o_field CU "evmc_bytes32::bytes")
         1
         (exec_specs.bytes32_be_values word)
         (bytes32_be_values_length_local word)).
  Qed.

  Definition unpacked_bytes32R_to_byte_arrayLR_local_F base word :=
    [FWD] (unpacked_bytes32R_to_byte_arrayLR_local base word).

  Lemma byte_arrayLR_split_half_local
      (base : ptr) bytes :
    length bytes = 32%nat ->
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte) bytes
    |--
    base |-> arrayLR Tuchar 0 32
      (fun byte : val =>
         primR Tuchar (cQp.mut (1 / 2)%Qp) byte) bytes
    ** base |-> arrayLR Tuchar 0 32
      (fun byte : val =>
         primR Tuchar (cQp.mut (1 / 2)%Qp) byte) bytes.
  Proof using CU MODd Sigma.
    intro Hlen.
    rewrite !array_sliceR.unlock.
    rewrite !_at_sep !_at_only_provable.
    repeat rewrite _at_offsetR.
    rewrite !offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite !lengthZ_correct Hlen.
    go.
  Qed.

  Definition byte_arrayLR_split_half_local_F base bytes Hlen :=
    [FWD] (byte_arrayLR_split_half_local base bytes Hlen).

  Lemma bytes32_byte_values_length_local digest :
    length (blake3specs.bytes32_byte_values digest) = 32%nat.
  Proof.
    reflexivity.
  Qed.

  Lemma byte_arrayLR_halves_to_arrayR_local
      (base : ptr) bytes :
    length bytes = 32%nat ->
    base |-> arrayLR Tuchar 0 32
      (fun byte : val =>
         primR Tuchar (cQp.mut (1 / 2)%Qp) byte) bytes
    ** base |-> arrayLR Tuchar 0 32
      (fun byte : val =>
         primR Tuchar (cQp.mut (1 / 2)%Qp) byte) bytes
    |--
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar 1$m byte) bytes.
  Proof using CU MODd Sigma.
    intro Hlen.
    rewrite !array_sliceR.unlock.
    rewrite !_at_sep !_at_only_provable.
    repeat rewrite _at_offsetR.
    rewrite !offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite !lengthZ_correct Hlen.
    go.
  Qed.

  Definition byte_arrayLR_halves_to_arrayR_local_F base bytes Hlen :=
    [FWD] (byte_arrayLR_halves_to_arrayR_local base bytes Hlen).

  Lemma bytes32R_from_two_half_byte_arrays_local
      (base : ptr) word :
    (word < 2 ^ 256)%N ->
    base |-> structR "monad::bytes32_t" 1$m
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
       |-> structR "evmc_bytes32" 1$m
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
       o_field CU "evmc_bytes32::bytes"
       |-> arrayLR Tuchar 0 32
            (fun byte : val =>
               primR Tuchar (cQp.mut (1 / 2)%Qp) byte)
            (exec_specs.bytes32_be_values word)
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
       o_field CU "evmc_bytes32::bytes"
       |-> arrayLR Tuchar 0 32
            (fun byte : val =>
               primR Tuchar (cQp.mut (1 / 2)%Qp) byte)
            (exec_specs.bytes32_be_values word)
    |--
    base |-> exec_specs.bytes32R 1 word.
  Proof using CU MODd Sigma.
    intro Hword_range.
    Transparent exec_specs.evmc_bytes32_bytesR.
    rewrite /exec_specs.bytes32R /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR.
    Opaque exec_specs.evmc_bytes32_bytesR.
    go using
      (byte_arrayLR_halves_to_arrayR_local_F
         (base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
          o_field CU "evmc_bytes32::bytes")
         (exec_specs.bytes32_be_values word)
         (bytes32_be_values_length_local word)).
  Qed.

  Definition bytes32R_from_two_half_byte_arrays_local_F base word Hword_range :=
    [FWD] (bytes32R_from_two_half_byte_arrays_local base word Hword_range).

  Lemma merge_block_full_from_halves_local
      (base : ptr) (lhs rhs : blake3model.digest) :
    (base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values (blake3model.bytes32_to_N lhs)))
    ** (base .[ Tuchar ! 32 ] |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values (blake3model.bytes32_to_N rhs)))
    |--
    base |-> merge_block_rowR (MergeBlockFull (lhs, rhs)).
  Proof using CU MODd Sigma.
	    unfold merge_block_rowR, blake3specs.Blake3BlockR,
	      blake3_impl_h_specs.Blake3BlockR,
	      blake3specs.BlockR,
	      blake3_impl_h_specs.BlockR,
	      blake3specs.bytes64_byte_values,
      blake3_impl_h_specs.bytes64_byte_values,
      blake3specs.bytes32_byte_values,
      blake3_impl_h_specs.bytes32_byte_values.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite arrayR_app__N.
    rewrite lengthZ_correct.
    rewrite bytes32_be_values_length_local.
    change (length (exec_specs.bytes32_be_values
                      (blake3model.bytes32_to_N rhs))) with 32%nat.
    rewrite _at_sep _at_only_provable.
    repeat rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    replace (0 + 32)%Z with 32%Z by lia.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    go.
  Qed.

  Definition merge_block_full_from_halves_local_F base lhs rhs :=
    [FWD] (merge_block_full_from_halves_local base lhs rhs).

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

  Definition byte_arrayLR0_to_arrayR64_local_F base bytes Hlen :=
    [FWD] (byte_arrayLR0_to_arrayR64_local base bytes Hlen).

  Lemma merge_block_full_from_offset_halves_local
      (base : ptr) (lhs rhs : blake3model.digest) :
    (base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values (blake3model.bytes32_to_N lhs)))
    ** (base |-> arrayLR Tuchar 32 (32 + 32)
      (fun byte : val => primR Tuchar 1$m byte)
      (exec_specs.bytes32_be_values (blake3model.bytes32_to_N rhs)))
    |--
    base |-> merge_block_rowR (MergeBlockFull (lhs, rhs)).
  Proof using CU MODd Sigma.
    unfold merge_block_rowR, blake3specs.Blake3BlockR,
      blake3_impl_h_specs.Blake3BlockR,
      blake3specs.BlockR,
      blake3_impl_h_specs.BlockR,
      blake3specs.bytes64_byte_values,
      blake3_impl_h_specs.bytes64_byte_values,
      blake3specs.bytes32_byte_values,
      blake3_impl_h_specs.bytes32_byte_values.
    change (32 + 32)%Z with 64%Z.
    go using
      (arrayLR_app_combine_local_F
         Tuchar ltac:(apply has_size; exact _)
         base 0 32 64
         (fun byte : val => primR Tuchar 1$m byte)
         (exec_specs.bytes32_be_values
            (blake3model.bytes32_to_N lhs))
         (exec_specs.bytes32_be_values
            (blake3model.bytes32_to_N rhs))
         ltac:(rewrite lengthZ_correct; reflexivity)
         ltac:(rewrite lengthZ_correct; reflexivity)),
      (byte_arrayLR0_to_arrayR64_local_F
         base
         (exec_specs.bytes32_be_values
            (blake3model.bytes32_to_N lhs) ++
          exec_specs.bytes32_be_values
            (blake3model.bytes32_to_N rhs))
         ltac:(rewrite app_length; reflexivity)).
  Qed.

  Definition merge_block_full_from_offset_halves_local_F base lhs rhs :=
    [FWD] (merge_block_full_from_offset_halves_local base lhs rhs).

  Lemma uchar_index_cell_to_arrayLR0_1_local
      (base : ptr) index :
    base |-> typed_sliceR Tuchar 0 32
    ** base .[ Tuchar ! 0 ] |-> ucharR 1$m (Z.of_nat index)
    |--
    base |-> typed_sliceR Tuchar 0 32
    **
    base |-> arrayLR Tuchar 0 1
      (fun index : nat => ucharR 1$m (Z.of_nat index)) [index].
  Proof using CU MODd Sigma.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite arrDecompose.
    simpl.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    change (Z.of_nat 0) with 0%Z.
    repeat rewrite o_sub_0; auto.
    repeat rewrite _offsetR_id.
    normalize_ptrs.
    go.
  Qed.

  Definition uchar_index_cell_to_arrayLR0_1_local_F base index :=
    [FWD] (uchar_index_cell_to_arrayLR0_1_local base index).

  Lemma merge_input_cell_to_arrayLR0_1_local
      (base blocksp : ptr) :
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base .[ merge_input_ptr_ty ! 0 ]
      |-> ptrR<"unsigned char"> 1$m
            (blocksp .[ merge_block_row_ty ! 0 ])
    |--
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    **
    base |-> arrayLR merge_input_ptr_ty 0 1
      (fun job_index : nat =>
         primR merge_input_ptr_ty 1$m
           (Vptr (blocksp .[ merge_block_row_ty !
                             Z.of_nat job_index ]))) [0%nat].
  Proof using CU MODd Sigma.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite arrDecompose.
    simpl.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    change (Z.of_nat 0) with 0%Z.
    repeat rewrite o_sub_0; auto.
    repeat rewrite _offsetR_id.
    normalize_ptrs.
    go.
  Qed.

  Definition merge_input_cell_to_arrayLR0_1_local_F base blocksp :=
    [FWD] (merge_input_cell_to_arrayLR0_1_local base blocksp).

  Lemma merge_block_rows_one_prepare_local
      (base : ptr) (block : blake3model.bytes64) :
    type_ptr merge_block_row_ty (base .[ merge_block_row_ty ! 0 ])
    ** (base .[ merge_block_row_ty ! 0 ]
          |-> merge_block_rowR (MergeBlockFull block))
    ** (base |-> arrayLR merge_block_row_ty 1 32
          merge_block_rowR (replicateN 31 MergeBlockUninit))
    |--
    type_ptr merge_block_row_ty (base .[ merge_block_row_ty ! 0 ])
    ** (Exists x : merge_block_row,
      (base .[ merge_block_row_ty ! 0 ] |-> merge_block_rowR x)
      ** (base |-> arrayLR merge_block_row_ty 0 0
            merge_block_rowR
            (sliceZ 0 0 0
               (MergeBlockFull block ::
                replicateN 31 MergeBlockUninit)))
      ** (base |-> arrayLR merge_block_row_ty 1 32
            merge_block_rowR
            (sliceZ 0 1 32
               (MergeBlockFull block ::
                replicateN 31 MergeBlockUninit)))
      ** [| lengthN
             (MergeBlockFull block ::
              replicateN 31 MergeBlockUninit) =
           Z.to_N (32 - 0) |]
      ** [| (MergeBlockFull block ::
              replicateN 31 MergeBlockUninit) !! (0 - 0)%Z =
           Some x |]).
  Proof using CU MODd Sigma.
    simpl.
    go.
  Qed.

  Lemma merge_block_rows_one_from_cell_tail_local
      (base : ptr) (block : blake3model.bytes64) :
    type_ptr merge_block_row_ty (base .[ merge_block_row_ty ! 0 ])
    ** base .[ merge_block_row_ty ! 0 ]
       |-> merge_block_rowR (MergeBlockFull block)
    ** base |-> arrayLR merge_block_row_ty 1 32
       merge_block_rowR (replicateN 31 MergeBlockUninit)
    |--
    base |-> arrayLR merge_block_row_ty 0 32
      merge_block_rowR
      (MergeBlockFull block :: replicateN 31 MergeBlockUninit).
  Proof using CU MODd Sigma.
    assert (Hrows_mid : SolveArith (0 <= 0 /\ 0 < 32)%Z) by
      (constructor; lia).
    etransitivity.
    {
      apply merge_block_rows_one_prepare_local.
    }
    {
      exact
        (arrayLR_combine_middle_lookup_local
           merge_block_row_ty base 0 0 32 merge_block_rowR
           (MergeBlockFull block :: replicateN 31 MergeBlockUninit)
           Hrows_mid).
    }
  Qed.

  Definition merge_block_rows_one_from_cell_tail_local_F base block :=
    [FWD] (merge_block_rows_one_from_cell_tail_local base block).

  Lemma uchar_index_one_from_cell_tail_local
      (base : ptr) index :
    base |-> typed_sliceR Tuchar 0 32
    ** base .[ Tuchar ! 0 ] |-> ucharR 1$m (Z.of_nat index)
    ** base |-> arrayLR Tuchar 1 32
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateN 31 ())
    |--
    base |-> typed_sliceR Tuchar 0 32
    ** base |-> arrayLR Tuchar 0 1
       (fun index : nat => ucharR 1$m (Z.of_nat index)) [index]
    ** base |-> arrayLR Tuchar 1 32
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateN 31 ()).
  Proof using CU MODd Sigma.
    rewrite !bi.sep_assoc.
    etrans.
    {
      apply bi.sep_mono_l.
      exact (uchar_index_cell_to_arrayLR0_1_local base index).
    }
    go.
  Qed.

  Definition uchar_index_one_from_cell_tail_local_F base index :=
    [FWD] (uchar_index_one_from_cell_tail_local base index).

  Lemma merge_input_one_from_cell_tail_local
      (base blocksp : ptr) :
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base .[ merge_input_ptr_ty ! 0 ]
       |-> ptrR<"unsigned char"> 1$m
             (blocksp .[ merge_block_row_ty ! 0 ])
    ** base |-> arrayLR merge_input_ptr_ty 1 32
       (fun _ : unit => anyR merge_input_ptr_ty 1$m)
       (replicateN 31 ())
    |--
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base |-> arrayLR merge_input_ptr_ty 0 1
       (fun job_index : nat =>
          primR merge_input_ptr_ty 1$m
            (Vptr (blocksp .[ merge_block_row_ty !
                              Z.of_nat job_index ]))) [0%nat]
    ** base |-> arrayLR merge_input_ptr_ty 1 32
       (fun _ : unit => anyR merge_input_ptr_ty 1$m)
       (replicateN 31 ()).
  Proof using CU MODd Sigma.
    rewrite !bi.sep_assoc.
    etrans.
    {
      apply bi.sep_mono_l.
      exact (merge_input_cell_to_arrayLR0_1_local base blocksp).
    }
    go.
  Qed.

  Definition merge_input_one_from_cell_tail_local_F base blocksp :=
    [FWD] (merge_input_one_from_cell_tail_local base blocksp).

  Lemma merge_block_rows_one_from_blake3_tail_local
      (base : ptr) (block : blake3model.bytes64) :
    base |-> typed_sliceR merge_block_row_ty 0 32
    ** base .[ merge_block_row_ty ! 0 ]
       |-> blake3specs.Blake3BlockR 1 block
    ** base |-> arrayLR merge_block_row_ty 1 32
       merge_block_rowR (replicateN 31 MergeBlockUninit)
    |--
    base |-> typed_sliceR merge_block_row_ty 0 32
    ** base |-> arrayLR merge_block_row_ty 0 32
       merge_block_rowR
       (MergeBlockFull block :: replicateN 31 MergeBlockUninit).
  Proof using CU MODd Sigma.
    change (blake3specs.Blake3BlockR 1 block)
      with (merge_block_rowR (MergeBlockFull block)).
    go using (merge_block_rows_one_from_cell_tail_local_F base block).
  Qed.

  Definition merge_block_rows_one_from_blake3_tail_local_F base block :=
    [FWD] (merge_block_rows_one_from_blake3_tail_local base block).

  Lemma merge_index_arrayR_one_from_cell_tail_local
      (base : ptr) index :
    base |-> typed_sliceR Tuchar 0 32
    ** base .[ Tuchar ! 0 ] |-> ucharR 1$m (Z.of_nat index)
    ** base |-> arrayLR Tuchar 1 32
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateN 31 ())
    |--
    base |-> merge_index_arrayR [index].
  Proof using CU MODd Sigma.
    unfold merge_index_arrayR.
    simpl.
    rewrite _at_as_Rep.
    etrans.
    {
      exact (uchar_index_one_from_cell_tail_local base index).
    }
    go.
  Qed.

  Definition merge_index_arrayR_one_from_cell_tail_local_F base index :=
    [FWD] (merge_index_arrayR_one_from_cell_tail_local base index).

  Lemma merge_inputs_arrayR_one_from_cell_tail_local
      (base blocksp : ptr) job :
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base .[ merge_input_ptr_ty ! 0 ]
       |-> ptrR<"unsigned char"> 1$m
             (blocksp .[ merge_block_row_ty ! 0 ])
    ** base |-> arrayLR merge_input_ptr_ty 1 32
       (fun _ : unit => anyR merge_input_ptr_ty 1$m)
       (replicateN 31 ())
    |--
    base |-> merge_inputs_arrayR blocksp [job].
  Proof using CU MODd Sigma.
    unfold merge_inputs_arrayR.
    simpl.
    rewrite _at_as_Rep.
    etrans.
    {
      exact (merge_input_one_from_cell_tail_local base blocksp).
    }
    go.
  Qed.

  Definition merge_inputs_arrayR_one_from_cell_tail_local_F
      base blocksp job :=
    [FWD] (merge_inputs_arrayR_one_from_cell_tail_local
             base blocksp job).

  Lemma merge_index_arrayR_one_from_cell_tail_Z_local
      (base : ptr) index :
    base |-> typed_sliceR Tuchar 0 32
    ** base .[ Tuchar ! 0 ] |-> ucharR 1$m (Z.of_nat index)
    ** base |-> arrayLR Tuchar 1 32
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateZ (32 - 1%nat) ())
    |--
    base |-> merge_index_arrayR [index].
  Proof using CU MODd Sigma.
    change (replicateZ (32 - 1%nat) ())
      with (replicateN 31 ()).
    exact (merge_index_arrayR_one_from_cell_tail_local base index).
  Qed.

  Definition merge_index_arrayR_one_from_cell_tail_Z_local_F
      base index :=
    [FWD] (merge_index_arrayR_one_from_cell_tail_Z_local
             base index).

  Lemma merge_inputs_arrayR_one_from_cell_tail_Z_local
      (base blocksp : ptr) job :
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base .[ merge_input_ptr_ty ! 0 ]
       |-> ptrR<"unsigned char"> 1$m
             (blocksp .[ merge_block_row_ty ! 0 ])
    ** base |-> arrayLR merge_input_ptr_ty 1 32
       (fun _ : unit => anyR merge_input_ptr_ty 1$m)
       (replicateZ (32 - 1%nat) ())
    |--
    base |-> merge_inputs_arrayR blocksp [job].
  Proof using CU MODd Sigma.
    change (replicateZ (32 - 1%nat) ())
      with (replicateN 31 ()).
    exact (merge_inputs_arrayR_one_from_cell_tail_local
             base blocksp job).
  Qed.

  Definition merge_inputs_arrayR_one_from_cell_tail_Z_local_F
      base blocksp job :=
    [FWD] (merge_inputs_arrayR_one_from_cell_tail_Z_local
             base blocksp job).

  Lemma merge_inputs_arrayR_one_from_base_cell_tail_local
      (base blocksp : ptr) job :
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base |-> ptrR<"unsigned char"> 1$m blocksp
    ** base |-> arrayLR merge_input_ptr_ty 1 32
       (fun _ : unit => anyR merge_input_ptr_ty 1$m)
       (replicateN 31 ())
    |--
    base |-> merge_inputs_arrayR blocksp [job].
  Proof using CU MODd Sigma.
    replace blocksp with
      (blocksp .[ merge_block_row_ty ! 0%nat]) at 1.
    2: {
      transitivity
        (blocksp .[ merge_block_row_ty ! Z.of_nat 0%nat]).
      { exact (ptr_o_sub_N_of_nat
                 merge_block_row_ty blocksp 0%nat). }
      rewrite offset_ptr_sub_0.
      2: { apply has_size; exact _. }
      reflexivity.
    }
    replace base with
      (base .[ merge_input_ptr_ty ! 0]) at 2.
    2: {
      rewrite offset_ptr_sub_0.
      2: { apply has_size; exact _. }
      reflexivity.
    }
    unfold merge_inputs_arrayR.
    simpl.
    rewrite _at_as_Rep.
    go using
      (arrayLR_singleton_cell_local_F
         merge_input_ptr_ty ltac:(apply has_size; exact _)
         base 0
         (fun _ : nat => ptrR<"unsigned char"> 1$m blocksp)
         0%nat).
  Qed.

  Definition merge_inputs_arrayR_one_from_base_cell_tail_local_F
      base blocksp job :=
    [FWD] (merge_inputs_arrayR_one_from_base_cell_tail_local
             base blocksp job).

  Lemma merge_inputs_arrayR_one_from_base_cell_tail_Z_local
      (base blocksp : ptr) job :
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base |-> ptrR<"unsigned char"> 1$m blocksp
    ** base |-> arrayLR merge_input_ptr_ty 1 32
       (fun _ : unit => anyR merge_input_ptr_ty 1$m)
       (replicateZ (32 - 1%nat) ())
    |--
    base |-> merge_inputs_arrayR blocksp [job].
  Proof using CU MODd Sigma.
    change (replicateZ (32 - 1%nat) ())
      with (replicateN 31 ()).
    exact (merge_inputs_arrayR_one_from_base_cell_tail_local
             base blocksp job).
  Qed.

  Definition merge_inputs_arrayR_one_from_base_cell_tail_Z_local_F
      base blocksp job :=
    [FWD] (merge_inputs_arrayR_one_from_base_cell_tail_Z_local
             base blocksp job).

  Definition merge_inputs_arrayR_one_from_base_cell_tail_Z_local_B
      base blocksp job :=
    [BWD] (merge_inputs_arrayR_one_from_base_cell_tail_Z_local
             base blocksp job).

  Lemma merge_block_rows_one_from_blake3_tail_model_local
      (base : ptr) (job : merge_job) :
    base |-> typed_sliceR merge_block_row_ty 0 32
    ** base .[ merge_block_row_ty ! 0 ]
       |-> blake3specs.Blake3BlockR 1 (merge_job_input job)
    ** base |-> arrayLR merge_block_row_ty 1 32
       merge_block_rowR (replicateN 31 MergeBlockUninit)
    |--
    base |-> arrayLR merge_block_row_ty 0 32
       merge_block_rowR (merge_block_rows [job]).
  Proof using CU MODd Sigma.
    unfold merge_block_rows.
    simpl.
    go using
      (merge_block_rows_one_from_blake3_tail_local_F
         base (merge_job_input job)).
  Qed.

  Definition merge_block_rows_one_from_blake3_tail_model_local_F
      base job :=
    [FWD] (merge_block_rows_one_from_blake3_tail_model_local
             base job).

  Lemma merge_index_arrayR_one_from_arrays_local
      (base : ptr) index :
    base |-> typed_sliceR Tuchar 0 32
    ** base |-> arrayLR Tuchar 0 1
       (fun index : nat => ucharR 1$m (Z.of_nat index)) [index]
    ** base |-> arrayLR Tuchar 1 32
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateN 31 ())
    |--
    base |-> merge_index_arrayR [index].
  Proof using CU MODd Sigma.
    unfold merge_index_arrayR.
    simpl.
    rewrite _at_as_Rep.
    go.
  Qed.

  Definition merge_index_arrayR_one_from_arrays_local_F base index :=
    [FWD] (merge_index_arrayR_one_from_arrays_local base index).

  Lemma merge_inputs_arrayR_one_from_arrays_local
      (base blocksp : ptr) job :
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base |-> arrayLR merge_input_ptr_ty 0 1
       (fun job_index : nat =>
          primR merge_input_ptr_ty 1$m
            (Vptr (blocksp .[ merge_block_row_ty !
                              Z.of_nat job_index ]))) [0%nat]
    ** base |-> arrayLR merge_input_ptr_ty 1 32
       (fun _ : unit => anyR merge_input_ptr_ty 1$m)
       (replicateN 31 ())
    |--
    base |-> merge_inputs_arrayR blocksp [job].
  Proof using CU MODd Sigma.
    unfold merge_inputs_arrayR.
    simpl.
    rewrite _at_as_Rep.
    go.
  Qed.

  Definition merge_inputs_arrayR_one_from_arrays_local_F
      base blocksp job :=
    [FWD] (merge_inputs_arrayR_one_from_arrays_local
             base blocksp job).

  Lemma merge_index_arrayR_snoc_from_parts_local
      (base : ptr) indexes index :
    (length indexes < 32)%nat ->
    type_ptr Tuchar (base .[ Tuchar ! Z.of_nat (length indexes) ])
    ** base |-> arrayLR Tuchar 0 (Z.of_nat (length indexes))
         (fun index : nat => ucharR 1$m (Z.of_nat index)) indexes
    ** base .[ Tuchar ! Z.of_nat (length indexes) ]
       |-> ucharR 1$m (Z.of_nat index)
    ** base |-> arrayLR Tuchar
         (Z.of_nat (length indexes) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ (32 - (Z.of_nat (length indexes) + 1)) ())
    |--
    base |-> merge_index_arrayR (indexes ++ [index]).
  Proof using CU MODd Sigma.
    intro Hindexes.
    unfold merge_index_arrayR.
    rewrite _at_as_Rep.
    rewrite app_length.
    simpl.
    destruct indexes as [| first rest].
    {
      simpl.
      go using
        (arrayLR_singleton_cell_local_F
           Tuchar ltac:(apply has_size; exact _)
           base 0
           (fun index : nat => ucharR 1$m (Z.of_nat index)) index).
    }
    {
      simpl.
      go1 using
        (arrayLR_singleton_cell_local_F
           Tuchar ltac:(apply has_size; exact _)
           base (Z.of_nat (S (length rest)))
           (fun index : nat => ucharR 1$m (Z.of_nat index)) index).
      replace
        (PosDef.Pos.of_succ_nat (length rest) + 1)%positive
        with (PosDef.Pos.of_succ_nat (length rest + 1)) by lia.
      eapply coq_tactics.tac_pure_intro.
      { apply _. }
      { apply _. }
      {
        unfold replicateZ.
        repeat rewrite lengthN_replicateN.
        f_equal.
        lia.
      }
    }
  Qed.

  Definition merge_index_arrayR_snoc_from_parts_local_F
      base indexes index Hindexes :=
    [FWD] (merge_index_arrayR_snoc_from_parts_local
             base indexes index Hindexes).

  Lemma merge_inputs_arrayR_snoc_from_parts_local
      (base blocksp : ptr) jobs job :
    (length jobs < 32)%nat ->
    type_ptr merge_input_ptr_ty
      (base .[ merge_input_ptr_ty ! Z.of_nat (length jobs) ])
    ** base |-> arrayLR merge_input_ptr_ty
         0 (Z.of_nat (length jobs))
         (fun job_index : nat =>
            primR merge_input_ptr_ty 1$m
              (Vptr
                 (blocksp .[ merge_block_row_ty !
                             Z.of_nat job_index ])))
         (seq 0 (length jobs))
    ** base .[ merge_input_ptr_ty ! Z.of_nat (length jobs) ]
       |-> ptrR<"unsigned char"> 1$m
             (blocksp .[ merge_block_row_ty !
                         Z.of_nat (length jobs) ])
    ** base |-> arrayLR merge_input_ptr_ty
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR merge_input_ptr_ty 1$m)
         (replicateZ (32 - (Z.of_nat (length jobs) + 1)) ())
    |--
    base |-> merge_inputs_arrayR blocksp (jobs ++ [job]).
  Proof using CU MODd Sigma.
    intro Hjobs.
    unfold merge_inputs_arrayR.
    rewrite _at_as_Rep.
    rewrite app_length.
    simpl.
    replace (seq 0 (length jobs + 1))
      with (seq 0 (length jobs) ++ [length jobs]).
    2: {
      rewrite (seq_app (length jobs) 1 0).
      simpl.
      reflexivity.
    }
    destruct jobs as [| first rest].
    {
      simpl.
      go using
        (arrayLR_singleton_cell_local_F
           merge_input_ptr_ty ltac:(apply has_size; exact _)
           base 0
           (fun job_index : nat =>
              primR merge_input_ptr_ty 1$m
                (Vptr
                   (blocksp .[ merge_block_row_ty !
                               Z.of_nat job_index ])))
           0%nat).
    }
    {
      simpl.
      go1 using
        (arrayLR_singleton_cell_local_F
           merge_input_ptr_ty ltac:(apply has_size; exact _)
           base (Z.of_nat (S (length rest)))
           (fun job_index : nat =>
              primR merge_input_ptr_ty 1$m
                (Vptr
                   (blocksp .[ merge_block_row_ty !
                               Z.of_nat job_index ])))
           (S (length rest))).
      replace
        (PosDef.Pos.of_succ_nat (length rest) + 1)%positive
        with (PosDef.Pos.of_succ_nat (length rest + 1)) by lia.
      eapply coq_tactics.tac_pure_intro.
      { apply _. }
      { apply _. }
      {
        unfold replicateZ.
        repeat rewrite lengthN_replicateN.
        f_equal.
        lia.
      }
    }
  Qed.

  Definition merge_inputs_arrayR_snoc_from_parts_local_F
      base blocksp jobs job Hjobs :=
    [FWD] (merge_inputs_arrayR_snoc_from_parts_local
             base blocksp jobs job Hjobs).

  Lemma merge_inputs_arrayR_snoc_from_slice_parts_local
      (base blocksp : ptr) jobs job :
    (length jobs < 32)%nat ->
    base |-> typed_sliceR merge_input_ptr_ty 0 32
    ** base |-> arrayLR merge_input_ptr_ty
         0 (Z.of_nat (length jobs))
         (fun job_index : nat =>
            primR merge_input_ptr_ty 1$m
              (Vptr
                 (blocksp .[ merge_block_row_ty !
                             Z.of_nat job_index ])))
         (seq 0 (length jobs))
    ** base .[ merge_input_ptr_ty ! Z.of_nat (length jobs) ]
       |-> ptrR<"unsigned char"> 1$m
             (blocksp .[ merge_block_row_ty !
                         Z.of_nat (length jobs) ])
    ** base |-> arrayLR merge_input_ptr_ty
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR merge_input_ptr_ty 1$m)
         (replicateZ (32 - Z.of_nat (length jobs) - 1) ())
    |--
    base |-> merge_inputs_arrayR blocksp (jobs ++ [job]).
  Proof using CU MODd Sigma.
    intro Hjobs.
    transitivity
      (type_ptr merge_input_ptr_ty
         (base .[ merge_input_ptr_ty ! Z.of_nat (length jobs) ])
       ** base |-> arrayLR merge_input_ptr_ty
            0 (Z.of_nat (length jobs))
            (fun job_index : nat =>
               primR merge_input_ptr_ty 1$m
                 (Vptr
                    (blocksp .[ merge_block_row_ty !
                                Z.of_nat job_index ])))
            (seq 0 (length jobs))
       ** base .[ merge_input_ptr_ty ! Z.of_nat (length jobs) ]
          |-> ptrR<"unsigned char"> 1$m
                (blocksp .[ merge_block_row_ty !
                            Z.of_nat (length jobs) ])
       ** base |-> arrayLR merge_input_ptr_ty
            (Z.of_nat (length jobs) + 1) 32
            (fun _ : unit => anyR merge_input_ptr_ty 1$m)
            (replicateZ (32 - (Z.of_nat (length jobs) + 1)) ())).
    {
      replace
        (32 - Z.of_nat (length jobs) - 1)%Z
        with (32 - (Z.of_nat (length jobs) + 1))%Z
        by lia.
      go using
        (typed_sliceR_elim_type_ptr_C
           merge_input_ptr_ty 0 32 base
           (i := Z.of_nat (length jobs))
           (ty2 := merge_input_ptr_ty)
           (p2 := base .[ merge_input_ptr_ty !
                          Z.of_nat (length jobs) ])
           ltac:(constructor; lia)).
    }
    {
      go using
        (merge_inputs_arrayR_snoc_from_parts_local_F
           base blocksp jobs job Hjobs).
    }
  Qed.

  Definition merge_inputs_arrayR_snoc_from_slice_parts_local_F
      base blocksp jobs job Hjobs :=
    [FWD] (merge_inputs_arrayR_snoc_from_slice_parts_local
             base blocksp jobs job Hjobs).

  Lemma merge_block_rows_snoc_from_parts_local
      (base : ptr) jobs job :
    (length jobs < 32)%nat ->
    type_ptr merge_block_row_ty
      (base .[ merge_block_row_ty ! Z.of_nat (length jobs) ])
    ** base |-> arrayLR merge_block_row_ty
         0 (Z.of_nat (length jobs)) merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs)
    ** base .[ merge_block_row_ty ! Z.of_nat (length jobs) ]
       |-> blake3specs.Blake3BlockR 1 (merge_job_input job)
    ** base |-> arrayLR merge_block_row_ty
         (Z.of_nat (length jobs) + 1) 32 merge_block_rowR
         (replicateZ
            (32 - (Z.of_nat (length jobs) + 1)) MergeBlockUninit)
    |--
    base |-> arrayLR merge_block_row_ty 0 32
      merge_block_rowR (merge_block_rows (jobs ++ [job])).
  Proof using CU MODd Sigma.
    intro Hjobs.
    change (blake3specs.Blake3BlockR 1 (merge_job_input job))
      with (merge_block_rowR (MergeBlockFull (merge_job_input job))).
    unfold merge_block_rows.
    rewrite map_app app_length.
    simpl.
    replace
      (map (fun job0 : merge_job =>
              MergeBlockFull (merge_job_input job0)) jobs ++
       MergeBlockFull (merge_job_input job) :: nil)
      with
      (map (fun job0 : merge_job =>
              MergeBlockFull (merge_job_input job0)) jobs ++
       [MergeBlockFull (merge_job_input job)]) by reflexivity.
    go1 using
      (arrayLR_singleton_cell_local_F
         merge_block_row_ty ltac:(apply has_size; exact _)
         base (Z.of_nat (length jobs))
         merge_block_rowR
         (MergeBlockFull (merge_job_input job))).
    replace (32 - Z.of_nat (length jobs) - 1)%Z
      with (32 - (Z.of_nat (length jobs) + 1))%Z by lia.
    replace (Z.of_nat (length jobs) + 1)%Z
      with (Z.of_nat (length jobs + 1)) by lia.
    go using
      (arrayLR_app_combine_local_F
         merge_block_row_ty ltac:(apply has_size; exact _)
         base 0 (Z.of_nat (length jobs))
         (Z.of_nat (length jobs) + 1)
         merge_block_rowR
         (map (fun job0 : merge_job =>
                 MergeBlockFull (merge_job_input job0)) jobs)
         [MergeBlockFull (merge_job_input job)]
         ltac:(rewrite lengthZ_correct length_map; lia)
         ltac:(rewrite lengthZ_correct; simpl; lia)).
  Qed.

  Definition merge_block_rows_snoc_from_parts_local_F
      base jobs job Hjobs :=
    [FWD] (merge_block_rows_snoc_from_parts_local
             base jobs job Hjobs).

  Lemma merge_block_rows_snoc_from_slice_parts_local
      (base : ptr) jobs job :
    (length jobs < 32)%nat ->
    base |-> typed_sliceR merge_block_row_ty 0 32
    ** base |-> arrayLR merge_block_row_ty
         0 (Z.of_nat (length jobs)) merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs)
    ** base .[ merge_block_row_ty ! Z.of_nat (length jobs) ]
       |-> blake3specs.Blake3BlockR 1 (merge_job_input job)
    ** base |-> arrayLR merge_block_row_ty
         (Z.of_nat (length jobs) + 1) 32 merge_block_rowR
         (replicateZ
            (32 - (Z.of_nat (length jobs) + 1)) MergeBlockUninit)
    |--
    base |-> arrayLR merge_block_row_ty 0 32
      merge_block_rowR (merge_block_rows (jobs ++ [job])).
  Proof using CU MODd Sigma.
    intro Hjobs.
    change (blake3specs.Blake3BlockR 1 (merge_job_input job))
      with (merge_block_rowR (MergeBlockFull (merge_job_input job))).
    unfold merge_block_rows.
    rewrite map_app app_length.
    simpl.
    replace
      (map (fun job0 : merge_job =>
              MergeBlockFull (merge_job_input job0)) jobs ++
       MergeBlockFull (merge_job_input job) :: nil)
      with
      (map (fun job0 : merge_job =>
              MergeBlockFull (merge_job_input job0)) jobs ++
       [MergeBlockFull (merge_job_input job)]) by reflexivity.
    go1 using
      (arrayLR_singleton_cell_local_F
         merge_block_row_ty ltac:(apply has_size; exact _)
         base (Z.of_nat (length jobs))
         merge_block_rowR
         (MergeBlockFull (merge_job_input job))).
    replace (32 - Z.of_nat (length jobs) - 1)%Z
      with (32 - (Z.of_nat (length jobs) + 1))%Z by lia.
    replace (Z.of_nat (length jobs) + 1)%Z
      with (Z.of_nat (length jobs + 1)) by lia.
    go using
      (arrayLR_app_combine_local_F
         merge_block_row_ty ltac:(apply has_size; exact _)
         base 0 (Z.of_nat (length jobs))
         (Z.of_nat (length jobs) + 1)
         merge_block_rowR
         (map (fun job0 : merge_job =>
                 MergeBlockFull (merge_job_input job0)) jobs)
         [MergeBlockFull (merge_job_input job)]
         ltac:(rewrite lengthZ_correct length_map; lia)
         ltac:(rewrite lengthZ_correct; simpl; lia)).
  Qed.

  Definition merge_block_rows_snoc_from_slice_parts_local_F
      base jobs job Hjobs :=
    [FWD] (merge_block_rows_snoc_from_slice_parts_local
             base jobs job Hjobs).

  Lemma merge_index_arraysR_snoc_from_parts_local
      leftsp rightsp left_indexes right_indexes left_index right_index :
    (length left_indexes < 32)%nat ->
    (length right_indexes < 32)%nat ->
    type_ptr Tuchar
      (leftsp .[ Tuchar ! Z.of_nat (length left_indexes) ])
    ** type_ptr Tuchar
      (rightsp .[ Tuchar ! Z.of_nat (length right_indexes) ])
    ** leftsp |-> arrayLR Tuchar 0
         (Z.of_nat (length left_indexes))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         left_indexes
    ** rightsp |-> arrayLR Tuchar 0
         (Z.of_nat (length right_indexes))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         right_indexes
    ** leftsp .[ Tuchar ! Z.of_nat (length left_indexes) ]
       |-> ucharR 1$m (Z.of_nat left_index)
    ** rightsp .[ Tuchar ! Z.of_nat (length right_indexes) ]
       |-> ucharR 1$m (Z.of_nat right_index)
    ** leftsp |-> arrayLR Tuchar
         (Z.of_nat (length left_indexes) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ
            (32 - (Z.of_nat (length left_indexes) + 1)) ())
    ** rightsp |-> arrayLR Tuchar
         (Z.of_nat (length right_indexes) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ
            (32 - (Z.of_nat (length right_indexes) + 1)) ())
    |--
    leftsp |-> merge_index_arrayR (left_indexes ++ [left_index])
    ** rightsp |-> merge_index_arrayR (right_indexes ++ [right_index]).
  Proof using CU MODd Sigma.
    intros Hleft Hright.
    go using
      (merge_index_arrayR_snoc_from_parts_local_F
         leftsp left_indexes left_index Hleft),
      (merge_index_arrayR_snoc_from_parts_local_F
         rightsp right_indexes right_index Hright).
  Qed.

  Definition merge_index_arraysR_snoc_from_parts_local_F
      leftsp rightsp left_indexes right_indexes left_index right_index
      Hleft Hright :=
    [FWD] (merge_index_arraysR_snoc_from_parts_local
             leftsp rightsp left_indexes right_indexes
             left_index right_index Hleft Hright).

  Lemma merge_index_arraysR_snoc_from_minus_parts_local
      leftsp rightsp left_indexes right_indexes left_index right_index :
    (length left_indexes < 32)%nat ->
    (length right_indexes < 32)%nat ->
    type_ptr Tuchar
      (leftsp .[ Tuchar ! Z.of_nat (length left_indexes) ])
    ** type_ptr Tuchar
      (rightsp .[ Tuchar ! Z.of_nat (length right_indexes) ])
    ** leftsp |-> arrayLR Tuchar 0
         (Z.of_nat (length left_indexes))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         left_indexes
    ** rightsp |-> arrayLR Tuchar 0
         (Z.of_nat (length right_indexes))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         right_indexes
    ** leftsp .[ Tuchar ! Z.of_nat (length left_indexes) ]
       |-> ucharR 1$m (Z.of_nat left_index)
    ** rightsp .[ Tuchar ! Z.of_nat (length right_indexes) ]
       |-> ucharR 1$m (Z.of_nat right_index)
    ** leftsp |-> arrayLR Tuchar
         (Z.of_nat (length left_indexes) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ
            (32 - Z.of_nat (length left_indexes) - 1) ())
    ** rightsp |-> arrayLR Tuchar
         (Z.of_nat (length right_indexes) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ
            (32 - Z.of_nat (length right_indexes) - 1) ())
    |--
    leftsp |-> merge_index_arrayR (left_indexes ++ [left_index])
    ** rightsp |-> merge_index_arrayR (right_indexes ++ [right_index]).
  Proof using CU MODd Sigma.
    intros Hleft Hright.
    replace
      (32 - Z.of_nat (length left_indexes) - 1)%Z
      with (32 - (Z.of_nat (length left_indexes) + 1))%Z
      by lia.
    replace
      (32 - Z.of_nat (length right_indexes) - 1)%Z
      with (32 - (Z.of_nat (length right_indexes) + 1))%Z
      by lia.
    go using
      (merge_index_arraysR_snoc_from_parts_local_F
         leftsp rightsp left_indexes right_indexes
         left_index right_index Hleft Hright).
  Qed.

  Definition merge_index_arraysR_snoc_from_minus_parts_local_F
      leftsp rightsp left_indexes right_indexes left_index right_index
      Hleft Hright :=
    [FWD] (merge_index_arraysR_snoc_from_minus_parts_local
             leftsp rightsp left_indexes right_indexes
             left_index right_index Hleft Hright).

  Lemma merge_index_arrayR_snoc_from_minus_len_parts_local
      (base : ptr) indexes index n :
    n = length indexes ->
    (n < 32)%nat ->
    type_ptr Tuchar (base .[ Tuchar ! Z.of_nat n ])
    ** base |-> arrayLR Tuchar 0 (Z.of_nat n)
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         indexes
    ** base .[ Tuchar ! Z.of_nat n ]
       |-> ucharR 1$m (Z.of_nat index)
    ** base |-> arrayLR Tuchar (Z.of_nat n + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ (32 - Z.of_nat n - 1) ())
    |--
    base |-> merge_index_arrayR (indexes ++ [index]).
  Proof using CU MODd Sigma.
    intros Hn Hlt.
    subst n.
    replace (32 - Z.of_nat (length indexes) - 1)%Z
      with (32 - (Z.of_nat (length indexes) + 1))%Z by lia.
    go using
      (merge_index_arrayR_snoc_from_parts_local_F
         base indexes index Hlt).
  Qed.

  Definition merge_index_arrayR_snoc_from_minus_len_parts_local_F
      base indexes index n Hn Hlt :=
    [FWD] (merge_index_arrayR_snoc_from_minus_len_parts_local
             base indexes index n Hn Hlt).

  Lemma merge_index_arraysR_snoc_jobs_from_minus_parts_local
      leftsp rightsp jobs job :
    (length jobs < 32)%nat ->
    type_ptr Tuchar
      (leftsp .[ Tuchar ! Z.of_nat (length jobs) ])
    ** type_ptr Tuchar
      (rightsp .[ Tuchar ! Z.of_nat (length jobs) ])
    ** leftsp |-> arrayLR Tuchar 0
         (Z.of_nat (length jobs))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         (map merge_job_left_index jobs)
    ** rightsp |-> arrayLR Tuchar 0
         (Z.of_nat (length jobs))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         (map merge_job_right_index jobs)
    ** leftsp .[ Tuchar ! Z.of_nat (length jobs) ]
       |-> ucharR 1$m (Z.of_nat (merge_job_left_index job))
    ** rightsp .[ Tuchar ! Z.of_nat (length jobs) ]
       |-> ucharR 1$m (Z.of_nat (merge_job_right_index job))
    ** leftsp |-> arrayLR Tuchar
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ (32 - Z.of_nat (length jobs) - 1) ())
    ** rightsp |-> arrayLR Tuchar
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ (32 - Z.of_nat (length jobs) - 1) ())
    |--
    leftsp |-> merge_index_arrayR
      (map merge_job_left_index jobs ++ [merge_job_left_index job])
    ** rightsp |-> merge_index_arrayR
      (map merge_job_right_index jobs ++ [merge_job_right_index job]).
  Proof using CU MODd Sigma.
    intro Hjobs.
    go using
      (merge_index_arrayR_snoc_from_minus_len_parts_local_F
         leftsp
         (map merge_job_left_index jobs)
         (merge_job_left_index job)
         (length jobs)
         ltac:(rewrite length_map; reflexivity)
         Hjobs),
      (merge_index_arrayR_snoc_from_minus_len_parts_local_F
         rightsp
         (map merge_job_right_index jobs)
         (merge_job_right_index job)
         (length jobs)
         ltac:(rewrite length_map; reflexivity)
         Hjobs).
  Qed.

  Definition merge_index_arraysR_snoc_jobs_from_minus_parts_local_F
      leftsp rightsp jobs job Hjobs :=
    [FWD] (merge_index_arraysR_snoc_jobs_from_minus_parts_local
             leftsp rightsp jobs job Hjobs).

  Lemma merge_index_arraysR_snoc_jobs_from_minus_slice_parts_local
      (leftsp rightsp : ptr) jobs job :
    (length jobs < 32)%nat ->
    leftsp |-> typed_sliceR Tuchar 0 32
    ** rightsp |-> typed_sliceR Tuchar 0 32
    ** leftsp |-> arrayLR Tuchar 0
         (Z.of_nat (length jobs))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         (map merge_job_left_index jobs)
    ** rightsp |-> arrayLR Tuchar 0
         (Z.of_nat (length jobs))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         (map merge_job_right_index jobs)
    ** leftsp .[ Tuchar ! Z.of_nat (length jobs) ]
       |-> ucharR 1$m (Z.of_nat (merge_job_left_index job))
    ** rightsp .[ Tuchar ! Z.of_nat (length jobs) ]
       |-> ucharR 1$m (Z.of_nat (merge_job_right_index job))
    ** leftsp |-> arrayLR Tuchar
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ (32 - Z.of_nat (length jobs) - 1) ())
    ** rightsp |-> arrayLR Tuchar
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ (32 - Z.of_nat (length jobs) - 1) ())
    |--
    leftsp |-> merge_index_arrayR
      (map merge_job_left_index jobs ++ [merge_job_left_index job])
    ** rightsp |-> merge_index_arrayR
      (map merge_job_right_index jobs ++ [merge_job_right_index job]).
  Proof using CU MODd Sigma.
    intro Hjobs.
    transitivity
      (type_ptr Tuchar
         (leftsp .[ Tuchar ! Z.of_nat (length jobs) ])
       ** type_ptr Tuchar
         (rightsp .[ Tuchar ! Z.of_nat (length jobs) ])
       ** leftsp |-> arrayLR Tuchar 0
            (Z.of_nat (length jobs))
            (fun index : nat => ucharR 1$m (Z.of_nat index))
            (map merge_job_left_index jobs)
       ** rightsp |-> arrayLR Tuchar 0
            (Z.of_nat (length jobs))
            (fun index : nat => ucharR 1$m (Z.of_nat index))
            (map merge_job_right_index jobs)
       ** leftsp .[ Tuchar ! Z.of_nat (length jobs) ]
          |-> ucharR 1$m (Z.of_nat (merge_job_left_index job))
       ** rightsp .[ Tuchar ! Z.of_nat (length jobs) ]
          |-> ucharR 1$m (Z.of_nat (merge_job_right_index job))
       ** leftsp |-> arrayLR Tuchar
            (Z.of_nat (length jobs) + 1) 32
            (fun _ : unit => anyR Tuchar 1$m)
            (replicateZ (32 - Z.of_nat (length jobs) - 1) ())
       ** rightsp |-> arrayLR Tuchar
            (Z.of_nat (length jobs) + 1) 32
            (fun _ : unit => anyR Tuchar 1$m)
            (replicateZ (32 - Z.of_nat (length jobs) - 1) ())).
    {
      go using
        (typed_sliceR_elim_type_ptr_C
           Tuchar 0 32 leftsp
           (i := Z.of_nat (length jobs))
           (ty2 := Tuchar)
           (p2 := leftsp .[ Tuchar ! Z.of_nat (length jobs) ])
           ltac:(constructor; lia)),
        (typed_sliceR_elim_type_ptr_C
           Tuchar 0 32 rightsp
           (i := Z.of_nat (length jobs))
           (ty2 := Tuchar)
           (p2 := rightsp .[ Tuchar ! Z.of_nat (length jobs) ])
           ltac:(constructor; lia)).
    }
    {
      go using
        (merge_index_arraysR_snoc_jobs_from_minus_parts_local_F
           leftsp rightsp jobs job Hjobs).
    }
  Qed.

  Definition merge_index_arraysR_snoc_jobs_from_minus_slice_parts_local_F
      leftsp rightsp jobs job Hjobs :=
    [FWD] (merge_index_arraysR_snoc_jobs_from_minus_slice_parts_local
             leftsp rightsp jobs job Hjobs).

  Lemma merge_plan_arraysR_snoc_from_parts_local
      leftsp rightsp blocksp inputsp jobs job :
    (length jobs < 32)%nat ->
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** blocksp |-> typed_sliceR merge_block_row_ty 0 32
    ** leftsp |-> arrayLR Tuchar 0 (Z.of_nat (length jobs))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         (map merge_job_left_index jobs)
    ** rightsp |-> arrayLR Tuchar 0 (Z.of_nat (length jobs))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         (map merge_job_right_index jobs)
    ** blocksp |-> arrayLR merge_block_row_ty 0
         (Z.of_nat (length jobs)) merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs)
    ** inputsp |-> arrayLR merge_input_ptr_ty 0
         (Z.of_nat (length jobs))
         (fun job_index : nat =>
            primR merge_input_ptr_ty 1$m
              (Vptr
                 (blocksp .[ merge_block_row_ty !
                             Z.of_nat job_index ])))
         (seq 0 (length jobs))
    ** leftsp .[ Tuchar ! Z.of_nat (length jobs) ]
       |-> ucharR 1$m (Z.of_nat (merge_job_left_index job))
    ** rightsp .[ Tuchar ! Z.of_nat (length jobs) ]
       |-> ucharR 1$m (Z.of_nat (merge_job_right_index job))
    ** blocksp .[ merge_block_row_ty ! Z.of_nat (length jobs) ]
       |-> blake3specs.Blake3BlockR 1 (merge_job_input job)
    ** inputsp .[ merge_input_ptr_ty ! Z.of_nat (length jobs) ]
       |-> ptrR<"unsigned char"> 1$m
             (blocksp .[ merge_block_row_ty !
                         Z.of_nat (length jobs) ])
    ** leftsp |-> arrayLR Tuchar
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ (32 - (Z.of_nat (length jobs) + 1)) ())
    ** rightsp |-> arrayLR Tuchar
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateZ (32 - (Z.of_nat (length jobs) + 1)) ())
    ** blocksp |-> arrayLR merge_block_row_ty
         (Z.of_nat (length jobs) + 1) 32 merge_block_rowR
         (replicateZ
            (32 - (Z.of_nat (length jobs) + 1)) MergeBlockUninit)
    ** inputsp |-> arrayLR merge_input_ptr_ty
         (Z.of_nat (length jobs) + 1) 32
         (fun _ : unit => anyR merge_input_ptr_ty 1$m)
         (replicateZ (32 - (Z.of_nat (length jobs) + 1)) ())
    |--
    [| Z.to_N (Z.of_nat (length jobs) + 1) =
       N.of_nat (length (jobs ++ [job])) |] **
    [| (length (jobs ++ [job]) <= 32)%nat |] **
    merge_plan_arraysR leftsp rightsp blocksp inputsp
      (jobs ++ [job]).
  Proof using CU MODd Sigma.
    intro Hjobs.
    assert
      (Hleft_indexes_lt32 :
        (length (map merge_job_left_index jobs) < 32)%nat).
    {
      rewrite length_map.
      exact Hjobs.
    }
    assert
      (Hright_indexes_lt32 :
        (length (map merge_job_right_index jobs) < 32)%nat).
    {
      rewrite length_map.
      exact Hjobs.
    }
    transitivity
      (type_ptr merge_index_array_ty leftsp
       ** type_ptr merge_index_array_ty rightsp
       ** type_ptr merge_blocks_array_ty blocksp
       ** type_ptr merge_inputs_array_ty inputsp
       ** leftsp |-> merge_index_arrayR
            (map merge_job_left_index jobs ++
             [merge_job_left_index job])
       ** rightsp |-> merge_index_arrayR
            (map merge_job_right_index jobs ++
             [merge_job_right_index job])
       ** blocksp |-> arrayLR merge_block_row_ty 0 32
            merge_block_rowR (merge_block_rows (jobs ++ [job]))
       ** inputsp |-> merge_inputs_arrayR blocksp (jobs ++ [job])).
    {
      go1 using
        (merge_inputs_arrayR_snoc_from_parts_local_F
           inputsp blocksp jobs job Hjobs).
      replace
        (32 - Z.of_nat (length jobs) - 1)%Z
        with (32 - (Z.of_nat (length jobs) + 1))%Z
        by lia.
      go1 using
        (merge_block_rows_snoc_from_slice_parts_local_F
           blocksp jobs job Hjobs).
      replace
        (32 - Z.of_nat (length jobs) - 1)%Z
        with (32 - (Z.of_nat (length jobs) + 1))%Z
        by lia.
      go using
        (merge_index_arraysR_snoc_jobs_from_minus_parts_local_F
           leftsp rightsp jobs job Hjobs).
    }
    {
      change [merge_job_left_index job]
        with (map merge_job_left_index [job]).
      change [merge_job_right_index job]
        with (map merge_job_right_index [job]).
      rewrite <- !map_app.
      go using merge_plan_arraysR_pack_F.
      eapply coq_tactics.tac_pure_intro.
      { apply _. }
      { apply _. }
      { rewrite app_length; simpl; lia. }
    }
  Qed.

  Definition merge_plan_arraysR_snoc_from_parts_local_F
      leftsp rightsp blocksp inputsp jobs job Hjobs :=
    [FWD] (merge_plan_arraysR_snoc_from_parts_local
             leftsp rightsp blocksp inputsp jobs job Hjobs).

  Lemma merge_block_rows_one_from_arrays_model_local
      (base : ptr) (job : merge_job) :
    base |-> typed_sliceR merge_block_row_ty 0 32
    ** base |-> arrayLR merge_block_row_ty 0 32
       merge_block_rowR
       (MergeBlockFull (merge_job_input job) ::
        replicateN 31 MergeBlockUninit)
    |--
    base |-> arrayLR merge_block_row_ty 0 32
       merge_block_rowR (merge_block_rows [job]).
  Proof using CU MODd Sigma.
    unfold merge_block_rows.
    simpl.
    go.
  Qed.

  Definition merge_block_rows_one_from_arrays_model_local_F
      base job :=
    [FWD] (merge_block_rows_one_from_arrays_model_local base job).

  Lemma merge_plan_arraysR_one_from_cells_local
      leftsp rightsp blocksp inputsp
      (previous current : live_node) :
    ((leftsp |-> typed_sliceR Tuchar 0 32 : mpred)
     ** (leftsp .[ Tuchar ! 0 ]
         |-> ucharR 1$m previous.(live_index) : mpred)
     ** (leftsp |-> arrayLR Tuchar 1 32
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 31 ()) : mpred))
    ** ((rightsp |-> typed_sliceR Tuchar 0 32 : mpred)
        ** (rightsp .[ Tuchar ! 0 ]
            |-> ucharR 1$m current.(live_index) : mpred)
        ** (rightsp |-> arrayLR Tuchar 1 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 31 ()) : mpred))
    ** ((blocksp |-> typed_sliceR merge_block_row_ty 0 32 : mpred)
        ** (blocksp .[ merge_block_row_ty ! 0 ]
            |-> blake3specs.Blake3BlockR 1
                  (eval_tree previous.(live_tree),
                   eval_tree current.(live_tree)) : mpred)
        ** (blocksp |-> arrayLR merge_block_row_ty 1 32
              merge_block_rowR (replicateN 31 MergeBlockUninit) : mpred))
    ** ((inputsp |-> typed_sliceR merge_input_ptr_ty 0 32 : mpred)
        ** (inputsp .[ merge_input_ptr_ty ! 0 ]
            |-> ptrR<"unsigned char"> 1$m
                  (blocksp .[ merge_block_row_ty ! 0 ]) : mpred)
        ** (inputsp |-> arrayLR merge_input_ptr_ty 1 32
              (fun _ : unit => anyR merge_input_ptr_ty 1$m)
              (replicateN 31 ()) : mpred))
    ** (type_ptr merge_index_array_ty leftsp
        ** type_ptr merge_index_array_ty rightsp
        ** type_ptr merge_blocks_array_ty blocksp
        ** type_ptr merge_inputs_array_ty inputsp)
    |--
    merge_plan_arraysR leftsp rightsp blocksp inputsp
      [{|
         merge_left := previous;
         merge_right := current;
       |}].
  Proof using CU MODd Sigma.
    change
      (blake3specs.Blake3BlockR 1
         (eval_tree previous.(live_tree),
          eval_tree current.(live_tree)))
      with
      (merge_block_rowR
         (MergeBlockFull
            (eval_tree previous.(live_tree),
             eval_tree current.(live_tree)))).
    etrans.
    {
      apply bi.sep_mono_l.
      exact
        (uchar_index_one_from_cell_tail_local
           leftsp previous.(live_index)).
    }
    etrans.
    {
      apply bi.sep_mono_r.
      apply bi.sep_mono_l.
      exact
        (uchar_index_one_from_cell_tail_local
           rightsp current.(live_index)).
    }
    etrans.
    {
      apply bi.sep_mono_r.
      apply bi.sep_mono_r.
      apply bi.sep_mono_l.
      exact
        (merge_block_rows_one_from_blake3_tail_local
           blocksp
           (eval_tree previous.(live_tree),
            eval_tree current.(live_tree))).
    }
    etrans.
    {
      apply bi.sep_mono_r.
      apply bi.sep_mono_r.
      apply bi.sep_mono_r.
      apply bi.sep_mono_l.
      exact (merge_input_one_from_cell_tail_local inputsp blocksp).
    }
    {
      etrans.
      {
        apply bi.sep_mono_l.
        exact
          (merge_index_arrayR_one_from_arrays_local
             leftsp previous.(live_index)).
      }
      etrans.
      {
        apply bi.sep_mono_r.
        apply bi.sep_mono_l.
        exact
          (merge_index_arrayR_one_from_arrays_local
             rightsp current.(live_index)).
      }
      etrans.
      {
        apply bi.sep_mono_r.
        apply bi.sep_mono_r.
        apply bi.sep_mono_l.
        exact
	          (merge_block_rows_one_from_arrays_model_local
	             blocksp
		                   {|
		                     merge_left := previous;
		                     merge_right := current;
		                   |}).
		            }
      etrans.
      {
        apply bi.sep_mono_r.
        apply bi.sep_mono_r.
        apply bi.sep_mono_r.
        apply bi.sep_mono_l.
        exact
          (merge_inputs_arrayR_one_from_arrays_local
             inputsp blocksp
             {|
               merge_left := previous;
               merge_right := current;
             |}).
      }
      transitivity
        (type_ptr merge_index_array_ty leftsp
         ** type_ptr merge_index_array_ty rightsp
         ** type_ptr merge_blocks_array_ty blocksp
         ** type_ptr merge_inputs_array_ty inputsp
         ** leftsp |-> merge_index_arrayR [previous.(live_index)]
         ** rightsp |-> merge_index_arrayR [current.(live_index)]
         ** blocksp |-> arrayLR merge_block_row_ty 0 32
              merge_block_rowR
              (merge_block_rows
                 [{|
                    merge_left := previous;
                    merge_right := current;
                  |}])
         ** inputsp |-> merge_inputs_arrayR blocksp
              [{|
                 merge_left := previous;
                 merge_right := current;
               |}]).
      {
        go.
      }
      {
        exact
          (merge_plan_arraysR_pack
             leftsp rightsp blocksp inputsp
             [{|
                merge_left := previous;
                merge_right := current;
              |}]).
      }
    }
  Qed.

  Lemma merge_plan_arraysR_one_from_cells_for_fwd_local
      leftsp rightsp blocksp inputsp
      (previous current : live_node) :
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** leftsp |-> typed_sliceR Tuchar 0 32
    ** leftsp .[ Tuchar ! 0 ]
       |-> ucharR 1$m previous.(live_index)
    ** leftsp |-> arrayLR Tuchar 1 32
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateN 31 ())
    ** rightsp |-> typed_sliceR Tuchar 0 32
    ** rightsp .[ Tuchar ! 0 ]
       |-> ucharR 1$m current.(live_index)
    ** rightsp |-> arrayLR Tuchar 1 32
       (fun _ : unit => anyR Tuchar 1$m)
       (replicateN 31 ())
    ** blocksp |-> typed_sliceR merge_block_row_ty 0 32
    ** blocksp .[ merge_block_row_ty ! 0 ]
       |-> blake3specs.Blake3BlockR 1
             (eval_tree previous.(live_tree),
              eval_tree current.(live_tree))
    ** blocksp |-> arrayLR merge_block_row_ty 1 32
       merge_block_rowR (replicateN 31 MergeBlockUninit)
    ** inputsp |-> typed_sliceR merge_input_ptr_ty 0 32
    ** inputsp .[ merge_input_ptr_ty ! 0 ]
       |-> ptrR<"unsigned char"> 1$m
             (blocksp .[ merge_block_row_ty ! 0 ])
    ** inputsp |-> arrayLR merge_input_ptr_ty 1 32
       (fun _ : unit => anyR merge_input_ptr_ty 1$m)
       (replicateN 31 ())
    |--
    merge_plan_arraysR leftsp rightsp blocksp inputsp
      [{|
         merge_left := previous;
         merge_right := current;
       |}].
  Proof using CU MODd Sigma.
    transitivity
      (((leftsp |-> typed_sliceR Tuchar 0 32 : mpred)
        ** (leftsp .[ Tuchar ! 0 ]
            |-> ucharR 1$m previous.(live_index) : mpred)
        ** (leftsp |-> arrayLR Tuchar 1 32
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 31 ()) : mpred))
       ** ((rightsp |-> typed_sliceR Tuchar 0 32 : mpred)
           ** (rightsp .[ Tuchar ! 0 ]
               |-> ucharR 1$m current.(live_index) : mpred)
           ** (rightsp |-> arrayLR Tuchar 1 32
                 (fun _ : unit => anyR Tuchar 1$m)
                 (replicateN 31 ()) : mpred))
       ** ((blocksp |-> typed_sliceR merge_block_row_ty 0 32 : mpred)
           ** (blocksp .[ merge_block_row_ty ! 0 ]
               |-> blake3specs.Blake3BlockR 1
                     (eval_tree previous.(live_tree),
                      eval_tree current.(live_tree)) : mpred)
           ** (blocksp |-> arrayLR merge_block_row_ty 1 32
                 merge_block_rowR (replicateN 31 MergeBlockUninit) : mpred))
       ** ((inputsp |-> typed_sliceR merge_input_ptr_ty 0 32 : mpred)
           ** (inputsp .[ merge_input_ptr_ty ! 0 ]
               |-> ptrR<"unsigned char"> 1$m
                     (blocksp .[ merge_block_row_ty ! 0 ]) : mpred)
           ** (inputsp |-> arrayLR merge_input_ptr_ty 1 32
                 (fun _ : unit => anyR merge_input_ptr_ty 1$m)
                 (replicateN 31 ()) : mpred))
       ** (type_ptr merge_index_array_ty leftsp
           ** type_ptr merge_index_array_ty rightsp
           ** type_ptr merge_blocks_array_ty blocksp
           ** type_ptr merge_inputs_array_ty inputsp)).
    {
      rewrite !bi.sep_assoc.
      go.
    }
    {
      exact
        (merge_plan_arraysR_one_from_cells_local
           leftsp rightsp blocksp inputsp previous current).
    }
  Qed.

  Definition merge_plan_arraysR_one_from_cells_for_fwd_local_F
      leftsp rightsp blocksp inputsp previous current :=
    [FWD] (merge_plan_arraysR_one_from_cells_for_fwd_local
             leftsp rightsp blocksp inputsp previous current).

  Definition merge_scan_prev_value (state : merge_scan_state) : Z :=
    match state.(scan_pending) with
    | None => 255%Z
    | Some node => Z.of_nat node.(live_index)
    end.

  Lemma live_nodes_bitmap_word_acc_testbit acc nodes idx :
    N.testbit
      (fold_left
         (fun bm node =>
            N.lor bm (2 ^ N.of_nat node.(live_index))) nodes acc)
      (N.of_nat idx) =
    N.testbit acc (N.of_nat idx) ||
    existsb
      (fun node => Nat.eqb idx node.(live_index)) nodes.
  Proof.
    revert acc.
    induction nodes as [| node rest IH]; intro acc.
    { simpl. now rewrite Bool.orb_false_r. }
    simpl.
    rewrite IH.
    rewrite N.lor_spec.
    rewrite N.pow2_bits_eqb.
    assert
      (Heqb :
        (N.of_nat node.(live_index) =? N.of_nat idx)%N =
        Nat.eqb idx node.(live_index)).
    {
      destruct (Nat.eqb idx node.(live_index)) eqn:Hnat.
      {
        apply Nat.eqb_eq in Hnat.
        subst idx.
        now rewrite N.eqb_refl.
      }
      apply Nat.eqb_neq in Hnat.
      apply N.eqb_neq.
      lia.
    }
    rewrite Heqb.
    destruct (N.testbit acc (N.of_nat idx));
      destruct (Nat.eqb idx node.(live_index));
      destruct
        (existsb
           (fun node0 : live_node =>
              Nat.eqb idx node0.(live_index)) rest);
      reflexivity.
  Qed.

  Lemma live_nodes_bitmap_word_testbit_nat nodes idx :
    N.testbit (live_nodes_bitmap_word nodes) (N.of_nat idx) =
    existsb
      (fun node => Nat.eqb idx node.(live_index)) nodes.
  Proof.
    unfold live_nodes_bitmap_word.
    rewrite live_nodes_bitmap_word_acc_testbit.
    reflexivity.
  Qed.

  Lemma live_nodes_bitmap_word_in node nodes :
    In node nodes ->
    N.testbit
      (live_nodes_bitmap_word nodes)
      (N.of_nat node.(live_index)) = true.
  Proof.
    intro Hnode.
    rewrite live_nodes_bitmap_word_testbit_nat.
    apply existsb_exists.
    exists node.
    split; [exact Hnode |].
    apply Nat.eqb_refl.
  Qed.

  Lemma live_nodes_bitmap_word_zero_wf_nil nodes :
    live_nodes_well_formed nodes ->
    live_nodes_bitmap_word nodes = 0%N ->
    nodes = [].
  Proof.
    intros Hwf Hzero.
    destruct nodes as [| node rest]; [reflexivity |].
    exfalso.
    pose proof
      (live_nodes_bitmap_word_in node (node :: rest)
         ltac:(simpl; auto)) as Hbit.
    rewrite Hzero in Hbit.
    rewrite N.bits_0 in Hbit.
    discriminate.
  Qed.

  Lemma scan_one_node_preserves_jobs_nonempty bit state node :
    state.(scan_jobs) <> [] ->
    (scan_one_node bit state node).(scan_jobs) <> [].
  Proof.
    destruct state as [[pending |] jobs]; simpl.
    {
      destruct
        (sibling_candidate bit pending.(live_index) node.(live_index));
        simpl; intro Hnonempty; [destruct jobs |]; simpl; congruence.
    }
    exact (fun Hnonempty => Hnonempty).
  Qed.

  Lemma scan_nodes_from_preserves_jobs_nonempty bit nodes state :
    state.(scan_jobs) <> [] ->
    (scan_nodes_from bit state nodes).(scan_jobs) <> [].
  Proof.
    revert state.
    induction nodes as [| node rest IH]; intros state Hnonempty.
    { exact Hnonempty. }
    simpl.
    apply IH.
    apply scan_one_node_preserves_jobs_nonempty.
    exact Hnonempty.
  Qed.

  Lemma scan_nodes_from_empty_jobs_after_false
      bit current next rest :
    sibling_candidate bit current.(live_index) next.(live_index) = false ->
    scan_jobs
      (scan_nodes_from bit
         {|
           scan_pending := Some next;
           scan_jobs := [];
         |} rest) = [] ->
    merge_jobs bit (next :: rest) = [].
  Proof.
    intros _ Hjobs.
    unfold merge_jobs, scan_nodes, initial_merge_scan_state.
    simpl.
    exact Hjobs.
  Qed.

  Lemma merge_jobs_nil_merge_level bit nodes :
    merge_jobs bit nodes = [] ->
    merge_level bit nodes = nodes.
  Proof.
    remember (length nodes) as fuel eqn:Hfuel.
    revert nodes Hfuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros nodes Hfuel Hjobs.
    destruct nodes as [| current [| next later]].
    { reflexivity. }
    { reflexivity. }
    simpl.
    destruct
      (sibling_candidate bit current.(live_index) next.(live_index))
      eqn:Hsibling.
    {
      exfalso.
      unfold merge_jobs, scan_nodes, initial_merge_scan_state in Hjobs.
      simpl in Hjobs.
      rewrite Hsibling in Hjobs.
      pose proof
        (scan_nodes_from_preserves_jobs_nonempty
           bit later
           {|
             scan_pending := None;
             scan_jobs :=
	               [{|
	                  merge_left := current;
	                  merge_right := next;
	                |}];
	           |}) as Hnonempty.
      apply Hnonempty in Hjobs.
      { contradiction. }
      simpl.
      discriminate.
    }
    f_equal.
    assert (Htail_jobs : merge_jobs bit (next :: later) = []).
    {
      unfold merge_jobs, scan_nodes, initial_merge_scan_state in *.
      simpl in Hjobs.
      rewrite Hsibling in Hjobs.
      exact Hjobs.
    }
    change (merge_level bit (next :: later) = next :: later).
    apply
      (IH (length (next :: later))).
    { rewrite Hfuel; simpl; lia. }
    { reflexivity. }
    exact Htail_jobs.
  Qed.

  Lemma scan_nodes_from_pending_source bit nodes state pending :
    (scan_nodes_from bit state nodes).(scan_pending) = Some pending ->
    state.(scan_pending) = Some pending \/ In pending nodes.
  Proof.
    revert state pending.
    induction nodes as [| node rest IH]; intros state pending Hpending.
    { simpl in Hpending; left; exact Hpending. }
    simpl in Hpending.
    apply IH in Hpending.
    destruct Hpending as [Hone | Hin].
    2: {
      right.
      now right.
    }
    unfold scan_one_node in Hone.
    destruct state as [[previous |] jobs]; simpl in *.
    {
      destruct
        (sibling_candidate bit previous.(live_index) node.(live_index));
        simpl in Hone.
      {
        discriminate.
      }
      right.
      left.
      now inversion Hone.
    }
    {
      right.
      left.
      now inversion Hone.
    }
  Qed.

  Lemma scan_nodes_pending_in bit nodes pending :
    (scan_nodes_from bit initial_merge_scan_state nodes).(scan_pending) =
    Some pending ->
    In pending nodes.
  Proof.
    intro Hpending.
    pose proof
      (scan_nodes_from_pending_source
         bit nodes initial_merge_scan_state pending Hpending)
      as [Hinitial | Hin].
    { discriminate. }
    exact Hin.
  Qed.

  Lemma scan_nodes_from_app bit left right state :
    scan_nodes_from bit state (left ++ right) =
    scan_nodes_from bit (scan_nodes_from bit state left) right.
  Proof.
    revert state.
    induction left as [| node left IH]; intro state.
    { reflexivity. }
    simpl.
    apply IH.
  Qed.

  Lemma live_nodes_well_formed_from_in_index lower nodes node :
    live_nodes_well_formed_from lower nodes ->
    In node nodes ->
    (node.(live_index) < page_pair_count)%nat.
  Proof.
    revert lower.
    induction nodes as [| current rest IH]; intros lower Hwf Hin.
    { contradiction. }
    simpl in Hwf.
    destruct Hwf as [[_ Hcurrent_upper] Hrest].
    destruct Hin as [Hhead | Htail].
    {
      subst node.
      exact Hcurrent_upper.
    }
    eapply IH.
    { exact Hrest. }
    exact Htail.
  Qed.

  Lemma live_nodes_well_formed_in_index nodes node :
    live_nodes_well_formed nodes ->
    In node nodes ->
    (node.(live_index) < page_pair_count)%nat.
  Proof.
    apply live_nodes_well_formed_from_in_index.
  Qed.

  Lemma live_nodes_well_formed_from_app_prefix_before_head
      lower prefix current rest previous :
    live_nodes_well_formed_from lower (prefix ++ current :: rest) ->
    In previous prefix ->
    (previous.(live_index) < current.(live_index))%nat.
  Proof.
    revert lower previous.
    induction prefix as [| node prefix IH]; intros lower previous Hwf Hin.
    { contradiction. }
    simpl in Hwf.
    destruct Hwf as [[Hnode_lower _] Hrest].
    destruct Hin as [Hhead | Htail].
    {
      subst previous.
      destruct prefix as [| next prefix_tail].
      {
        simpl in Hrest.
        destruct Hrest as [[Hcurrent_lower _] _].
        lia.
      }
      {
        assert
          (Hnext_before :
            (next.(live_index) < current.(live_index))%nat).
        {
          pose proof
            (IH (S node.(live_index)) next Hrest
               ltac:(simpl; auto)) as Hbefore.
          exact Hbefore.
        }
        simpl in Hrest.
        destruct Hrest as [[Hnext_lower _] _].
        lia.
      }
    }
    eapply IH.
    { exact Hrest. }
    exact Htail.
  Qed.

  Lemma live_nodes_well_formed_app_prefix_before_head
      prefix current rest previous :
    live_nodes_well_formed (prefix ++ current :: rest) ->
    In previous prefix ->
    (previous.(live_index) < current.(live_index))%nat.
  Proof.
    apply live_nodes_well_formed_from_app_prefix_before_head.
  Qed.

  Transparent countr_zero64 countr_zero_fuel.

  Lemma countr_zero_fuel_min_bit fuel word index :
    (index < fuel)%nat ->
    N.testbit word (N.of_nat index) = true ->
    (forall lower,
        (lower < index)%nat ->
        N.testbit word (N.of_nat lower) = false) ->
    countr_zero_fuel fuel word = N.of_nat index.
  Proof.
    revert word index.
    induction fuel as [| fuel IH]; intros word index Hindex Hbit Hlower.
    { lia. }
    destruct index as [| index].
    {
      simpl.
      destruct (word =? 0)%N eqn:Hzero.
      {
        apply N.eqb_eq in Hzero.
        subst word.
        rewrite N.bits_0 in Hbit.
        discriminate.
      }
      rewrite N.bit0_odd in Hbit.
      rewrite Hbit.
      reflexivity.
    }
    simpl.
    destruct (word =? 0)%N eqn:Hzero.
    {
      apply N.eqb_eq in Hzero.
      subst word.
      rewrite N.bits_0 in Hbit.
      discriminate.
    }
    assert (Hodd : N.odd word = false).
    {
      rewrite <- N.bit0_odd.
      change 0%N with (N.of_nat 0%nat).
      apply Hlower.
      lia.
    }
    rewrite Hodd.
    assert
      (Hshift_bit :
        N.testbit (N.shiftr word 1) (N.of_nat index) = true).
    {
      rewrite N.shiftr_spec'.
      replace (N.of_nat index + 1)%N
        with (N.of_nat (S index)) by lia.
      exact Hbit.
    }
    assert
      (Hshift_lower :
        forall lower,
          (lower < index)%nat ->
          N.testbit (N.shiftr word 1) (N.of_nat lower) = false).
    {
      intros lower Hlt.
      rewrite N.shiftr_spec'.
      replace (N.of_nat lower + 1)%N
        with (N.of_nat (S lower)) by lia.
      apply Hlower.
      lia.
    }
    rewrite (IH (N.shiftr word 1) index ltac:(lia)
               Hshift_bit Hshift_lower).
    lia.
  Qed.

  Lemma live_nodes_bitmap_word_no_lower_from lower nodes index :
    live_nodes_well_formed_from lower nodes ->
    (index < lower)%nat ->
    N.testbit (live_nodes_bitmap_word nodes) (N.of_nat index) = false.
  Proof.
    revert lower index.
    induction nodes as [| node rest IH]; intros lower index Hwf Hlt.
    {
      rewrite live_nodes_bitmap_word_testbit_nat.
      reflexivity.
    }
    {
      rewrite live_nodes_bitmap_word_testbit_nat.
      simpl.
      simpl in Hwf.
      destruct Hwf as [[Hnode_lower _] Hrest].
      replace (index =? node.(live_index))%nat with false
        by (symmetry; apply Nat.eqb_neq; lia).
      simpl.
      rewrite <- live_nodes_bitmap_word_testbit_nat.
      apply (IH (S node.(live_index)) index).
      { exact Hrest. }
      lia.
    }
  Qed.

  Lemma live_nodes_bitmap_word_cons_no_lower current rest index :
    live_nodes_well_formed (current :: rest) ->
    (index < current.(live_index))%nat ->
    N.testbit
      (live_nodes_bitmap_word (current :: rest))
      (N.of_nat index) = false.
  Proof.
    intros Hwf Hlt.
    rewrite live_nodes_bitmap_word_testbit_nat.
    simpl in Hwf.
    destruct Hwf as [[_ Hcurrent_upper] Hrest].
    simpl.
    replace (index =? current.(live_index))%nat with false
      by (symmetry; apply Nat.eqb_neq; lia).
    simpl.
    rewrite <- live_nodes_bitmap_word_testbit_nat.
    apply live_nodes_bitmap_word_no_lower_from with
      (lower := S current.(live_index)).
    { exact Hrest. }
    lia.
  Qed.

  Lemma live_nodes_bitmap_word_cons_countr_zero current rest :
    live_nodes_well_formed (current :: rest) ->
    countr_zero64 (live_nodes_bitmap_word (current :: rest)) =
    N.of_nat current.(live_index).
  Proof.
    intro Hwf.
    unfold countr_zero64.
    apply countr_zero_fuel_min_bit.
    {
      simpl in Hwf.
      destruct Hwf as [[_ Hupper] _].
      unfold page_pair_count in *.
      lia.
    }
    {
      apply live_nodes_bitmap_word_in.
      simpl; auto.
    }
    intros lower Hlower.
    apply live_nodes_bitmap_word_cons_no_lower.
    { exact Hwf. }
    exact Hlower.
  Qed.

  Lemma trim8_nat_small index :
    (index < 256)%nat ->
    trim 8 (Z.of_nat index) = Z.of_nat index.
  Proof.
    intro Hindex.
    unfold trim.
    rewrite Z.mod_small.
    { reflexivity. }
    change (2 ^ 8)%Z with 256%Z.
    lia.
  Qed.

  Lemma merge_block_rows_append_slot_lookup_local jobs row :
    (length jobs < 32)%nat ->
    (map (fun job : merge_job =>
            MergeBlockFull (merge_job_input job)) jobs ++
     replicateZ (32 - Z.of_nat (length jobs)) MergeBlockUninit) !!
      Z.of_nat (length jobs) = Some row ->
    row = MergeBlockUninit.
  Proof.
    intros Hjobs Hlookup.
    rewrite lookupZ_app in Hlookup.
    rewrite lengthZ_correct length_map in Hlookup.
    replace
      (asbool (Z.of_nat (length jobs) < Z.of_nat (length jobs)))
      with false in Hlookup.
    2: {
      symmetry.
      apply bool_decide_eq_false_2.
      lia.
    }
    replace (Z.of_nat (length jobs) - Z.of_nat (length jobs))%Z
      with 0%Z in Hlookup by lia.
    apply lookupZ_replicateZ_Some in Hlookup.
    tauto.
  Qed.

  Lemma merge_block_rows_cons_tail_lookup_local first_job later_jobs row :
    (length (first_job :: later_jobs) < 32)%nat ->
    (MergeBlockFull (merge_job_input first_job) ::
     map
       (fun job : merge_job =>
          MergeBlockFull (merge_job_input job))
       later_jobs ++
     replicateN
       (Z.to_N (32 - S (length later_jobs)))
       MergeBlockUninit) !!
      Z.pos (PosDef.Pos.of_succ_nat (length later_jobs)) =
    Some row ->
    row = MergeBlockUninit.
  Proof.
    intros Hjobs Hlookup.
    eapply merge_block_rows_append_slot_lookup_local.
    { exact Hjobs. }
    change
      (map
         (fun job : merge_job =>
            MergeBlockFull (merge_job_input job))
         (first_job :: later_jobs) ++
       replicateZ
         (32 - Z.of_nat (length (first_job :: later_jobs)))
         MergeBlockUninit)
      with
      (MergeBlockFull (merge_job_input first_job) ::
       map
         (fun job : merge_job =>
            MergeBlockFull (merge_job_input job))
         later_jobs ++
       replicateN
         (Z.to_N (32 - S (length later_jobs)))
         MergeBlockUninit).
    change
      (Z.of_nat (length (first_job :: later_jobs)))
      with (Z.pos (PosDef.Pos.of_succ_nat (length later_jobs))).
    exact Hlookup.
  Qed.

  Lemma sliceZ_replicateZ_tail_one_local {A : Type}
      (value : A) start stop :
    (start < stop)%Z ->
    sliceZ start (start + 1) stop
      (replicateZ (stop - start) value) =
    replicateZ (stop - (start + 1)) value.
  Proof.
    intro Hlt.
    unfold sliceZ.
    replace (start + 1 - start)%Z with 1%Z by lia.
    replace (stop - start)%Z
      with (1 + (stop - (start + 1)))%Z by lia.
    change (Z.to_N 1) with 1%N.
    rewrite takeN_replicateN.
    replace
      (Z.to_N (1 + (stop - (start + 1))) `min`
       Z.to_N (1 + (stop - (start + 1))))%N
      with (Z.to_N (1 + (stop - (start + 1)))) by lia.
    rewrite dropN_replicateN.
    replace
      (Z.to_N (1 + (stop - (start + 1))) - 1)%N
      with (Z.to_N (stop - (start + 1))) by lia.
    reflexivity.
  Qed.

  Lemma sliceZ_prefix_app_replicate_local {A : Type}
      (xs : list A) (value : A) :
    sliceZ 0 0 (Z.of_nat (length xs))
      (xs ++ replicateZ (32 - Z.of_nat (length xs)) value) =
    xs.
  Proof.
    unfold sliceZ, takeN, dropN.
    replace (N.to_nat (Z.to_N (0 - 0))) with 0%nat by lia.
    replace
      (N.to_nat (Z.to_N (Z.of_nat (length xs) - 0)))
      with (length xs) by lia.
    simpl.
    rewrite firstn_app.
    rewrite firstn_all.
    rewrite Nat.sub_diag.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma sliceZ_tail_after_one_app_replicate_local {A : Type}
      (xs : list A) (value : A) :
    (length xs < 32)%nat ->
    sliceZ 0 (Z.of_nat (length xs) + 1) 32
      (xs ++ replicateZ (32 - Z.of_nat (length xs)) value) =
    replicateZ (32 - (Z.of_nat (length xs) + 1)) value.
  Proof.
    intro Hxs.
    unfold sliceZ, takeN, dropN.
    replace
      (N.to_nat (Z.to_N (Z.of_nat (length xs) + 1 - 0)))
      with (length xs + 1)%nat by lia.
    replace (N.to_nat (Z.to_N (32 - 0))) with 32%nat by lia.
    rewrite firstn_all2.
    2: {
      rewrite app_length.
      unfold replicateZ.
      rewrite length_replicate.
      lia.
    }
    rewrite skipn_app.
    rewrite skipn_all2.
    2: {
      lia.
    }
    simpl.
    replace (length xs + 1 - length xs)%nat with 1%nat by lia.
    simpl.
    unfold replicateZ.
    rewrite drop_replicate.
    replace
      (N.to_nat (Z.to_N (32 - Z.of_nat (length xs))) - 1)%nat
      with (N.to_nat (Z.to_N (32 - (Z.of_nat (length xs) + 1))))
      by lia.
    reflexivity.
  Qed.

  Lemma sliceZ_prefix_cons_app_replicate_local {A : Type}
      (x : A) (xs : list A) (value : A) :
    sliceZ 0 0 (Z.of_nat (S (length xs)))
      (x :: xs ++ replicateZ
             (32 - Z.of_nat (S (length xs))) value) =
    x :: xs.
  Proof.
    change (Z.of_nat (S (length xs)))
      with (Z.of_nat (length (x :: xs))).
    change (32 - Z.of_nat (S (length xs)))%Z
      with (32 - Z.of_nat (length (x :: xs)))%Z.
    exact (sliceZ_prefix_app_replicate_local (x :: xs) value).
  Qed.

  Lemma sliceZ_tail_after_one_cons_app_replicate_local {A : Type}
      (x : A) (xs : list A) (value : A) :
    (S (length xs) < 32)%nat ->
    sliceZ 0 (Z.of_nat (S (length xs)) + 1) 32
      (x :: xs ++ replicateZ
             (32 - Z.of_nat (S (length xs))) value) =
    replicateZ (32 - (Z.of_nat (S (length xs)) + 1)) value.
  Proof.
    intro Hxs.
    change (Z.of_nat (S (length xs)))
      with (Z.of_nat (length (x :: xs))).
    change (32 - Z.of_nat (S (length xs)))%Z
      with (32 - Z.of_nat (length (x :: xs)))%Z.
    exact
      (sliceZ_tail_after_one_app_replicate_local
         (x :: xs) value Hxs).
  Qed.

  Lemma sliceZ_prefix_cons_map_app_replicate_local
      {A B : Type} (f : A -> B) (x : B) (xs : list A)
      (value : B) :
    sliceZ 0 0 (Z.of_nat (S (length xs)))
      (x :: map f xs ++
       replicateZ (32 - Z.of_nat (S (length xs))) value) =
    x :: map f xs.
  Proof.
    replace (Z.of_nat (S (length xs)))
      with (Z.of_nat (length (x :: map f xs)))
      by (simpl; rewrite length_map; lia).
    replace (32 - Z.of_nat (S (length xs)))%Z
      with (32 - Z.of_nat (length (x :: map f xs)))%Z
      by (simpl; rewrite length_map; lia).
    exact (sliceZ_prefix_app_replicate_local (x :: map f xs) value).
  Qed.

  Lemma sliceZ_tail_after_one_cons_map_app_replicate_local
      {A B : Type} (f : A -> B) (x : B) (xs : list A)
      (value : B) :
    (S (length xs) < 32)%nat ->
    sliceZ 0 (Z.of_nat (S (length xs)) + 1) 32
      (x :: map f xs ++
       replicateZ (32 - Z.of_nat (S (length xs))) value) =
    replicateZ (32 - (Z.of_nat (S (length xs)) + 1)) value.
  Proof.
    intro Hxs.
    replace (Z.of_nat (S (length xs)))
      with (Z.of_nat (length (x :: map f xs)))
      by (simpl; rewrite length_map; lia).
    replace (32 - Z.of_nat (S (length xs)))%Z
      with (32 - Z.of_nat (length (x :: map f xs)))%Z
      by (simpl; rewrite length_map; lia).
    exact
      (sliceZ_tail_after_one_app_replicate_local
         (x :: map f xs) value ltac:(simpl; rewrite length_map; lia)).
  Qed.

  Lemma sliceZ_tail_after_one_replicate_local {A : Type}
      (n : nat) (value : A) :
    (n < 32)%nat ->
    sliceZ (Z.of_nat n) (Z.of_nat n + 1) 32
      (replicateZ (32 - Z.of_nat n) value) =
    replicateZ (32 - (Z.of_nat n + 1)) value.
  Proof.
    intro Hn.
    unfold sliceZ, takeN, dropN.
    replace
      (N.to_nat (Z.to_N (Z.of_nat n + 1 - Z.of_nat n)))
      with 1%nat by lia.
    assert
      (Htake :
        take (N.to_nat (Z.to_N (32 - Z.of_nat n)))
          (replicateZ (32 - Z.of_nat n) value) =
        replicateZ (32 - Z.of_nat n) value).
    {
      apply firstn_all2.
      unfold replicateZ.
      rewrite length_replicate.
      lia.
    }
    rewrite Htake.
    unfold replicateZ.
    rewrite drop_replicate.
    replace
      (N.to_nat (Z.to_N (32 - Z.of_nat n)) - 1)%nat
      with (N.to_nat (Z.to_N (32 - (Z.of_nat n + 1))))
      by lia.
    reflexivity.
  Qed.

  Lemma subtree_width_pow2_nat bit :
    subtree_width bit = (2 ^ bit)%nat.
  Proof.
    induction bit as [| bit IH].
    { reflexivity. }
    simpl.
    rewrite IH.
    lia.
  Qed.

  Lemma subtree_width_Z bit :
    Z.of_nat (subtree_width bit) = Z.pow 2 (Z.of_nat bit).
  Proof.
    rewrite subtree_width_pow2_nat.
    rewrite Nat2Z.inj_pow.
    reflexivity.
  Qed.

  Lemma Z_shiftr_of_nat_div_pow2 index shift :
    0 <= shift ->
    Z.of_nat index ≫ shift =
    Z.of_nat (index / subtree_width (Z.to_nat shift)).
  Proof.
    intro Hshift.
    rewrite Z.shiftr_div_pow2.
    2: {
      lia.
    }
    rewrite
      (Nat2Z.inj_div index (subtree_width (Z.to_nat shift))).
    f_equal.
    rewrite subtree_width_Z.
    rewrite Z2Nat.id.
    2: {
      lia.
    }
    reflexivity.
  Qed.

  Lemma Z_odd_of_nat index :
    Z.odd (Z.of_nat index) = Nat.odd index.
  Proof.
    induction index as [| index IH].
    { reflexivity. }
    rewrite Nat2Z.inj_succ.
    rewrite Z.odd_succ.
    rewrite Nat.odd_succ.
    rewrite <- Z.negb_odd.
    rewrite IH.
    rewrite Nat.negb_odd.
    reflexivity.
  Qed.

  Lemma Z_land_one_zero_of_nat_even index :
    asbool (Z.of_nat index `land` 1 = 0) =
    Nat.even index.
  Proof.
    rewrite <- Nat.negb_odd.
    rewrite <- Z_odd_of_nat.
    rewrite <- bool_decide_land_one_odd.
    destruct (asbool (Z.of_nat index `land` 1 = 0)) eqn:Hzero;
      destruct (asbool (Z.of_nat index `land` 1 <> 0)) eqn:Hnonzero;
      try reflexivity.
    {
      apply bool_decide_eq_true_1 in Hzero.
      apply bool_decide_eq_true_1 in Hnonzero.
      lia.
    }
    {
      apply bool_decide_eq_false_1 in Hzero.
      apply bool_decide_eq_false_1 in Hnonzero.
      exfalso.
      apply Hzero.
      lia.
    }
  Qed.

  Lemma same_parent_at_level_cpp_asbool bit lhs rhs :
    0 <= bit ->
    asbool
      (Z.of_nat lhs ≫ (bit + 1) =
       Z.of_nat rhs ≫ (bit + 1)) =
    same_parent_at_level (Z.to_nat bit) lhs rhs.
  Proof.
    intro Hbit.
    unfold same_parent_at_level.
    rewrite (Z_shiftr_of_nat_div_pow2 lhs (bit + 1)).
    2: {
      lia.
    }
    rewrite (Z_shiftr_of_nat_div_pow2 rhs (bit + 1)).
    2: {
      lia.
    }
    replace (Z.to_nat (bit + 1))
      with (S (Z.to_nat bit)) by lia.
    destruct
      (lhs / subtree_width (S (Z.to_nat bit)) =?
       rhs / subtree_width (S (Z.to_nat bit)))%nat eqn:Heq.
    {
      apply Nat.eqb_eq in Heq.
      apply bool_decide_eq_true_2.
      lia.
    }
    {
      apply Nat.eqb_neq in Heq.
      apply bool_decide_eq_false_2.
      intro Hsame.
      apply Heq.
      lia.
    }
  Qed.

  Lemma same_parent_at_level_cpp_asbool_mixed bit lhs rhs :
    0 <= bit ->
    asbool
      (Z.of_nat lhs ≫ (bit + 1) =
       N.of_nat rhs ≫ (bit + 1)) =
    same_parent_at_level (Z.to_nat bit) lhs rhs.
  Proof.
    intro Hbit.
    rewrite <- (same_parent_at_level_cpp_asbool bit lhs rhs Hbit).
    assert
      (Hrhs :
        N.of_nat rhs ≫ (bit + 1) =
        Z.of_nat rhs ≫ (bit + 1)).
    {
      rewrite nat_N_Z.
      reflexivity.
    }
    rewrite Hrhs.
    reflexivity.
  Qed.

  Lemma index_bit_is_zero_cpp_asbool bit index :
    0 <= bit ->
    asbool ((Z.of_nat index ≫ bit) `land` 1 = 0) =
    index_bit_is_zero (Z.to_nat bit) index.
  Proof.
    intro Hbit.
    unfold index_bit_is_zero.
    rewrite Z_shiftr_of_nat_div_pow2.
    2: {
      lia.
    }
    apply Z_land_one_zero_of_nat_even.
  Qed.

  Lemma N_clearbit_even_succ word index :
    N.clearbit (2 * word)%N (N.succ (N.of_nat index)) =
    (2 * N.clearbit word (N.of_nat index))%N.
  Proof.
    apply N.bits_inj.
    intro bit.
    destruct (N.eq_dec bit 0%N) as [Hzero | Hnonzero].
    {
      subst bit.
      rewrite N.clearbit_neq.
      2: {
        lia.
      }
      rewrite !N.bit0_odd.
      rewrite !N.odd_even.
      reflexivity.
    }
    replace bit with (N.succ (N.pred bit)) by lia.
    rewrite N.clearbit_eqb.
    repeat rewrite N.testbit_succ_r_div2; try lia.
    repeat rewrite N.div2_even.
    rewrite N.clearbit_eqb.
    replace
      (N.succ (N.of_nat index) =?
       N.succ (N.pred bit))%N
      with (N.of_nat index =? N.pred bit)%N.
    2: {
      destruct
        (N.eq_dec (N.of_nat index) (N.pred bit))
        as [Heq | Hneq].
      {
        rewrite Heq.
        rewrite !N.eqb_refl.
        reflexivity.
      }
      replace
        (N.of_nat index =? N.pred bit)%N
        with false by (symmetry; apply N.eqb_neq; exact Hneq).
      replace
        (N.succ (N.of_nat index) =?
         N.succ (N.pred bit))%N
        with false by (symmetry; apply N.eqb_neq; lia).
      reflexivity.
    }
    reflexivity.
  Qed.

  Lemma N_land_sub_one_clearbit_lowest_nat index word :
    N.testbit word (N.of_nat index) = true ->
    (forall lower,
        (lower < index)%nat ->
        N.testbit word (N.of_nat lower) = false) ->
    (word `land` (word - 1))%N =
    N.clearbit word (N.of_nat index).
  Proof.
    revert word.
    induction index as [| index IH]; intros word Hbit Hlower.
    {
      assert (Hodd : N.odd word = true).
      { now rewrite <- N.bit0_odd. }
      assert (Hword_nonzero : word <> 0%N).
      {
        intro Hzero.
        subst word.
        rewrite N.bits_0 in Hbit.
        discriminate.
      }
      assert (Hpred_div2 :
                N.div2 (word - 1) = N.div2 word).
      {
        rewrite N.sub_1_r.
        pose proof (N.div2_odd word) as Hword.
        rewrite Hodd in Hword.
        replace (N.pred word) with (2 * N.div2 word)%N.
        2: {
          rewrite Hword.
          rewrite N.pred_sub.
          change (N.b2n true) with 1%N.
          rewrite N.div2_odd'.
          rewrite N.add_sub.
          reflexivity.
        }
        apply N.div2_even.
      }
      apply N.bits_inj.
      intro bit.
      rewrite N.land_spec.
      rewrite N.clearbit_eqb.
      destruct (N.eq_dec bit 0%N) as [Hzero | Hnonzero].
      {
        subst bit.
        rewrite N.eqb_refl.
        simpl.
        rewrite !N.bit0_odd.
        rewrite N.sub_1_r.
        rewrite N.odd_pred.
        2: {
          exact Hword_nonzero.
        }
        rewrite <- N.negb_odd.
        rewrite Hodd.
        simpl.
        reflexivity.
      }
      replace bit with (N.succ (N.pred bit)) by lia.
      repeat rewrite N.testbit_succ_r_div2; try lia.
      rewrite Hpred_div2.
      replace (N.of_nat 0 =? N.succ (N.pred bit))%N with false
        by (symmetry; apply N.eqb_neq; lia).
      destruct (N.testbit (N.div2 word) (N.pred bit));
        reflexivity.
    }
    assert (Hbit0 : N.odd word = false).
    {
      rewrite <- N.bit0_odd.
      change 0%N with (N.of_nat 0%nat).
      apply Hlower.
      lia.
    }
    assert (Hword_even : word = (2 * N.div2 word)%N).
    {
      pose proof (N.div2_odd word) as Hword.
      rewrite Hbit0 in Hword.
      simpl in Hword.
      rewrite N.add_0_r in Hword.
      exact Hword.
    }
    assert (Hdiv_nonzero : N.div2 word <> 0%N).
    {
      intro Hzero.
      assert
        (Hdiv_bit :
          N.testbit (N.div2 word) (N.of_nat index) = true).
      {
        rewrite N.testbit_div2.
        replace (N.succ (N.of_nat index))
          with (N.of_nat (S index)) by lia.
        exact Hbit.
      }
      rewrite Hzero in Hdiv_bit.
      rewrite N.bits_0 in Hdiv_bit.
      discriminate.
    }
    rewrite Hword_even.
    replace (2 * N.div2 word - 1)%N
      with (2 * (N.div2 word - 1) + 1)%N by lia.
    rewrite N.land_even_odd.
    replace (N.of_nat (S index))
      with (N.succ (N.of_nat index)) by lia.
    rewrite N_clearbit_even_succ.
    f_equal.
    apply IH.
    {
      rewrite N.testbit_div2.
      replace (N.succ (N.of_nat index))
        with (N.of_nat (S index)) by lia.
      exact Hbit.
    }
    intros lower Hlower_index.
    rewrite N.testbit_div2.
    replace (N.succ (N.of_nat lower))
      with (N.of_nat (S lower)) by lia.
    apply Hlower.
    lia.
  Qed.

  Lemma live_nodes_bitmap_word_cons_clearbit current rest :
    live_nodes_well_formed (current :: rest) ->
    N.clearbit
      (live_nodes_bitmap_word (current :: rest))
      (N.of_nat current.(live_index)) =
    live_nodes_bitmap_word rest.
  Proof.
    intro Hwf.
    apply N.bits_inj.
    intro bit.
    rewrite N.clearbit_eqb.
    rewrite <- (N2Nat.id bit).
    rewrite !live_nodes_bitmap_word_testbit_nat.
    simpl.
    destruct
      (N.to_nat bit =? current.(live_index))%nat
      eqn:Heq.
    {
      apply Nat.eqb_eq in Heq.
      rewrite Heq.
      replace
        (N.of_nat current.(live_index) =?
         N.of_nat current.(live_index))%N
        with true by (symmetry; apply N.eqb_refl).
      simpl.
      rewrite <- live_nodes_bitmap_word_testbit_nat.
      simpl in Hwf.
      destruct Hwf as [_ Hrest].
      symmetry.
      apply live_nodes_bitmap_word_no_lower_from with
        (lower := S current.(live_index)).
      { exact Hrest. }
      lia.
    }
    apply Nat.eqb_neq in Heq.
    replace
      (N.of_nat current.(live_index) =?
       N.of_nat (N.to_nat bit))%N
      with false.
    2: {
      symmetry.
      apply N.eqb_neq.
      lia.
    }
    simpl.
    rewrite Bool.andb_true_r.
    reflexivity.
  Qed.

  Lemma live_nodes_bitmap_word_cons_clear_lowest current rest :
    live_nodes_well_formed (current :: rest) ->
    (live_nodes_bitmap_word (current :: rest)
     `land` (live_nodes_bitmap_word (current :: rest) - 1))%N =
    live_nodes_bitmap_word rest.
  Proof.
    intro Hwf.
    transitivity
      (N.clearbit
         (live_nodes_bitmap_word (current :: rest))
         (N.of_nat current.(live_index))).
    {
      apply N_land_sub_one_clearbit_lowest_nat.
      {
        apply live_nodes_bitmap_word_in.
        simpl; auto.
      }
      intros lower Hlower.
      apply live_nodes_bitmap_word_cons_no_lower.
      { exact Hwf. }
      exact Hlower.
    }
    apply live_nodes_bitmap_word_cons_clearbit.
    exact Hwf.
  Qed.

  Lemma Z_to_N_of_N_land_sub_one word :
    word <> 0%N ->
    Z.to_N (Z.of_N word `land` (Z.of_N word - 1)) =
    (word `land` (word - 1))%N.
  Proof.
    intro Hword_nonzero.
    replace (Z.of_N word - 1)%Z with (Z.of_N (word - 1)).
    {
      rewrite <- N2Z.inj_land.
      apply N2Z.id.
    }
    {
      rewrite N2Z.inj_sub.
      { reflexivity. }
      destruct word as [| word].
      { contradiction. }
      lia.
    }
  Qed.

  Lemma live_nodes_bitmap_word_cons_clear_lowest_Z current rest :
    live_nodes_well_formed (current :: rest) ->
    Z.to_N
      (Z.of_N (live_nodes_bitmap_word (current :: rest))
       `land`
       (Z.of_N (live_nodes_bitmap_word (current :: rest)) - 1)) =
    live_nodes_bitmap_word rest.
  Proof.
    intro Hwf.
    rewrite Z_to_N_of_N_land_sub_one.
    { apply live_nodes_bitmap_word_cons_clear_lowest. exact Hwf. }
    intro Hzero.
    pose proof
      (live_nodes_bitmap_word_in current (current :: rest)
         ltac:(simpl; auto)) as Hbit.
    rewrite Hzero in Hbit.
    rewrite N.bits_0 in Hbit.
    discriminate.
  Qed.

  Lemma live_nodes_bitmap_word_cons_unfold current rest :
    fold_left
      (fun bm node =>
         (bm `lor` 2 ^ N.of_nat node.(live_index))%N)
      rest
      (0 `lor` 2 ^ N.of_nat current.(live_index))%N =
    live_nodes_bitmap_word (current :: rest).
  Proof.
    reflexivity.
  Qed.

  Opaque countr_zero64 countr_zero_fuel.


  (* Support copied from the former [apply_merge_scratch_outputs] proof. *)

Lemma scan_nodes_from_jobs_app bit nodes pending jobs :
  (scan_nodes_from bit
     {| scan_pending := pending; scan_jobs := jobs |} nodes).(scan_jobs) =
  jobs ++
  (scan_nodes_from bit
     {| scan_pending := pending; scan_jobs := [] |} nodes).(scan_jobs).
Proof.
  revert pending jobs.
  induction nodes as [| node rest IH]; intros pending jobs.
  {
    destruct pending as [pending |].
    {
      simpl.
      rewrite app_nil_r.
      reflexivity.
    }
    simpl.
    rewrite app_nil_r.
    reflexivity.
  }
  {
    destruct pending as [pending |].
    {
      simpl.
      destruct
        (sibling_candidate bit pending.(live_index) node.(live_index)).
      {
        rewrite (IH None (jobs ++
          [{| merge_left := pending; merge_right := node |}])).
        rewrite (IH None
          [{| merge_left := pending; merge_right := node |}]).
        rewrite app_assoc.
        reflexivity.
      }
      {
        exact (IH (Some node) jobs).
      }
    }
    simpl.
    exact (IH (Some node) jobs).
  }
Qed.

Lemma merge_jobs_sibling bit current next later :
  sibling_candidate bit current.(live_index) next.(live_index) = true ->
  merge_jobs bit (current :: next :: later) =
  {| merge_left := current; merge_right := next |} ::
  merge_jobs bit later.
Proof.
  intro Hsibling.
  unfold merge_jobs, scan_nodes.
  simpl.
  rewrite Hsibling.
  rewrite scan_nodes_from_jobs_app.
  reflexivity.
Qed.

Lemma merge_jobs_not_sibling bit current next later :
  sibling_candidate bit current.(live_index) next.(live_index) = false ->
  merge_jobs bit (current :: next :: later) =
  merge_jobs bit (next :: later).
Proof.
  intro Hsibling.
  unfold merge_jobs, scan_nodes.
  simpl.
  rewrite Hsibling.
  reflexivity.
Qed.

Lemma merge_hash_outputs_lookup jobs old_outputs i job :
  jobs !! i = Some job ->
  merge_hash_outputs jobs old_outputs !! i =
  Some (merge_job_output job).
Proof.
  intro Hlookup.
  apply lookup_app_l_Some.
  unfold merge_hash_outputs, blake3specs.blake3_hash_many_outputs,
    merge_job_output.
  rewrite !list_lookup_fmap.
  rewrite Hlookup.
  reflexivity.
Qed.

Lemma lookup_nat_of_lookupZ_nat {A : Type} (xs : list A) i x :
  xs !! Z.of_nat i = Some x ->
  xs !! i = Some x.
Proof.
  intro Hlookup.
  destruct (proj1 (lookupZ_Some_to_nat xs (Z.of_nat i) x) Hlookup)
    as [_ Hlookup_nat].
  rewrite Nat2Z.id in Hlookup_nat.
  exact Hlookup_nat.
Qed.

Lemma lookupZ_nat_of_lookup_nat {A : Type} (xs : list A) i x :
  xs !! i = Some x ->
  xs !! Z.of_nat i = Some x.
Proof.
  intro Hlookup.
  apply lookupZ_Some_to_nat.
  split.
  {
    lia.
  }
  {
    rewrite Nat2Z.id.
    exact Hlookup.
  }
Qed.

Lemma apply_merge_jobs_to_scratch_app scratch lhs rhs :
  apply_merge_jobs_to_scratch scratch (lhs ++ rhs) =
  apply_merge_jobs_to_scratch
    (apply_merge_jobs_to_scratch scratch lhs) rhs.
Proof.
  revert scratch.
  induction lhs as [| job rest IH]; intro scratch.
  {
    reflexivity.
  }
  {
    simpl.
    exact (IH (apply_merge_job_to_scratch scratch job)).
  }
Qed.

Lemma apply_merge_jobs_to_scratch_take_succ scratch jobs i job :
  jobs !! i = Some job ->
  apply_merge_jobs_to_scratch scratch (take (S i) jobs) =
  apply_merge_job_to_scratch
    (apply_merge_jobs_to_scratch scratch (take i jobs)) job.
Proof.
  intro Hlookup.
  rewrite (take_S_r jobs i job Hlookup).
  rewrite apply_merge_jobs_to_scratch_app.
  reflexivity.
Qed.

Lemma apply_merge_jobs_to_bitmap_app bm lhs rhs :
  apply_merge_jobs_to_bitmap bm (lhs ++ rhs) =
  apply_merge_jobs_to_bitmap
    (apply_merge_jobs_to_bitmap bm lhs) rhs.
Proof.
  revert bm.
  induction lhs as [| job rest IH]; intro bm.
  {
    reflexivity.
  }
  {
    simpl.
    exact (IH (apply_merge_job_to_bitmap bm job)).
  }
Qed.

Lemma apply_merge_jobs_to_bitmap_take_succ bm jobs i job :
  jobs !! i = Some job ->
  apply_merge_jobs_to_bitmap bm (take (S i) jobs) =
  apply_merge_job_to_bitmap
    (apply_merge_jobs_to_bitmap bm (take i jobs)) job.
Proof.
  intro Hlookup.
  rewrite (take_S_r jobs i job Hlookup).
  rewrite apply_merge_jobs_to_bitmap_app.
  reflexivity.
Qed.

Lemma to_nat_Z_to_N_N_of_nat_succ i :
  N.to_nat (Z.to_N (N.of_nat i + 1)) = S i.
Proof.
  replace (Z.to_N (N.of_nat i + 1)) with (N.succ (N.of_nat i)) by lia.
  rewrite N2Nat.inj_succ.
  rewrite Nat2N.id.
  reflexivity.
Qed.

Lemma clearbit_ulong_expr bm idx :
  (bm < 2 ^ 64)%N ->
  (idx < 64)%nat ->
  Z.to_N
    (bm `land`
     trim 64 (Z.lnot (trim 64 (1 ≪ idx)))) =
  N.clearbit bm (N.of_nat idx).
Proof.
  intros Hbm Hidx.
  assert
    (Hshift :
      trim 64 (1 ≪ idx) = (2 ^ Z.of_nat idx)%Z).
  {
    rewrite Z.shiftl_1_l.
    apply to_unsigned_bits_id.
    split.
    {
      apply Z.pow_nonneg.
      lia.
    }
    {
      apply Z.pow_lt_mono_r; lia.
    }
  }
  rewrite Hshift.
  assert
    (Hmask :
      (bm `land` trim 64 (Z.lnot (2 ^ Z.of_nat idx)))%Z =
      (bm `land` Z.lnot (2 ^ Z.of_nat idx))%Z).
  {
    rewrite modulo.trim_as_bitwise_and.
    rewrite Z.land_assoc.
    assert (Hbm_ones : (bm `land` Z.ones 64)%Z = Z.of_N bm).
    {
      rewrite Z.land_ones.
      {
        rewrite Z.mod_small.
        { reflexivity. }
        { lia. }
      }
      lia.
    }
    rewrite Hbm_ones.
    reflexivity.
  }
  rewrite Hmask.
  rewrite <- Z.ldiff_land.
  rewrite N.clearbit_spec'.
  replace (2 ^ Z.of_nat idx)%Z with (Z.of_N (2 ^ N.of_nat idx)).
  2: {
    rewrite N2Z.inj_pow.
    rewrite nat_N_Z.
    reflexivity.
  }
  rewrite <- N2Z.inj_ldiff.
  apply N2Z.id.
Qed.

Lemma apply_merge_job_to_scratch_length scratch job :
  length (apply_merge_job_to_scratch scratch job) = length scratch.
Proof.
  unfold apply_merge_job_to_scratch.
  apply length_insert.
Qed.

Lemma apply_merge_jobs_to_scratch_length scratch jobs :
  length (apply_merge_jobs_to_scratch scratch jobs) = length scratch.
Proof.
  revert scratch.
  induction jobs as [| job rest IH]; intro scratch.
  {
    reflexivity.
  }
  {
    simpl.
    rewrite IH.
    apply apply_merge_job_to_scratch_length.
  }
Qed.

Lemma live_nodes_well_formed_from_member_bounds lower nodes node :
  live_nodes_well_formed_from lower nodes ->
  In node nodes ->
  (lower <= live_index node < page_pair_count)%nat.
Proof.
  revert lower.
  induction nodes as [| current rest IH]; intros lower Hwf Hin.
  {
    contradiction.
  }
  {
    simpl in Hwf, Hin.
    destruct Hwf as [Hcurrent Hrest].
    destruct Hin as [Hin | Hin].
    {
      subst.
      exact Hcurrent.
    }
    {
      specialize (IH (S (live_index current)) Hrest Hin).
      lia.
    }
  }
Qed.

Lemma merge_jobs_member_indices_bound_from bit lower nodes job :
  live_nodes_well_formed_from lower nodes ->
  In job (merge_jobs bit nodes) ->
  (lower <= merge_job_left_index job < page_pair_count)%nat /\
  (lower <= merge_job_right_index job < page_pair_count)%nat.
Proof.
  remember (length nodes) as fuel eqn:Hfuel.
  revert lower nodes Hfuel.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros lower nodes Hfuel Hwf Hin.
  destruct nodes as [| current rest].
  {
    unfold merge_jobs, scan_nodes, initial_merge_scan_state in Hin.
    simpl in Hin.
    contradiction.
  }
  destruct rest as [| next later].
  {
    unfold merge_jobs, scan_nodes, initial_merge_scan_state in Hin.
    simpl in Hin.
    contradiction.
  }
  simpl in Hwf.
  destruct Hwf as [Hcurrent Hrest].
  simpl in Hrest.
  destruct Hrest as [Hnext Hlater].
  destruct
    (sibling_candidate bit current.(live_index) next.(live_index))
    eqn:Hsibling.
  {
    rewrite (merge_jobs_sibling bit current next later Hsibling) in Hin.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    {
      subst job.
      unfold merge_job_left_index, merge_job_right_index.
      simpl.
      split; lia.
    }
    assert (Hlater_len : (length later < fuel)%nat).
    {
      rewrite Hfuel.
      simpl.
      lia.
    }
    specialize
      (IH (length later) Hlater_len
         (S next.(live_index)) later eq_refl Hlater Hin)
      as [Hleft Hright].
    split; lia.
  }
  {
    rewrite (merge_jobs_not_sibling bit current next later Hsibling) in Hin.
    assert (Hrest_len : (length (next :: later) < fuel)%nat).
    {
      rewrite Hfuel.
      simpl.
      lia.
    }
    specialize
      (IH (length (next :: later)) Hrest_len
         (S current.(live_index)) (next :: later) eq_refl
         (conj Hnext Hlater) Hin)
      as [Hleft Hright].
    split; lia.
  }
Qed.

Lemma merge_jobs_lookup_left_index_bound bit nodes i job :
  live_nodes_well_formed nodes ->
  merge_jobs bit nodes !! i = Some job ->
  (merge_job_left_index job < page_pair_count)%nat.
Proof.
  intros Hwf Hlookup.
  pose proof
    (merge_jobs_member_indices_bound_from
       bit 0 nodes job Hwf
       (proj1 (list_elem_of_In (merge_jobs bit nodes) job)
          (list_elem_of_lookup_2 (merge_jobs bit nodes) i job Hlookup)))
    as [Hleft _].
  lia.
Qed.

  Lemma merge_jobs_lookup_right_index_bound bit nodes i job :
    live_nodes_well_formed nodes ->
    merge_jobs bit nodes !! i = Some job ->
    (merge_job_right_index job < page_pair_count)%nat.
Proof.
  intros Hwf Hlookup.
  pose proof
    (merge_jobs_member_indices_bound_from
       bit 0 nodes job Hwf
       (proj1 (list_elem_of_In (merge_jobs bit nodes) job)
          (list_elem_of_lookup_2 (merge_jobs bit nodes) i job Hlookup)))
    as [_ Hright].
    lia.
  Qed.

  Lemma nth_insert_eq {A : Type} (xs : list A) i (x d : A) :
    (i < length xs)%nat ->
    nth i (<[i := x]> xs) d = x.
  Proof.
    intro Hlt.
    apply nth_lookup_Some.
    apply list_lookup_insert_eq.
    exact Hlt.
  Qed.

  Lemma nth_insert_ne {A : Type} (xs : list A) i j (x d : A) :
    i <> j ->
    nth i (<[j := x]> xs) d = nth i xs d.
  Proof.
    intro Hne.
    rewrite !nth_lookup.
    rewrite list_lookup_insert_ne.
    {
      reflexivity.
    }
    {
      intro Heq.
      apply Hne.
      symmetry.
      exact Heq.
    }
  Qed.

  Lemma apply_merge_jobs_to_scratch_nth_below bit lower nodes scratch idx :
    live_nodes_well_formed_from lower nodes ->
    (idx < lower)%nat ->
    nth idx
      (apply_merge_jobs_to_scratch scratch (merge_jobs bit nodes)) 0%N =
    nth idx scratch 0%N.
  Proof.
    remember (length nodes) as fuel eqn:Hfuel.
    revert lower nodes scratch Hfuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros lower nodes scratch Hfuel Hwf Hidx.
    destruct nodes as [| current rest].
    {
      reflexivity.
    }
    destruct rest as [| next later].
    {
      reflexivity.
    }
    simpl in Hwf.
    destruct Hwf as [Hcurrent Hrest].
    simpl in Hrest.
    destruct Hrest as [Hnext Hlater].
    destruct
      (sibling_candidate bit current.(live_index) next.(live_index))
      eqn:Hsibling.
    {
      rewrite (merge_jobs_sibling bit current next later Hsibling).
      simpl.
      assert (Hlater_len : (length later < fuel)%nat).
      {
        rewrite Hfuel.
        simpl.
        lia.
      }
      rewrite
        (IH (length later) Hlater_len
           (S next.(live_index)) later
           (apply_merge_job_to_scratch scratch
              {| merge_left := current; merge_right := next |})
           eq_refl Hlater).
      2: {
        lia.
      }
      unfold apply_merge_job_to_scratch.
      rewrite nth_insert_ne.
      {
        reflexivity.
      }
      {
        unfold merge_job_left_index.
        simpl.
        lia.
      }
    }
    {
      rewrite (merge_jobs_not_sibling bit current next later Hsibling).
      assert (Hrest_len : (length (next :: later) < fuel)%nat).
      {
        rewrite Hfuel.
        simpl.
        lia.
      }
      eapply IH.
      {
        exact Hrest_len.
      }
      {
        reflexivity.
      }
      {
        exact (conj Hnext Hlater).
      }
      {
        lia.
      }
    }
  Qed.

  Local Transparent
    exec_specs.bytes32_be_values_from
    exec_specs.bytes32_be_values.

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
    blake3specs.bytes32_byte_values.
  rewrite List.length_app.
  rewrite !bytes32_be_values_length.
  reflexivity.
Qed.

Local Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values.

Lemma apply_merge_jobs_to_bitmap_testbit_nat bm jobs idx :
  N.testbit (apply_merge_jobs_to_bitmap bm jobs) (N.of_nat idx) =
  N.testbit bm (N.of_nat idx) &&
  negb
    (existsb
       (fun job =>
          N.eqb
            (N.of_nat (merge_job_right_index job))
            (N.of_nat idx)) jobs).
Proof.
  revert bm.
  induction jobs as [| job rest IH]; intro bm.
  {
    simpl.
    destruct (N.testbit bm (N.of_nat idx)); reflexivity.
  }
  {
    simpl.
    rewrite IH.
    unfold apply_merge_job_to_bitmap, merge_job_right_index.
    rewrite N.clearbit_eqb.
    simpl.
    destruct (N.testbit bm (N.of_nat idx));
      destruct (N.of_nat (live_index (merge_right job)) =? N.of_nat idx)%N;
      destruct
        (existsb
           (fun job0 : merge_job =>
              (N.of_nat (merge_job_right_index job0) =?
               N.of_nat idx)%N) rest);
      reflexivity.
  }
Qed.

Lemma live_node_existsb_nat_eqb_to_N nodes idx :
  existsb
    (fun node : live_node =>
       (idx =? node.(live_index))%nat) nodes =
  existsb
    (fun node : live_node =>
       (N.of_nat node.(live_index) =? N.of_nat idx)%N) nodes.
Proof.
  induction nodes as [| node rest IH].
  { reflexivity. }
  simpl.
  rewrite IH.
  assert
    (Heqb :
      (idx =? live_index node)%nat =
      (N.of_nat (live_index node) =? N.of_nat idx)%N).
  {
    destruct (Nat.eqb idx node.(live_index)) eqn:Hnat.
    {
      apply Nat.eqb_eq in Hnat.
      subst idx.
      now rewrite N.eqb_refl.
    }
    apply Nat.eqb_neq in Hnat.
    symmetry.
    apply N.eqb_neq.
    lia.
  }
  rewrite Heqb.
  reflexivity.
Qed.

Lemma existsb_live_node_index_below_false lower nodes idx :
  live_nodes_well_formed_from lower nodes ->
  (idx < lower)%nat ->
  existsb
    (fun node =>
       N.eqb (N.of_nat node.(live_index)) (N.of_nat idx)) nodes =
  false.
Proof.
  intros Hwf Hidx.
  destruct
    (existsb
       (fun node : live_node =>
          (N.of_nat (live_index node) =? N.of_nat idx)%N) nodes)
    eqn:Hexists.
  2: {
    reflexivity.
  }
  apply existsb_exists in Hexists.
  destruct Hexists as [node [Hin Heq]].
  apply N.eqb_eq in Heq.
  apply Nat2N.inj in Heq.
  pose proof
    (live_nodes_well_formed_from_member_bounds
       lower nodes node Hwf Hin) as Hbounds.
  lia.
Qed.

Lemma existsb_merge_job_right_below_false bit lower nodes idx :
  live_nodes_well_formed_from lower nodes ->
  (idx < lower)%nat ->
  existsb
    (fun job =>
       N.eqb
         (N.of_nat (merge_job_right_index job))
         (N.of_nat idx)) (merge_jobs bit nodes) =
  false.
Proof.
  intros Hwf Hidx.
  destruct
    (existsb
       (fun job : merge_job =>
          (N.of_nat (merge_job_right_index job) =?
           N.of_nat idx)%N) (merge_jobs bit nodes))
    eqn:Hexists.
  2: {
    reflexivity.
  }
  apply existsb_exists in Hexists.
  destruct Hexists as [job [Hin Heq]].
  apply N.eqb_eq in Heq.
  apply Nat2N.inj in Heq.
  pose proof
    (merge_jobs_member_indices_bound_from
       bit lower nodes job Hwf Hin) as [_ Hright].
  lia.
Qed.

Lemma merge_level_index_existsb_jobs_from bit lower nodes idx :
  live_nodes_well_formed_from lower nodes ->
  existsb
    (fun node =>
       N.eqb (N.of_nat node.(live_index)) (N.of_nat idx))
    (merge_level bit nodes) =
  existsb
    (fun node =>
       N.eqb (N.of_nat node.(live_index)) (N.of_nat idx)) nodes &&
  negb
    (existsb
       (fun job =>
          N.eqb
            (N.of_nat (merge_job_right_index job))
            (N.of_nat idx)) (merge_jobs bit nodes)).
Proof.
  remember (length nodes) as fuel eqn:Hfuel.
  revert lower nodes Hfuel.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros lower nodes Hfuel Hwf.
  destruct nodes as [| current rest].
  {
    reflexivity.
  }
  destruct rest as [| next later].
  {
    simpl.
    destruct
      (N.of_nat (live_index current) =? N.of_nat idx)%N;
      reflexivity.
  }
  simpl in Hwf.
  destruct Hwf as [Hcurrent Hrest].
  simpl in Hrest.
  destruct Hrest as [Hnext Hlater].
  destruct
    (sibling_candidate bit current.(live_index) next.(live_index))
    eqn:Hsibling.
  {
    rewrite (merge_jobs_sibling bit current next later Hsibling).
    simpl.
    rewrite Hsibling.
    simpl.
    cbn [merge_job_right_index].
    change (let (live_index, _) := next in live_index)
      with (live_index next) in *.
    assert (Hlater_len : (length later < fuel)%nat).
    {
      rewrite Hfuel.
      simpl.
      lia.
    }
    rewrite (IH (length later) Hlater_len
               (S next.(live_index)) later eq_refl Hlater).
    set (c :=
      (N.of_nat (live_index current) =? N.of_nat idx)%N).
    set (n :=
      (N.of_nat (live_index next) =? N.of_nat idx)%N).
    set (l :=
      existsb
        (fun node : live_node =>
           (N.of_nat (live_index node) =? N.of_nat idx)%N) later).
    set (j :=
      existsb
        (fun job : merge_job =>
           (N.of_nat (merge_job_right_index job) =?
            N.of_nat idx)%N) (merge_jobs bit later)).
    assert (Hc : c = true -> n = false /\ l = false /\ j = false).
    {
      intro Hc.
      subst c n l j.
      apply N.eqb_eq in Hc.
      apply Nat2N.inj in Hc.
      split.
      {
        apply N.eqb_neq.
        intro Hn.
        apply Nat2N.inj in Hn.
        lia.
      }
      split.
      {
        apply existsb_live_node_index_below_false with
          (lower := S next.(live_index)).
        {
          exact Hlater.
        }
        {
          lia.
        }
      }
      {
        apply existsb_merge_job_right_below_false with
          (lower := S next.(live_index)).
        {
          exact Hlater.
        }
        {
          lia.
        }
      }
    }
    assert (Hn : n = true -> l = false /\ j = false).
    {
      intro Hn.
      subst n l j.
      apply N.eqb_eq in Hn.
      apply Nat2N.inj in Hn.
      split.
      {
        apply existsb_live_node_index_below_false with
          (lower := S next.(live_index)).
        {
          exact Hlater.
        }
        {
          lia.
        }
      }
      {
        apply existsb_merge_job_right_below_false with
          (lower := S next.(live_index)).
        {
          exact Hlater.
        }
        {
          lia.
        }
      }
    }
    destruct c eqn:Hc_eq.
    {
      destruct (Hc eq_refl) as [-> [-> ->]].
      reflexivity.
    }
    destruct n eqn:Hn_eq.
    {
      destruct (Hn eq_refl) as [-> ->].
      reflexivity.
    }
    destruct l; destruct j; reflexivity.
  }
  {
    rewrite (merge_jobs_not_sibling bit current next later Hsibling).
    simpl.
    rewrite Hsibling.
    simpl.
    cbn [merge_job_right_index].
    change (let (live_index, _) := current in live_index)
      with (live_index current) in *.
    assert (Hrest_len : (length (next :: later) < fuel)%nat).
    {
      rewrite Hfuel.
      simpl.
      lia.
    }
    rewrite (IH (length (next :: later)) Hrest_len
               (S current.(live_index)) (next :: later)
               eq_refl (conj Hnext Hlater)).
    simpl.
    set (c :=
      (N.of_nat (live_index current) =? N.of_nat idx)%N).
    set (j :=
      existsb
        (fun job : merge_job =>
           (N.of_nat (merge_job_right_index job) =?
            N.of_nat idx)%N) (merge_jobs bit (next :: later))).
    assert (Hc : c = true -> j = false).
    {
      intro Hc.
      subst c j.
      apply N.eqb_eq in Hc.
      apply Nat2N.inj in Hc.
      apply existsb_merge_job_right_below_false with
        (lower := S current.(live_index)).
      {
        exact (conj Hnext Hlater).
      }
      {
        lia.
      }
    }
    destruct c eqn:Hc_eq.
    {
      rewrite (Hc eq_refl).
      reflexivity.
    }
    destruct
      (existsb
         (fun node : live_node =>
            (N.of_nat (live_index node) =? N.of_nat idx)%N)
         (next :: later));
      destruct j;
      reflexivity.
  }
Qed.

Lemma apply_merge_jobs_to_bitmap_live_nodes bit nodes :
  live_nodes_well_formed nodes ->
  apply_merge_jobs_to_bitmap
    (live_nodes_bitmap_word nodes) (merge_jobs bit nodes) =
  live_nodes_bitmap_word (merge_level bit nodes).
Proof.
  intro Hwf.
  apply N_ext.
  intro i.
  pose (idx := N.to_nat i).
  replace i with (N.of_nat idx) by (subst idx; apply N2Nat.id).
  rewrite apply_merge_jobs_to_bitmap_testbit_nat.
  rewrite !live_nodes_bitmap_word_testbit_nat.
  rewrite !live_node_existsb_nat_eqb_to_N.
  symmetry.
  exact (merge_level_index_existsb_jobs_from bit 0 nodes idx Hwf).
Qed.

Lemma apply_merge_jobs_to_scratch_represents bit nodes scratch :
  live_nodes_well_formed nodes ->
  scratch_represents_live_nodes scratch nodes ->
  scratch_represents_live_nodes
    (apply_merge_jobs_to_scratch scratch (merge_jobs bit nodes))
    (merge_level bit nodes).
Proof.
  remember (length nodes) as fuel eqn:Hfuel.
  revert nodes scratch Hfuel.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros nodes scratch Hfuel Hwf Hscratch.
  destruct Hscratch as [Hscratch_len Hscratch_nodes].
  split.
  {
    rewrite apply_merge_jobs_to_scratch_length.
    exact Hscratch_len.
  }
  intros node Hnode.
  destruct nodes as [| current rest].
  {
    contradiction.
  }
  destruct rest as [| next later].
  {
    simpl in Hnode.
    destruct Hnode as [Hnode | Hnode].
    {
      subst node.
      exact (Hscratch_nodes current (or_introl eq_refl)).
    }
    {
      contradiction.
    }
  }
  simpl in Hwf.
  destruct Hwf as [Hcurrent Hrest].
  simpl in Hrest.
  destruct Hrest as [Hnext Hlater].
  destruct
    (sibling_candidate bit current.(live_index) next.(live_index))
    eqn:Hsibling.
  {
    rewrite (merge_jobs_sibling bit current next later Hsibling).
    simpl.
    simpl in Hnode.
    rewrite Hsibling in Hnode.
    destruct Hnode as [Hnode | Hnode].
    {
      subst node.
      assert (Hlater_len : (length later < fuel)%nat).
      {
        rewrite Hfuel.
        simpl.
        lia.
      }
      rewrite
        (apply_merge_jobs_to_scratch_nth_below
           bit (S next.(live_index)) later
           (apply_merge_job_to_scratch scratch
              {| merge_left := current; merge_right := next |})
           current.(live_index) Hlater).
      2: {
        lia.
      }
      unfold apply_merge_job_to_scratch, merge_job_left_index.
      simpl.
      rewrite nth_insert_eq.
      {
        reflexivity.
      }
      {
        rewrite Hscratch_len.
        lia.
      }
    }
    {
      assert
        (Hscratch_later :
          scratch_represents_live_nodes
            (apply_merge_job_to_scratch scratch
               {| merge_left := current; merge_right := next |})
            later).
      {
        split.
        {
          unfold apply_merge_job_to_scratch.
          rewrite length_insert.
          exact Hscratch_len.
        }
        intros later_node Hlater_node.
        unfold apply_merge_job_to_scratch, merge_job_left_index.
        simpl.
        rewrite nth_insert_ne.
        {
          apply Hscratch_nodes.
          right.
          right.
          exact Hlater_node.
        }
        {
          pose proof
            (live_nodes_well_formed_from_member_bounds
               (S next.(live_index)) later later_node
               Hlater Hlater_node) as Hlater_bounds.
          lia.
        }
      }
      assert
        (Hlater_len : (length later < fuel)%nat).
      {
        rewrite Hfuel.
        simpl.
        lia.
      }
      assert (Hlater_wf : live_nodes_well_formed later).
      {
        unfold live_nodes_well_formed.
        eapply live_nodes_well_formed_from_weaken with
          (lower := S next.(live_index)).
        2: {
          exact Hlater.
        }
        lia.
      }
      pose proof
        (IH (length later) Hlater_len later
           (apply_merge_job_to_scratch scratch
              {| merge_left := current; merge_right := next |})
           eq_refl Hlater_wf Hscratch_later)
        as [_ Hlater_rep].
      exact (Hlater_rep node Hnode).
    }
  }
  {
    rewrite (merge_jobs_not_sibling bit current next later Hsibling).
    simpl in Hnode.
    rewrite Hsibling in Hnode.
    destruct Hnode as [Hnode | Hnode].
    {
      subst node.
      rewrite
        (apply_merge_jobs_to_scratch_nth_below
           bit (S current.(live_index)) (next :: later)
           scratch current.(live_index) (conj Hnext Hlater)).
      {
        apply Hscratch_nodes.
        left.
        reflexivity.
      }
      {
        lia.
      }
    }
    {
      assert
        (Hscratch_rest :
          scratch_represents_live_nodes scratch (next :: later)).
      {
        split.
        {
          exact Hscratch_len.
        }
        intros rest_node Hrest_node.
        apply Hscratch_nodes.
        right.
        exact Hrest_node.
      }
      assert (Hrest_len : (length (next :: later) < fuel)%nat).
      {
        rewrite Hfuel.
        simpl.
        lia.
      }
      assert (Hrest_wf : live_nodes_well_formed (next :: later)).
      {
        unfold live_nodes_well_formed.
        eapply live_nodes_well_formed_from_weaken with
          (lower := S current.(live_index)).
        2: {
          simpl.
          exact (conj Hnext Hlater).
        }
        lia.
      }
      pose proof
        (IH (length (next :: later)) Hrest_len (next :: later)
           scratch eq_refl Hrest_wf Hscratch_rest)
        as [_ Hrest_rep].
      exact (Hrest_rep node Hnode).
    }
  }
Qed.

  #[local] Hint Resolve
    UNSAFE_read_prim_cancel
    type_ptr_elim_type_ptr_C
    typed_sliceR_elim_type_ptr_C : sl_opacity.
  #[local] Hint Opaque
    ScratchR live_nodes_bitmap_word merge_level merge_jobs
    merge_plan_arraysR merge_plan_arrays_cleanupR
    merge_index_arrayR merge_inputs_arrayR
    merge_hash_outputs apply_merge_jobs_to_scratch
    apply_merge_jobs_to_bitmap : sl_opacity.

  Lemma use_wand_local_r (P Q : mpred) :
    P ** (P -* Q) |-- Q.
  Proof using CU MODd Sigma.
    go.
  Qed.

	  Definition use_wand_local_r_F P Q :=
	    [FWD] (use_wand_local_r P Q).

	  Lemma merge_scratch_level_done_bit_wand
	      (Post : ptr -> mpred)
	      qiv bit nodes scratch_final
	      (scratchp bit_addr bm_addr scratch_addr retp : ptr) :
	    scratch_represents_live_nodes
	      scratch_final (merge_level (Z.to_nat bit) nodes) ->
	    (Forall t : list N,
	        _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
	          qiv model.blake3_iv_words **
	        scratchp |-> ScratchR 1 t **
	        [| scratch_represents_live_nodes
	             t (merge_level (Z.to_nat bit) (nodes ++ [])) |] -*
	        Forall x : ptr,
	          bit_addr |-> anyR Tuchar 1$m **
	          bm_addr |-> anyR Tulong 1$m **
	          scratch_addr |-> anyR scratch_ref_arg_ty 1$m **
	          x |-> tptsto_fuzzyR Tulong 1$m
	                (Vn (live_nodes_bitmap_word
	                       (merge_level (Z.to_nat bit) (nodes ++ [])))) -*
	          Post x)
	    ** _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
	         qiv model.blake3_iv_words
	    ** bm_addr |-> ulongR 1$m
	         (live_nodes_bitmap_word (merge_level (Z.to_nat bit) nodes))
	    ** scratch_addr |-> refR<scratch_array_ty> 1$m scratchp
	    ** scratchp |-> ScratchR 1 scratch_final
	    ** retp |-> ulongR 1$m
	         (live_nodes_bitmap_word (merge_level (Z.to_nat bit) nodes))
	    |--
	    bit_addr |-> ucharR 1$m bit -* ▷ Post retp.
	  Proof using CU MODd Sigma.
	    intro Hscratch.
	    assert
	      (Hscratch_app :
	        scratch_represents_live_nodes
	          scratch_final (merge_level (Z.to_nat bit) (nodes ++ []))).
	    {
	      rewrite app_nil_r.
	      exact Hscratch.
	    }
	    replace
	      (live_nodes_bitmap_word (merge_level (Z.to_nat bit) nodes))
	      with
	      (live_nodes_bitmap_word (merge_level (Z.to_nat bit) (nodes ++ [])))
	      by (rewrite app_nil_r; reflexivity).
	    go.
	    rewrite <- (bi.exist_intro scratch_final).
	    rewrite (only_provable_True _ Hscratch_app) right_id.
	    go.
	  Qed.

	  Definition merge_scratch_level_done_bit_wand_F
	      Post qiv bit nodes scratch_final
	      scratchp bit_addr bm_addr scratch_addr retp Hscratch :=
	    [FWD]
	      (merge_scratch_level_done_bit_wand
	         Post qiv bit nodes scratch_final
	         scratchp bit_addr bm_addr scratch_addr retp Hscratch).

	  Definition merge_scratch_level_done_bit_wand_C
	      Post qiv bit nodes scratch_final
	      scratchp bit_addr bm_addr scratch_addr retp Hscratch :=
	    [CANCEL]
	      (merge_scratch_level_done_bit_wand
	         Post qiv bit nodes scratch_final
	         scratchp bit_addr bm_addr scratch_addr retp Hscratch).
	  #[local] Hint Resolve
	    merge_scratch_level_done_bit_wand_C : sl_opacity.

	  Lemma merge_scratch_level_done_with_frame
	      (Post : ptr -> mpred)
	      (Frame : mpred)
	      qiv bit nodes scratch_final
	      (scratchp bit_addr bm_addr scratch_addr retp : ptr) :
	    scratch_represents_live_nodes
	      scratch_final (merge_level (Z.to_nat bit) nodes) ->
	    (Forall t : list N,
	        _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
	          qiv model.blake3_iv_words **
	        scratchp |-> ScratchR 1 t **
	        [| scratch_represents_live_nodes
	             t (merge_level (Z.to_nat bit) (nodes ++ [])) |] -*
	        Forall x : ptr,
	          bit_addr |-> anyR Tuchar 1$m **
	          bm_addr |-> anyR Tulong 1$m **
	          scratch_addr |-> anyR scratch_ref_arg_ty 1$m **
	          x |-> tptsto_fuzzyR Tulong 1$m
	                (Vn (live_nodes_bitmap_word
	                       (merge_level (Z.to_nat bit) (nodes ++ [])))) -*
	          Post x)
	    ** _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
	         qiv model.blake3_iv_words
	    ** bm_addr |-> ulongR 1$m
	         (live_nodes_bitmap_word (merge_level (Z.to_nat bit) nodes))
	    ** scratch_addr |-> refR<scratch_array_ty> 1$m scratchp
	    ** scratchp |-> ScratchR 1 scratch_final
	    ** retp |-> ulongR 1$m
	         (live_nodes_bitmap_word (merge_level (Z.to_nat bit) nodes))
	    ** Frame
	    |--
	    (bit_addr |-> ucharR 1$m bit -* ▷ Post retp) ** Frame.
	  Proof using CU MODd Sigma.
	    intro Hscratch.
	    rewrite !bi.sep_assoc.
	    apply bi.sep_mono_l.
	    rewrite <- !bi.sep_assoc.
	    exact
	      (merge_scratch_level_done_bit_wand
	         Post qiv bit nodes scratch_final
	         scratchp bit_addr bm_addr scratch_addr retp Hscratch).
	  Qed.

	  Definition merge_scratch_level_done_with_frame_F
	      Post Frame qiv bit nodes scratch_final
	      scratchp bit_addr bm_addr scratch_addr retp Hscratch :=
	    [FWD]
	      (merge_scratch_level_done_with_frame
	         Post Frame qiv bit nodes scratch_final
	         scratchp bit_addr bm_addr scratch_addr retp Hscratch).

	  Lemma merge_index_arrayR_read_cell_with_wand
	      (base : ptr) (indexes : list nat) i idx :
    indexes !! i = Some idx ->
    (length indexes <= 32)%nat ->
    base |-> merge_index_arrayR indexes |--
    type_ptr Tuchar (base .[ Tuchar ! Z.of_nat i ])
    ** base .[ Tuchar ! Z.of_nat i ] |-> ucharR 1$m (Z.of_nat idx)
    ** (base .[ Tuchar ! Z.of_nat i ] |-> ucharR 1$m (Z.of_nat idx) -*
        base |-> merge_index_arrayR indexes).
  Proof using CU MODd Sigma.
    intros Hlookup Hlen.
    pose proof (lookup_lt_Some _ _ _ Hlookup) as Hlt.
    unfold merge_index_arrayR.
    destruct indexes as [| first rest].
    {
      inversion Hlookup.
    }
    simpl in Hlookup |- *.
    rewrite _at_as_Rep.
    assert
      (Hijk :
        SolveArith
          (0 <= Z.of_nat i /\
           Z.of_nat i < Z.of_nat (S (length rest)))%Z).
    {
      constructor.
      split.
      {
        lia.
      }
      {
        change (length (first :: rest)) with (S (length rest)) in Hlt.
        apply Nat2Z.inj_lt.
        exact Hlt.
      }
    }
    rewrite
      (arrayLR_extract_middle_lookup_equiv_local
         Tuchar base 0 (Z.of_nat i) (Z.of_nat (S (length rest)))
         (fun index : nat => ucharR 1$m (Z.of_nat index))
         (first :: rest) Hijk).
    assert
      (Hlookup_idx :
        forall t, (first :: rest) !! Z.of_nat i = Some t -> t = idx).
    {
      intros t Ht.
      apply lookup_nat_of_lookupZ_nat in Ht.
      congruence.
    }
    assert
      (Hlookup_idx_Z :
        forall t, (first :: rest) !! (Z.of_nat i - 0)%Z = Some t -> t = idx).
    {
      intros t Ht.
      apply Hlookup_idx.
      replace (Z.of_nat i) with (Z.of_nat i - 0)%Z by lia.
      exact Ht.
    }
    assert
      (Hlookup_Z :
        (first :: rest) !! (Z.of_nat i - 0)%Z = Some idx).
    {
      replace (Z.of_nat i - 0)%Z with (Z.of_nat i) by lia.
      apply lookupZ_nat_of_lookup_nat.
      exact Hlookup.
    }
    go.
  Qed.

  Definition merge_index_arrayR_read_cell_with_wand_F
      base indexes i idx Hlookup Hlen :=
    [FWD] (merge_index_arrayR_read_cell_with_wand
             base indexes i idx Hlookup Hlen).

  Lemma merge_plan_left_index_read_with_wand
      leftsp rightsp blocksp inputsp jobs i idx :
    map merge_job_left_index jobs !! i = Some idx ->
    (length jobs <= 32)%nat ->
    merge_plan_arraysR leftsp rightsp blocksp inputsp jobs |--
    type_ptr Tuchar (leftsp .[ Tuchar ! Z.of_nat i ])
    ** leftsp .[ Tuchar ! Z.of_nat i ] |-> ucharR 1$m (Z.of_nat idx)
    ** (leftsp .[ Tuchar ! Z.of_nat i ] |-> ucharR 1$m (Z.of_nat idx) -*
        merge_plan_arraysR leftsp rightsp blocksp inputsp jobs).
  Proof using CU MODd Sigma.
    intros Hlookup Hlen.
    assert
      (Hlen_left :
        (length (map merge_job_left_index jobs) <= 32)%nat).
    {
      rewrite length_map.
      exact Hlen.
    }
    unfold merge_plan_arraysR.
    go using
      (merge_index_arrayR_read_cell_with_wand_F
         leftsp (map merge_job_left_index jobs) i idx Hlookup Hlen_left).
  Qed.

  Definition merge_plan_left_index_read_with_wand_F
      leftsp rightsp blocksp inputsp jobs i idx Hlookup Hlen :=
    [FWD] (merge_plan_left_index_read_with_wand
             leftsp rightsp blocksp inputsp jobs i idx Hlookup Hlen).

  Lemma merge_plan_right_index_read_with_wand
      leftsp rightsp blocksp inputsp jobs i idx :
    map merge_job_right_index jobs !! i = Some idx ->
    (length jobs <= 32)%nat ->
    merge_plan_arraysR leftsp rightsp blocksp inputsp jobs |--
    type_ptr Tuchar (rightsp .[ Tuchar ! Z.of_nat i ])
    ** rightsp .[ Tuchar ! Z.of_nat i ] |-> ucharR 1$m (Z.of_nat idx)
    ** (rightsp .[ Tuchar ! Z.of_nat i ] |-> ucharR 1$m (Z.of_nat idx) -*
        merge_plan_arraysR leftsp rightsp blocksp inputsp jobs).
  Proof using CU MODd Sigma.
    intros Hlookup Hlen.
    assert
      (Hlen_right :
        (length (map merge_job_right_index jobs) <= 32)%nat).
    {
      rewrite length_map.
      exact Hlen.
    }
    unfold merge_plan_arraysR.
    go using
      (merge_index_arrayR_read_cell_with_wand_F
         rightsp (map merge_job_right_index jobs) i idx Hlookup Hlen_right).
  Qed.

  Definition merge_plan_right_index_read_with_wand_F
      leftsp rightsp blocksp inputsp jobs i idx Hlookup Hlen :=
    [FWD] (merge_plan_right_index_read_with_wand
             leftsp rightsp blocksp inputsp jobs i idx Hlookup Hlen).

  Lemma ScratchR_pack (base : ptr) q xs :
    length xs = page_pair_count ->
    base |-> arrayR bytes32_ty (exec_specs.bytes32R (cQp.mut q)) xs |--
    base |-> ScratchR q xs.
  Proof.
    intro Hlen.
    unfold ScratchR.
    go.
  Qed.

  Definition ScratchR_pack_F base q xs Hlen :=
    [FWD] (ScratchR_pack base q xs Hlen).

  Lemma bytes32_arrayR_expand_32_cells
      (base : ptr) values :
    length values = 32%nat ->
    base |-> arrayR bytes32_ty (exec_specs.bytes32R 1) values |--
    Exists v v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
       v10 v11 v12 v13 v14 v15 v16 v17
       v18 v19 v20 v21 v22 v23 v24 v25
       v26 v27 v28 v29 v30 : N,
      base .[ bytes32_ty ! 0%nat ] |-> exec_specs.bytes32R 1 v30 **
      base .[ bytes32_ty ! 1%nat ] |-> exec_specs.bytes32R 1 v29 **
      base .[ bytes32_ty ! 2%nat ] |-> exec_specs.bytes32R 1 v28 **
      base .[ bytes32_ty ! 3%nat ] |-> exec_specs.bytes32R 1 v27 **
      base .[ bytes32_ty ! 4%nat ] |-> exec_specs.bytes32R 1 v26 **
      base .[ bytes32_ty ! 5%nat ] |-> exec_specs.bytes32R 1 v25 **
      base .[ bytes32_ty ! 6%nat ] |-> exec_specs.bytes32R 1 v24 **
      base .[ bytes32_ty ! 7%nat ] |-> exec_specs.bytes32R 1 v23 **
      base .[ bytes32_ty ! 8%nat ] |-> exec_specs.bytes32R 1 v22 **
      base .[ bytes32_ty ! 9%nat ] |-> exec_specs.bytes32R 1 v21 **
      base .[ bytes32_ty ! 10%nat ] |-> exec_specs.bytes32R 1 v20 **
      base .[ bytes32_ty ! 11%nat ] |-> exec_specs.bytes32R 1 v19 **
      base .[ bytes32_ty ! 12%nat ] |-> exec_specs.bytes32R 1 v18 **
      base .[ bytes32_ty ! 13%nat ] |-> exec_specs.bytes32R 1 v17 **
      base .[ bytes32_ty ! 14%nat ] |-> exec_specs.bytes32R 1 v16 **
      base .[ bytes32_ty ! 15%nat ] |-> exec_specs.bytes32R 1 v15 **
      base .[ bytes32_ty ! 16%nat ] |-> exec_specs.bytes32R 1 v14 **
      base .[ bytes32_ty ! 17%nat ] |-> exec_specs.bytes32R 1 v13 **
      base .[ bytes32_ty ! 18%nat ] |-> exec_specs.bytes32R 1 v12 **
      base .[ bytes32_ty ! 19%nat ] |-> exec_specs.bytes32R 1 v11 **
      base .[ bytes32_ty ! 20%nat ] |-> exec_specs.bytes32R 1 v10 **
      base .[ bytes32_ty ! 21%nat ] |-> exec_specs.bytes32R 1 v9 **
      base .[ bytes32_ty ! 22%nat ] |-> exec_specs.bytes32R 1 v8 **
      base .[ bytes32_ty ! 23%nat ] |-> exec_specs.bytes32R 1 v7 **
      base .[ bytes32_ty ! 24%nat ] |-> exec_specs.bytes32R 1 v6 **
      base .[ bytes32_ty ! 25%nat ] |-> exec_specs.bytes32R 1 v5 **
      base .[ bytes32_ty ! 26%nat ] |-> exec_specs.bytes32R 1 v4 **
      base .[ bytes32_ty ! 27%nat ] |-> exec_specs.bytes32R 1 v3 **
      base .[ bytes32_ty ! 28%nat ] |-> exec_specs.bytes32R 1 v2 **
      base .[ bytes32_ty ! 29%nat ] |-> exec_specs.bytes32R 1 v1 **
      base .[ bytes32_ty ! 30%nat ] |-> exec_specs.bytes32R 1 v0 **
      base .[ bytes32_ty ! 31%nat ] |-> exec_specs.bytes32R 1 v.
  Proof.
    intro Hlen.
    destruct values as [|x0 values]; [discriminate|].
    destruct values as [|x1 values]; [discriminate|].
    destruct values as [|x2 values]; [discriminate|].
    destruct values as [|x3 values]; [discriminate|].
    destruct values as [|x4 values]; [discriminate|].
    destruct values as [|x5 values]; [discriminate|].
    destruct values as [|x6 values]; [discriminate|].
    destruct values as [|x7 values]; [discriminate|].
    destruct values as [|x8 values]; [discriminate|].
    destruct values as [|x9 values]; [discriminate|].
    destruct values as [|x10 values]; [discriminate|].
    destruct values as [|x11 values]; [discriminate|].
    destruct values as [|x12 values]; [discriminate|].
    destruct values as [|x13 values]; [discriminate|].
    destruct values as [|x14 values]; [discriminate|].
    destruct values as [|x15 values]; [discriminate|].
    destruct values as [|x16 values]; [discriminate|].
    destruct values as [|x17 values]; [discriminate|].
    destruct values as [|x18 values]; [discriminate|].
    destruct values as [|x19 values]; [discriminate|].
    destruct values as [|x20 values]; [discriminate|].
    destruct values as [|x21 values]; [discriminate|].
    destruct values as [|x22 values]; [discriminate|].
    destruct values as [|x23 values]; [discriminate|].
    destruct values as [|x24 values]; [discriminate|].
    destruct values as [|x25 values]; [discriminate|].
    destruct values as [|x26 values]; [discriminate|].
    destruct values as [|x27 values]; [discriminate|].
    destruct values as [|x28 values]; [discriminate|].
    destruct values as [|x29 values]; [discriminate|].
    destruct values as [|x30 values]; [discriminate|].
    destruct values as [|x31 values]; [discriminate|].
    destruct values as [|extra values]; [|discriminate].
    clear Hlen.
    rewrite <- (bi.exist_intro x31).
    rewrite <- (bi.exist_intro x30).
    rewrite <- (bi.exist_intro x29).
    rewrite <- (bi.exist_intro x28).
    rewrite <- (bi.exist_intro x27).
    rewrite <- (bi.exist_intro x26).
    rewrite <- (bi.exist_intro x25).
    rewrite <- (bi.exist_intro x24).
    rewrite <- (bi.exist_intro x23).
    rewrite <- (bi.exist_intro x22).
    rewrite <- (bi.exist_intro x21).
    rewrite <- (bi.exist_intro x20).
    rewrite <- (bi.exist_intro x19).
    rewrite <- (bi.exist_intro x18).
    rewrite <- (bi.exist_intro x17).
    rewrite <- (bi.exist_intro x16).
    rewrite <- (bi.exist_intro x15).
    rewrite <- (bi.exist_intro x14).
    rewrite <- (bi.exist_intro x13).
    rewrite <- (bi.exist_intro x12).
    rewrite <- (bi.exist_intro x11).
    rewrite <- (bi.exist_intro x10).
    rewrite <- (bi.exist_intro x9).
    rewrite <- (bi.exist_intro x8).
    rewrite <- (bi.exist_intro x7).
    rewrite <- (bi.exist_intro x6).
    rewrite <- (bi.exist_intro x5).
    rewrite <- (bi.exist_intro x4).
    rewrite <- (bi.exist_intro x3).
    rewrite <- (bi.exist_intro x2).
    rewrite <- (bi.exist_intro x1).
    rewrite <- (bi.exist_intro x0).
    go using _at_arrayR_cons_F, _at_arrayR_nil_F.
    normalize_ptrs.
    cbn.
    go.
  Qed.

  Definition bytes32_arrayR_expand_32_cells_F
      base values Hlen :=
    [FWD] (bytes32_arrayR_expand_32_cells base values Hlen).

  Definition merge_block_cleanup_rowR : Rep :=
    arrayLR Tuchar 0 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 64 ()).

  #[local] Hint Opaque merge_block_cleanup_rowR : sl_opacity.

  Fixpoint merge_block_cleanup_rows_from
      (base : ptr) (start count : nat) : mpred :=
    match count with
    | O => emp
    | S count' =>
        base .[ merge_block_row_ty ! Z.of_nat start ]
          |-> merge_block_cleanup_rowR
        ** merge_block_cleanup_rows_from base (S start) count'
    end.

  Lemma merge_block_cleanup_rows_expand_from
      (base : ptr) start count :
    base |-> arrayLR merge_block_row_ty
      (Z.of_nat start) (Z.of_nat (start + count))
      (fun _ : unit => merge_block_cleanup_rowR)
      (replicateN (N.of_nat count) ())
    |-- merge_block_cleanup_rows_from base start count.
  Proof using CU MODd Sigma.
    revert base start.
    induction count as [| count IH]; intros base start.
    {
      cbn [merge_block_cleanup_rows_from].
      change (replicateN (N.of_nat 0) ()) with (@nil unit).
      go.
    }
    {
      rewrite Nat2N.inj_succ.
      replace (N.succ (N.of_nat count))
        with (N.of_nat count + 1)%N by lia.
      rewrite replicateN_succ.
      replace (Z.of_nat (start + S count))
        with (Z.of_nat start + 1 + Z.of_nat count)%Z by lia.
      rewrite array_sliceR_cons.
      replace (Z.of_nat start + 1)%Z
        with (Z.of_nat (S start)) by lia.
      replace (Z.of_nat (S start) + Z.of_nat count)%Z
        with (Z.of_nat (S start + count)) by lia.
      cbn [merge_block_cleanup_rows_from].
      etrans.
      {
        apply bi.sep_mono_r.
        exact (IH base (S start)).
      }
      go using type_ptr_valid.
    }
  Qed.

  Definition merge_block_cleanup_rows_expand_from_F
      base start count :=
    [FWD] (merge_block_cleanup_rows_expand_from
             base start count).

  Definition merge_block_cleanup_rows_expanded (base : ptr) : mpred :=
    merge_block_cleanup_rows_from base 0 32.

  Lemma merge_block_cleanup_rows_expand_32_cells
      (base : ptr) :
    base |-> arrayLR merge_block_row_ty 0 32
      (fun _ : unit =>
         arrayLR Tuchar 0 64
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 64 ()))
      (replicateN 32 ())
    |-- merge_block_cleanup_rows_expanded base.
  Proof using CU MODd Sigma.
    change (replicateN 32 ()) with
      (replicateN (N.of_nat 32) ()).
    change
      (fun _ : unit =>
         arrayLR Tuchar 0 64
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 64 ()))
      with (fun _ : unit => merge_block_cleanup_rowR).
    etrans.
    {
      apply (merge_block_cleanup_rows_expand_from base 0 32).
    }
    change
      (merge_block_cleanup_rows_from base 0 32
       |-- merge_block_cleanup_rows_from base 0 32).
    reflexivity.
  Qed.

  Definition merge_block_cleanup_rows_expand_32_cells_F base :=
    [FWD] (merge_block_cleanup_rows_expand_32_cells base).

  Definition merge_plan_arrays_cleanup_splitR
      (leftsp rightsp blocksp inputsp : ptr) : mpred :=
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** leftsp |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 32 ())
    ** rightsp |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 32 ())
    ** merge_block_cleanup_rows_expanded blocksp
    ** inputsp |-> arrayLR merge_input_ptr_ty 0 32
      (fun _ : unit => anyR merge_input_ptr_ty 1$m)
      (replicateN 32 ()).

  Lemma merge_plan_arrays_cleanup_split
      leftsp rightsp blocksp inputsp jobs :
    merge_plan_arrays_cleanupR leftsp rightsp blocksp inputsp jobs
    |-- merge_plan_arrays_cleanup_splitR
          leftsp rightsp blocksp inputsp.
  Proof using CU MODd Sigma.
    unfold merge_plan_arrays_cleanupR,
      merge_plan_arrays_cleanup_splitR.
    go using (merge_block_cleanup_rows_expand_32_cells_F blocksp).
  Qed.

  Definition merge_plan_arrays_cleanup_split_F
      leftsp rightsp blocksp inputsp jobs :=
    [FWD]
      (merge_plan_arrays_cleanup_split
         leftsp rightsp blocksp inputsp jobs).

  Lemma merge_scratch_level_done_with_cleanup
      (Post : ptr -> mpred)
      qiv bit nodes scratch_final
      (scratchp bit_addr bm_addr scratch_addr retp : ptr)
      leftsp rightsp blocksp inputsp jobs :
    scratch_represents_live_nodes
      scratch_final (merge_level (Z.to_nat bit) nodes) ->
    (Forall t : list N,
        _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
          qiv model.blake3_iv_words **
        scratchp |-> ScratchR 1 t **
        [| scratch_represents_live_nodes
             t (merge_level (Z.to_nat bit) (nodes ++ [])) |] -*
        Forall x : ptr,
          bit_addr |-> anyR Tuchar 1$m **
          bm_addr |-> anyR Tulong 1$m **
          scratch_addr |-> anyR scratch_ref_arg_ty 1$m **
          x |-> tptsto_fuzzyR Tulong 1$m
                (Vn (live_nodes_bitmap_word
                       (merge_level (Z.to_nat bit) (nodes ++ [])))) -*
          Post x)
    ** _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
         qiv model.blake3_iv_words
    ** bm_addr |-> ulongR 1$m
         (live_nodes_bitmap_word (merge_level (Z.to_nat bit) nodes))
    ** scratch_addr |-> refR<scratch_array_ty> 1$m scratchp
    ** scratchp |-> ScratchR 1 scratch_final
	    ** retp |-> ulongR 1$m
	         (live_nodes_bitmap_word (merge_level (Z.to_nat bit) nodes))
	    ** merge_plan_arrays_cleanupR leftsp rightsp blocksp inputsp jobs
	    |--
	    (bit_addr |-> ucharR 1$m bit -* ▷ Post retp)
	    ** merge_plan_arrays_cleanup_splitR
	         leftsp rightsp blocksp inputsp.
  Proof using CU MODd Sigma.
    intro Hscratch.
    etrans.
    {
      do 6 apply bi.sep_mono_r.
      exact
        (merge_plan_arrays_cleanup_split
           leftsp rightsp blocksp inputsp jobs).
    }
    etrans.
    {
      exact
        (merge_scratch_level_done_with_frame
           Post
           (merge_plan_arrays_cleanup_splitR
              leftsp rightsp blocksp inputsp)
           qiv bit nodes scratch_final
           scratchp bit_addr bm_addr scratch_addr retp Hscratch).
    }
    reflexivity.
  Qed.

  Definition merge_scratch_level_done_with_cleanup_F
      Post qiv bit nodes scratch_final
      scratchp bit_addr bm_addr scratch_addr retp
      leftsp rightsp blocksp inputsp jobs Hscratch :=
    [FWD]
      (merge_scratch_level_done_with_cleanup
         Post qiv bit nodes scratch_final
         scratchp bit_addr bm_addr scratch_addr retp
         leftsp rightsp blocksp inputsp jobs Hscratch).

  Lemma ScratchR_update_cell_with_wand
      (base : ptr) xs i old new :
    xs !! i = Some old ->
    base |-> ScratchR 1 xs |--
    base .[ bytes32_ty ! Z.of_nat i ] |-> exec_specs.bytes32R 1 old
    ** (base .[ bytes32_ty ! Z.of_nat i ]
          |-> exec_specs.bytes32R 1 new -*
        base |-> ScratchR 1 (<[i := new]> xs)).
  Proof using CU MODd Sigma.
    intro Hlookup.
    unfold ScratchR.
    rewrite _at_sep _at_only_provable.
    rewrite
      (arrayR_update_cell_with_wand
         bytes32_ty (exec_specs.bytes32R 1) base xs i old new Hlookup).
    rewrite length_insert.
    go.
  Qed.

  Definition ScratchR_update_cell_with_wand_F
      base xs i old new Hlookup :=
    [FWD] (ScratchR_update_cell_with_wand
             base xs i old new Hlookup).

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

  Lemma leaf_index_prefix_forget_from (base : ptr) start indices :
    base |-> arrayLR Tuchar start
      (start + Z.of_nat (length indices))
      (fun index : nat => ucharR 1$m (Z.of_nat index)) indices |--
    base |-> arrayLR Tuchar start
      (start + Z.of_nat (length indices))
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN (N.of_nat (length indices)) ()).
  Proof using MODd.
    revert start.
    induction indices as [| index rest IH].
    {
      go.
    }
    {
      intro start.
      cbn [length replicateN].
      rewrite Nat2Z.inj_succ.
      rewrite Nat2N.inj_succ.
      replace (N.succ (N.of_nat (length rest)))
        with (N.of_nat (length rest) + 1)%N by lia.
      rewrite replicateN_succ.
      replace (start + Z.succ (Z.of_nat (length rest)))%Z
        with (start + 1 + Z.of_nat (length rest))%Z by lia.
      pose (IH_F := [FWD] (IH (start + 1)%Z)).
      rewrite !array_sliceR_cons.
      go using primR_anyR_F, IH_F.
    }
  Qed.

  Lemma leaf_index_prefix_forget (base : ptr) indices :
    base |-> arrayLR Tuchar 0 (Z.of_nat (length indices))
      (fun index : nat => ucharR 1$m (Z.of_nat index)) indices |--
    base |-> arrayLR Tuchar 0 (Z.of_nat (length indices))
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN (N.of_nat (length indices)) ()).
  Proof using MODd.
    replace (Z.of_nat (length indices))%Z
      with (0 + Z.of_nat (length indices))%Z by lia.
    apply leaf_index_prefix_forget_from.
  Qed.

  Definition leaf_index_prefix_forget_F base indices :=
    [FWD] (leaf_index_prefix_forget base indices).

  Lemma merge_index_arrayR_forget_32
      (base : ptr) indexes :
    (length indexes <= 32)%nat ->
    base |-> merge_index_arrayR indexes |--
    base |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 32 ()).
  Proof using CU MODd Sigma.
    intro Hlen.
    unfold merge_index_arrayR.
    rewrite _at_as_Rep.
    destruct indexes as [| first rest].
    {
      go.
    }
    replace (replicateN 32 ()) with
      ((replicateN (N.of_nat (length (first :: rest))) ()) ++
       (replicateZ (32 - Z.of_nat (length (first :: rest))) ()))%list.
    2: {
      unfold replicateZ, replicateN.
      rewrite <- repeat_app_local.
      f_equal.
      lia.
    }
    rewrite
      (@array_sliceR_app'
         _ _ _ _ unit Tuchar base
         0 (Z.of_nat (length (first :: rest))) 32
         (fun _ : unit => anyR Tuchar 1$m)
         (replicateN (N.of_nat (length (first :: rest))) ())
         (replicateZ
            (32 - Z.of_nat (length (first :: rest))) ()));
      try solve [rewrite lengthN_replicateN; lia | lia].
    unfold replicateZ.
    go using (leaf_index_prefix_forget_F base (first :: rest)).
  Qed.

  Definition merge_index_arrayR_forget_32_F
      base indexes Hlen :=
    [FWD] (merge_index_arrayR_forget_32 base indexes Hlen).

  Lemma merge_inputs_prefix_forget
      (base blocksp : ptr) (jobs : list merge_job) :
    base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun job_index : nat =>
         primR merge_input_ptr_ty 1$m
           (Vptr (blocksp .[ merge_block_row_ty ! Z.of_nat job_index ])))
      (seq 0 (length jobs)) |--
    base |-> arrayLR merge_input_ptr_ty
      0 (Z.of_nat (length jobs))
      (fun _ : unit => anyR merge_input_ptr_ty 1$m)
      (replicateN (N.of_nat (length jobs)) ()).
  Proof using CU MODd Sigma.
    go using primR_anyR_F.
    rewrite lengthN_replicateN.
    go.
  Qed.

  Definition merge_inputs_prefix_forget_F
      base blocksp jobs :=
    [FWD] (merge_inputs_prefix_forget base blocksp jobs).

  Lemma merge_inputs_arrayR_forget_32
      (base blocksp : ptr) jobs :
    (length jobs <= 32)%nat ->
    base |-> merge_inputs_arrayR blocksp jobs |--
    base |-> arrayLR merge_input_ptr_ty 0 32
      (fun _ : unit => anyR merge_input_ptr_ty 1$m)
      (replicateN 32 ()).
  Proof using CU MODd Sigma.
    intro Hlen.
    unfold merge_inputs_arrayR.
    rewrite _at_as_Rep.
    destruct jobs as [| first rest].
    {
      go.
    }
    replace (replicateN 32 ()) with
      ((replicateN (N.of_nat (length (first :: rest))) ()) ++
       (replicateZ (32 - Z.of_nat (length (first :: rest))) ()))%list.
    2: {
      unfold replicateZ, replicateN.
      rewrite <- repeat_app_local.
      f_equal.
      lia.
    }
    rewrite
      (@array_sliceR_app'
         _ _ _ _ unit merge_input_ptr_ty base
         0 (Z.of_nat (length (first :: rest))) 32
         (fun _ : unit => anyR merge_input_ptr_ty 1$m)
         (replicateN (N.of_nat (length (first :: rest))) ())
         (replicateZ
            (32 - Z.of_nat (length (first :: rest))) ()));
      try solve [rewrite lengthN_replicateN; lia | lia].
    unfold replicateZ.
    go using
      (merge_inputs_prefix_forget_F base blocksp (first :: rest)).
  Qed.

  Definition merge_inputs_arrayR_forget_32_F
      base blocksp jobs Hlen :=
    [FWD] (merge_inputs_arrayR_forget_32 base blocksp jobs Hlen).

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
      rewrite (offset_ptr_sub_0 base Tuchar).
      2: {
        vm_compute.
        eauto.
      }
      go using primR_anyR_F.
    }
  Qed.

  Definition uchar_arrayR_values_forget_F base values :=
    [FWD] (uchar_arrayR_values_forget base values).

  Lemma merge_block_rowR_forget (p : ptr) row :
    p |-> merge_block_rowR row |--
    p |-> arrayLR Tuchar 0 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 64 ()).
  Proof using CU MODd Sigma.
    destruct row as [| lhs | block].
    {
      go.
    }
    {
      simpl.
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
           _ _ _ _ unit Tuchar p
           0 32 64
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 32 ())
           (replicateN 32 ()));
        try solve [rewrite lengthN_replicateN; lia | lia].
      go using primR_anyR_F, uninitR_anyR_F.
    }
    {
      unfold merge_block_rowR, blake3specs.Blake3BlockR,
        blake3_impl_h_specs.Blake3BlockR,
        blake3specs.BlockR,
        blake3_impl_h_specs.BlockR.
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
      go using
        (uchar_arrayR_values_forget_F p
           (blake3specs.bytes64_byte_values block)).
    }
  Qed.

  Definition merge_block_rowR_forget_F p row :=
    [FWD] (merge_block_rowR_forget p row).

  Lemma replicateN_length_unit_map {A : Type} (xs : list A) :
    replicateN (N.of_nat (length xs)) () =
    map (fun _ : A => ()) xs.
  Proof.
    induction xs as [| x rest IH].
    {
      reflexivity.
    }
    {
      cbn [length].
      rewrite Nat2N.inj_succ.
      replace (N.succ (N.of_nat (length rest)))
        with (N.of_nat (length rest) + 1)%N by lia.
      rewrite replicateN_succ.
      simpl.
      rewrite IH.
      reflexivity.
    }
  Qed.

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

  Lemma merge_block_rows_prefix_forget
      (base : ptr) rows :
    base |-> arrayLR merge_block_row_ty 0 (Z.of_nat (length rows))
      merge_block_rowR rows |--
    base |-> arrayLR merge_block_row_ty 0 (Z.of_nat (length rows))
        (fun _ : unit =>
           arrayLR Tuchar 0 64
             (fun _ : unit => anyR Tuchar 1$m)
             (replicateN 64 ()))
      (replicate (length rows) ()).
  Proof using CU MODd Sigma.
    rewrite replicate_length_unit_map.
    rewrite
      (array_sliceR_fmap
         (ty := merge_block_row_ty)
         0 (Z.of_nat (length rows)) rows
           (fun _ : unit =>
              arrayLR Tuchar 0 64
                (fun _ : unit => anyR Tuchar 1$m)
                (replicateN 64 ()))
           (fun _ : merge_block_row => ()))
        /=.
    apply _at_mono.
    f_equiv.
    intro row.
    apply Rep_entails_at => p.
    apply merge_block_rowR_forget.
  Qed.

  Definition merge_block_rows_prefix_forget_F base rows :=
    [FWD] (merge_block_rows_prefix_forget base rows).

  Definition merge_block_rows_prefix_forget_C base rows :=
    [CANCEL] (merge_block_rows_prefix_forget base rows).

  Lemma merge_block_rows_forget_32
      (base : ptr) jobs :
    (length jobs <= 32)%nat ->
    base |-> arrayLR merge_block_row_ty 0 32
      merge_block_rowR (merge_block_rows jobs) |--
    base |-> arrayLR merge_block_row_ty 0 32
      (fun _ : unit =>
         arrayLR Tuchar 0 64
           (fun _ : unit => anyR Tuchar 1$m)
           (replicateN 64 ()))
      (replicateN 32 ()).
  Proof using CU MODd Sigma.
    intro Hlen.
    unfold merge_block_rows.
    replace (replicateN 32 ()) with
      ((replicateN (N.of_nat (length jobs)) ()) ++
       (replicateZ (32 - Z.of_nat (length jobs)) ()))%list.
    2: {
      unfold replicateZ, replicateN.
      rewrite <- repeat_app_local.
      f_equal.
      lia.
    }
    rewrite
      (@array_sliceR_app'
         _ _ _ _ unit merge_block_row_ty base
         0 (Z.of_nat (length jobs)) 32
         (fun _ : unit =>
            arrayLR Tuchar 0 64
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 64 ()))
         (replicateN (N.of_nat (length jobs)) ())
         (replicateZ (32 - Z.of_nat (length jobs)) ()));
      try solve [rewrite lengthN_replicateN; lia | lia].
    rewrite
      (@array_sliceR_app'
         _ _ _ _ merge_block_row merge_block_row_ty base
         0 (Z.of_nat (length jobs)) 32
         merge_block_rowR
         (map (fun job => MergeBlockFull (merge_job_input job)) jobs)
         (replicateZ
            (32 - Z.of_nat (length jobs)) MergeBlockUninit));
      try solve [rewrite lengthN_map; rewrite lengthN_length; lia | lia].
    unfold replicateZ.
    replace
      (replicateN (Z.to_N (32 - Z.of_nat (length jobs)))
         MergeBlockUninit)
      with
      (map (fun _ : unit => MergeBlockUninit)
         (replicateN (Z.to_N (32 - Z.of_nat (length jobs))) ())).
    2: {
      unfold replicateN.
      induction (N.to_nat (Z.to_N (32 - Z.of_nat (length jobs)))).
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
         (ty := merge_block_row_ty)
         (Z.of_nat (length jobs)) 32
         (replicateN (Z.to_N (32 - Z.of_nat (length jobs))) ())
         merge_block_rowR
         (fun _ : unit => MergeBlockUninit)).
    cbn [merge_block_rowR].
    replace (replicateN (N.of_nat (length jobs)) ()) with
      (replicate (length jobs) ()).
    2: {
      unfold replicateN.
      rewrite Nat2N.id.
      reflexivity.
    }
    replace (Z.of_nat (length jobs)) with
      (Z.of_nat
         (length
            (map
               (fun job : merge_job =>
                  MergeBlockFull (merge_job_input job)) jobs))).
    2: {
      rewrite length_map.
      reflexivity.
    }
    replace (replicate (length jobs) ()) with
      (replicate
         (length
            (map
               (fun job : merge_job =>
                  MergeBlockFull (merge_job_input job)) jobs)) ()).
    2: {
      rewrite length_map.
      reflexivity.
    }
    go using
      (merge_block_rows_prefix_forget_C base
         (map
            (fun job : merge_job =>
               MergeBlockFull (merge_job_input job)) jobs)).
  Qed.

  Definition merge_block_rows_forget_32_F
      base jobs Hlen :=
    [FWD] (merge_block_rows_forget_32 base jobs Hlen).

  Lemma merge_plan_arraysR_cleanup
      leftsp rightsp blocksp inputsp jobs :
    (length jobs <= 32)%nat ->
    merge_plan_arraysR leftsp rightsp blocksp inputsp jobs |--
    merge_plan_arrays_cleanupR leftsp rightsp blocksp inputsp jobs.
  Proof using CU MODd Sigma.
    intro Hlen.
    unfold merge_plan_arraysR, merge_plan_arrays_cleanupR.
    go using
      (merge_index_arrayR_forget_32_F
         leftsp (map merge_job_left_index jobs) ltac:(rewrite length_map; exact Hlen)),
      (merge_index_arrayR_forget_32_F
         rightsp (map merge_job_right_index jobs) ltac:(rewrite length_map; exact Hlen)),
      (merge_block_rows_forget_32_F blocksp jobs Hlen),
      (merge_inputs_arrayR_forget_32_F inputsp blocksp jobs Hlen).
  Qed.

  Definition merge_plan_arraysR_cleanup_F
      leftsp rightsp blocksp inputsp jobs Hlen :=
    [FWD] (merge_plan_arraysR_cleanup
             leftsp rightsp blocksp inputsp jobs Hlen).

  Lemma merge_plan_arraysR_cleanup_split_direct
      leftsp rightsp blocksp inputsp jobs :
    (length jobs <= 32)%nat ->
    merge_plan_arraysR leftsp rightsp blocksp inputsp jobs
    |-- merge_plan_arrays_cleanup_splitR
          leftsp rightsp blocksp inputsp.
  Proof using CU MODd Sigma.
    intro Hlen.
    etrans.
    {
      exact
        (merge_plan_arraysR_cleanup
           leftsp rightsp blocksp inputsp jobs Hlen).
    }
    exact
      (merge_plan_arrays_cleanup_split
         leftsp rightsp blocksp inputsp jobs).
  Qed.

  Definition merge_plan_arraysR_cleanup_split_direct_F
      leftsp rightsp blocksp inputsp jobs Hlen :=
    [FWD]
      (merge_plan_arraysR_cleanup_split_direct
         leftsp rightsp blocksp inputsp jobs Hlen).


  #[local] Hint Resolve
    wp_init_implicit_B_local
    wp.wp_init_initlist_struct_B
    wp_operand_initlist_default_B
    wp_init_default_array_B
    wp_init_initlist_prim_array_implicit_erased_B
    wp_init_bytes32_array_zero_local_B
    default_initialize_array_of_arrays_uninit_local_B
    uninitR_anyR_F
    type_ptr_reference_to_B_local
    type_ptr_elim_type_ptr_C
    typed_sliceR_elim_type_ptr_C
    UNSAFE_read_prim_cancel : sl_opacity.
  #[local] Hint Opaque
    ScratchR merge_jobs merge_level live_nodes_bitmap_word
    merge_plan_arraysR merge_plan_arrays_cleanupR
    merge_index_arrayR merge_inputs_arrayR
    merge_block_rows merge_hash_outputs : sl_opacity.
  #[local] Hint Resolve
    merge_jobs_length_le_32
    merge_hash_outputs_replicate32_length : pure.

  Lemma prf_merge_at_level :
    verify[source] storage_merge_at_level_spec.
  Proof using MODd.
    verify_spec.
    name_locals.
    go.
    (* Inline proof of collect_merge_scratch_level_jobs at the old call site. *)
    go.
    wp_while (fun _ =>
      Exists done todo state bits merge_count prev,
        [| nodes = done ++ todo |]
        ** [| live_nodes_well_formed todo |]
        ** [| state =
              scan_nodes_from (Z.to_nat bit)
                initial_merge_scan_state done |]
        ** [| bits = live_nodes_bitmap_word todo |]
        ** [| merge_count =
              N.of_nat (length state.(scan_jobs)) |]
        ** [| prev = merge_scan_prev_value state |]
        ** [| (length state.(scan_jobs) <= 32)%nat |]
        ** merge_plan_arraysR lefts_addr rights_addr blocks_addr inputs_addr
             state.(scan_jobs)
        ** bits_addr |-> ulongR 1$m bits
        ** merge_count_addr |-> ulongR 1$m merge_count
        ** prev_addr |-> ucharR 1$m prev).
    rewrite <- (bi.exist_intro ([] : list live_node)).
    rewrite <- (bi.exist_intro nodes).
    rewrite <- (bi.exist_intro initial_merge_scan_state).
    rewrite <- (bi.exist_intro (live_nodes_bitmap_word nodes)).
    rewrite <- (bi.exist_intro 0%N).
    rewrite <- (bi.exist_intro 255%Z).
    go1 using
      (arrayLR_uninit_anyR_F
         Tuchar lefts_addr 0 32 1$m (replicateN 32 ())).
    go1 using
      (arrayLR_uninit_anyR_F
         Tuchar rights_addr 0 32 1$m (replicateN 32 ())).
    go1 using
      (arrayLR_uninit_anyR_F
         merge_input_ptr_ty inputs_addr 0 32 1$m (replicateN 32 ())).
    go1 using (merge_block_any_rows_init_F blocks_addr).
    go1 using (merge_index_arrayR_pack_F lefts_addr []).
    go1 using (merge_index_arrayR_pack_F rights_addr []).
    go1 using (merge_inputs_arrayR_null_pack_F inputs_addr blocks_addr).
    go1 using (merge_plan_arraysR_pack_B lefts_addr rights_addr blocks_addr inputs_addr []).
    go.
    wp_if.
    {
      intro Hbits_nonzero.
      match goal with
      | Hnz : live_nodes_bitmap_word ?todo <> 0%N |- _ =>
          destruct todo as [| current rest];
          [simpl in Hnz; contradiction |]
      end.
      assert
        (Hwf_todo : live_nodes_well_formed (current :: rest))
        by assumption.
      pose proof
        (live_nodes_bitmap_word_cons_countr_zero
           current rest Hwf_todo) as Hctz.
      assert
        (Hcurrent_index_lt256 :
          (current.(live_index) < 256)%nat)
        by
          (simpl in Hwf_todo;
           destruct Hwf_todo as [[_ Hcurrent_upper] _];
           unfold page_pair_count in Hcurrent_upper;
           lia).
      pose proof
        (trim8_nat_small
           current.(live_index) Hcurrent_index_lt256) as Htrim_pos.
      go.
      match goal with
      | H : scratch_represents_live_nodes
              scratch (?prefix ++ current :: rest) |- _ =>
          set (done_prefix := prefix) in *;
          clearbody done_prefix
      end.
      assert
        (Hwf_all :
          live_nodes_well_formed (done_prefix ++ current :: rest))
        by assumption.
      change
        (fold_left
           (fun bm node =>
              (bm `lor` 2 ^ N.of_nat node.(live_index))%N)
           rest
           (0 `lor` 2 ^ N.of_nat current.(live_index))%N)
        with (live_nodes_bitmap_word (current :: rest)).
      rewrite Hctz.
      destruct
        (scan_nodes_from (Z.to_nat bit)
           initial_merge_scan_state done_prefix)
        as [[previous |] jobs] eqn:Hscan_done;
        simpl in *.
      {
        assert (Hprevious_in_done : In previous done_prefix).
        {
          apply scan_nodes_pending_in
            with (bit := Z.to_nat bit).
          rewrite Hscan_done.
          reflexivity.
        }
        assert
          (Hprevious_index_lt :
            (previous.(live_index) < page_pair_count)%nat).
        {
          eapply live_nodes_well_formed_in_index.
          { exact Hwf_all. }
          apply in_or_app.
          left.
          exact Hprevious_in_done.
        }
        assert
          (Hprevious_index_not_255 :
            previous.(live_index) <> 255%nat).
        {
          unfold page_pair_count in Hprevious_index_lt.
          lia.
        }
        assert (Hjobs_lt32 : (length jobs < 32)%nat).
        {
          pose proof
            (scan_nodes_from_jobs_bound
               (Z.to_nat bit) done_prefix
               initial_merge_scan_state) as Hbound.
          rewrite Hscan_done in Hbound.
          simpl in Hbound.
          pose proof (live_nodes_well_formed_length
                        (done_prefix ++ current :: rest) Hwf_all)
            as Hall_len.
          rewrite app_length in Hall_len.
          unfold page_pair_count in Hall_len.
          lia.
        }
        replace
          (asbool (Z.of_nat previous.(live_index) <> 255))
          with true.
        2: {
          symmetry.
          apply bool_decide_eq_true_2.
          lia.
        }
        go.
        rewrite
          (same_parent_at_level_cpp_asbool_mixed
             bit previous.(live_index) current.(live_index) a).
        destruct
          (same_parent_at_level
             (Z.to_nat bit) previous.(live_index)
             current.(live_index)) eqn:Hsame_parent.
        {
          go.
          rewrite
            (index_bit_is_zero_cpp_asbool
               bit previous.(live_index) a).
          destruct
            (index_bit_is_zero
               (Z.to_nat bit) previous.(live_index))
            eqn:Hindex_zero.
          {
            destruct jobs as [| first_job later_jobs].
            {
              assert
                (Hprev_scratch_lookup :
                  nth_error scratch previous.(live_index) =
                  Some
                    (blake3model.bytes32_to_N (eval_tree previous.(live_tree)))).
              {
                pose proof _H_0 as Hscratch_rep.
                destruct Hscratch_rep as
                  [Hscratch_len Hscratch_nodes].
                erewrite <- Hscratch_nodes.
                2: {
                  apply in_or_app.
                  left.
                  exact Hprevious_in_done.
                }
                apply nth_error_nth'.
                rewrite Hscratch_len.
                exact Hprevious_index_lt.
              }
              assert
                (Hprev_scratch_lookup_N :
                  nth_error scratch
                    (N.to_nat (N.of_nat previous.(live_index))) =
                  Some
                    (blake3model.bytes32_to_N (eval_tree previous.(live_tree)))).
              {
                rewrite Nat2N.id.
                exact Hprev_scratch_lookup.
              }
              setoid_rewrite
                (scratchR_unfold_local scratchp 1 scratch) at 1.
              rewrite
                (_at_arrayR_cellN
                   (N.of_nat previous.(live_index)) scratch bytes32_ty
                   (exec_specs.bytes32R 1) scratchp
                   (blake3model.bytes32_to_N (eval_tree previous.(live_tree)))
                   Hprev_scratch_lookup_N).
              rewrite nat_N_Z.
              Transparent exec_specs.evmc_bytes32_bytesR.
              rewrite /exec_specs.bytes32R /exec_specs.evmc_bytes32_wordR
                /exec_specs.evmc_bytes32_bytesR.
              Opaque exec_specs.evmc_bytes32_bytesR.
              go1 using
                (merge_plan_arraysR_expanded_unpack_F
                   lefts_addr rights_addr blocks_addr inputs_addr []).
              rewrite
                (byte_arrayR_to_arrayLR_local
                   (scratchp .[ bytes32_ty !
                                previous.(live_index) ] ,,
                    o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
                    o_field CU "evmc_bytes32::bytes")
                   1
                   (exec_specs.bytes32_be_values
                      (blake3model.bytes32_to_N
                         (eval_tree previous.(live_tree))))
                   (bytes32_be_values_length_local
                      (blake3model.bytes32_to_N
                         (eval_tree previous.(live_tree))))).
              assert
                (Hblock_slot :
                  SolveArith (0 <= 0 /\ 0 < 32)%Z)
                by (constructor; lia).
              go1 using
                (arrayLR_extract_middle_lookup_local_F
                   merge_block_row_ty blocks_addr 0 0 32
                   merge_block_rowR
                   (replicateZ (32 - 0%nat) MergeBlockUninit)
                   Hblock_slot).
              cbn [merge_block_rowR].
              go1 using
                (merge_block_uninit_row_split_first_local_F
                   (blocks_addr .[ merge_block_row_ty ! 0 ])).
              go1 using
                (any_unit_arrayLR32_to_val_arrayLR32_local_F
                   (blocks_addr .[ merge_block_row_ty ! 0 ])).
              assert
                (Hprevious_before_current :
                  (previous.(live_index) < current.(live_index))%nat).
              {
                eapply live_nodes_well_formed_app_prefix_before_head.
                { exact Hwf_all. }
                exact Hprevious_in_done.
              }
              assert
                (Hcurrent_index_lt :
                  (current.(live_index) < page_pair_count)%nat).
              {
                simpl in Hwf_todo.
                destruct Hwf_todo as [[_ Hcurrent_upper] _].
                exact Hcurrent_upper.
              }
              assert
                (Hcurrent_scratch_lookup :
                  nth_error scratch current.(live_index) =
                  Some
                    (blake3model.bytes32_to_N
                       (eval_tree current.(live_tree)))).
              {
                pose proof _H_0 as Hscratch_rep.
                destruct Hscratch_rep as
                  [Hscratch_len Hscratch_nodes].
                erewrite <- Hscratch_nodes.
                2: {
                  apply in_or_app.
                  right.
                  left.
                  reflexivity.
                }
                apply nth_error_nth'.
                rewrite Hscratch_len.
                exact Hcurrent_index_lt.
              }
              assert
                (Hcurrent_suffix_lookup :
                  nth_error
                    (drop
                       (N.to_nat
                          (N.of_nat previous.(live_index) + 1))
                       scratch)
                    (N.to_nat
                       (N.of_nat
                          (current.(live_index) -
                           S previous.(live_index)))) =
                  Some
                    (blake3model.bytes32_to_N
                       (eval_tree current.(live_tree)))).
              {
                rewrite nth_error_skipn.
                rewrite N2Nat.inj_add.
                rewrite Nat2N.id.
                change (N.to_nat 1) with 1%nat.
                rewrite Nat.add_1_r.
                rewrite Nat2N.id.
                replace
                  (S previous.(live_index) +
                   (current.(live_index) -
                    S previous.(live_index)))%nat
                  with current.(live_index) by lia.
                exact Hcurrent_scratch_lookup.
              }
              rewrite
                (_at_arrayR_cellN
                   (N.of_nat
                      (current.(live_index) -
                       S previous.(live_index)))
                   (drop
                      (N.to_nat
                         (N.of_nat previous.(live_index) + 1))
                      scratch)
                   bytes32_ty
                   (exec_specs.bytes32R 1)
                   (scratchp .[ bytes32_ty !
                                previous.(live_index) + 1 ])
                   (blake3model.bytes32_to_N
                   (eval_tree current.(live_tree)))
                   Hcurrent_suffix_lookup).
              repeat rewrite o_sub_sub.
              repeat rewrite N2Z.inj_add.
              change (Z.of_N 1) with 1%Z.
              rewrite nat_N_Z.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%Z
                with (Z.of_nat current.(live_index)) by lia.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   ((current.(live_index) -
                     S previous.(live_index)) + 1))%Z
                with (Z.of_nat current.(live_index) + 1)%Z by lia.
              go1 using
                (unpacked_bytes32R_to_byte_arrayLR_local_F
                   (scratchp .[ bytes32_ty !
                                current.(live_index) ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))).
              go1 using
                (any_unit_arrayLR32_64_to_val_arrayLR0_32_local_F
                   (blocks_addr .[ merge_block_row_ty ! 0 ])).
              assert
                (Hsibling_candidate :
                  sibling_candidate (Z.to_nat bit)
                    previous.(live_index) current.(live_index) = true).
              {
                unfold sibling_candidate.
                rewrite Hsame_parent Hindex_zero.
                reflexivity.
              }
              assert
                (Hscan_after :
                  scan_nodes_from (Z.to_nat bit)
                    initial_merge_scan_state
                    (done_prefix ++ [current]) =
                  {|
                    scan_pending := None;
                    scan_jobs :=
                      [{|
                         merge_left := previous;
                         merge_right := current;
                       |}];
                  |}).
              {
                rewrite scan_nodes_from_app.
                rewrite Hscan_done.
                simpl.
                rewrite Hsibling_candidate.
                reflexivity.
              }
              assert
                (Hwf_rest : live_nodes_well_formed rest).
              {
                simpl in Hwf_todo.
                destruct Hwf_todo as [_ Hrest].
                eapply live_nodes_well_formed_from_weaken.
                { lia. }
                exact Hrest.
	              }
	              go.
              rewrite <- (bi.exist_intro (cQp.mut 1)).
              rewrite <- (bi.exist_intro (Z.of_N <$>
                z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
                  (Z.of_N (blake3model.bytes32_to_N
                    (eval_tree previous.(live_tree)))))).
              rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
              rewrite (eq_trans
                (eq_sym (list_fmap_compose Z.of_N Vint
                  (z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
                    (Z.of_N (blake3model.bytes32_to_N
                      (eval_tree previous.(live_tree)))))))
                (eq_sym (bytes32_be_values_to_Z_to_bytes
                  (blake3model.bytes32_to_N
                    (eval_tree previous.(live_tree)))))).
              go using (typed_slice_nonempty_nonnull_B
                (scratchp .[ bytes32_ty ! previous.(live_index) ] ,,
                  o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
                  o_field CU "evmc_bytes32::bytes") Tuchar 32 ltac:(lia)).
	              go1 using
	                (byte_arrayR_to_arrayLR_local_F
	                   (scratchp .[ bytes32_ty !
                                previous.(live_index) ] ,,
                    o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
                    o_field CU "evmc_bytes32::bytes")
                   1
                   (exec_specs.bytes32_be_values
                      (blake3model.bytes32_to_N
                         (eval_tree previous.(live_tree))))
                   (bytes32_be_values_length_local
                      (blake3model.bytes32_to_N
                         (eval_tree previous.(live_tree))))).
              go1 using
                (bytes32R_to_byte_arrayLR_local_F
                   (scratchp .[ bytes32_ty !
                                previous.(live_index) + 1 +
                                N.of_nat
                                  (current.(live_index) -
                                   S previous.(live_index)) ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))).
	              go using primR_split_C.
	              go.
              unhideAllFromWork.
              go1 using
                (bytes32R_from_two_half_byte_arrays_local_F
                   (scratchp .[ bytes32_ty !
                                previous.(live_index) ])
                   (blake3model.bytes32_to_N
                      (eval_tree previous.(live_tree)))
                   (blake3model.bytes32_to_N_range
                      (eval_tree previous.(live_tree)))).
              go1 using
                (bytes32R_from_two_half_byte_arrays_local_F
                   (scratchp .[ bytes32_ty !
                                current.(live_index) ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))
                   (blake3model.bytes32_to_N_range
                      (eval_tree current.(live_tree)))).
              go1 using
                (merge_block_full_from_halves_local_F
                   (blocks_addr .[ merge_block_row_ty ! 0 ])
                   (eval_tree previous.(live_tree))
                   (eval_tree current.(live_tree))).
              simpl.
              change
                (blake3specs.Blake3BlockR 1
                   (eval_tree previous.(live_tree),
                    eval_tree current.(live_tree)))
                with
                (merge_block_rowR
                   (MergeBlockFull
                      (eval_tree previous.(live_tree),
                       eval_tree current.(live_tree)))).
              go1 using
                (merge_index_arrayR_one_from_cell_tail_local_F
                   lefts_addr previous.(live_index)).
              go1 using
                (merge_index_arrayR_one_from_cell_tail_Z_local_F
                   rights_addr current.(live_index)).
              change
                (sliceZ 0 1 32
                   (replicateN 32 MergeBlockUninit))
                with (replicateN 31 MergeBlockUninit).
              go1 using
                (merge_block_rows_one_from_blake3_tail_model_local_F
                   blocks_addr
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}).
              go1 using
                (merge_inputs_arrayR_one_from_cell_tail_Z_local_F
                   inputs_addr blocks_addr
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}).
              go1 using
                (merge_plan_arraysR_pack_B
                   lefts_addr rights_addr blocks_addr inputs_addr
                   [{|
                      merge_left := previous;
                      merge_right := current;
                    |}]).
              go.
		              go using
		                (merge_block_uninit_row_split_first_local_F
		                   (blocks_addr .[ merge_block_row_ty ! 0 ])),
		                (any_unit_arrayLR32_to_val_arrayLR32_local_F
		                   (blocks_addr .[ merge_block_row_ty ! 0 ])),
		                (memcpy_dst_any_val32_witness_local_F
		                   (blocks_addr .[ merge_block_row_ty ! 0 ]) _).
              repeat rewrite o_sub_sub.
              repeat rewrite N2Z.inj_add.
              change (Z.of_N 1) with 1%Z.
              rewrite nat_N_Z.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%Z
                with (Z.of_nat current.(live_index)) by lia.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   ((current.(live_index) -
                     S previous.(live_index)) + 1))%Z
                with (Z.of_nat current.(live_index) + 1)%Z by lia.
	              go using primR_split_C.
              rewrite <- (bi.exist_intro (cQp.mut 1)).
              rewrite <- (bi.exist_intro (Z.of_N <$>
                z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
                  (Z.of_N (blake3model.bytes32_to_N
                    (eval_tree current.(live_tree)))))).
              rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
              rewrite (eq_trans
                (eq_sym (list_fmap_compose Z.of_N Vint
                  (z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
                    (Z.of_N (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))))))
                (eq_sym (bytes32_be_values_to_Z_to_bytes
                  (blake3model.bytes32_to_N
                    (eval_tree current.(live_tree)))))).
              go using (typed_slice_nonempty_nonnull_B
                (scratchp .[ bytes32_ty ! current.(live_index) ] ,,
                  o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
                  o_field CU "evmc_bytes32::bytes") Tuchar 32 ltac:(lia)).
		              rewrite <- (bi.exist_intro
		                             (A := list live_node)
		                             (done_prefix ++ [current])).
              rewrite <- (bi.exist_intro
                             (A := list live_node) rest).
              change
                (fold_left
                   (fun bm node =>
                      (bm `lor` 2 ^ N.of_nat node.(live_index))%N)
                   rest
                   (0 `lor` 2 ^ N.of_nat current.(live_index))%N)
                with (live_nodes_bitmap_word (current :: rest)).
              rewrite
                (live_nodes_bitmap_word_cons_clear_lowest_Z
                   current rest Hwf_todo).
              rewrite Hscan_after.
              simpl.
              rewrite scratchR_unfold_local.
              rewrite
                (_at_arrayR_cellN
                   (N.of_nat previous.(live_index)) scratch bytes32_ty
                   (exec_specs.bytes32R 1) scratchp
                   (blake3model.bytes32_to_N
                      (eval_tree previous.(live_tree)))
                   Hprev_scratch_lookup_N).
              rewrite
                (_at_arrayR_cellN
                   (N.of_nat
                      (current.(live_index) -
                       S previous.(live_index)))
                   (drop
                      (N.to_nat
                         (N.of_nat previous.(live_index) + 1))
                      scratch)
                   bytes32_ty
                   (exec_specs.bytes32R 1)
                   (scratchp .[ bytes32_ty !
                                N.of_nat previous.(live_index) + 1 ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))
                   Hcurrent_suffix_lookup).
              repeat rewrite o_sub_sub.
              repeat rewrite N2Z.inj_add.
              change (Z.of_N 1) with 1%Z.
              rewrite nat_N_Z.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%Z
                with (Z.of_nat current.(live_index)) by lia.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   ((current.(live_index) -
                     S previous.(live_index)) + 1))%Z
                with (Z.of_nat current.(live_index) + 1)%Z by lia.
              replace
                (N.of_nat previous.(live_index) + 1 +
                 N.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%N
                with (N.of_nat current.(live_index)) by lia.
              replace
                (N.of_nat previous.(live_index) + 1 +
                 (N.of_nat
                    (current.(live_index) -
                     S previous.(live_index)) + 1))%N
                with (N.of_nat current.(live_index) + 1)%N by lia.
              unhideAllFromWork.
              go1 using
                (bytes32R_from_two_half_byte_arrays_local_F
                   (scratchp .[ bytes32_ty !
                                previous.(live_index) ])
                   (blake3model.bytes32_to_N
                      (eval_tree previous.(live_tree)))
                   (blake3model.bytes32_to_N_range
                      (eval_tree previous.(live_tree)))).
              go1 using
                (bytes32R_from_two_half_byte_arrays_local_F
                   (scratchp .[ bytes32_ty !
                                current.(live_index) ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))
                   (blake3model.bytes32_to_N_range
                      (eval_tree current.(live_tree)))).
              go1 using
                (merge_block_full_from_halves_local_F
                   (blocks_addr .[ merge_block_row_ty ! 0 ])
                   (eval_tree previous.(live_tree))
                   (eval_tree current.(live_tree))).
              go1 using
                (merge_block_rows_one_from_blake3_tail_model_local_F
                   blocks_addr
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}).
              go1 using
                (merge_inputs_arrayR_one_from_cell_tail_Z_local_F
                   inputs_addr blocks_addr
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}).
              set (leftsp := lefts_addr).
              set (rightsp := rights_addr).
              set (blocksp := blocks_addr).
              go1 using
                (merge_plan_arraysR_pack_B
                   leftsp rightsp blocksp inputs_addr
                   [{|
                      merge_left := previous;
                      merge_right := current;
                    |}]).
              try subst blocksp.
              try subst rightsp.
              try subst leftsp.
              go.
              go using
                (merge_block_uninit_row_split_first_local_F
                   (blocks_addr .[ merge_block_row_ty ! 0 ])),
                (any_unit_arrayLR32_to_val_arrayLR32_local_F
                   (blocks_addr .[ merge_block_row_ty ! 0 ])),
                (memcpy_dst_any_val32_witness_local_F
                   (blocks_addr .[ merge_block_row_ty ! 0 ]) _).
              go1 using
                (merge_block_full_from_offset_halves_local_F
                   blocks_addr
                   (eval_tree previous.(live_tree))
                   (eval_tree current.(live_tree))).
              go1 using
                (merge_index_arrayR_one_from_cell_tail_local_F
                   lefts_addr previous.(live_index)).
              go1 using
                (merge_index_arrayR_one_from_cell_tail_local_F
                   rights_addr current.(live_index)).
              go1 using
                (merge_inputs_arrayR_one_from_base_cell_tail_local_F
                   inputs_addr blocks_addr
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}).
              normalize_ptrs.
              repeat rewrite o_sub_sub.
              replace
                (N.of_nat previous.(live_index) + 1 +
                 N.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%N
                with (N.of_nat current.(live_index)) by lia.
              replace
                (N.of_nat previous.(live_index) + 1 +
                 (N.of_nat
                    (current.(live_index) -
                     S previous.(live_index)) + 1))%N
                with (N.of_nat current.(live_index) + 1)%N by lia.
              go1 using
                (merge_block_full_from_offset_halves_local_F
                   blocks_addr
                   (eval_tree previous.(live_tree))
                   (eval_tree current.(live_tree))).
              go1 using
                (merge_inputs_arrayR_one_from_base_cell_tail_local_F
                   inputs_addr blocks_addr
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}).
              go1 using
                (bytes32_current_suffix_as_offset_local_F
                   scratchp previous.(live_index)
                   current.(live_index) scratch
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))
                   Hprevious_before_current).
              normalize_ptrs.
              repeat rewrite N2Z.inj_add.
              rewrite nat_N_Z.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat (current.(live_index) - S previous.(live_index)))%Z
                with (Z.of_nat current.(live_index)) by lia.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 (Z.of_nat (current.(live_index) - S previous.(live_index)) + 1))%Z
                with (Z.of_nat current.(live_index) + 1)%Z by lia.
              go using bytes_field_to_bytes32R_B.
		            }
	            {
              go1 using
                (merge_plan_arraysR_expanded_unpack_F
                   lefts_addr rights_addr blocks_addr inputs_addr
                   (first_job :: later_jobs)).
              rewrite !length_map.
              assert
                (Hleft_slot :
                  SolveArith
                    (Z.of_nat (length (first_job :: later_jobs)) <=
                     Z.of_nat (length (first_job :: later_jobs)) /\
                     Z.of_nat (length (first_job :: later_jobs)) < 32)%Z)
                by (constructor; lia).
              assert
                (Hleft_tail_slot :
                  SolveArith
                    (Z.pos
                       (PosDef.Pos.of_succ_nat
                          (length later_jobs)) <=
                     Z.pos
                       (PosDef.Pos.of_succ_nat
                          (length later_jobs)) < 32)%Z).
              {
                destruct Hleft_slot as [Hleft_slot_ok].
                constructor.
                change
                  (Z.pos
                     (PosDef.Pos.of_succ_nat
                        (length later_jobs)))
                  with
                  (Z.of_nat (length (first_job :: later_jobs))).
                lia.
              }
              go1 using
                (arrayLR_extract_middle_lookup_local_F
                   Tuchar lefts_addr
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs)))
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs))) 32
                   (fun _ : unit => anyR Tuchar 1$m)
                   (replicateN
                      (Z.to_N
                         (32 -
                          Z.pos
                            (PosDef.Pos.of_succ_nat
                               (length later_jobs)))) ())
                   Hleft_tail_slot).
              go.
              assert
                (Hprev_scratch_lookup :
                  nth_error scratch previous.(live_index) =
                  Some
                    (blake3model.bytes32_to_N
                       (eval_tree previous.(live_tree)))).
              {
                pose proof _H_0 as Hscratch_rep.
                destruct Hscratch_rep as [Hscratch_len Hscratch_nodes].
                erewrite <- Hscratch_nodes.
                2: {
                  apply in_or_app.
                  left.
                  exact Hprevious_in_done.
                }
                apply nth_error_nth'.
                rewrite Hscratch_len.
                exact Hprevious_index_lt.
              }
              assert
                (Hprev_scratch_lookup_N :
                  nth_error scratch
                    (N.to_nat (N.of_nat previous.(live_index))) =
                  Some
                    (blake3model.bytes32_to_N
                       (eval_tree previous.(live_tree)))).
              {
                rewrite Nat2N.id.
                exact Hprev_scratch_lookup.
              }
              setoid_rewrite
                (scratchR_unfold_local scratchp 1 scratch) at 1.
              rewrite
                (_at_arrayR_cellN
                   (N.of_nat previous.(live_index)) scratch bytes32_ty
                   (exec_specs.bytes32R 1) scratchp
                   (blake3model.bytes32_to_N
                      (eval_tree previous.(live_tree)))
                   Hprev_scratch_lookup_N).
              rewrite nat_N_Z.
              go1 using
                (bytes32R_to_byte_arrayLR_local_F
                   (scratchp .[ bytes32_ty !
                                previous.(live_index) ])
                   (blake3model.bytes32_to_N
                      (eval_tree previous.(live_tree)))).
              assert
                (Hblock_slot :
                  SolveArith
                    (0 <= Z.of_nat (length (first_job :: later_jobs)) /\
                     Z.of_nat (length (first_job :: later_jobs)) < 32)%Z)
                by (constructor; lia).
              go1 using
                (arrayLR_extract_middle_lookup_local_F
                   merge_block_row_ty blocks_addr 0
                   (Z.of_nat (length (first_job :: later_jobs))) 32
                   merge_block_rowR
                   (map
                      (fun job : merge_job =>
                         MergeBlockFull (merge_job_input job))
                      (first_job :: later_jobs) ++
                    replicateZ
                      (32 - Z.of_nat
                              (length (first_job :: later_jobs)))
                      MergeBlockUninit)
                   Hblock_slot).
              go1 using
                (merge_block_uninit_row_split_first_local_F
                   (blocks_addr .[ merge_block_row_ty !
                               Z.of_nat
                                 (length (first_job :: later_jobs)) ])).
              go1 using
                (any_unit_arrayLR32_to_val_arrayLR32_local_F
                   (blocks_addr .[ merge_block_row_ty !
                               Z.of_nat
                                 (length (first_job :: later_jobs)) ])).
              assert
                (Hprevious_before_current :
                  (previous.(live_index) < current.(live_index))%nat).
              {
                eapply live_nodes_well_formed_app_prefix_before_head.
                { exact Hwf_all. }
                exact Hprevious_in_done.
              }
              assert
                (Hcurrent_index_lt :
                  (current.(live_index) < page_pair_count)%nat).
              {
                simpl in Hwf_todo.
                destruct Hwf_todo as [[_ Hcurrent_upper] _].
                exact Hcurrent_upper.
              }
              assert
                (Hcurrent_scratch_lookup :
                  nth_error scratch current.(live_index) =
                  Some
                    (blake3model.bytes32_to_N
                       (eval_tree current.(live_tree)))).
              {
                pose proof _H_0 as Hscratch_rep.
                destruct Hscratch_rep as [Hscratch_len Hscratch_nodes].
                erewrite <- Hscratch_nodes.
                2: {
                  apply in_or_app.
                  right.
                  left.
                  reflexivity.
                }
                apply nth_error_nth'.
                rewrite Hscratch_len.
                exact Hcurrent_index_lt.
              }
              assert
                (Hcurrent_suffix_lookup :
                  nth_error
                    (drop
                       (N.to_nat
                          (N.of_nat previous.(live_index) + 1))
                       scratch)
                    (N.to_nat
                       (N.of_nat
                          (current.(live_index) -
                           S previous.(live_index)))) =
                  Some
                    (blake3model.bytes32_to_N
                       (eval_tree current.(live_tree)))).
              {
                rewrite nth_error_skipn.
                rewrite N2Nat.inj_add.
                rewrite Nat2N.id.
                change (N.to_nat 1) with 1%nat.
                rewrite Nat.add_1_r.
                rewrite Nat2N.id.
                replace
                  (S previous.(live_index) +
                   (current.(live_index) -
                    S previous.(live_index)))%nat
                  with current.(live_index) by lia.
                exact Hcurrent_scratch_lookup.
              }
              rewrite
                (_at_arrayR_cellN
                   (N.of_nat
                      (current.(live_index) -
                       S previous.(live_index)))
                   (drop
                      (N.to_nat
                         (N.of_nat previous.(live_index) + 1))
                      scratch)
                   bytes32_ty
                   (exec_specs.bytes32R 1)
                   (scratchp .[ bytes32_ty !
                                previous.(live_index) + 1 ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))
                   Hcurrent_suffix_lookup).
              repeat rewrite o_sub_sub.
              rewrite nat_N_Z.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%Z
                with (Z.of_nat current.(live_index)) by lia.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   ((current.(live_index) -
                     S previous.(live_index)) + 1))%Z
                with (Z.of_nat current.(live_index) + 1)%Z by lia.
              go1 using
                (unpacked_bytes32R_to_byte_arrayLR_local_F
                   (scratchp .[ bytes32_ty !
                                current.(live_index) ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))).
              go1 using
                (any_unit_arrayLR32_64_to_val_arrayLR0_32_local_F
                   (blocks_addr .[ merge_block_row_ty !
                               Z.of_nat
                                 (length (first_job :: later_jobs)) ])).
              assert
                (Htail_slot :
                  SolveArith
                    (Z.pos
                       (PosDef.Pos.of_succ_nat
                          (length later_jobs)) <=
                     Z.pos
                       (PosDef.Pos.of_succ_nat
                          (length later_jobs)) < 32)%Z).
              {
                destruct Hleft_slot as [Hleft_slot_ok].
                constructor.
                change
                  (Z.pos
                     (PosDef.Pos.of_succ_nat
                        (length later_jobs)))
                  with
                  (Z.of_nat (length (first_job :: later_jobs))).
                lia.
              }
              go1 using
                (arrayLR_extract_middle_lookup_local_F
                   merge_input_ptr_ty inputs_addr
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs)))
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs))) 32
                   (fun _ : unit => anyR merge_input_ptr_ty 1$m)
                   (replicateN
                      (Z.to_N
                         (32 -
                          Z.pos
                            (PosDef.Pos.of_succ_nat
                               (length later_jobs)))) ())
                   Htail_slot).
              go1 using
                (arrayLR_extract_middle_lookup_local_F
                   Tuchar lefts_addr
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs)))
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs))) 32
                   (fun _ : unit => anyR Tuchar 1$m)
                   (replicateN
                      (Z.to_N
                         (32 -
                          Z.pos
                            (PosDef.Pos.of_succ_nat
                               (length later_jobs)))) ())
                   Htail_slot).
              go.
              go1 using
                (arrayLR_extract_middle_lookup_local_F
                   Tuchar rights_addr
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs)))
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs))) 32
                   (fun _ : unit => anyR Tuchar 1$m)
                   (replicateN
                      (Z.to_N
                         (32 -
                          Z.pos
                            (PosDef.Pos.of_succ_nat
                               (length later_jobs)))) ())
                   Htail_slot).
              set
                (new_job :=
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}).
              assert
                (Hsibling_candidate :
                  sibling_candidate (Z.to_nat bit)
                    previous.(live_index) current.(live_index) = true).
              {
                unfold sibling_candidate.
                rewrite Hsame_parent Hindex_zero.
                reflexivity.
              }
              assert
                (Hscan_after :
                  scan_nodes_from (Z.to_nat bit)
                    initial_merge_scan_state
                    (done_prefix ++ [current]) =
                  {|
                    scan_pending := None;
                    scan_jobs :=
                      (first_job :: later_jobs) ++ [new_job];
                  |}).
              {
                rewrite scan_nodes_from_app.
                rewrite Hscan_done.
                simpl.
                rewrite Hsibling_candidate.
                reflexivity.
              }
              assert
                (Hwf_rest : live_nodes_well_formed rest).
              {
                simpl in Hwf_todo.
                pose proof (proj2 Hwf_todo) as Hrest.
                unfold live_nodes_well_formed.
                eapply live_nodes_well_formed_from_weaken with
                  (lower := S current.(live_index)).
                { exact (Nat.le_0_l _). }
                exact Hrest.
              }
              assert
                (Hblock_tail_slot :
                  SolveArith
                    (0 <=
                     Z.pos
                       (PosDef.Pos.of_succ_nat
                          (length later_jobs)) /\
                     Z.pos
                       (PosDef.Pos.of_succ_nat
                          (length later_jobs)) < 32)%Z).
              {
                destruct Hleft_slot as [Hleft_slot_ok].
                constructor.
                change
                  (Z.pos
                     (PosDef.Pos.of_succ_nat
                        (length later_jobs)))
                  with
                  (Z.of_nat (length (first_job :: later_jobs))).
                lia.
              }
              go1 using
                (arrayLR_extract_middle_lookup_local_F
                   merge_block_row_ty blocks_addr 0
                   (Z.pos
                      (PosDef.Pos.of_succ_nat
                         (length later_jobs))) 32
                   merge_block_rowR
                   (MergeBlockFull (merge_job_input first_job) ::
                    map
                      (fun job : merge_job =>
                         MergeBlockFull (merge_job_input job))
                      later_jobs ++
                   replicateN
                      (Z.to_N (32 - S (length later_jobs)))
                      MergeBlockUninit)
                   Hblock_tail_slot).
              match goal with
              | Hlookup : ?rows !! ?idx = Some x
                |- _ =>
                  pose proof
                    (merge_block_rows_cons_tail_lookup_local
                       first_job later_jobs x Hjobs_lt32 Hlookup)
              end.
              subst x.
              go1 using
                (merge_block_uninit_row_split_first_local_F
                   (blocks_addr .[ merge_block_row_ty !
                               Z.pos
                                 (PosDef.Pos.of_succ_nat
                                    (length later_jobs)) ])).
              go.
              rewrite <- (bi.exist_intro (cQp.mut 1)).
              rewrite <- (bi.exist_intro (Z.of_N <$>
                z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
                  (Z.of_N (blake3model.bytes32_to_N
                    (eval_tree previous.(live_tree)))))).
              rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
              rewrite (eq_trans
                (eq_sym (list_fmap_compose Z.of_N Vint
                  (z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
                    (Z.of_N (blake3model.bytes32_to_N
                      (eval_tree previous.(live_tree)))))))
                (eq_sym (bytes32_be_values_to_Z_to_bytes
                  (blake3model.bytes32_to_N
                    (eval_tree previous.(live_tree)))))).
              go using (typed_slice_nonempty_nonnull_B
                (scratchp .[ bytes32_ty ! previous.(live_index) ] ,,
                  o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
                  o_field CU "evmc_bytes32::bytes") Tuchar 32 ltac:(lia)).
              repeat rewrite o_sub_sub.
              repeat rewrite N2Z.inj_add.
              change (Z.of_N 1) with 1%Z.
              rewrite nat_N_Z.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%Z
                with (Z.of_nat current.(live_index))
                by (clear -Hprevious_before_current; lia).
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   ((current.(live_index) -
                     S previous.(live_index)) + 1))%Z
                with (Z.of_nat current.(live_index) + 1)%Z
                by (clear -Hprevious_before_current; lia).
              go1 using
                (bytes32R_to_byte_arrayLR_local_F
                   (scratchp .[ bytes32_ty !
                                current.(live_index) ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))).
              go using primR_split_C.
              rewrite <- (bi.exist_intro (cQp.mut 1)).
              rewrite <- (bi.exist_intro (Z.of_N <$>
                z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
                  (Z.of_N (blake3model.bytes32_to_N
                    (eval_tree current.(live_tree)))))).
              rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
              rewrite (eq_trans
                (eq_sym (list_fmap_compose Z.of_N Vint
                  (z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
                    (Z.of_N (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))))))
                (eq_sym (bytes32_be_values_to_Z_to_bytes
                  (blake3model.bytes32_to_N
                    (eval_tree current.(live_tree)))))).
              go using (typed_slice_nonempty_nonnull_B
                (scratchp .[ bytes32_ty ! current.(live_index) ] ,,
                  o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
                  o_field CU "evmc_bytes32::bytes") Tuchar 32 ltac:(lia)).
              rewrite <- (bi.exist_intro
                             (A := list live_node)
                             (done_prefix ++ [current])).
              rewrite <- (bi.exist_intro
                             (A := list live_node) rest).
              rewrite Hscan_after.
              rewrite scratchR_unfold_local.
              rewrite
                (_at_arrayR_cellN
                   (N.of_nat previous.(live_index)) scratch bytes32_ty
                   (exec_specs.bytes32R 1) scratchp
                   (blake3model.bytes32_to_N
                      (eval_tree previous.(live_tree)))
                   Hprev_scratch_lookup_N).
              rewrite
                (_at_arrayR_cellN
                   (N.of_nat
                      (current.(live_index) -
                       S previous.(live_index)))
                   (drop
                      (N.to_nat
                         (N.of_nat previous.(live_index) + 1))
                      scratch)
                   bytes32_ty
                   (exec_specs.bytes32R 1)
                   (scratchp .[ bytes32_ty !
                                N.of_nat previous.(live_index) + 1 ])
                   (blake3model.bytes32_to_N
                      (eval_tree current.(live_tree)))
                   Hcurrent_suffix_lookup).
              repeat rewrite o_sub_sub.
              rewrite nat_N_Z.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%Z
                with (Z.of_nat current.(live_index))
                by (clear -Hprevious_before_current; lia).
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   ((current.(live_index) -
                     S previous.(live_index)) + 1))%Z
                with (Z.of_nat current.(live_index) + 1)%Z
                by (clear -Hprevious_before_current; lia).
              unhideAllFromWork.
              assert
                (Hjobs_count :
                  Z.to_N
                    (Z.pos
                       (PosDef.Pos.of_succ_nat
                          (length later_jobs)) + 1) =
                  N.pos
                    (PosDef.Pos.of_succ_nat
                       (length
                          (later_jobs ++
                           [{|
                              merge_left := previous;
                              merge_right := current;
                            |}])))).
              {
                rewrite app_length.
                simpl.
                clear -Hjobs_lt32; lia.
              }
              assert
                (Hjobs_bound :
                  (S
                     (length
                        (later_jobs ++
                         [{|
                            merge_left := previous;
                            merge_right := current;
                          |}])) <= 32)%nat).
              {
                rewrite app_length.
                simpl.
                clear -Hjobs_lt32.
                cbn in Hjobs_lt32.
                lia.
              }
              change
                (fold_left
                   (fun bm node =>
                      (bm `lor` 2 ^ N.of_nat node.(live_index))%N)
                   rest
                   (0 `lor` 2 ^ N.of_nat current.(live_index))%N)
                with (live_nodes_bitmap_word (current :: rest)).
              rewrite
                (live_nodes_bitmap_word_cons_clear_lowest_Z
                   current rest Hwf_todo).
              repeat rewrite o_sub_sub.
              rewrite nat_N_Z.
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   (current.(live_index) -
                    S previous.(live_index)))%Z
                with (Z.of_nat current.(live_index))
                by (clear -Hprevious_before_current; lia).
              replace
                (Z.of_nat previous.(live_index) + 1 +
                 Z.of_nat
                   ((current.(live_index) -
                     S previous.(live_index)) + 1))%Z
                with (Z.of_nat current.(live_index) + 1)%Z
                by (clear -Hprevious_before_current; lia).
              go1 using
                (merge_block_full_from_offset_halves_local_F
                   (blocks_addr .[ merge_block_row_ty !
                               Z.of_nat
                                 (length (first_job :: later_jobs)) ])
                   (eval_tree previous.(live_tree))
                   (eval_tree current.(live_tree))).
              rewrite
                (sliceZ_tail_after_one_replicate_local
                   (S (length later_jobs)) ()
                   ltac:(exact Hjobs_lt32)).
              rewrite
                (sliceZ_prefix_cons_map_app_replicate_local
                   (fun job : merge_job =>
                      MergeBlockFull (merge_job_input job))
                   (MergeBlockFull (merge_job_input first_job))
                   later_jobs
                   MergeBlockUninit).
              rewrite
                (sliceZ_tail_after_one_cons_map_app_replicate_local
                   (fun job : merge_job =>
                      MergeBlockFull (merge_job_input job))
                   (MergeBlockFull (merge_job_input first_job))
                   later_jobs
                   MergeBlockUninit
                   ltac:(simpl; exact Hjobs_lt32)).
              replace
                (32 - S (length later_jobs) - 1)%Z
                with
                (32 - (S (length later_jobs) + 1))%Z
                by lia.
              go1 using
                (merge_inputs_arrayR_snoc_from_slice_parts_local_F
                   inputs_addr blocks_addr (first_job :: later_jobs)
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}
                   Hjobs_lt32).
              replace
                (32 - S (length later_jobs) - 1)%Z
                with
                (32 - (S (length later_jobs) + 1))%Z
                by lia.
              go1 using
                (merge_block_rows_snoc_from_slice_parts_local_F
                   blocks_addr (first_job :: later_jobs)
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}
                   Hjobs_lt32).
              replace
                (32 - S (length later_jobs) - 1)%Z
                with
                (32 - (S (length later_jobs) + 1))%Z
                by lia.
              go1 using
                (merge_index_arraysR_snoc_jobs_from_minus_slice_parts_local_F
                   lefts_addr rights_addr (first_job :: later_jobs)
                   {|
                     merge_left := previous;
                     merge_right := current;
                   |}
                   Hjobs_lt32).
              change [merge_job_left_index
                        {|
                          merge_left := previous;
                          merge_right := current;
                        |}]
                with
                (map merge_job_left_index
                   [{|
                      merge_left := previous;
                      merge_right := current;
                    |}]).
              change [merge_job_right_index
                        {|
                          merge_left := previous;
                          merge_right := current;
                        |}]
                with
                (map merge_job_right_index
                   [{|
                      merge_left := previous;
                      merge_right := current;
                    |}]).
              rewrite <- !map_app.
              change
                (MergeBlockFull (merge_job_input first_job) ::
                 map
                   (fun job : merge_job =>
                      MergeBlockFull (merge_job_input job))
                   (later_jobs ++
                    [{|
                       merge_left := previous;
                       merge_right := current;
                     |}]) ++
                 replicateZ
                   (32 -
                    S
                      (length
                         (later_jobs ++
                          [{|
                             merge_left := previous;
                             merge_right := current;
                           |}])))
                   MergeBlockUninit)
                with
                (merge_block_rows
                   (first_job ::
                    later_jobs ++
                    [{|
                       merge_left := previous;
                       merge_right := current;
                     |}])).
              change
                (merge_job_left_index first_job ::
                 map merge_job_left_index
                   (later_jobs ++
                    [{|
                       merge_left := previous;
                       merge_right := current;
                     |}]))
                with
                (map merge_job_left_index
                   (first_job ::
                    later_jobs ++
                    [{|
                       merge_left := previous;
                       merge_right := current;
                     |}])).
              change
                (merge_job_right_index first_job ::
                 map merge_job_right_index
                   (later_jobs ++
                    [{|
                       merge_left := previous;
                       merge_right := current;
                     |}]))
                with
                (map merge_job_right_index
                   (first_job ::
                    later_jobs ++
                    [{|
                       merge_left := previous;
                       merge_right := current;
                     |}])).
              unfold merge_plan_arraysR.
              go using bytes_field_to_bytes32R_B.
            }
          }
          {
            assert
              (Hsibling_candidate :
                sibling_candidate (Z.to_nat bit)
                  previous.(live_index) current.(live_index) = false).
            {
              unfold sibling_candidate.
              rewrite Hsame_parent Hindex_zero.
              reflexivity.
            }
            assert
              (Hscan_after :
                scan_nodes_from (Z.to_nat bit)
                  initial_merge_scan_state
                  (done_prefix ++ [current]) =
                {|
                  scan_pending := Some current;
                  scan_jobs := jobs;
                |}).
            {
              rewrite scan_nodes_from_app.
              rewrite Hscan_done.
              simpl.
              rewrite Hsibling_candidate.
              reflexivity.
            }
            assert (Hwf_rest : live_nodes_well_formed rest).
            {
              simpl in Hwf_todo.
              destruct Hwf_todo as [_ Hrest].
              eapply live_nodes_well_formed_from_weaken.
              {
                lia.
              }
              exact Hrest.
            }
            go.
            rewrite <- (bi.exist_intro (done_prefix ++ [current])).
            rewrite <- (bi.exist_intro rest).
            rewrite Hscan_after.
            change
              (fold_left
                 (fun bm node =>
                    (bm `lor` 2 ^ N.of_nat node.(live_index))%N)
                 rest
                 (0 `lor` 2 ^ N.of_nat current.(live_index))%N)
              with (live_nodes_bitmap_word (current :: rest)).
            rewrite
              (live_nodes_bitmap_word_cons_clear_lowest_Z
                 current rest Hwf_todo).
            unfold ScratchR.
            go.
          }
        }
        {
          assert
            (Hsibling_candidate :
              sibling_candidate (Z.to_nat bit)
                previous.(live_index) current.(live_index) = false).
          {
            unfold sibling_candidate.
            rewrite Hsame_parent.
            reflexivity.
          }
          assert
            (Hscan_after :
              scan_nodes_from (Z.to_nat bit)
                initial_merge_scan_state
                (done_prefix ++ [current]) =
              {|
                scan_pending := Some current;
                scan_jobs := jobs;
              |}).
          {
            rewrite scan_nodes_from_app.
            rewrite Hscan_done.
            simpl.
            rewrite Hsibling_candidate.
            reflexivity.
          }
          assert (Hwf_rest : live_nodes_well_formed rest).
          {
            simpl in Hwf_todo.
            destruct Hwf_todo as [_ Hrest].
            eapply live_nodes_well_formed_from_weaken.
            {
              lia.
            }
            exact Hrest.
          }
          go.
          rewrite <- (bi.exist_intro (done_prefix ++ [current])).
          rewrite <- (bi.exist_intro rest).
          rewrite Hscan_after.
          change
            (fold_left
               (fun bm node =>
                  (bm `lor` 2 ^ N.of_nat node.(live_index))%N)
               rest
               (0 `lor` 2 ^ N.of_nat current.(live_index))%N)
            with (live_nodes_bitmap_word (current :: rest)).
          rewrite
            (live_nodes_bitmap_word_cons_clear_lowest_Z
               current rest Hwf_todo).
          unfold ScratchR.
          go.
        }
      }
      {
        assert
          (Hscan_after :
            scan_nodes_from (Z.to_nat bit)
              initial_merge_scan_state
              (done_prefix ++ [current]) =
            {|
              scan_pending := Some current;
              scan_jobs := jobs;
            |}).
        {
          rewrite scan_nodes_from_app.
          rewrite Hscan_done.
          simpl.
          reflexivity.
        }
        assert (Hwf_rest : live_nodes_well_formed rest).
        {
          simpl in Hwf_todo.
          destruct Hwf_todo as [_ Hrest].
          eapply live_nodes_well_formed_from_weaken.
          {
            lia.
          }
          exact Hrest.
        }
        go.
        rewrite <- (bi.exist_intro (done_prefix ++ [current])).
        rewrite <- (bi.exist_intro rest).
        rewrite Hscan_after.
        change
          (fold_left
             (fun bm node =>
                (bm `lor` 2 ^ N.of_nat node.(live_index))%N)
             rest
             (0 `lor` 2 ^ N.of_nat current.(live_index))%N)
          with (live_nodes_bitmap_word (current :: rest)).
        rewrite
          (live_nodes_bitmap_word_cons_clear_lowest_Z
             current rest Hwf_todo).
        unfold ScratchR.
        go.
      }
    }
    {
      intro Hbits_zero.
      match goal with
      | Hwf : live_nodes_well_formed ?todo,
          Hzero : live_nodes_bitmap_word ?todo = 0%N |- _ =>
          pose proof
            (live_nodes_bitmap_word_zero_wf_nil todo Hwf Hzero)
            as Htodo_nil;
          subst todo
      end.
      match goal with
      | Hwf_done : live_nodes_well_formed (?done ++ []) |- _ =>
          set (nodes := done) in *
      end.
      rewrite app_nil_r.
      unfold ScratchR.
      go.
      (* Back in merge_scratch_level after collect_merge_scratch_level_jobs. *)
      unfold merge_plan_arraysR, merge_index_arrayR, merge_inputs_arrayR,
        merge_block_rows.
      simpl.
      wp_if.
      2: {
        intros Hnonzero.
	        go using wp_seq_B, wp.wp_block_nil_B.
	        go.
	        rewrite <-
	          (bi.exist_intro false).
	        rewrite <- (bi.exist_intro 1%Qp).
	        rewrite <-
	          (bi.exist_intro
	             (merge_input_blocks blocks_addr
                (merge_jobs (Z.to_nat bit) nodes))).
        assert
          (Hjobs_le_blake3 :
            (length (merge_jobs (Z.to_nat bit) nodes) <= 32)%nat).
        {
          match goal with
          | Hjobs_le :
              (length
                 (scan_jobs
                    (scan_nodes_from
                       (Z.to_nat bit) initial_merge_scan_state nodes)) <=
               32)%nat |- _ =>
              unfold merge_jobs, scan_nodes;
              exact Hjobs_le
          end.
        }
        change
          (scan_jobs
             (scan_nodes_from
                (Z.to_nat bit) initial_merge_scan_state nodes))
          with (merge_jobs (Z.to_nat bit) nodes) in *.
        go using
          merge_inputs_arrayR_pack_F,
          merge_block_rows_blake3_unpack_F,
          merge_inputs_arrayR_blake3_unpack_F,
          merge_inputs_arrayR_blake3_inputs_pack_F,
          merge_input_blocks_length.
        go1 using
          (merge_block_rows_blake3_pack_F
             blocks_addr (merge_jobs (Z.to_nat bit) nodes)).
        go1 using
          (merge_inputs_arrayR_blake3_inputs_unpack_F
             inputs_addr blocks_addr
             (merge_jobs (Z.to_nat bit) nodes)).
        go1 using
          (merge_inputs_arrayR_blake3_pack_F
             inputs_addr blocks_addr (merge_jobs (Z.to_nat bit) nodes)).
        go1 using
          (merge_plan_arraysR_expanded_pack_F
             lefts_addr rights_addr blocks_addr inputs_addr
             (merge_jobs (Z.to_nat bit) nodes)).
        set (old_outputs_prefix :=
          firstn
            (length (merge_jobs (Z.to_nat bit) nodes))
            (replicateN 32 0%N)).
        assert (Hold_outputs_prefix_length :
          length old_outputs_prefix =
          length (merge_jobs (Z.to_nat bit) nodes)).
        {
          subst old_outputs_prefix.
          rewrite firstn_length_le.
          {
            reflexivity.
          }
          {
            rewrite rwdb.length_replicateN.
            exact Hjobs_le_blake3.
          }
        }
        go.
        set (jobs := merge_jobs (Z.to_nat bit) nodes).
        set (outputs :=
          blake3_hash_many_outputs blake3model.merge_mode
            (map merge_job_input jobs) ++
          skipn (length jobs) (replicateN 32 0%N)).
        assert
          (Houtputs_eq :
            outputs =
            merge_hash_outputs jobs (replicateN 32 0%N)).
        {
          subst outputs.
          unfold merge_hash_outputs.
          reflexivity.
        }
        assert (Hjobs_le : (length jobs <= 32)%nat).
        {
          subst jobs.
          exact Hjobs_le_blake3.
        }
        assert (Hwf_nodes : live_nodes_well_formed nodes).
        {
          match goal with
          | Hwf : live_nodes_well_formed (nodes ++ []) |- _ =>
              rewrite <- (app_nil_r nodes);
              exact Hwf
          end.
        }
        assert
          (Hscratch_nodes :
            scratch_represents_live_nodes scratch nodes).
        {
          match goal with
          | Hscratch :
              scratch_represents_live_nodes scratch (nodes ++ []) |- _ =>
              rewrite <- (app_nil_r nodes);
              exact Hscratch
          end.
        }
        match goal with
        | Hlen : length scratch = page_pair_count |- _ =>
            go1 using (ScratchR_pack_F scratchp 1 scratch Hlen)
        end.
        go using (merge_output_words32_zero_pack_cells_F flat_out_addr).
        rewrite <- (bi.exist_intro old_outputs_prefix).
        go using
          Hold_outputs_prefix_length,
          (blake3_output_words_split_prefix_to_bytes_F
             flat_out_addr (replicateN 32 0%N)
             (length (merge_jobs (Z.to_nat bit) nodes))
             Hjobs_le_blake3).
        go.
	        rewrite merge_input_blocks_data.
        change (map model.bytes32_to_N _) with
          (blake3_hash_many_outputs_from_params
            (blake3_hash_many_call_params
              model.blake3_iv_words 0 false 0 1 2)
            (map merge_job_input jobs)).
	        rewrite merge_hash_outputs_from_call_params.
	        rewrite !merge_input_blocks_length.
        assert
          (Hmerge_output_range :
            List.Forall (fun x => (x < 2 ^ 256)%N)
              (blake3_hash_many_outputs blake3model.merge_mode
                 (map merge_job_input jobs))).
        {
          apply blake3specs.blake3_hash_many_outputs_range.
        }
	        go using
	          (blake3_output_bytes_prefix_tail_to_words_F
	             flat_out_addr
             (blake3_hash_many_outputs blake3model.merge_mode
                (map merge_job_input jobs))
             (skipn (length jobs) (replicateN 32 0%N))
             (length jobs)
	             Hmerge_output_range
	             (eq_sym (merge_hash_outputs_length jobs))).
	        rewrite !List.length_map.
	        go1 using (merge_block_rows_blake3_pack_F blocks_addr jobs Hjobs_le).
	        repeat rewrite combine_seq_jobs_length.
	        go1 using
	          (merge_input_blocks_ptr_array_to_input_ptrs_F
	             inputs_addr blocks_addr jobs).
	        go1 using (merge_inputs_arrayR_ptr_pack_F inputs_addr blocks_addr jobs).
        go1 using (merge_block_rows_pack_F blocks_addr jobs).
        wp_for (fun _ =>
          Exists j bm_loop : N,
          Exists scratch_loop : list N,
            [| (j <= N.of_nat (length jobs))%N |]
            ** [| bm_loop =
                  apply_merge_jobs_to_bitmap
                    (live_nodes_bitmap_word nodes)
                    (take (N.to_nat j) jobs) |]
            ** [| scratch_loop =
                  apply_merge_jobs_to_scratch
                    scratch (take (N.to_nat j) jobs) |]
            ** scratch_addr |-> refR<scratch_array_ty> 1$m scratchp
            ** scratchp |-> ScratchR 1 scratch_loop
            ** merge_plan_arraysR lefts_addr rights_addr blocks_addr inputs_addr jobs
            ** flat_out_addr |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
                 outputs
            ** bm_addr |-> ulongR 1$m bm_loop
            ** j_addr |-> ulongR 1$m j).
        rewrite <- (bi.exist_intro 0%N).
        rewrite <- (bi.exist_intro (live_nodes_bitmap_word nodes)).
        rewrite <- (bi.exist_intro scratch).
        change (N.to_nat 0) with 0%nat.
        cbn [take apply_merge_jobs_to_bitmap apply_merge_jobs_to_scratch].
        go using
          (merge_plan_arraysR_pack_B
             lefts_addr rights_addr blocks_addr inputs_addr jobs),
          (merge_index_arrayR_pack_B
             lefts_addr (map merge_job_left_index jobs)),
          (merge_index_arrayR_pack_B
             rights_addr (map merge_job_right_index jobs)).
        rewrite !List.length_map.
        go.
        wp_if.
        {
          intro Hloop.
          lazymatch type of Hloop with
          | (Z.of_N ?j < _)%Z => set (jN := j) in *
          end.
          set (job_index := N.to_nat jN) in *.
          assert (Hjob_bound : (job_index < length jobs)%nat).
          {
            subst job_index.
            lia.
          }
          destruct (lookup_lt_is_Some_2 jobs job_index Hjob_bound)
            as [job Hjob_lookup].
          assert
            (Hleft_lookup :
              map merge_job_left_index jobs !! job_index =
              Some (merge_job_left_index job)).
          {
            rewrite list_lookup_fmap.
            rewrite Hjob_lookup.
            reflexivity.
          }
          assert
            (Hright_lookup :
              map merge_job_right_index jobs !! job_index =
              Some (merge_job_right_index job)).
          {
            rewrite list_lookup_fmap.
            rewrite Hjob_lookup.
            reflexivity.
          }
          assert
            (Hout_lookup :
              outputs !! job_index = Some (merge_job_output job)).
          {
            rewrite Houtputs_eq.
            apply merge_hash_outputs_lookup.
            exact Hjob_lookup.
          }
          assert
            (Hjob_lookup_model :
              merge_jobs (Z.to_nat bit) nodes !! job_index =
              Some job).
          {
            unfold jobs in Hjob_lookup.
            exact Hjob_lookup.
          }
          match goal with
          | Hwf : live_nodes_well_formed nodes |- _ =>
              pose proof
                (merge_jobs_lookup_left_index_bound
                   (Z.to_nat bit) nodes job_index job Hwf
                   Hjob_lookup_model)
                as Hleft_bound;
              pose proof
                (merge_jobs_lookup_right_index_bound
                   (Z.to_nat bit) nodes job_index job Hwf
                   Hjob_lookup_model)
                as Hright_bound
          end.
          assert
            (Hscratch_len :
              length
                (apply_merge_jobs_to_scratch
                   scratch (take job_index jobs)) =
              page_pair_count).
          {
            rewrite apply_merge_jobs_to_scratch_length.
            match goal with
            | Hscratch :
                scratch_represents_live_nodes scratch nodes |- _ =>
                destruct Hscratch as [Hscratch_len _];
                exact Hscratch_len
            end.
          }
          assert
            (Hscratch_bound :
              (merge_job_left_index job <
               length
                 (apply_merge_jobs_to_scratch
                    scratch (take job_index jobs)))%nat).
          {
            rewrite Hscratch_len.
            exact Hleft_bound.
          }
          destruct
            (lookup_lt_is_Some_2
               (apply_merge_jobs_to_scratch
                  scratch (take job_index jobs))
               (merge_job_left_index job) Hscratch_bound)
            as [old_cell Hscratch_lookup].
          go using
            (merge_plan_left_index_read_with_wand_F
               lefts_addr rights_addr blocks_addr inputs_addr jobs job_index
               (merge_job_left_index job) Hleft_lookup Hjobs_le),
            (merge_plan_right_index_read_with_wand_F
               lefts_addr rights_addr blocks_addr inputs_addr jobs job_index
               (merge_job_right_index job) Hright_lookup Hjobs_le),
            (arrayR_read_cell_with_wand_F
               bytes32_ty (exec_specs.bytes32R 1) flat_out_addr outputs
               job_index (merge_job_output job) Hout_lookup),
            (ScratchR_update_cell_with_wand_F
               scratchp
               (apply_merge_jobs_to_scratch
                  scratch (take job_index jobs))
               (merge_job_left_index job) old_cell
               (merge_job_output job) Hscratch_lookup),
            type_ptr_reference_to_B_local.
          replace jN with (N.of_nat job_index) by
            (subst job_index; apply N2Nat.id).
          rewrite (ptr_o_sub_N_of_nat bytes32_ty flat_out_addr job_index).
          go.
          rewrite (ptr_o_sub_N_of_nat Tuchar lefts_addr job_index).
          go.
          rewrite (ptr_o_sub_N_of_nat Tuchar rights_addr job_index).
          go using
            (use_wand_local_r_F
               (lefts_addr .[ Tuchar ! Z.of_nat job_index ]
                |-> ucharR 1$m (Z.of_nat (merge_job_left_index job)))
               (merge_plan_arraysR lefts_addr rights_addr blocks_addr inputs_addr jobs)),
            (merge_plan_right_index_read_with_wand_F
               lefts_addr rights_addr blocks_addr inputs_addr jobs job_index
               (merge_job_right_index job) Hright_lookup Hjobs_le).
          rewrite to_nat_Z_to_N_N_of_nat_succ.
          rewrite
            (apply_merge_jobs_to_bitmap_take_succ
               (live_nodes_bitmap_word nodes) jobs job_index job
               Hjob_lookup).
          rewrite
            (apply_merge_jobs_to_scratch_take_succ
               scratch jobs job_index job Hjob_lookup).
          unfold apply_merge_job_to_bitmap.
          rewrite
            (clearbit_ulong_expr
               (apply_merge_jobs_to_bitmap
                  (live_nodes_bitmap_word nodes)
                  (take job_index jobs))
               (merge_job_right_index job)).
          2: {
            arith_solve.
          }
          2: {
            unfold page_pair_count in Hright_bound.
            exact Hright_bound.
          }
          unfold apply_merge_job_to_scratch.
          go using
            (use_wand_local_r_F
               (scratchp .[ bytes32_ty !
                  Z.of_nat (merge_job_left_index job) ]
                |-> exec_specs.bytes32R 1 (merge_job_output job))
               (scratchp |-> ScratchR 1
                  (<[merge_job_left_index job := merge_job_output job]>
                     (apply_merge_jobs_to_scratch
                        scratch (take job_index jobs))))).
        }
        {
          intro Hdone.
          lazymatch goal with
          | Hle : (?jv <= N.of_nat (length jobs))%N |- _ =>
              set (done_j := jv) in *
          end.
          go.
          replace (N.to_nat done_j) with (length jobs).
          2: {
            lia.
          }
          rewrite firstn_all.
          unfold jobs.
          rewrite
            (apply_merge_jobs_to_bitmap_live_nodes
               (Z.to_nat bit) nodes Hwf_nodes).
          pose proof
            (apply_merge_jobs_to_scratch_represents
               (Z.to_nat bit) nodes scratch Hwf_nodes Hscratch_nodes)
            as Hscratch_merge.
        go1 using
          (merge_plan_arraysR_cleanup_split_direct_F
             lefts_addr rights_addr blocks_addr inputs_addr jobs Hjobs_le).
        change (map model.bytes32_to_N _ ++ _) with outputs.
        rewrite Houtputs_eq.
        rewrite
          (bytes32_arrayR_expand_32_cells
             flat_out_addr
             (merge_hash_outputs jobs (replicateN 32 0%N))
             (merge_hash_outputs_replicate32_length jobs Hjobs_le)).
        Opaque exec_specs.bytes32R.
        rewrite PostCondition.unlock.
        go1 using
          (merge_scratch_level_done_with_frame_F
             _
             (merge_plan_arrays_cleanup_splitR
                lefts_addr rights_addr blocks_addr inputs_addr)
             qiv bit nodes
             (apply_merge_jobs_to_scratch scratch jobs)
             scratchp level_addr bm_addr scratch_addr _
             Hscratch_merge).
        unfold merge_plan_arrays_cleanup_splitR.
        cbn [merge_block_cleanup_rows_expanded
             merge_block_cleanup_rows_from].
        unfold merge_block_cleanup_rowR.
        go using type_ptr_valid.
        rewrite <-
          (bi.exist_intro (apply_merge_jobs_to_scratch scratch jobs)).
        rewrite app_nil_r.
        go using type_ptr_valid.
         }
      }
      {
        intros Hzero.
        change
          (scan_jobs
             (scan_nodes_from
                (Z.to_nat bit) initial_merge_scan_state nodes))
          with (merge_jobs (Z.to_nat bit) nodes) in Hzero |- *.
        assert
          (Hjobs_nil : merge_jobs (Z.to_nat bit) nodes = []).
        { apply nil_length_inv.
          apply Nat2N.inj.
          exact Hzero. }
        pose proof
          (merge_jobs_nil_merge_level
             (Z.to_nat bit) nodes Hjobs_nil) as Hmerge_level.
        rewrite Hjobs_nil.
        simpl.
        go1.
        go1.
        go1.
        go1.
        go1 using
          (wp_destroy_merge_inputs_array_cleanup_local_B
             source inputs_addr _).
        go1 using (merge_block_uninit_rows_forget_F blocks_addr).
        go1 using
          (wp_destroy_merge_blocks_array_cleanup_local_B
             source blocks_addr _).
        go1.
        go1 using
          (destroy_run_merge_index_array_cleanup_local_B
             source rights_addr _).
        go1.
        go1 using
          (destroy_run_merge_index_array_cleanup_local_B
             source lefts_addr _).
        match goal with
        | Hscratch :
            scratch_represents_live_nodes scratch (nodes ++ []) |- _ =>
            assert
              (Hscratch_nodes :
                scratch_represents_live_nodes scratch nodes)
              by (rewrite <- app_nil_r; exact Hscratch)
        end.
        match goal with
        | Hlen : length scratch = page_pair_count |- _ =>
            go1 using (ScratchR_pack_F scratchp 1 scratch Hlen)
        end.
        rewrite <- (bi.exist_intro scratch).
        rewrite app_nil_r.
        rewrite Hmerge_level.
        go.
	      }
    }
  Qed.
End with_Sigma.

#[global] Opaque
  countr_zero64
  countr_zero_fuel
  popcount64
  popcount_fuel
  exec_specs.bytes32R
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32_be_values
  exec_specs.bytes32_be_values_from.

#[global] Hint Opaque
  countr_zero64
  countr_zero_fuel
  popcount64
  popcount_fuel
  exec_specs.bytes32R
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32_be_values
  exec_specs.bytes32_be_values_from : sl_opacity.
