Set Default Goal Selector "!".

From Stdlib Require Import List NArith ZArith Lia.
Import ListNotations.

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.brick_upstream.
Require Import monad.proofs.execproofs.mip8.blake3specs.
Require Import skylabs.auto.cpp.hints.cast.

Transparent
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R
  blake3_impl_h_specs.bytes32_byte_values
  blake3_impl_h_specs.bytes64_byte_values
  blake3_impl_h_specs.RawDigestBytesR
  blake3_impl_h_specs.Blake3BlockR
  blake3_impl_h_specs.Blake3KeyWordsR
  blake3_impl_h_specs.Blake3ConstKeyWordsR
  blake3specs.blake3_seal_digest
  blake3specs.blake3_seal_model.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Definition uninitR_anyR_F ty q :=
    [FWD] (uninitR_anyR ty q).

  Definition primR_anyR_F ty q v :=
    [FWD] (primR_anyR ty q v).

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

  Lemma byte_arrayR_to_arrayLR
      (base : ptr) q bytes len :
    length bytes = Z.to_nat len ->
    (0 <= len)%Z ->
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes
    |--
    base |-> arrayLR Tuchar 0 len
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes.
  Proof using CU MODd Sigma.
    intros Hlen Hlen_nonneg.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite lengthZ_correct Hlen.
    replace (Z.of_nat (Z.to_nat len)) with len by lia.
    go.
  Qed.

  Definition byte_arrayR_to_arrayLR_F base q bytes len Hlen Hlen_nonneg :=
    [FWD] (byte_arrayR_to_arrayLR base q bytes len Hlen Hlen_nonneg).

  Lemma byte_arrayR_at_to_arrayLR
      (base : ptr) q start len bytes :
    length bytes = Z.to_nat len ->
    (0 <= len)%Z ->
    base .[ Tuchar ! start ] |-> arrayR Tuchar
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes
    |--
    base |-> arrayLR Tuchar start (start + len)
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes.
  Proof using CU MODd Sigma.
    intros Hlen Hlen_nonneg.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite lengthZ_correct Hlen.
    replace (Z.of_nat (Z.to_nat len)) with len by lia.
    go.
  Qed.

  Definition byte_arrayR_at_to_arrayLR_F base q start len bytes
      Hlen Hlen_nonneg :=
    [FWD]
      (byte_arrayR_at_to_arrayLR
         base q start len bytes Hlen Hlen_nonneg).

  Lemma arrayLR_shift_base_local {A : Type}
      (ty : type) (Hty : @HasSize CU ty)
      (base : ptr) start i j (f : A -> Rep) xs :
    base |-> arrayLR ty (start + i) (start + j) f xs
    |--
    base .[ ty ! start ] |-> arrayLR ty i j f xs.
  Proof using CU MODd Sigma.
    rewrite !array_sliceR.unlock.
    rewrite !_at_sep !_at_only_provable.
    repeat rewrite _at_offsetR.
    rewrite o_sub_sub.
    normalize_ptrs.
    go.
  Qed.

  Definition arrayLR_shift_base_local_F {A : Type}
      ty (Hty : @HasSize CU ty) base start i j f (xs : list A) :=
    [FWD] (@arrayLR_shift_base_local
             A ty Hty base start i j f xs).

  Lemma byte_arrayLR_to_arrayR
      (base : ptr) q bytes len :
    length bytes = Z.to_nat len ->
    (0 <= len)%Z ->
    base |-> arrayLR Tuchar 0 len
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes
    |--
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar (cQp.mut q) byte) bytes.
  Proof using CU MODd Sigma.
    intros Hlen Hlen_nonneg.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite lengthZ_correct Hlen.
    replace (Z.of_nat (Z.to_nat len)) with len by lia.
    go.
  Qed.

  Definition byte_arrayLR_to_arrayR_F base q bytes len Hlen Hlen_nonneg :=
    [FWD] (byte_arrayLR_to_arrayR base q bytes len Hlen Hlen_nonneg).

  Lemma z_byte_arrayR_to_val_arrayLR
      (base : ptr) q bytes len :
    length bytes = Z.to_nat len ->
    (0 <= len)%Z ->
    base |-> arrayR Tuchar
      (fun byte : Z => ucharR q byte) bytes
    |--
    base |-> arrayLR Tuchar 0 len
      (fun byte : val => primR Tuchar q byte)
      (map Vint bytes).
  Proof using CU MODd Sigma.
    intros Hlen Hlen_nonneg.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite lengthZ_correct.
    rewrite map_length Hlen.
    replace (Z.of_nat (Z.to_nat len)) with len by lia.
    rewrite arrayR_map'.
    go.
  Qed.

  Definition z_byte_arrayR_to_val_arrayLR_F
      base q bytes len Hlen Hlen_nonneg :=
    [FWD]
      (z_byte_arrayR_to_val_arrayLR
         base q bytes len Hlen Hlen_nonneg).

  Lemma z_byte_arrayLR_to_arrayR
      (base : ptr) q bytes len :
    length bytes = Z.to_nat len ->
    (0 <= len)%Z ->
    base |-> arrayLR Tuchar 0 len
      (fun byte : val => primR Tuchar q byte)
      (map Vint bytes)
    |--
    base |-> arrayR Tuchar
      (fun byte : Z => ucharR q byte) bytes.
  Proof using CU MODd Sigma.
    intros Hlen Hlen_nonneg.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    rewrite lengthZ_correct.
    rewrite map_length Hlen.
    replace (Z.of_nat (Z.to_nat len)) with len by lia.
    rewrite arrayR_map'.
    go.
  Qed.

  Definition z_byte_arrayLR_to_arrayR_F
      base q bytes len Hlen Hlen_nonneg :=
    [FWD]
      (z_byte_arrayLR_to_arrayR
         base q bytes len Hlen Hlen_nonneg).

  Lemma uint128_bytes_to_const_primR
      (base : ptr) bytes value :
    decodes_uint bytes (Z.of_N value) ->
    length bytes = N.to_nat 16 ->
    base |-> type_ptrR Tuint128_t
    ** base |-> arrayLR Tuchar 0 16
      (fun byte : val => primR Tuchar 1$c byte)
      (map Vint (Z.of_N <$> bytes))
    |-- base |-> primR Tuint128_t 1$c (Vint (Z.of_N value)).
  Proof using CU MODd Sigma.
    intros Hdecode Hlen.
    assert (Hbytes_len :
              length (Z.of_N <$> bytes) = Z.to_nat 16).
    {
      rewrite length_fmap Hlen.
      reflexivity.
    }
    rewrite
      (z_byte_arrayLR_to_arrayR
         base 1$c (Z.of_N <$> bytes) 16
         Hbytes_len ltac:(lia)).
    rewrite
      (decode_uint_primR 1$c int_rank.I128 (Z.of_N value)).
    rewrite <- (bi.exist_intro (A := list raw_byte)
                  (raw_int_byte <$> bytes)).
    rewrite <- (bi.exist_intro (A := list N) bytes).
    go.
  Qed.

  Definition uint128_bytes_to_const_primR_F base bytes value Hdecode Hlen :=
    [FWD] (uint128_bytes_to_const_primR
             base bytes value Hdecode Hlen).

  Lemma uint128_bytes_to_const_primR_from_type_ptr
      (base : ptr) bytes value :
    decodes_uint bytes (Z.of_N value) ->
    length bytes = N.to_nat 16 ->
    type_ptr Tuint128_t base
    ** base |-> arrayLR Tuchar 0 16
      (fun byte : val => primR Tuchar 1$c byte)
      (map Vint (Z.of_N <$> bytes))
    |-- base |-> primR Tuint128_t 1$c (Vint (Z.of_N value)).
  Proof using CU MODd Sigma.
    intros Hdecode Hlen.
    rewrite -(_at_type_ptrR base Tuint128_t).
    exact (uint128_bytes_to_const_primR base bytes value Hdecode Hlen).
  Qed.

  Definition uint128_bytes_to_const_primR_from_type_ptr_F
      base bytes value Hdecode Hlen :=
    [FWD] (uint128_bytes_to_const_primR_from_type_ptr
             base bytes value Hdecode Hlen).

  Lemma uint128_const_bytes_make_mutable
      (tu : translation_unit) (base : ptr) bytes value Q :
    decodes_uint bytes (Z.of_N value) ->
    length bytes = N.to_nat 16 ->
    base |-> type_ptrR Tuint128_t
    ** base |-> arrayLR Tuchar 0 16
         (fun byte : val => primR Tuchar 1$c byte)
         (map Vint (Z.of_N <$> bytes))
    ** (base |-> anyR Tuint128_t 1$m -* Q)
    |-- wp_make_mutable tu base Tuint128_t Q.
  Proof using CU MODd Sigma.
    intros Hdecode Hlen.
    transitivity
      (base |-> primR Tuint128_t 1$c (Vint (Z.of_N value))
       ** (base |-> anyR Tuint128_t 1$m -* Q)).
    {
      rewrite bi.sep_assoc.
      apply bi.sep_mono_l.
      exact
        (uint128_bytes_to_const_primR
           base bytes value Hdecode Hlen).
    }
    rewrite <- (primR_wp_const_val
                  tu 1$c 1$m base Tuint128_t Q
                  ltac:(vm_compute; reflexivity)).
    cbn.
    rewrite <-
      (bi.exist_intro (A := val) (Vint (Z.of_N value))).
    go using primR_anyR_F.
  Qed.

  Definition uint128_const_bytes_make_mutable_B
      tu base bytes value Q Hdecode Hlen :=
    [BWD] (uint128_const_bytes_make_mutable
             tu base bytes value Q Hdecode Hlen).

  Lemma uint128_const_bytes_make_mutable_from_type_ptr
      (tu : translation_unit) (base : ptr) bytes value Q :
    decodes_uint bytes (Z.of_N value) ->
    length bytes = N.to_nat 16 ->
    type_ptr Tuint128_t base
    ** base |-> arrayLR Tuchar 0 16
         (fun byte : val => primR Tuchar 1$c byte)
         (map Vint (Z.of_N <$> bytes))
    ** (base |-> anyR Tuint128_t 1$m -* Q)
    |-- wp_make_mutable tu base Tuint128_t Q.
  Proof using CU MODd Sigma.
    intros Hdecode Hlen.
    rewrite -(_at_type_ptrR base Tuint128_t).
    exact (uint128_const_bytes_make_mutable
             tu base bytes value Q Hdecode Hlen).
  Qed.

  Definition uint128_const_bytes_make_mutable_from_type_ptr_B
      tu base bytes value Q Hdecode Hlen :=
    [BWD] (uint128_const_bytes_make_mutable_from_type_ptr
             tu base bytes value Q Hdecode Hlen).

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
      pose (IH_F :=
        [FWD] (IH (base .[ Tuchar ! 1 ]))).
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

  Lemma uchar_cell_to_any_arrayLR0_1 (base : ptr) value :
    base |-> ucharR 1$m value
    |--
    base |-> arrayLR Tuchar 0 1
      (fun _ : unit => anyR Tuchar 1$m) [()].
  Proof using CU MODd Sigma.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    go using _at_arrayR_cons_B, _at_arrayR_nil_B, primR_anyR_F.
  Qed.

  Definition uchar_cell_to_any_arrayLR0_1_F base value :=
    [FWD] (uchar_cell_to_any_arrayLR0_1 base value).

  Lemma uchar_arrayLR_values_forget_unit
      (base : ptr) start stop values :
    base |-> arrayLR Tuchar start stop
      (fun byte : val => primR Tuchar 1$m byte) values
    |--
    base |-> arrayLR Tuchar start stop
      (fun _ : unit => anyR Tuchar 1$m)
      (map (fun _ : val => tt) values).
  Proof using CU MODd Sigma.
    rewrite array_sliceR_fmap.
    go using primR_anyR_F.
  Qed.

  Definition uchar_arrayLR_values_forget_unit_F
      base start stop values :=
    [FWD] (uchar_arrayLR_values_forget_unit
             base start stop values).

  Lemma seal_nonempty_dst32_prefix_any (base : ptr) :
    base .[ Tuchar ! 16 ] |-> ucharR 1$m 0
    ** base |-> arrayLR Tuchar 17 48
      (fun byte : val => primR Tuchar 1$m byte)
      (replicateN 31 (Vint 0))
    |--
    base .[ Tuchar ! 16 ] |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ()).
  Proof using CU MODd Sigma.
    change (replicateN 32 ())
      with ([()] ++ replicateN 31 ())%list.
    rewrite <-
      (@arrayLR_app_combine_local
         unit Tuchar _ (base .[ Tuchar ! 16 ]) 0 1 32
         (fun _ : unit => anyR Tuchar 1$m)
         [()] (replicateN 31 ())
         ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity)).
    change (replicateN 31 ())
      with (map (fun _ : val => tt) (replicateN 31 (Vint 0))).
    apply bi.sep_mono.
    {
      apply uchar_cell_to_any_arrayLR0_1.
    }
    {
      transitivity
        (base .[ Tuchar ! 16 ] |-> arrayLR Tuchar 1 32
           (fun byte : val => primR Tuchar 1$m byte)
           (replicateN 31 (Vint 0))).
      {
        exact
          (@arrayLR_shift_base_local
             val Tuchar _ base 16 1 32
             (fun byte : val => primR Tuchar 1$m byte)
             (replicateN 31 (Vint 0))).
      }
      {
        apply uchar_arrayLR_values_forget_unit.
      }
    }
  Qed.

  Definition seal_nonempty_dst32_prefix_any_F base :=
    [FWD] (seal_nonempty_dst32_prefix_any base).

  Lemma seal_nonempty_dst32_from_zero_suffix (base : ptr) :
    base .[ Tuchar ! 16 ] |-> ucharR 1$m 0
    ** base |-> arrayLR Tuchar (16 + 1) 64
      (fun byte : val => primR Tuchar 1$m byte)
      (replicateN 47 (Vint 0))
    |--
    base .[ Tuchar ! 16 ] |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ())
    ** base |-> arrayLR Tuchar 48 64
      (fun byte : val => primR Tuchar 1$m byte)
      (replicateN 16 (Vint 0)).
  Proof using CU MODd Sigma.
    replace (16 + 1)%Z with 17%Z by lia.
    change (replicateN 47 (Vint 0))
      with ((replicateN 31 (Vint 0)) ++
            (replicateN 16 (Vint 0)))%list.
    rewrite
      (@arrayLR_app_local
         val Tuchar base 17 48 64
         (fun byte : val => primR Tuchar 1$m byte)
         (replicateN 31 (Vint 0)) (replicateN 16 (Vint 0))
         ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity)).
    rewrite bi.sep_assoc.
    apply bi.sep_mono.
    {
      apply seal_nonempty_dst32_prefix_any.
    }
    {
      go.
    }
  Qed.

  Definition seal_nonempty_dst32_from_zero_suffix_F base :=
    [FWD] (seal_nonempty_dst32_from_zero_suffix base).

  Lemma seal_nonempty_dst32_from_zero_tail (base : ptr) :
    base |-> arrayLR Tuchar 16 64
      (fun byte : val => primR Tuchar 1$m byte)
      (replicateN 48 (Vint 0))
    |--
    base .[ Tuchar ! 16 ] |-> arrayLR Tuchar 0 32
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 32 ())
    ** base |-> arrayLR Tuchar 48 64
      (fun byte : val => primR Tuchar 1$m byte)
      (replicateN 16 (Vint 0)).
  Proof using CU MODd Sigma.
    change (replicateN 48 (Vint 0))
      with ([Vint 0] ++ replicateN 47 (Vint 0))%list.
    rewrite
      (@arrayLR_app_local
         val Tuchar base 16 17 64
         (fun byte : val => primR Tuchar 1$m byte)
         [Vint 0] (replicateN 47 (Vint 0))
         ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity)).
    rewrite array_sliceR_singleton'.
    go using seal_nonempty_dst32_from_zero_suffix_F.
  Qed.

  Definition seal_nonempty_dst32_from_zero_tail_F base :=
    [FWD] (seal_nonempty_dst32_from_zero_tail base).

  Definition wp_eval_uchar_add_16_32_B tu Q :=
    [BWD]
      (monad.proofs.execproofs.mip8.storage_page_cpp_proofs.brick_upstream.wp_eval_uchar_add_int_16_32
         tu Q).

  Lemma zero_block_split_prefix16 (base : ptr) :
    base |-> arrayR Tuchar
      (primR Tuchar 1$m) (replicateN 64 (Vint 0))
    |--
    base |-> arrayLR Tuchar 0 16
      (fun _ : unit => anyR Tuchar 1$m) (replicateN 16 ())
    ** base |-> arrayLR Tuchar 16 64
      (fun byte : val => primR Tuchar 1$m byte)
      (replicateN 48 (Vint 0)).
  Proof using CU MODd Sigma.
    change (replicateN 64 (Vint 0))
      with ((replicateN 16 (Vint 0)) ++
            (replicateN 48 (Vint 0)))%list.
    rewrite arrayR_app__N.
    rewrite _at_sep _at_offsetR.
    change (lengthN (replicateN 16 (Vint 0))) with 16%N.
    go using
      (byte_arrayR_to_arrayLR_F
         base 1 (replicateN 16 (Vint 0)) 16
         ltac:(vm_compute; reflexivity)
         ltac:(lia)),
      (byte_arrayR_at_to_arrayLR_F
         base 1 16 48 (replicateN 48 (Vint 0))
         ltac:(vm_compute; reflexivity)
         ltac:(lia)),
      primR_anyR_F.
  Qed.

  Definition zero_block_split_prefix16_F base :=
    [FWD] (zero_block_split_prefix16 base).

  Lemma bytes32_byte_values_length digest :
    length (bytes32_byte_values digest) = 32%nat.
  Proof.
    reflexivity.
  Qed.

  Lemma bytes64_byte_values_length block :
    length (bytes64_byte_values block) = 64%nat.
  Proof.
    unfold bytes64_byte_values,
      blake3_impl_h_specs.bytes64_byte_values,
      bytes32_byte_values,
      blake3_impl_h_specs.bytes32_byte_values.
    rewrite List.length_app.
    change (length (exec_specs.bytes32_be_values
                      (model.bytes32_to_N (fst block)))) with 32%nat.
    change (length (exec_specs.bytes32_be_values
                      (model.bytes32_to_N (snd block)))) with 32%nat.
    reflexivity.
  Qed.

  Lemma seal_root_bytes_arrayR_to_arrayLR
      (base : ptr) q digest :
    base |-> RawDigestBytesR q digest
    |--
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar q byte)
      (bytes32_byte_values digest).
  Proof using CU MODd Sigma.
    unfold RawDigestBytesR, blake3specs.RawDigestBytesR,
      blake3_impl_h_specs.RawDigestBytesR.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    change (lengthZ (bytes32_byte_values digest)) with 32%Z.
    go.
  Qed.

  Definition seal_root_bytes_arrayR_to_arrayLR_F base q digest :=
    [FWD] (seal_root_bytes_arrayR_to_arrayLR base q digest).

  Lemma seal_root_bytes_arrayLR_to_arrayR
      (base : ptr) q digest :
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar q byte)
      (bytes32_byte_values digest)
    |--
    base |-> RawDigestBytesR q digest.
  Proof using CU MODd Sigma.
    unfold RawDigestBytesR, blake3specs.RawDigestBytesR,
      blake3_impl_h_specs.RawDigestBytesR.
    rewrite array_sliceR.unlock.
    rewrite _at_sep _at_only_provable.
    rewrite _at_offsetR.
    rewrite offset_ptr_sub_0.
    2: {
      apply has_size.
      exact _.
    }
    change (lengthZ (bytes32_byte_values digest)) with 32%Z.
    go.
  Qed.

  Definition seal_root_bytes_arrayLR_to_arrayR_F base q digest :=
    [FWD] (seal_root_bytes_arrayLR_to_arrayR base q digest).

  Definition seal_root_bytes_arrayLR_to_arrayR_B base q digest :=
    [BWD] (seal_root_bytes_arrayLR_to_arrayR base q digest).

  Lemma seal_root_bytes_arrayLR_to_arrayR_unfolded
      (base : ptr) q digest :
    base |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar q byte)
      (exec_specs.bytes32_be_values (model.bytes32_to_N digest))
    |--
    base |-> RawDigestBytesR q digest.
  Proof using CU MODd Sigma.
    exact (seal_root_bytes_arrayLR_to_arrayR base q digest).
  Qed.

  Definition seal_root_bytes_arrayLR_to_arrayR_unfolded_F base q digest :=
    [FWD] (seal_root_bytes_arrayLR_to_arrayR_unfolded base q digest).

  Lemma type_ptrR_nonnull (base : ptr) ty :
    base |-> type_ptrR ty
    |-- base |-> type_ptrR ty ** [| base <> nullptr |].
  Proof using CU MODd Sigma.
    rewrite <- (_at_nonnullR base).
    rewrite <- _at_sep.
    exact (observe_elim_rep nonnullR (type_ptrR ty) base
             (type_ptrR_observe_nonnull ty)).
  Qed.

  Definition type_ptrR_nonnull_F base ty :=
    [FWD] (type_ptrR_nonnull base ty).

  Lemma raw_digest_field_to_bytes32R
      (base : ptr) digest :
    base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
      o_field CU "evmc_bytes32::bytes"
      |-> RawDigestBytesR 1$m digest
    ** base |-> structR "monad::bytes32_t"%cpp_name 1$m
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
      |-> structR "evmc_bytes32"%cpp_name 1$m
    |--
    base |-> exec_specs.bytes32R 1
      (blake3model.bytes32_to_N digest).
  Proof using CU MODd Sigma.
    rewrite /exec_specs.bytes32R
      /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR
      /RawDigestBytesR
      /blake3specs.RawDigestBytesR
      /blake3_impl_h_specs.RawDigestBytesR
      /bytes32_byte_values
      /blake3_impl_h_specs.bytes32_byte_values
      /exec_specs.bytes32_be_values.
    rewrite (only_provable_True _
               (blake3model.bytes32_to_N_range digest)).
    go.
  Qed.

  Definition raw_digest_field_to_bytes32R_B base digest :=
    [BWD] (raw_digest_field_to_bytes32R base digest).

  Lemma bytes32R_zero_to_any_field (base : ptr) :
    base |-> exec_specs.bytes32R 1 0
    |--
    base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
      o_field CU "evmc_bytes32::bytes"
      |-> arrayLR Tuchar 0 32
            (fun _ : unit => anyR Tuchar 1$m)
            (replicateN 32 ())
    ** base |-> structR "monad::bytes32_t"%cpp_name 1$m
    ** base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
      |-> structR "evmc_bytes32"%cpp_name 1$m.
  Proof using CU MODd Sigma.
    rewrite /exec_specs.bytes32R
      /exec_specs.evmc_bytes32_wordR
      /exec_specs.evmc_bytes32_bytesR
      /exec_specs.bytes32_be_values.
    cbn.
    go using
      (byte_arrayR_to_arrayLR_F
         (base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
            o_field CU "evmc_bytes32::bytes")
         1 (replicateN 32 (Vint 0)) 32
         ltac:(vm_compute; reflexivity)
         ltac:(lia)),
      primR_anyR_F.
  Qed.

  Definition bytes32R_zero_to_any_field_F base :=
    [FWD] (bytes32R_zero_to_any_field base).

  Lemma storage_evmc_bytes32R_zero_fold (base : ptr) :
    base ,, o_field CU "evmc_bytes32::bytes"
      |-> arrayR Tuchar (primR Tuchar 1$m) (replicateN 32 (Vint 0))
    ** base |-> structR "evmc_bytes32"%cpp_name 1$m
    |-- base |-> exec_specs.evmc_bytes32R 1.
  Proof using CU MODd Sigma.
    unfold exec_specs.evmc_bytes32R,
      exec_specs.evmc_bytes32_wordR,
      exec_specs.evmc_bytes32_bytesR,
      exec_specs.bytes32_be_values.
    cbn.
    go.
  Qed.

  Definition storage_evmc_bytes32R_zero_fold_B base :=
    [BWD] (storage_evmc_bytes32R_zero_fold base).

  Lemma storage_evmc_bytes32R_zero_unfold (base : ptr) :
    base |-> exec_specs.evmc_bytes32R 1
    |--
    base ,, o_field CU "evmc_bytes32::bytes"
      |-> arrayR Tuchar (primR Tuchar 1$m) (replicateN 32 (Vint 0))
    ** base |-> structR "evmc_bytes32"%cpp_name 1$m.
  Proof using CU MODd Sigma.
    unfold exec_specs.evmc_bytes32R,
      exec_specs.evmc_bytes32_wordR,
      exec_specs.evmc_bytes32_bytesR,
      exec_specs.bytes32_be_values.
    cbn.
    go.
  Qed.

  Definition storage_evmc_bytes32R_zero_unfold_F base :=
    [FWD] (storage_evmc_bytes32R_zero_unfold base).

  Definition seal_block_model
      (slot_bitmap : N) (root : option blake3model.digest)
      : blake3model.bytes64 :=
    model.bytes64_of_bytes
      (blake3model.seal_input_bytes
         (blake3model.bytes16_of_N slot_bitmap) root).

  Definition seal_cv_words_model
      (slot_bitmap : N) (root : option blake3model.digest)
      : model.blake3_cv :=
    model.blake3_compress_in_place_model
      model.blake3_iv_words
      (seal_block_model slot_bitmap root)
      (blake3model.seal_input_len root)
      0
      blake3model.blake3_seal_flags.

  Lemma seal_cv_words_model_length slot_bitmap root :
    length (seal_cv_words_model slot_bitmap root) = 8%nat.
  Proof.
    unfold seal_cv_words_model.
    apply model.blake3_compress_in_place_model_length.
  Qed.

  Lemma seal_cv_words_model_range slot_bitmap root :
    List.Forall model.blake3_word_in_range
      (seal_cv_words_model slot_bitmap root).
  Proof.
    unfold seal_cv_words_model.
    apply model.blake3_compress_in_place_model_range.
  Qed.

  Lemma blake3_seal_model_as_cv_digest slot_bitmap root :
    blake3specs.blake3_seal_model slot_bitmap root =
    model.bytes32_to_N
      (model.blake3_cv_digest
         (seal_cv_words_model slot_bitmap root)).
  Proof.
    unfold seal_cv_words_model, seal_block_model,
      blake3specs.blake3_seal_model,
      blake3specs.blake3_seal_digest,
      blake3model.seal_empty,
      blake3model.seal_nonempty,
      blake3model.seal_compress_digest.
    destruct root; reflexivity.
  Qed.

  Definition blake3_const_key_words_to_bytes_F
      p q words Hlen Hrange :=
    [FWD]
      (byte_bridges.blake3_const_key_words_to_bytes
         p q words Hlen Hrange storage_page_cpp_little_endian).

  Definition blake3_const_key_words_from_bytes_B
      p q words Hlen Hrange :=
    [BWD]
      (byte_bridges.blake3_const_key_words_from_bytes
         p q words Hlen Hrange storage_page_cpp_little_endian).

  Definition blake3_key_words_to_bytes_F
      p q words Hlen Hrange :=
    [FWD]
      (byte_bridges.blake3_key_words_to_bytes
         p q words Hlen Hrange storage_page_cpp_little_endian).

  Definition blake3_key_words_from_bytes_B
      p q words Hlen Hrange :=
    [BWD]
      (byte_bridges.blake3_key_words_from_bytes
         p q words Hlen Hrange storage_page_cpp_little_endian).

  Lemma blake3_key_words_from_bytes_arrayR
      (p : ptr) q words :
    length words = 8%nat ->
    List.Forall model.blake3_word_in_range words ->
    p |-> typed_sliceR Tuint 0 8
    ** p |-> arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar (cQp.mut q) byte)
      (blake3_impl_h_specs.blake3_cv_byte_values words)
    |--
    p |-> arrayR Tuint
      (fun word => uintR (cQp.mut q) (Z.of_N word)) words.
  Proof using CU MODd Sigma.
    intros Hlen Hrange.
    rewrite (byte_bridges.blake3_key_words_from_bytes
               p q words Hlen Hrange storage_page_cpp_little_endian).
    unfold blake3specs.Blake3KeyWordsR,
      blake3_impl_h_specs.Blake3KeyWordsR.
    go.
  Qed.

  Definition blake3_key_words_from_bytes_arrayR_B
      p q words Hlen Hrange :=
    [BWD]
      (blake3_key_words_from_bytes_arrayR
         p q words Hlen Hrange).

  Definition uint32_array8_uninit_to_byte_any_F p :=
    [FWD] (byte_bridges.uint32_array8_uninit_to_byte_any p).

  Definition blake3_key_words_to_uint32_any_F p words Hlen :=
    [FWD]
      (byte_bridges.blake3_key_words_to_uint32_any p words Hlen).

  Definition blake3_key_word_bytes_to_uint32_any_F
      p words Hlen Hrange :=
    [FWD]
      (byte_bridges.blake3_key_word_bytes_to_uint32_any
         p words Hlen Hrange storage_page_cpp_little_endian).

  Definition blake3_seal_nonempty_blockR_B
      base slot_bitmap bitmap_bytes root Hdecode Hlen :=
    [BWD]
      (blake3specs.blake3_seal_nonempty_blockR
         base slot_bitmap bitmap_bytes root Hdecode Hlen).

  Definition blake3_seal_empty_blockR_B
      base slot_bitmap bitmap_bytes Hdecode Hlen :=
    [BWD]
      (blake3specs.blake3_seal_empty_blockR
         base slot_bitmap bitmap_bytes Hdecode Hlen).

  Definition blake3_cv_bytes_field_to_bytes32R_B base words Hlen :=
    [BWD]
      (storage_page_byte_bridges.blake3_cv_bytes_field_to_bytes32R
         base words Hlen).

  Definition blake3_cv_bytes_field_to_bytes32R_any_B :=
    [BWD] storage_page_byte_bridges.blake3_cv_bytes_field_to_bytes32R.

  Lemma blake3_cv_bytes_field_to_bytes32R_return_order
      (base : ptr) words :
    length words = 8%nat ->
    (base ,, o_base CU "monad::bytes32_t" "evmc_bytes32"
       |-> structR "evmc_bytes32"%cpp_name 1$m)
    ** (base |-> structR "monad::bytes32_t"%cpp_name 1$m)
    ** (base ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
        o_field CU "evmc_bytes32::bytes"
        |-> arrayLR Tuchar 0 32
              (fun byte : val => primR Tuchar 1$m byte)
              (blake3_impl_h_specs.blake3_cv_byte_values words))
    |--
    base |-> exec_specs.bytes32R 1
      (model.bytes32_to_N (model.blake3_cv_digest words)).
  Proof using CU MODd Sigma.
    intro Hlen.
    go using
      (blake3_cv_bytes_field_to_bytes32R_B base words Hlen).
  Qed.

  Definition blake3_cv_bytes_field_to_bytes32R_return_order_B
      base words Hlen :=
    [BWD]
      (blake3_cv_bytes_field_to_bytes32R_return_order
         base words Hlen).

  Definition blake3_cv_bytes_field_from_bytes32R_F base words Hlen :=
    [FWD]
      (storage_page_byte_bridges.blake3_cv_bytes_field_from_bytes32R
         base words Hlen).

  Lemma wp_destroy_uchar64_array_cleanup_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    base |-> arrayLR Tuchar 0 64
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN 64 ())
    ** Q
    |-- wp_destroy_val tu QM (Tarray Tuchar 64%N) base Q.
  Proof using CU MODd Sigma.
    intros tu base Q.
    rewrite -destroy.wp_destroy_val_array.
    cbn.
    go.
  Qed.

  Definition wp_destroy_uchar64_array_cleanup_local_B
      tu base Q :=
    [BWD] (wp_destroy_uchar64_array_cleanup_local tu base Q).

  Lemma wp_destroy_uint32x8_array_cleanup_local :
    forall (tu : translation_unit) (base : ptr) (Q : epred),
    base |-> arrayLR Tuint 0 8
      (fun _ : unit => anyR Tuint 1$m)
      (replicateN 8 ())
    ** Q
    |-- wp_destroy_val tu QM (Tarray Tuint 8%N) base Q.
  Proof using CU MODd Sigma.
    intros tu base Q.
    rewrite -destroy.wp_destroy_val_array.
    cbn.
    go.
  Qed.

  Definition wp_destroy_uint32x8_array_cleanup_local_B
      tu base Q :=
    [BWD] (wp_destroy_uint32x8_array_cleanup_local tu base Q).

  #[local] Hint Resolve
    seal_cv_words_model_length
    model.blake3_compress_in_place_model_length : pure.

  #[local] Hint Resolve
    wp_init_implicit_B_local
    wp_init_implicit_char_array_local_B
    wp_init_uchar_array_zero_local_B
    wp.wp_init_initlist_struct_B
    wp_operand_initlist_default_B
    wp_init_default_array_B
    wp_eval_uchar_add_16_32_B
    uninitR_anyR_F
    storage_evmc_bytes32R_zero_fold_B
    primR_anyR_F
    UNSAFE_read_prim_cancel : sl_opacity.

  Lemma prf_storage_blake3_seal :
    verify[source] storage_blake3_seal_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    go.
    rewrite (decode_uint_primR 1$c int_rank.I128 (Z.of_N slot_bitmap)).
    go1.
    match goal with
    | Hlen : length ?l = N.to_nat 16 |- _ =>
        assert (Hslot_bytes_len :
                  length (Z.of_N <$> l) = Z.to_nat 16)
          by (rewrite length_map Hlen; reflexivity);
        assert (Hslot_16_nonneg : (0 <= 16)%Z) by lia;
        go1 using
          (z_byte_arrayR_to_val_arrayLR_F
             slot_bitmap_addr 1$c (Z.of_N <$> l) 16
             Hslot_bytes_len Hslot_16_nonneg),
          zero_block_split_prefix16_F
    end.
    rewrite <- (bi.exist_intro (cQp.const 1)).
    rewrite <- (bi.exist_intro (Z.of_N <$> l)).
    rewrite <- (array_sliceR_fmap 0 16 _ (primR Tuchar 1$c) Vint).
    rewrite <- (array_sliceR_fmap 0 16 _ (primR Tuchar 1$m) Vint).
    go.
    destruct root as [root_digest |].
    {
      rewrite /SealRootArgR /blake3specs.SealRootArgR.
      go using type_ptrR_nonnull_F.
      go using
        seal_nonempty_dst32_from_zero_tail_F,
        seal_root_bytes_arrayR_to_arrayLR_F.
      rewrite <- (bi.exist_intro (cQp.const 1)).
      rewrite <- (bi.exist_intro (Z.of_N <$>
        z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
          (Z.of_N (model.bytes32_to_N root_digest)))).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$c) Vint).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
      rewrite (eq_trans (eq_sym (list_fmap_compose Z.of_N Vint
        (z_to_bytes._Z_to_bytes 32 types.Big types.Unsigned
          (Z.of_N (model.bytes32_to_N root_digest)))))
        (eq_sym (bytes32_be_values_to_Z_to_bytes
          (model.bytes32_to_N root_digest)))).
      go.
      rewrite (blake3_seal_model_as_cv_digest
                 slot_bitmap (Some root_digest)).
      go using
        wp_eval_uchar_add_16_32_B,
        (blake3_const_key_words_to_bytes_F
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        uint32_array8_uninit_to_byte_any_F,
        (blake3_key_words_from_bytes_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_from_bytes_arrayR_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_seal_nonempty_blockR_B
           block_addr slot_bitmap l root_digest
           ltac:(assumption) ltac:(assumption)),
        (blake3_key_words_to_bytes_F
           cv_addr 1 (seal_cv_words_model slot_bitmap (Some root_digest))
           ltac:(apply seal_cv_words_model_length)
           ltac:(apply seal_cv_words_model_range)),
        blake3_cv_bytes_field_to_bytes32R_any_B.
      have ? := _global_nonnull CU "IV"%cpp_name.
      rewrite <- (bi.exist_intro (cQp.const qiv)).
      rewrite <- (bi.exist_intro
        (map (fun b => Z.of_N (fin.to_N b))
          (model.blake3_cv_bytes model.blake3_iv_words))).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar qiv$c) Vint).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_from_bytes_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_from_bytes_arrayR_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_seal_nonempty_blockR_B
           block_addr slot_bitmap l root_digest
           ltac:(assumption) ltac:(assumption)).
      rewrite <- (bi.exist_intro model.blake3_iv_words).
      rewrite <-
        (bi.exist_intro
           (seal_block_model slot_bitmap (Some root_digest))).
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_from_bytes_arrayR_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_seal_nonempty_blockR_B
           block_addr slot_bitmap l root_digest
           ltac:(assumption) ltac:(assumption)).
      go using
        storage_evmc_bytes32R_zero_fold_B,
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_to_bytes_F
           cv_addr 1 (seal_cv_words_model slot_bitmap (Some root_digest))
           ltac:(apply seal_cv_words_model_length)
           ltac:(apply seal_cv_words_model_range)),
        blake3_cv_bytes_field_to_bytes32R_any_B.
      go using storage_evmc_bytes32R_zero_unfold_F.
      rewrite <- (bi.exist_intro (cQp.mut 1)).
      rewrite <- (bi.exist_intro
        (map (fun b => Z.of_N (fin.to_N b))
          (model.blake3_cv_bytes
            (seal_cv_words_model slot_bitmap (Some root_digest))))).
      rewrite <- (bi.exist_intro
                    (A := list unit) (replicateN 32 ())).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
      change (Vint <$> map (fun b => Z.of_N (fin.to_N b))
        (model.blake3_cv_bytes (seal_cv_words_model slot_bitmap (Some root_digest))))
        with (map Vint (map (fun b => Z.of_N (fin.to_N b))
          (model.blake3_cv_bytes (seal_cv_words_model slot_bitmap (Some root_digest))))).
      rewrite map_map.
      change (map (fun b : model.byte => Vint (Z.of_N (fin.to_N b)))
        (model.blake3_cv_bytes (seal_cv_words_model slot_bitmap (Some root_digest))))
        with (blake3_impl_h_specs.blake3_cv_byte_values
          (seal_cv_words_model slot_bitmap (Some root_digest))).
      go using bytes32R_zero_to_any_field_F.
      go using (typed_slice_nonempty_nonnull_B
        (out_addr ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
          o_field CU "evmc_bytes32::bytes") Tuchar 32 ltac:(lia)).
      go using
        bytes32R_zero_to_any_field_F,
        (blake3_key_word_bytes_to_uint32_any_F
           cv_addr (seal_cv_words_model slot_bitmap (Some root_digest))
           ltac:(apply seal_cv_words_model_length)
           ltac:(apply seal_cv_words_model_range)),
        blake3_cv_bytes_field_to_bytes32R_any_B.
      go using
        (uint128_bytes_to_const_primR_from_type_ptr_F
           slot_bitmap_addr l slot_bitmap
           ltac:(assumption) ltac:(assumption)).
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (seal_root_bytes_arrayLR_to_arrayR_F rootp 1$c root_digest),
        blake3_cv_bytes_field_to_bytes32R_any_B,
        (uint128_const_bytes_make_mutable_from_type_ptr_B
           storage_page_cpp.source slot_bitmap_addr l slot_bitmap _
           ltac:(assumption) ltac:(assumption)),
        uchar_arrayR_values_forget_F.
      fold (exec_specs.bytes32_be_values_from
              32 (model.bytes32_to_N root_digest)).
      fold (exec_specs.bytes32_be_values
              (model.bytes32_to_N root_digest)).
      fold (bytes32_byte_values root_digest).
      go using
        (seal_root_bytes_arrayLR_to_arrayR_B rootp 1$c root_digest),
        (uint128_const_bytes_make_mutable_from_type_ptr_B
           storage_page_cpp.source slot_bitmap_addr l slot_bitmap _
           ltac:(assumption) ltac:(assumption)).
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (seal_root_bytes_arrayLR_to_arrayR_F rootp 1$c root_digest),
        (blake3_cv_bytes_field_from_bytes32R_F
           out_addr
           (seal_cv_words_model slot_bitmap (Some root_digest))
           ltac:(apply seal_cv_words_model_length)),
        primR_anyR_F.
      fold (exec_specs.bytes32_be_values_from
              32 (model.bytes32_to_N root_digest)).
      fold (exec_specs.bytes32_be_values
              (model.bytes32_to_N root_digest)).
      fold (bytes32_byte_values root_digest).
      rewrite (seal_root_bytes_arrayLR_to_arrayR_unfolded
                 rootp 1$c root_digest).
      wapply
        (blake3_cv_bytes_field_to_bytes32R_return_order
           out_addr
           (seal_cv_words_model slot_bitmap (Some root_digest))
           ltac:(apply seal_cv_words_model_length)).
      go using
        wp_lval_lval_cast_noop_B,
        wp_lval_xval_cast_noop_B,
        wp_xval_xval_cast_noop_B,
        wp_xval_lval_cast_noop_B,
        exec_specs.bytes32_copy_ctor_spec,
        exec_specs.bytes32_dtor_spec,
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (wp_destroy_uchar64_array_cleanup_local_B
           storage_page_cpp.source block_addr _),
        (wp_destroy_uint32x8_array_cleanup_local_B
           storage_page_cpp.source cv_addr _).
    }
    {
      rewrite /SealRootArgR /blake3specs.SealRootArgR.
      go.
      rewrite (blake3_seal_model_as_cv_digest slot_bitmap None).
      go using
        (blake3_const_key_words_to_bytes_F
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        uint32_array8_uninit_to_byte_any_F,
        (blake3_key_words_from_bytes_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_from_bytes_arrayR_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_seal_empty_blockR_B
           block_addr slot_bitmap l
           ltac:(assumption) ltac:(assumption)),
        (blake3_key_words_to_bytes_F
           cv_addr 1 (seal_cv_words_model slot_bitmap None)
           ltac:(apply seal_cv_words_model_length)
           ltac:(apply seal_cv_words_model_range)),
        blake3_cv_bytes_field_to_bytes32R_any_B.
      have ? := _global_nonnull CU "IV"%cpp_name.
      rewrite <- (bi.exist_intro (cQp.const qiv)).
      rewrite <- (bi.exist_intro
        (map (fun b => Z.of_N (fin.to_N b))
          (model.blake3_cv_bytes model.blake3_iv_words))).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar qiv$c) Vint).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_from_bytes_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_from_bytes_arrayR_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_seal_empty_blockR_B
           block_addr slot_bitmap l
           ltac:(assumption) ltac:(assumption)).
      rewrite <- (bi.exist_intro model.blake3_iv_words).
      rewrite <-
        (bi.exist_intro (seal_block_model slot_bitmap None)).
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_from_bytes_arrayR_B
           cv_addr 1 model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_seal_empty_blockR_B
           block_addr slot_bitmap l
           ltac:(assumption) ltac:(assumption)).
      go using
        storage_evmc_bytes32R_zero_fold_B,
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_key_words_to_bytes_F
           cv_addr 1 (seal_cv_words_model slot_bitmap None)
           ltac:(apply seal_cv_words_model_length)
           ltac:(apply seal_cv_words_model_range)),
        blake3_cv_bytes_field_to_bytes32R_any_B.
      go using storage_evmc_bytes32R_zero_unfold_F.
      rewrite <- (bi.exist_intro (cQp.mut 1)).
      rewrite <- (bi.exist_intro
        (map (fun b => Z.of_N (fin.to_N b))
          (model.blake3_cv_bytes (seal_cv_words_model slot_bitmap None)))).
      rewrite <- (bi.exist_intro
                    (A := list unit) (replicateN 32 ())).
      rewrite <- (array_sliceR_fmap 0 32 _ (primR Tuchar 1$m) Vint).
      change (Vint <$> map (fun b => Z.of_N (fin.to_N b))
        (model.blake3_cv_bytes (seal_cv_words_model slot_bitmap None)))
        with (map Vint (map (fun b => Z.of_N (fin.to_N b))
          (model.blake3_cv_bytes (seal_cv_words_model slot_bitmap None)))).
      rewrite map_map.
      change (map (fun b : model.byte => Vint (Z.of_N (fin.to_N b)))
        (model.blake3_cv_bytes (seal_cv_words_model slot_bitmap None)))
        with (blake3_impl_h_specs.blake3_cv_byte_values
          (seal_cv_words_model slot_bitmap None)).
      go using bytes32R_zero_to_any_field_F.
      go using (typed_slice_nonempty_nonnull_B
        (out_addr ,, o_base CU "monad::bytes32_t" "evmc_bytes32" ,,
          o_field CU "evmc_bytes32::bytes") Tuchar 32 ltac:(lia)).
      go using
        bytes32R_zero_to_any_field_F,
        (blake3_key_word_bytes_to_uint32_any_F
           cv_addr (seal_cv_words_model slot_bitmap None)
           ltac:(apply seal_cv_words_model_length)
           ltac:(apply seal_cv_words_model_range)),
        blake3_cv_bytes_field_to_bytes32R_any_B.
      rewrite <- (bi.exist_intro (A := Qp) 1%Qp).
      rewrite <-
        (bi.exist_intro
           (model.bytes32_to_N
              (model.blake3_cv_digest
                 (seal_cv_words_model slot_bitmap None)))).
      go using
        (uint128_bytes_to_const_primR_from_type_ptr_F
           slot_bitmap_addr l slot_bitmap
           ltac:(assumption) ltac:(assumption)).
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (blake3_cv_bytes_field_from_bytes32R_F
           out_addr
           (seal_cv_words_model slot_bitmap None)
           ltac:(apply seal_cv_words_model_length)),
        blake3_cv_bytes_field_to_bytes32R_any_B,
        (uint128_const_bytes_make_mutable_from_type_ptr_B
           storage_page_cpp.source slot_bitmap_addr l slot_bitmap _
           ltac:(assumption) ltac:(assumption)),
        uchar_arrayR_values_forget_F.
      rewrite <-
        (bi.exist_intro
           (model.bytes32_to_N
              (model.blake3_cv_digest
                 (seal_cv_words_model slot_bitmap None)))).
      go using
        (blake3_const_key_words_from_bytes_B
           (_global "IV") qiv model.blake3_iv_words
           ltac:(vm_compute; reflexivity)
           model.blake3_iv_words_range),
        (uint128_const_bytes_make_mutable_from_type_ptr_B
           storage_page_cpp.source slot_bitmap_addr l slot_bitmap _
           ltac:(assumption) ltac:(assumption)),
        (blake3_cv_bytes_field_from_bytes32R_F
           p
           (seal_cv_words_model slot_bitmap None)
           ltac:(apply seal_cv_words_model_length)),
        blake3_cv_bytes_field_to_bytes32R_any_B.
    }
  Qed.
End with_Sigma.

#[global] Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R
  blake3_impl_h_specs.bytes32_byte_values
  blake3_impl_h_specs.bytes64_byte_values
  blake3_impl_h_specs.RawDigestBytesR
  blake3_impl_h_specs.Blake3BlockR
  blake3_impl_h_specs.Blake3KeyWordsR
  blake3_impl_h_specs.Blake3ConstKeyWordsR
  blake3specs.blake3_seal_digest
  blake3specs.blake3_seal_model.
#[global] Hint Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_bytesR
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R
  blake3_impl_h_specs.bytes32_byte_values
  blake3_impl_h_specs.bytes64_byte_values
  blake3_impl_h_specs.RawDigestBytesR
  blake3_impl_h_specs.Blake3BlockR
  blake3_impl_h_specs.Blake3KeyWordsR
  blake3_impl_h_specs.Blake3ConstKeyWordsR
  blake3specs.blake3_seal_digest
  blake3specs.blake3_seal_model : sl_opacity.
