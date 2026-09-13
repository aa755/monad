(** * MIP-8 storage-page BLAKE3 helper specs

    The reusable BLAKE3 model and upstream library specs live under
    [monad.proofs.libspecs.blake3].  This file contains only the MIP-8
    storage-page helpers from [storage_page.cpp]:

    - [get_leaf_iv], the anonymous-namespace helper that derives the leaf key;
    - [blake3_seal], the anonymous-namespace helper that hashes the bitmap seal.

    Compatibility aliases keep existing MIP-8 proof files readable while the
    actual [blake3.h] and [blake3_impl.h] specs are owned by [libspecs].
*)

Set Default Goal Selector "!".

From Stdlib Require Import List NArith ZArith Lia.
Import ListNotations.

Require Import skylabs.prelude.arith.z_to_bytes.
Require Import skylabs.prelude.fin.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.cpp.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.execproofs.mip8.blake3model.
Require monad.proofs.libspecs.blake3.model.
Require Import monad.proofs.libspecs.blake3.blake3_impl_h_specs.

Import cQp_compat.

Local Open Scope Z_scope.

Definition blake3_hash_many_mode
    (flags flags_start flags_end : Z) : option hash_mode :=
  if (flags =? model.blake3_flag_value model.FlagDeriveKeyMaterial)
     && (flags_start =? 0)
     && (flags_end =? 0)
  then Some leaf_mode
  else
    if (flags =? 0)
       && (flags_start =? model.blake3_flag_value model.FlagChunkStart)
       && (flags_end =? model.blake3_flag_value model.FlagChunkEnd)
    then Some merge_mode
    else None.

Definition blake3_hash_many_outputs
    (mode : hash_mode) (inputs : list bytes64) : list N :=
  blake3_impl_h_specs.blake3_hash_many_outputs_from_params
    (params_for_hash_mode mode) inputs.

Lemma blake3_hash_many_call_params_leaf :
  blake3_impl_h_specs.blake3_hash_many_call_params
    mip8_leaf_iv_words 0 false
    (model.blake3_flag_value model.FlagDeriveKeyMaterial) 0 0 =
  leaf_hash_many_params.
Proof.
  cbn [blake3_impl_h_specs.blake3_hash_many_call_params
       blake3_impl_h_specs.blake3_flags_of_Z
       blake3_impl_h_specs.blake3_flag_is_set
       blake3_impl_h_specs.all_blake3_flags
       model.blake3_flag_value leaf_hash_many_params].
  reflexivity.
Qed.

Lemma blake3_hash_many_call_params_merge :
  blake3_impl_h_specs.blake3_hash_many_call_params
    model.blake3_iv_words 0 false 0
    (model.blake3_flag_value model.FlagChunkStart)
    (model.blake3_flag_value model.FlagChunkEnd) =
  merge_hash_many_params.
Proof.
  cbn [blake3_impl_h_specs.blake3_hash_many_call_params
       blake3_impl_h_specs.blake3_flags_of_Z
       blake3_impl_h_specs.blake3_flag_is_set
       blake3_impl_h_specs.all_blake3_flags
       model.blake3_flag_value merge_hash_many_params].
  reflexivity.
Qed.

Lemma blake3_hash_many_outputs_range mode inputs :
  List.Forall (fun x => (x < 2 ^ 256)%N)
    (blake3_hash_many_outputs mode inputs).
Proof.
  apply blake3_impl_h_specs.blake3_hash_many_outputs_from_params_range.
Qed.

Definition blake3_seal_digest
    (slot_bitmap : N) (root : option digest) : digest :=
  match root with
  | None => seal_empty (bytes16_of_N slot_bitmap)
  | Some root => seal_nonempty (bytes16_of_N slot_bitmap) root
  end.

Definition blake3_seal_model
    (slot_bitmap : N) (root : option digest) : N :=
  bytes32_to_N (blake3_seal_digest slot_bitmap root).

Opaque blake3_seal_digest blake3_seal_model.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition bytes32_ty : type := blake3_impl_h_specs.bytes32_ty.

  Definition blake3_input_ptr_ty_for :=
    blake3_impl_h_specs.blake3_input_ptr_ty_for.

  Definition blake3_input_ptr_ty :=
    blake3_impl_h_specs.blake3_input_ptr_ty.

  Definition blake3_input_ptr_store_ty_for :=
    blake3_impl_h_specs.blake3_input_ptr_store_ty_for.

  Definition blake3_input_ptr_store_ty :=
    blake3_impl_h_specs.blake3_input_ptr_store_ty.

  Definition blake3_input_ptr_value_ty_for :=
    blake3_impl_h_specs.blake3_input_ptr_value_ty_for.

  Definition blake3_input_ptr_value_ty :=
    blake3_impl_h_specs.blake3_input_ptr_value_ty.

  Definition byte_value :=
    blake3_impl_h_specs.byte_value.

  Definition bytes32_byte_values :=
    blake3_impl_h_specs.bytes32_byte_values.

  Definition bytes64_byte_values :=
    blake3_impl_h_specs.bytes64_byte_values.

  Definition RawDigestBytesR :=
    blake3_impl_h_specs.RawDigestBytesR.

  Definition blake3_input_block : Type :=
    blake3_impl_h_specs.blake3_input_block.

  Definition mk_blake3_input_block :=
    blake3_impl_h_specs.Build_blake3_input_block.

  Definition blake3_input_block_ptr :=
    blake3_impl_h_specs.blake3_input_block_ptr.

  Definition blake3_input_block_data :=
    blake3_impl_h_specs.blake3_input_block_data.

  Definition BlockR :=
    blake3_impl_h_specs.BlockR.

  Definition Blake3BlockR :=
    blake3_impl_h_specs.Blake3BlockR.

  Definition Blake3InputBlocksDataR :=
    blake3_impl_h_specs.Blake3InputBlocksDataR.

  Definition Blake3InputBlocksR :=
    blake3_impl_h_specs.Blake3InputBlocksR.

  Definition Blake3OutputWordsR :=
    blake3_impl_h_specs.Blake3OutputWordsR.

  Definition Blake3OutputBytesR :=
    blake3_impl_h_specs.Blake3OutputBytesR.

  Definition blake3_hash_many_outputs_from_params_range :=
    blake3_impl_h_specs.blake3_hash_many_outputs_from_params_range.

  Definition Blake3KeyWordsR :=
    blake3_impl_h_specs.Blake3KeyWordsR.

  Definition Blake3ConstKeyWordsR :=
    blake3_impl_h_specs.Blake3ConstKeyWordsR.

  Definition storage_get_leaf_iv_lambda_name : name :=
    Nscoped
      (Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
         (Nfunction function_qualifiers.N "get_leaf_iv" nil))
      (Nanon 0).

  Definition storage_get_leaf_iv_lambda_call_name : name :=
    Nscoped storage_get_leaf_iv_lambda_name
      (Nop function_qualifiers.Nc OOCall nil).

  Definition storage_get_leaf_iv_static_cached_name : name :=
    Nscoped
      (Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
         (Nfunction function_qualifiers.N "get_leaf_iv" nil))
      (Nid "cached").

  Definition storage_leaf_domain_key_name : name :=
    Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
      (Nid "DOMAIN_KEY").

  Definition storage_get_leaf_iv_static_iv_name : name :=
    Nscoped storage_get_leaf_iv_lambda_call_name (Nid "iv").

  Definition storage_leaf_domain_key_values : list val :=
    blake3_impl_h_specs.byte_values mip8_leaf_domain_bytes.

  Definition StorageLeafDomainKeyR (q : Qp) : Rep :=
    arrayLR Tuchar 0 32
      (fun byte : val => primR Tuchar (cQp.const q) byte)
      storage_leaf_domain_key_values.

  Definition StorageLeafIvCacheR
      (ready : bool) (qcache : cQp.t) (qleaf : Qp) : mpred :=
    static_initialized
      storage_get_leaf_iv_static_cached_name
      (if ready then initialized else uninitialized)
    ** if ready then
         _global storage_get_leaf_iv_static_cached_name
           |-> primR
                 (Tptr Tuint) qcache
                 (Vptr (_global storage_get_leaf_iv_static_iv_name))
         ** _global storage_get_leaf_iv_static_iv_name
              |-> Blake3ConstKeyWordsR qleaf mip8_leaf_iv_words
       else
         static_initialized storage_get_leaf_iv_static_iv_name
           uninitialized.

  Definition storage_leaf_iv_cache_qcache_after
      (ready : bool) (qcache : cQp.t) : cQp.t :=
    if ready then qcache else cQp.const 1%Qp.

  Definition storage_leaf_iv_cache_qleaf_after
      (ready : bool) (qleaf : Qp) : Qp :=
    if ready then qleaf else (1 / 2)%Qp.

  Definition StorageLeafDomainKeyMaybeR
      (need_init : bool) (qdomain : Qp) : mpred :=
    if need_init
    then
      _global storage_leaf_domain_key_name
        |-> StorageLeafDomainKeyR qdomain
    else emp.

  Definition StorageLeafIvInitInputsR
      (need_init : bool) (qiv qdomain : Qp) : mpred :=
    if need_init
    then
      type_ptr (Tarray Tuint 8) (_global "IV")
      ** _global "IV" |-> Blake3ConstKeyWordsR qiv model.blake3_iv_words
      ** _global storage_leaf_domain_key_name
           |-> StorageLeafDomainKeyR qdomain
    else emp.

  #[global] Arguments StorageLeafIvCacheR : simpl never.
  #[global] Arguments StorageLeafDomainKeyMaybeR : simpl never.
  #[global] Arguments StorageLeafIvInitInputsR : simpl never.
  #[global] Hint Opaque
    StorageLeafIvCacheR
    StorageLeafDomainKeyMaybeR
    StorageLeafIvInitInputsR : sl_opacity.

  Definition storage_blake3_hash_many_spec : mpred :=
    blake3_impl_h_specs.blake3_hash_many_spec.

  Definition SealRootArgR (rootp : ptr) (root : option digest) : mpred :=
    match root with
    | None => [| rootp = nullptr |]
    | Some root =>
        rootp |-> type_ptrR (Tarray Tuchar 32)
        ** rootp |-> RawDigestBytesR 1$c root
    end.

  Definition blake3_seal_block_bytesR
      (base : ptr) (slot_bitmap : N) (bitmap_bytes : list N)
      (root : option digest) : mpred :=
    match root with
    | Some root =>
        base |-> arrayLR Tuchar 0 16
          (fun byte : val => primR Tuchar 1$m byte)
          (map Vint (Z.of_N <$> bitmap_bytes))
        ** base .[ Tuchar ! 16 ] |-> arrayLR Tuchar 0 32
          (fun byte : val => primR Tuchar 1$m byte)
          (bytes32_byte_values root)
        ** base |-> arrayLR Tuchar 48 64
          (fun byte : val => primR Tuchar 1$m byte)
          (replicateN 16 (Vint 0))
    | None =>
        base |-> arrayLR Tuchar 0 16
          (fun byte : val => primR Tuchar 1$m byte)
          (map Vint (Z.of_N <$> bitmap_bytes))
        ** base |-> arrayLR Tuchar 16 64
          (fun byte : val => primR Tuchar 1$m byte)
          (replicateN 48 (Vint 0))
    end.

  Definition byte_in_range (byte : N) : Prop := (byte < 256)%N.

  Lemma bytes16_le_bytes_length word :
    length (bytes16_le_bytes word) = 16%nat.
  Proof using.
    reflexivity.
  Qed.

  Lemma bytes32_be_bytes_length word :
    length (bytes32_be_bytes word) = 32%nat.
  Proof using.
    reflexivity.
  Qed.

  Lemma byte_value_byte_of_N word :
    blake3_impl_h_specs.byte_value (model.byte_of_N word) =
    Vint (Z.of_N (word mod 256)).
  Proof using.
    unfold blake3_impl_h_specs.byte_value, model.byte_of_N.
    change (model.pow2N 8) with 256%N.
    rewrite (fin.to_of_N' (model.pow2N_pos 8) (word mod 256)).
    {
      reflexivity.
    }
    {
      apply N.mod_upper_bound.
      discriminate.
    }
  Qed.

  Lemma get_byte_of_N (word : N) (idx : nat) :
    Z.to_N (builtins._get_byte (Z.of_N word) idx) =
    N.land (N.shiftr word (8 * N.of_nat idx)) 255.
  Proof using.
    revert word.
    induction idx as [| idx IH]; intro word.
    {
      rewrite _get_byte_0_small_id.
      rewrite Z2N.inj_mod.
      2,3: lia.
      rewrite N2Z.id.
      rewrite N.shiftr_0_r.
      change 255%N with (N.ones 8).
      rewrite N.land_ones.
      reflexivity.
    }
    {
      rewrite builtins._get_byte_S_idx.
      rewrite Z_of_N_shiftr.
      2: {
        lia.
      }
      rewrite (IH (N.shiftr word 8)).
      rewrite N.shiftr_shiftr.
      change (Z.to_N 8) with 8%N.
      replace (8 + 8 * N.of_nat idx)%N
        with (8 * N.of_nat (S idx))%N by lia.
      reflexivity.
    }
  Qed.

  Lemma get_bytes_shiftr_seq word start len :
    map (fun idx =>
           Z.to_N
             (builtins._get_byte (Z.of_N (N.shiftr word 8)) idx))
      (seq start len) =
    map (fun idx =>
           Z.to_N (builtins._get_byte (Z.of_N word) idx))
      (seq (S start) len).
  Proof using.
    revert start.
    induction len as [| len IH]; intro start.
    {
      reflexivity.
    }
    {
      cbn [seq List.map].
      rewrite !get_byte_of_N.
      rewrite N.shiftr_shiftr.
      change (Z.to_N 8) with 8%N.
      replace (8 + 8 * N.of_nat start)%N
        with (8 * N.of_nat (S start))%N by lia.
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma get_bytes_shiftr_seq_comp word start len :
    map
      (Z.to_N ∘ builtins._get_byte (Z.of_N (N.shiftr word 8)))
      (seq start len) =
    map
      (Z.to_N ∘ builtins._get_byte (Z.of_N word))
      (seq (S start) len).
  Proof using.
    apply get_bytes_shiftr_seq.
  Qed.

  Lemma byte_values_bytes_of_N_le len word :
    blake3_impl_h_specs.byte_values
      (model.bytes_of_N_le len word) =
    map (fun byte => Vint (Z.of_N byte))
      (_Z_to_bytes len Little Unsigned (Z.of_N word)).
  Proof using.
    rewrite _Z_to_bytes_eq.
    unfold _Z_to_bytes_def, _Z_to_bytes_le,
      _Z_to_bytes_unsigned_le, _Z_to_bytes_unsigned_le'.
    revert word.
    induction len as [| len IH]; intro word.
    {
      reflexivity.
    }
    {
      cbn [seq List.map model.bytes_of_N_le blake3_impl_h_specs.byte_values].
      rewrite byte_value_byte_of_N.
      cbn [Basics.compose].
      rewrite get_byte_of_N.
      rewrite N.shiftr_0_r.
      change 255%N with (N.ones 8).
      rewrite N.land_ones.
      change
        (map blake3_impl_h_specs.byte_value
           (model.bytes_of_N_le len (word ≫ 8)))
        with
        (blake3_impl_h_specs.byte_values
           (model.bytes_of_N_le len (word ≫ 8))).
      rewrite (IH (N.shiftr word 8)).
      f_equal.
      rewrite <- (get_bytes_shiftr_seq_comp word 0 len).
      reflexivity.
    }
  Qed.

  Lemma byte_values_bytes16_of_N_from_decodes_uint
      `{MODd : storage_page_cpp.source ⊧ CU}
      slot_bitmap bitmap_bytes :
    decodes_uint bitmap_bytes (Z.of_N slot_bitmap) ->
    length bitmap_bytes = N.to_nat 16 ->
    map Vint (Z.of_N <$> bitmap_bytes) =
    blake3_impl_h_specs.byte_values
      (bytes16_le_bytes (bytes16_of_N slot_bitmap)).
  Proof using.
    intros Hdecode Hlength.
    unfold decodes_uint in Hdecode.
    rewrite (genv_byte_order_tu storage_page_cpp.source CU MODd) in Hdecode.
    cbn [byte_order] in Hdecode.
    destruct Hdecode as [Hbytes Hdecode].
    rewrite byte_values_bytes_of_N_le.
    unfold bytes16_le_bytes, bytes16_of_N.
    rewrite (fin.to_of_N' (model.pow2N_pos 128)
               (slot_bitmap mod model.pow2N 128)).
    2: {
      apply N.mod_upper_bound.
      pose proof (model.pow2N_pos 128).
      lia.
    }
    change (model.pow2N 128) with (2 ^ 128)%N.
    assert (Hbyte_bounds : List.Forall byte_in_range bitmap_bytes).
    {
      clear Hlength Hdecode.
      induction Hbytes as [| byte rest Hbyte _ IH].
      {
        constructor.
      }
      {
        constructor.
        {
          rewrite has_int_type' in Hbyte.
          destruct Hbyte as [[z [Hz Hbound]] | [raw [Hraw Hraw_ty]]].
          {
            inversion Hz.
            subst z.
            unfold bitsize.bound, bitsize.min_val,
              bitsize.max_val in Hbound.
            cbn in Hbound.
            unfold byte_in_range.
            lia.
          }
          {
            discriminate Hraw.
          }
        }
        exact IH.
      }
    }
    assert (Hroundtrip :
              _Z_to_bytes 16 Little Unsigned (Z.of_N slot_bitmap) =
              bitmap_bytes).
    {
      rewrite <- Hdecode.
      apply _Z_to_from_bytes_roundtrip.
      {
        exact Hbyte_bounds.
      }
      {
        exact (eq_sym Hlength).
      }
    }
    pose proof (_Z_from_bytes_Unsigned_bound Little bitmap_bytes) as Hbound.
    rewrite Hdecode in Hbound.
    rewrite Hlength in Hbound.
    change (256 ^ Z.of_nat (N.to_nat 16))%Z with (2 ^ 128)%Z in Hbound.
    rewrite N.mod_small.
    2: {
      apply (proj2 (N2Z.inj_lt slot_bitmap (2 ^ 128))).
      change (Z.of_N (2 ^ 128)%N) with (2 ^ 128)%Z.
      lia.
    }
    rewrite Hroundtrip.
    unfold blake3_impl_h_specs.byte_values,
      blake3_impl_h_specs.byte_value.
    rewrite map_map.
    reflexivity.
  Qed.

  Local Transparent exec_specs.bytes32_be_values
    exec_specs.bytes32_be_values_from
    model.N_of_bytes_be.

  Lemma byte_values_bytes_of_N_be len word :
    blake3_impl_h_specs.byte_values
      (model.bytes_of_N_be len word) =
    bytes32_be_values_from len word.
  Proof using.
    revert word.
    induction len as [| len IH]; intro word.
    {
      reflexivity.
    }
    {
      cbn [model.bytes_of_N_be bytes32_be_values_from
           blake3_impl_h_specs.byte_values List.map].
      rewrite byte_value_byte_of_N.
      change 255%N with (N.ones 8).
      rewrite N.land_ones.
      f_equal.
      exact (IH word).
    }
  Qed.

  Lemma byte_values_bytes32_be_bytes root :
    bytes32_byte_values root =
    blake3_impl_h_specs.byte_values (model.bytes32_be_bytes root).
  Proof using.
    unfold bytes32_byte_values, blake3_impl_h_specs.bytes32_byte_values,
      model.bytes32_be_bytes, bytes32_be_values.
    rewrite byte_values_bytes_of_N_be.
    reflexivity.
  Qed.

  Lemma bytes32_byte_values_length root :
    length (bytes32_byte_values root) = 32%nat.
  Proof using.
    unfold bytes32_byte_values, blake3_impl_h_specs.bytes32_byte_values,
      bytes32_be_values.
    reflexivity.
  Qed.

  Lemma fin_to_N_bytes_bound (bytes : list model.byte) :
    List.Forall byte_in_range (map fin.to_N bytes).
  Proof using.
    induction bytes as [| b bytes IH].
    {
      constructor.
    }
    {
      constructor.
      {
        unfold byte_in_range.
        change 256%N with (model.pow2N 8).
        apply fin.to_N_lt.
      }
      exact IH.
    }
  Qed.

  Lemma bytes32_to_N_bytes32_of_be_bytes_full
      (bytes : list model.byte) :
    length bytes = 32%nat ->
    model.bytes32_to_N (model.bytes32_of_be_bytes bytes) =
    model.N_of_bytes_be bytes.
  Proof using.
    intro Hlen.
    unfold model.bytes32_of_be_bytes, model.bytes32_of_N,
      model.bytes32_to_N, model.N_of_bytes_be, model.pad_bytes.
    rewrite firstn_app.
    rewrite firstn_all2.
    2: {
      lia.
    }
    replace (32 - length bytes)%nat with 0%nat by lia.
    change (firstn 0 (repeat model.zero_byte 32))
      with (@nil model.byte).
    rewrite app_nil_r.
    rewrite (fin.to_of_N' (model.pow2N_pos 256)
               (Z.to_N
                  (_Z_from_bytes types.Big types.Unsigned
                     (map fin.to_N bytes)) mod model.pow2N 256)).
    2: {
      apply N.mod_upper_bound.
      pose proof (model.pow2N_pos 256).
      lia.
    }
    rewrite N.mod_small.
    {
      reflexivity.
    }
    {
      pose proof
        (_Z_from_bytes_Unsigned_bound types.Big (map fin.to_N bytes))
        as Hbound.
      rewrite map_length in Hbound.
      rewrite Hlen in Hbound.
      change (model.pow2N 256) with (2 ^ 256)%N.
      change (2 ^ 256)%N with (Z.to_N (2 ^ 256)).
      assert
        (Hbytes_nonneg :
           (0 <=
            _Z_from_bytes types.Big types.Unsigned
              (map fin.to_N bytes))%Z)
        by lia.
      assert (Hpow_nonneg : (0 <= 2 ^ 256)%Z) by lia.
      apply
        (proj1
           (Z2N.inj_lt
              (_Z_from_bytes types.Big types.Unsigned
                 (map fin.to_N bytes))
              (2 ^ 256)%Z
              Hbytes_nonneg
              Hpow_nonneg)).
      {
        change (Z.of_N (2 ^ 256)) with (2 ^ 256)%Z.
        change (256 ^ Z.of_nat 32)%Z with (2 ^ 256)%Z in Hbound.
        lia.
      }
    }
  Qed.

  Lemma bytes32_be_values_to_Z_to_bytes (word : N) :
    exec_specs.bytes32_be_values word =
    map (fun byte => Vint (Z.of_N byte))
      (_Z_to_bytes 32 types.Big types.Unsigned (Z.of_N word)).
  Proof using.
    unfold exec_specs.bytes32_be_values,
      exec_specs.bytes32_be_values_from.
    rewrite _Z_to_bytes_eq.
    unfold _Z_to_bytes_def, _Z_to_bytes_le,
      _Z_to_bytes_unsigned_le, _Z_to_bytes_unsigned_le'.
    cbn [seq List.map rev List.app Basics.compose].
    repeat rewrite get_byte_of_N.
    reflexivity.
  Qed.

  Lemma byte_values_bytes32_of_be_bytes_full
      (bytes : list model.byte) :
    length bytes = 32%nat ->
    blake3_impl_h_specs.byte_values bytes =
    blake3_impl_h_specs.bytes32_byte_values
      (model.bytes32_of_be_bytes bytes).
  Proof using.
    intro Hlen.
    unfold bytes32_byte_values, blake3_impl_h_specs.bytes32_byte_values.
    rewrite bytes32_be_values_to_Z_to_bytes.
    rewrite (bytes32_to_N_bytes32_of_be_bytes_full bytes Hlen).
    unfold model.N_of_bytes_be.
    rewrite Z2N.id.
    2: {
      pose proof
        (_Z_from_bytes_Unsigned_bound types.Big (map fin.to_N bytes)).
      lia.
    }
    rewrite (_Z_to_from_bytes_roundtrip
               (map fin.to_N bytes) types.Unsigned types.Big 32).
    2: {
      apply fin_to_N_bytes_bound.
    }
    2: {
      rewrite map_length.
      exact (eq_sym Hlen).
    }
    unfold blake3_impl_h_specs.byte_values,
      blake3_impl_h_specs.byte_value.
    rewrite map_map.
    reflexivity.
  Qed.

  Local Opaque exec_specs.bytes32_be_values
    exec_specs.bytes32_be_values_from
    model.N_of_bytes_be.

  Lemma byte_values_app xs ys :
    blake3_impl_h_specs.byte_values (xs ++ ys) =
    blake3_impl_h_specs.byte_values xs ++
    blake3_impl_h_specs.byte_values ys.
  Proof using.
    unfold blake3_impl_h_specs.byte_values.
    rewrite map_app.
    reflexivity.
  Qed.

  Lemma byte_values_zero_repeat len :
    blake3_impl_h_specs.byte_values (repeat model.zero_byte len) =
    repeat (Vint 0) len.
  Proof using.
    induction len as [| len IH].
    {
      reflexivity.
    }
    {
      cbn [repeat blake3_impl_h_specs.byte_values List.map replicateN].
      unfold model.zero_byte.
      rewrite byte_value_byte_of_N.
      change (0 mod 256)%N with 0%N.
      change
        (map blake3_impl_h_specs.byte_value
           (repeat (model.byte_of_N 0) len))
        with
        (blake3_impl_h_specs.byte_values
           (repeat model.zero_byte len)).
      rewrite IH.
      reflexivity.
    }
  Qed.

  Lemma pad_bytes_length len bytes :
    (length bytes <= len)%nat ->
    length (model.pad_bytes len bytes) = len.
  Proof using.
    intro Hlen.
    unfold model.pad_bytes.
    rewrite firstn_length.
    rewrite app_length.
    rewrite repeat_length.
    lia.
  Qed.

  Lemma bytes64_byte_values_of_bytes bytes :
    (length bytes <= 64)%nat ->
    blake3_impl_h_specs.bytes64_byte_values
      (model.bytes64_of_bytes bytes) =
    blake3_impl_h_specs.byte_values
      (model.pad_bytes 64 bytes).
  Proof using.
    intro Hlen.
    unfold blake3_impl_h_specs.bytes64_byte_values,
      model.bytes64_of_bytes.
    set (padded := model.pad_bytes 64 bytes).
    assert (Hpadded : length padded = 64%nat).
    {
      subst padded.
      apply pad_bytes_length.
      exact Hlen.
    }
    cbn [fst snd].
    rewrite <- (byte_values_bytes32_of_be_bytes_full (firstn 32 padded)).
    2: {
      rewrite length_firstn.
      lia.
    }
    rewrite <- (byte_values_bytes32_of_be_bytes_full
                  (firstn 32 (skipn 32 padded))).
    2: {
      rewrite firstn_all2.
      2: {
        rewrite length_skipn.
        lia.
      }
      rewrite length_skipn.
      lia.
    }
    rewrite <- byte_values_app.
    replace (firstn 32 padded ++ firstn 32 (skipn 32 padded))
      with padded.
    {
      reflexivity.
    }
    assert (Htail :
              firstn 32 (skipn 32 padded) = skipn 32 padded).
    {
      apply firstn_all2.
      {
        rewrite length_skipn.
        lia.
      }
    }
    rewrite Htail.
    symmetry.
    apply firstn_skipn.
  Qed.

  Lemma byte_values_bytes64_of_bytes_seal_input
      slot_bitmap root :
    blake3_impl_h_specs.bytes64_byte_values
      (model.bytes64_of_bytes
         (seal_input_bytes (bytes16_of_N slot_bitmap) root)) =
    match root with
    | Some root =>
        blake3_impl_h_specs.byte_values
          (bytes16_le_bytes (bytes16_of_N slot_bitmap)) ++
        bytes32_byte_values root ++
        replicateN 16 (Vint 0)
    | None =>
        blake3_impl_h_specs.byte_values
          (bytes16_le_bytes (bytes16_of_N slot_bitmap)) ++
        replicateN 48 (Vint 0)
    end.
  Proof using.
    destruct root as [root |].
    {
      rewrite bytes64_byte_values_of_bytes.
      2: {
        unfold seal_input_bytes.
        rewrite app_length.
        change (length (bytes16_le_bytes (bytes16_of_N slot_bitmap)))
          with 16%nat.
        change (length (bytes32_be_bytes root)) with 32%nat.
        change (length (model.bytes32_be_bytes root)) with 32%nat.
        lia.
      }
      unfold model.pad_bytes, seal_input_bytes.
      change (length (bytes16_le_bytes (bytes16_of_N slot_bitmap)))
        with 16%nat.
      change (length (bytes32_be_bytes root)) with 32%nat.
      rewrite firstn_app.
      rewrite firstn_all2.
      2: {
        rewrite app_length.
        change (length (bytes16_le_bytes (bytes16_of_N slot_bitmap)))
          with 16%nat.
        change (length (bytes32_be_bytes root)) with 32%nat.
        change (length (model.bytes32_be_bytes root)) with 32%nat.
        lia.
      }
      replace
        (64 -
           length
             (bytes16_le_bytes (bytes16_of_N slot_bitmap) ++
            bytes32_be_bytes root))%nat
        with 16%nat.
      2: {
        rewrite app_length.
        change (length (bytes16_le_bytes (bytes16_of_N slot_bitmap)))
          with 16%nat.
        change (length (bytes32_be_bytes root)) with 32%nat.
        change (length (model.bytes32_be_bytes root)) with 32%nat.
        lia.
      }
      change (firstn 16 (repeat model.zero_byte 64))
        with (repeat model.zero_byte 16).
      rewrite byte_values_app.
      rewrite byte_values_app.
      rewrite <- byte_values_bytes32_be_bytes.
      rewrite byte_values_zero_repeat.
      change (repeat (Vint 0) 16) with (replicateN 16 (Vint 0)).
      reflexivity.
    }
    {
      rewrite bytes64_byte_values_of_bytes.
      2: {
        unfold seal_input_bytes.
        rewrite bytes16_le_bytes_length.
        lia.
      }
      unfold model.pad_bytes, seal_input_bytes.
      change (length (bytes16_le_bytes (bytes16_of_N slot_bitmap)))
        with 16%nat.
      rewrite firstn_app.
      rewrite firstn_all2.
      2: {
        rewrite bytes16_le_bytes_length.
        lia.
      }
      replace
        (64 - length (bytes16_le_bytes (bytes16_of_N slot_bitmap)))%nat
        with 48%nat.
      2: {
        rewrite bytes16_le_bytes_length.
        lia.
      }
      change (firstn 48 (repeat model.zero_byte 64))
        with (repeat model.zero_byte 48).
      rewrite byte_values_app.
      rewrite byte_values_zero_repeat.
      change (repeat (Vint 0) 48) with (replicateN 48 (Vint 0)).
      reflexivity.
    }
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
  Proof using CU Sigma.
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
    assert (Hlen : lengthZ (xs ++ ys) = k - i).
    {
      change (Z.of_N (lengthN (xs ++ ys)) = k - i).
      rewrite lengthN_app.
      rewrite N2Z.inj_add.
      change (Z.of_N (lengthN xs)) with (lengthZ xs).
      change (Z.of_N (lengthN ys)) with (lengthZ ys).
      rewrite Hxs Hys.
      lia.
    }
    go.
  Qed.

  Lemma byte_arrayLR_to_arrayR
      (base : ptr) bytes :
    length bytes = 64%nat ->
    base |-> arrayLR Tuchar 0 64
      (fun byte : val => primR Tuchar 1$m byte) bytes
    |--
    base |-> arrayR Tuchar
      (fun byte : val => primR Tuchar 1$m byte) bytes.
  Proof using CU Sigma.
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

  Lemma arrayLR_shift_base_local {A : Type}
      (ty : type) (Hty : @HasSize CU ty)
      (base : ptr) start i j (f : A -> Rep) xs :
    base |-> arrayLR ty (start + i) (start + j) f xs
    |--
    base .[ ty ! start ] |-> arrayLR ty i j f xs.
  Proof using CU Sigma.
    rewrite !array_sliceR.unlock.
    rewrite !_at_sep !_at_only_provable.
    repeat rewrite _at_offsetR.
    rewrite o_sub_sub.
    normalize_ptrs.
    go.
  Qed.

  Lemma arrayLR_unshift_base_local {A : Type}
      (ty : type) (Hty : @HasSize CU ty)
      (base : ptr) start i j (f : A -> Rep) xs :
    base .[ ty ! start ] |-> arrayLR ty i j f xs
    |--
    base |-> arrayLR ty (start + i) (start + j) f xs.
  Proof using CU Sigma.
    rewrite !array_sliceR.unlock.
    rewrite !_at_sep !_at_only_provable.
    repeat rewrite _at_offsetR.
    rewrite o_sub_sub.
    normalize_ptrs.
    go.
  Qed.

  Lemma blake3_seal_blockR
      `{MODd : storage_page_cpp.source ⊧ CU} :
    forall (base : ptr) slot_bitmap bitmap_bytes root,
      decodes_uint bitmap_bytes (Z.of_N slot_bitmap) ->
      length bitmap_bytes = N.to_nat 16 ->
      blake3_seal_block_bytesR base slot_bitmap bitmap_bytes root
      |--
      base |-> Blake3BlockR 1
        (model.bytes64_of_bytes
           (seal_input_bytes
              (bytes16_of_N slot_bitmap) root)).
  Proof using CU Sigma.
    intros base slot_bitmap bitmap_bytes [root |] Hdecode Hlength.
    {
      unfold blake3_seal_block_bytesR.
      unfold Blake3BlockR, blake3_impl_h_specs.Blake3BlockR,
        blake3_impl_h_specs.BlockR.
      rewrite byte_values_bytes64_of_bytes_seal_input.
      rewrite <-
        (byte_values_bytes16_of_N_from_decodes_uint
           slot_bitmap bitmap_bytes Hdecode Hlength).
      change (lengthZ (map Vint (Z.of_N <$> bitmap_bytes))) with 16%Z.
      change (lengthZ (bytes32_byte_values root)) with 32%Z.
      assert
        (Hbitmap_len :
           lengthZ (map Vint (Z.of_N <$> bitmap_bytes)) = 16 - 0).
      {
        rewrite lengthZ_correct.
        rewrite map_length.
        rewrite map_length.
        rewrite Hlength.
        reflexivity.
      }
      assert
        (Hroot_len : lengthZ (bytes32_byte_values root) = 48 - 16).
      {
        rewrite lengthZ_correct.
        rewrite bytes32_byte_values_length.
        reflexivity.
      }
      assert
        (Hprefix_len :
           lengthZ
             (map Vint (Z.of_N <$> bitmap_bytes) ++
              bytes32_byte_values root) = 48 - 0).
      {
        rewrite lengthZ_correct.
        rewrite app_length.
        rewrite map_length.
        rewrite map_length.
        rewrite Hlength.
        rewrite bytes32_byte_values_length.
        reflexivity.
      }
      assert
        (Hzero16_len :
           lengthZ (replicateN 16 (Vint 0)) = 64 - 48).
      {
        vm_compute.
        reflexivity.
      }
      rewrite
        (@arrayLR_unshift_base_local
           val Tuchar _ base 16 0 32
           (fun byte : val => primR Tuchar 1$m byte)
           (bytes32_byte_values root)).
      change (16 + 0)%Z with 16%Z.
      change (16 + 32)%Z with 48%Z.
      rewrite bi.sep_assoc.
      rewrite
        (@arrayLR_app_combine_local
           val Tuchar _ base 0 16 48
           (fun byte : val => primR Tuchar 1$m byte)
           (map Vint (Z.of_N <$> bitmap_bytes))
           (bytes32_byte_values root)
           Hbitmap_len
           Hroot_len).
      rewrite
        (@arrayLR_app_combine_local
           val Tuchar _ base 0 48 64
           (fun byte : val => primR Tuchar 1$m byte)
           (map Vint (Z.of_N <$> bitmap_bytes) ++
            bytes32_byte_values root)
           (replicateN 16 (Vint 0))
           Hprefix_len
           Hzero16_len).
      rewrite app_assoc.
      apply byte_arrayLR_to_arrayR.
      rewrite app_length.
      rewrite app_length.
      rewrite map_length.
      rewrite map_length.
      rewrite Hlength.
      rewrite bytes32_byte_values_length.
      change (length (replicateN 16 (Vint 0))) with 16%nat.
      reflexivity.
    }
    {
      unfold blake3_seal_block_bytesR.
      unfold Blake3BlockR, blake3_impl_h_specs.Blake3BlockR,
        blake3_impl_h_specs.BlockR.
      rewrite byte_values_bytes64_of_bytes_seal_input.
      rewrite <-
        (byte_values_bytes16_of_N_from_decodes_uint
           slot_bitmap bitmap_bytes Hdecode Hlength).
      assert
        (Hbitmap_len :
           lengthZ (map Vint (Z.of_N <$> bitmap_bytes)) = 16 - 0).
      {
        rewrite lengthZ_correct.
        rewrite map_length.
        rewrite map_length.
        rewrite Hlength.
        reflexivity.
      }
      assert
        (Hzero48_len :
           lengthZ (replicateN 48 (Vint 0)) = 64 - 16).
      {
        vm_compute.
        reflexivity.
      }
      rewrite
        (@arrayLR_app_combine_local
           val Tuchar _ base 0 16 64
           (fun byte : val => primR Tuchar 1$m byte)
           (map Vint (Z.of_N <$> bitmap_bytes))
           (replicateN 48 (Vint 0))
           Hbitmap_len
           Hzero48_len).
      apply byte_arrayLR_to_arrayR.
      rewrite app_length.
      rewrite map_length.
      rewrite map_length.
      rewrite Hlength.
      change (length (replicateN 48 (Vint 0))) with 48%nat.
      reflexivity.
    }
  Qed.

  Lemma blake3_seal_nonempty_blockR
      `{MODd : storage_page_cpp.source ⊧ CU} :
    forall (base : ptr) slot_bitmap bitmap_bytes root,
      decodes_uint bitmap_bytes (Z.of_N slot_bitmap) ->
      length bitmap_bytes = N.to_nat 16 ->
      base |-> arrayLR Tuchar 0 16
        (fun byte : val => primR Tuchar 1$m byte)
        (map Vint (Z.of_N <$> bitmap_bytes))
      ** base .[ Tuchar ! 16 ] |-> arrayLR Tuchar 0 32
        (fun byte : val => primR Tuchar 1$m byte)
        (bytes32_byte_values root)
      ** base |-> arrayLR Tuchar 48 64
        (fun byte : val => primR Tuchar 1$m byte)
        (replicateN 16 (Vint 0))
      |--
      base |-> Blake3BlockR 1
        (model.bytes64_of_bytes
           (seal_input_bytes
              (bytes16_of_N slot_bitmap) (Some root))).
  Proof using.
    intros base slot_bitmap bitmap_bytes root Hdecode Hlength.
    exact
      (blake3_seal_blockR
         base slot_bitmap bitmap_bytes (Some root) Hdecode Hlength).
  Qed.

  Lemma blake3_seal_empty_blockR
      `{MODd : storage_page_cpp.source ⊧ CU} :
    forall (base : ptr) slot_bitmap bitmap_bytes,
      decodes_uint bitmap_bytes (Z.of_N slot_bitmap) ->
      length bitmap_bytes = N.to_nat 16 ->
      base |-> arrayLR Tuchar 0 16
        (fun byte : val => primR Tuchar 1$m byte)
        (map Vint (Z.of_N <$> bitmap_bytes))
      ** base |-> arrayLR Tuchar 16 64
        (fun byte : val => primR Tuchar 1$m byte)
        (replicateN 48 (Vint 0))
      |--
      base |-> Blake3BlockR 1
        (model.bytes64_of_bytes
           (seal_input_bytes
              (bytes16_of_N slot_bitmap) None)).
  Proof using.
    intros base slot_bitmap bitmap_bytes Hdecode Hlength.
    exact
      (blake3_seal_blockR
         base slot_bitmap bitmap_bytes None Hdecode Hlength).
  Qed.
End with_Sigma.
