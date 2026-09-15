Set Default Goal Selector "!".

(*
  Shared setup for the split [storage_page.cpp] proofs.

  Each proof of a concrete C++ function lives in its own file in this
  directory.  This file contains only the imports and proof-plumbing that are
  common to those files: the generated AST, the MIP-8 specs, the standard C++
  proof hints, and a small observation lemma for the storage-page length
  invariant.
*)

Require Export skylabs.auto.cpp.tactics4.
Require Export skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.hints.array.
Require Export monad.asts.storage_page_cpp.
Require Export monad.proofs.misc.
Require Export monad.proofs.execproofs.mip8.commitment.
Require Export monad.proofs.allspecs.
Require Export monad.proofs.execproofs.mip8.storage_page_specs.
Require Export monad.proofs.execproofs.mip8.storage_page_cpp_proofs.brick_upstream.
Require Export monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_byte_bridges.

Import linearity.

Set Warnings "+sl-impossible-patterns".

(* Reading primitive cells is a common generated-AST pattern.  This hint lets
   automation consume the read while leaving value-level arithmetic obligations
   explicit in the few places where they matter. *)
#[export] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

(* Keep the 64-step pair-bitmap model out of generic C++ proof search.  The
   dedicated [storage_page_t::pair_bitmap] proof unfolds it only through small
   pure lemmas tied to the loop invariant. *)
Opaque pair_bitmap_word pair_bitmap_prefix.
#[export] Hint Opaque pair_bitmap_word pair_bitmap_prefix : sl_opacity.

(* The page-commit specs mention the high-level Gallina root model.  Individual
   proofs use named bridge lemmas when they need to connect that model to a
   helper result, so the C++ automation should not reduce the whole root
   computation while opening a spec. *)
Opaque root page_slots_model page_subtree_root_model.
#[export] Hint Opaque
  root page_slots_model page_subtree_root_model : sl_opacity.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Lemma observeStoragePageLength (p : ptr) q page :
    Observe [| length page = page_slot_count |]
      (p |-> StoragePageR q page).
  Proof using.
    apply observe_intro; [exact _ |].
    unfold StoragePageR.
    rewrite !_at_sep.
    go.
  Qed.

  Definition observeStoragePageLength_F p q page :=
    @observe_fwd _ _ _ (observeStoragePageLength p q page).

  Lemma observeStoragePageRange (p : ptr) q page :
    Observe [| List.Forall (fun word => (word < 2 ^ 256)%N) page |]
      (p |-> StoragePageR q page).
  Proof using.
    apply observe_intro; [exact _ |].
    unfold StoragePageR.
    rewrite !_at_sep.
    go.
  Qed.

  Definition observeStoragePageRange_F p q page :=
    @observe_fwd _ _ _ (observeStoragePageRange p q page).

  Definition wp_init_implicit_B_local := [BWD] wp_init_implicit.

  Definition wp_init_implicit_char_array_local_B
      tu rho base len Q :=
    [BWD]
      (monad.proofs.libspecs.brick_upstream.wp_init_implicit_init_array
         tu rho len Tuchar base (Tarray Tuchar len) (Vint 0) Q
         ltac:(reflexivity) ltac:(reflexivity)).

  Definition wp_init_uchar_array_zero_local_B
      (tu : translation_unit) (rho : region) (base : ptr)
      (len : N) (Q : FreeTemps.t -> mpred) :=
    [BWD]
      (@hints.wp.wp_init_initlist_prim_array_implicit
         _ _ Sigma CU tu rho base (Tarray Tuchar len) Q
         Tuchar len (Vint 0)
         ltac:(reflexivity) ltac:(exact _) ltac:(reflexivity)
         ltac:(reflexivity)).

  Section with_storage_module.
    Context {MODd : storage_page_cpp.source ⊧ CU}.

    Lemma storage_page_cpp_little_endian :
      genv_byte_order CU = Little.
    Proof using MODd.
      rewrite (genv_byte_order_tu storage_page_cpp.source CU MODd).
      reflexivity.
    Qed.

    Remove Hints constRemB : sl_opacity.

    Lemma storage_page_values_iteratorR_const :
      const.CONST2 storage_page_cpp.source
        storage_page_values_iterator_name
        (boost_small_vector.SmallVectorIteratorR
           storage_page_values_iterator_ty bytes32_ty).
    Proof using CU MODd Sigma.
      const.prove.
      unfold boost_small_vector.SmallVectorIteratorR,
        boost_small_vector.small_vector_iterator_ptr_field,
        storage_page_values_iterator_ty.
      go.
    Qed.

    Definition storage_page_values_iteratorR_const_C :=
      [CANCEL] storage_page_values_iteratorR_const.

    #[local] Hint Resolve
      storage_page_values_iteratorR_const_C : sl_opacity.

    Lemma storage_raw_digest_bytesR_const digest :
      const.CONST const_specs.bytes32_const_tu (Tarray Tuchar 32)
        (fun q => blake3specs.RawDigestBytesR q digest).
    Proof using CU MODd Sigma.
      unfold blake3specs.RawDigestBytesR,
        blake3_impl_h_specs.RawDigestBytesR,
        blake3_impl_h_specs.bytes32_byte_values.
      exact
        (const_specs.bytes32_byte_array_const
           (blake3model.bytes32_to_N digest)).
    Qed.

    Definition storage_raw_digest_bytesR_const_C :=
      [CANCEL] storage_raw_digest_bytesR_const.

    #[local] Hint Resolve constRemB : sl_opacity.

    Lemma storage_evmc_bytes32R_zero_fold (p : ptr) :
      p ,, o_field CU "evmc_bytes32::bytes"
        |-> arrayR Tuchar (primR Tuchar 1$m)
              (replicateN 32 (Vint 0))
      ** p |-> structR "evmc_bytes32"%cpp_name 1$m
      |-- p |-> exec_specs.evmc_bytes32R 1.
    Proof using CU MODd Sigma.
      Transparent exec_specs.evmc_bytes32R
        exec_specs.evmc_bytes32_bytesR
        exec_specs.evmc_bytes32_wordR
        exec_specs.bytes32_be_values.
      unfold exec_specs.evmc_bytes32R,
        exec_specs.evmc_bytes32_wordR.
      unfold exec_specs.evmc_bytes32_bytesR,
        exec_specs.bytes32_be_values.
      cbn.
      go.
    Qed.

    Definition storage_evmc_bytes32R_zero_fold_B p :=
      [BWD] (storage_evmc_bytes32R_zero_fold p).

    Lemma storage_evmc_bytes32R_zero_unfold (p : ptr) :
      p |-> exec_specs.evmc_bytes32R 1
      |--
      p ,, o_field CU "evmc_bytes32::bytes"
        |-> arrayR Tuchar (primR Tuchar 1$m)
              (replicateN 32 (Vint 0))
      ** p |-> structR "evmc_bytes32"%cpp_name 1$m.
    Proof using CU MODd Sigma.
      Transparent exec_specs.evmc_bytes32R
        exec_specs.evmc_bytes32_bytesR
        exec_specs.evmc_bytes32_wordR
        exec_specs.bytes32_be_values.
      unfold exec_specs.evmc_bytes32R,
        exec_specs.evmc_bytes32_wordR.
      unfold exec_specs.evmc_bytes32_bytesR,
        exec_specs.bytes32_be_values.
      cbn.
      go.
    Qed.

    Definition storage_evmc_bytes32R_zero_unfold_F p :=
      [FWD] (storage_evmc_bytes32R_zero_unfold p).

    #[local] Instance storage_bytes32_zero_sem_const :
      SemConst_wp_initialize
        evmc_specs.bytes32_ty
        evmc_specs.bytes32_default_init_expr
        storage_page_cpp.source
        evmc_specs.bytes32_default_ctor_spec
        emp 0%N (exec_specs.bytes32R 1).
    Proof using CU MODd Sigma.
      constructor.
      unfold evmc_specs.bytes32_default_init_expr,
        evmc_specs.bytes32_ty,
        evmc_specs.bytes32_default_ctor_name.
      go using evmc_specs.bytes32_default_ctor_spec.
    Qed.

    (* Generated initialization of local [bytes32_t[N]] arrays is just the
       generic aggregate-array rule applied to the element constructor
       [bytes32_t()].  The semantic-constant instance above
       supplies the proof for one element; the upstream array hint lifts it to
       the whole array. *)
    Definition wp_init_bytes32_array_zero_local_B
        rho base len Q Hlen :=
      @array.aggregate_array_const_C thread_info _Σ Sigma CU
        storage_page_cpp.source rho storage_page_cpp.source
        evmc_specs.bytes32_default_ctor_name
        evmc_specs.bytes32_ty len Q base
        evmc_specs.bytes32_default_ctor_spec
        N 0%N (exec_specs.bytes32R 1)
        []
        ltac:(change (HasSize evmc_specs.bytes32_ty); exact _)
        Hlen
        storage_bytes32_zero_sem_const
        (ModuleLe_refl storage_page_cpp.source).

  End with_storage_module.

  (* Local [evmc::bytes32[N]] temporaries are ordinary arrays of values whose
     destructor has no semantic effect in the MIP-8 model.  The generated
     cleanup path otherwise expands into [N] separate calls to the byte-string
     destructor; this bridge packages that framework plumbing as one step while
     still requiring ownership of exactly the array length being destroyed. *)
  Definition wp_destroy_bytes32_array_local_B
      tu base len values Q Hlen :=
    [BWD] (evmc_specs.wp_destroy_bytes32_array
             tu base len values Q Hlen).

  Section with_output_layout.
    Context {MODd : storage_page_cpp.source ⊧ CU}.

  Definition blake3_output_words_to_bytes_F base q outputs :=
    [FWD] (storage_page_byte_bridges.blake3_output_words_to_bytes
             base q outputs).

  Definition blake3_output_bytes_to_words_F base q outputs Hrange :=
    [FWD] (storage_page_byte_bridges.blake3_output_bytes_to_words
             base q outputs Hrange).

  Lemma blake3_output_bytes_prefix_tail_to_words
      (base : ptr) (prefix tail : list N) (offset : nat) :
    List.Forall (fun word => (word < 2 ^ 256)%N) prefix ->
    offset = length prefix ->
    base |-> storage_page_byte_bridges.evmc_bytes32_array_spineR 1$m offset
    ** base |-> blake3specs.Blake3OutputBytesR 1 prefix
    ** base .[ blake3specs.bytes32_ty ! Z.of_nat offset ]
       |-> blake3specs.Blake3OutputWordsR 1 tail
    |--
    base |-> blake3specs.Blake3OutputWordsR 1 (prefix ++ tail).
  Proof using CU MODd Sigma.
    intros Hrange Hoffset.
    subst offset.
    go using (blake3_output_bytes_to_words_F base 1 prefix Hrange).
    go using arrayR_app_build_C.
  Qed.

  Definition blake3_output_bytes_prefix_tail_to_words_F
      base prefix tail offset Hrange Hoffset :=
    [FWD] (blake3_output_bytes_prefix_tail_to_words
             base prefix tail offset Hrange Hoffset).

  Lemma blake3_output_words_split_prefix_to_bytes
      (base : ptr) (values : list N) (n : nat) :
    (n <= length values)%nat ->
    base |-> blake3specs.Blake3OutputWordsR 1 values |--
    base |-> storage_page_byte_bridges.evmc_bytes32_array_spineR 1$m n
    ** base |-> blake3specs.Blake3OutputBytesR 1 (firstn n values)
    ** base .[ blake3specs.bytes32_ty ! Z.of_nat n ]
       |-> blake3specs.Blake3OutputWordsR 1 (skipn n values).
  Proof using CU MODd Sigma.
    intro Hle.
    change (base |-> blake3specs.Blake3OutputWordsR 1 values)
      with
      (base |-> arrayR blake3specs.bytes32_ty
         (exec_specs.bytes32R 1) values).
    etrans.
    {
      apply _at_mono.
      apply arrayR_split.
      exact Hle.
    }
    change
      (base |-> arrayR blake3specs.bytes32_ty
         (exec_specs.bytes32R 1) (firstn n values)
       ** base .[ blake3specs.bytes32_ty ! Z.of_nat n ]
          |-> arrayR blake3specs.bytes32_ty
                (exec_specs.bytes32R 1) (skipn n values))
      with
      (base |-> blake3specs.Blake3OutputWordsR 1 (firstn n values)
       ** base .[ blake3specs.bytes32_ty ! Z.of_nat n ]
          |-> blake3specs.Blake3OutputWordsR 1 (skipn n values)).
    go using
      (blake3_output_words_to_bytes_F base 1 (firstn n values)).
    rewrite length_firstn Nat.min_l; [go | exact Hle].
  Qed.

  Definition blake3_output_words_split_prefix_to_bytes_F
      base values n Hle :=
    [FWD] (blake3_output_words_split_prefix_to_bytes
             base values n Hle).

  End with_output_layout.

  (* Generated default-initialization for local two-dimensional primitive arrays
     such as [uint8_t blocks[32][64]] currently stops before exposing the
     per-row resources.  The proof only needs ownership of those bytes, not
     their initial contents, so this bridge exposes each row through [anyR].
     The later [memcpy] calls are responsible for giving the live prefix
     meaningful byte contents.  Upstream
     [array_sliceR_hints.default_initialize_array_fusion_B] covers arrays whose
     element type is primitive or pointer-like; it deliberately does not match
     when the element type itself is [Tarray Tuchar cols]. *)
  Definition default_initialize_array_of_arrays_uninit_local_B
      tu base rows cols Q :=
    [BWD] (brick_upstream.default_initialize_array_of_arrays_uninit
             tu base rows cols Q).

  Lemma uint128_land_valid lhs rhs :
    has_type_prop (Vn lhs) Tuint128_t ->
    has_type_prop (Vn rhs) Tuint128_t ->
    has_type_prop (Vn (N.land lhs rhs)) Tuint128_t.
  Proof using CU.
    intros Hlhs _.
    change (has_type_prop
              (Vint (Z.of_N (N.land lhs rhs)))
              (Tnum int_rank.I128 Unsigned)).
    apply has_int_type.
    change (bitsize.bound bitsize.W128 Unsigned
              (Z.of_N (N.land lhs rhs))).
    change (has_type_prop (Vint (Z.of_N lhs))
              (Tnum int_rank.I128 Unsigned)) in Hlhs.
    apply has_int_type in Hlhs.
    change (bitsize.bound bitsize.W128 Unsigned
              (Z.of_N lhs)) in Hlhs.
    destruct Hlhs as [_ Hlhs].
    split.
    { cbn. lia. }
    transitivity (Z.of_N lhs).
    {
      apply N2Z.inj_le.
      apply N.land_le_l.
    }
    lia.
  Qed.

  Lemma uint128_zero_valid :
    has_type_prop (Vint 0) Tuint128_t.
  Proof using CU.
    change (has_type_prop (Vint 0) (Tnum int_rank.I128 Unsigned)).
    apply has_int_type.
    unfold bitsize.bound.
    cbn.
    split; lia.
  Qed.

  Lemma wp_operand_int_zero
      (tu : translation_unit) (rho : region)
      (Q : val -> FreeTemps.t -> mpred) :
    Q (Vint 0) FreeTemps.id
    |-- wp_operand tu rho (Eint 0 Tint) Q.
  Proof using CU Sigma.
    rewrite <-
      (@wp_operand_int thread_info _Σ Sigma CU tu rho 0 Tint Q).
    go.
  Qed.

End with_Sigma.

#[global] Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R.

#[global] Hint Opaque
  exec_specs.bytes32_be_values_from
  exec_specs.bytes32_be_values
  exec_specs.evmc_bytes32_wordR
  exec_specs.bytes32R
  exec_specs.evmc_bytes32R : sl_opacity.

#[global] Hint Resolve uint128_land_valid uint128_zero_valid : core.
#[global] Hint Resolve uint128_land_valid uint128_zero_valid : sl_opacity.
#[global] Hint Resolve
  storage_raw_digest_bytesR_const_C storage_page_values_iteratorR_const_C
  : sl_opacity.
