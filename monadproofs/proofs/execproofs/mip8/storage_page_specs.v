Set Default Goal Selector "!".

(*
  Purpose of this file
  --------------------

  This is the execution-specification layer for the MIP 8 storage-page code in
  [category/execution/monad/db/storage_page.cpp].  It connects two documents:

  - "MIP 8 - Page-ified Storage State" supplies the concrete page layout:
    128 slots per page, page keys, slot offsets, compact page encoding, and the
    page commitment API.

  - "Merkle Commitments via Induced Subtrees" supplies the abstract commitment
    argument: a bitmap fixes a minimal induced tree, and sealing the bitmap plus
    values gives root uniqueness under collision-free concrete hash calls.

  The file has three layers.  First it defines pure Coq models for the storage
  page operations.  Then it states specs for library calls used by the generated
  C++ AST.  Finally it states the top-level specs that [storage_page_proofs.v]
  checks where the current dependency specs are strong enough.
*)

From Stdlib Require Import List NArith ZArith Lia.
Import ListNotations.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.prelude.fin.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.boost.small_vector_specs.
Require Import monad.proofs.libspecs.byte_string_specs.
Require Import monad.proofs.libspecs.evmc_specs.
Require Import monad.proofs.libspecs.outcome_specs.
Require Import monad.proofs.libspecs.outcome_status_code_specs.
Require Import monad.proofs.libspecs.result_model.
Require Import monad.proofs.libspecs.rlp_decode_error_model.
Require Import monad.proofs.libspecs.rlp_decode_error_specs.
Require Import monad.proofs.libspecs.rlp_specs.
Require Import monad.proofs.libspecs.stdlib_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require monad.proofs.libspecs.blake3.model.
Require Import monad.proofs.execproofs.mip8.blake3model.
Require Import monad.proofs.execproofs.mip8.blake3specs.
Require Import monad.proofs.execproofs.mip8.commitment.
Require Import monad.proofs.execproofs.mip8.storage_page_encoding.
Require Import monad.proofs.execproofs.mip8.storage_page_indexed_encoding.

Import cQp_compat.

#[local] Open Scope N_scope.

(** The storage-page proof layer uses [N] for bytes32 words because
    [bytes32R] is already phrased that way.  The commitment model itself works
    over optional concrete [slot_word] values.  These definitions are the
    page-local bridge between those two views. *)
Definition page_slot_value_model (word : N) : option slot_word :=
  if N.eq_dec word 0 then None else Some (bytes32_of_N word).

Fixpoint page_slots_model (page : list N) : slot_values :=
  match page with
  | [] => []
  | slot :: rest => page_slot_value_model slot :: page_slots_model rest
  end.

(** The production iterator scans the low half first, then the high half.
    The library bit scan returns 64 on zero, so the all-zero result is 128. *)
Definition lowest_offset_model (bitmap : N) : N :=
  let lo := N.land bitmap (N.ones 64) in
  if N.eqb lo 0
  then (64 + countr_zero64 (N.shiftr bitmap 64))%N
  else countr_zero64 lo.
Opaque lowest_offset_model.
#[global] Hint Opaque lowest_offset_model : sl_opacity typeclass_instances.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  cpp.spec "monad::lowest_offset(uint128_t)"
    from storage_page_cpp.source as lowest_offset_spec with (
      \arg{bitmap : N} "bitmap" (Vn bitmap)
      \post [Vn (lowest_offset_model bitmap)] emp).

  (* The generated AST uses fully elaborated C++ names.  These aliases keep the
     specs readable and isolate the proof from repeated type spelling noise. *)
  Definition bytes32_ty : type := "monad::bytes32_t"%cpp_type.
  Definition storage_page_ty : type := "monad::storage_page_t"%cpp_type.

  Definition byte_string_view_ty : type :=
    Tnamed
      (Ninst
         (Nscoped (Nglobal (Nid "std")) (Nid "basic_string_view"))
         [Atype Tuchar;
          Atype
            (Tnamed
               (Ninst
                  (Nscoped (Nglobal (Nid "evmc")) (Nid "byte_traits"))
                  [Atype Tuchar]))]).

  Definition result_storage_page_name : name :=
    outcome_result_name
      storage_page_ty outcome_error_ty
      (outcome_status_code_throw_policy_ty
         storage_page_ty outcome_error_ty).

  Definition result_storage_page_ty : type :=
    Tnamed result_storage_page_name.

  #[global] Instance storage_page_outcome_object_value :
    OutcomeObjectValue storage_page_ty := {}.

  (* The [get_leaf_iv] helper uses a captureless function-local lambda to
     initialize a static IV cache.  The closure object is empty and used at one
     call site only, so the proof should execute the generated [operator()]
     body rather than assume a semantic spec for the lambda. *)
  #[global] Instance storage_get_leaf_iv_lambda_call_inline :
    ShouldInlineFunction
      blake3specs.storage_get_leaf_iv_lambda_call_name := {}.
  #[global] Instance storage_get_leaf_iv_lambda_dtor_inline :
    ShouldInlineFunction
      (Nscoped blake3specs.storage_get_leaf_iv_lambda_name Ndtor) := {}.

  Definition compute_page_key_name : name :=
    Nscoped (Nglobal (Nid "monad"))
      (Nfunction function_qualifiers.N "compute_page_key"
         [Tref (Qconst bytes32_ty)]).

  Definition compute_slot_offset_name : name :=
    Nscoped (Nglobal (Nid "monad"))
      (Nfunction function_qualifiers.N "compute_slot_offset"
         [Tref (Qconst bytes32_ty)]).

  Definition compute_slot_key_name : name :=
    Nscoped (Nglobal (Nid "monad"))
      (Nfunction function_qualifiers.N "compute_slot_key"
         [Tref (Qconst bytes32_ty); Tuchar]).

  Definition page_commit_name : name :=
    Nscoped (Nglobal (Nid "monad"))
      (Nfunction function_qualifiers.N "page_commit"
         [Tref (Qconst storage_page_ty)]).

  Definition encode_storage_page_name : name :=
    Nscoped (Nglobal (Nid "monad"))
      (Nfunction function_qualifiers.N "encode_storage_page"
         [Tref (Qconst storage_page_ty)]).

  Definition decode_storage_page_name : name :=
    Nscoped (Nglobal (Nid "monad"))
      (Nfunction function_qualifiers.N "decode_storage_page"
         [byte_string_view_ty]).

  Definition storage_page_slots : offset :=
    _field "monad::storage_page_t::slots".

  Definition storage_page_bitmap_field : offset :=
    _field "monad::storage_page_t::bitmap_".

  Definition storage_page_values_field : offset :=
    _field "monad::storage_page_t::values_".

  Definition storage_page_values_ty : type :=
    "boost::container::small_vector<monad::bytes32_t, 4>"%cpp_type.

  Definition storage_page_values_name : name :=
    "boost::container::small_vector<monad::bytes32_t, 4ul, void, void>".

  Definition storage_page_values_small_vector_base_ty : type :=
    "boost::container::small_vector_base<monad::bytes32_t, void, void>"%cpp_type.

  Definition storage_page_values_small_vector_base_name : name :=
    "boost::container::small_vector_base<monad::bytes32_t, void, void>".

  Definition storage_page_values_vector_ty : type :=
    "boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>"%cpp_type.

  Definition storage_page_values_vector_name : name :=
    "boost::container::vector<monad::bytes32_t, boost::container::small_vector_allocator<monad::bytes32_t, boost::container::new_allocator<void>, void>, void>".

  Definition storage_page_values_iterator_name : name :=
    Ninst
      (Nscoped
         (Nscoped (Nglobal (Nid "boost")) (Nid "container"))
         (Nid "vec_iterator"))
      [Atype (Tptr bytes32_ty); Avalue (Eint 0%Z Tbool)].

  Definition storage_page_values_iterator_ty : type :=
    Tnamed storage_page_values_iterator_name.

  Definition storage_page_values_const_iterator_name : name :=
    Ninst
      (Nscoped
         (Nscoped (Nglobal (Nid "boost")) (Nid "container"))
         (Nid "vec_iterator"))
      [Atype (Tptr bytes32_ty); Avalue (Eint 1%Z Tbool)].

  Definition storage_page_values_const_iterator_ty : type :=
    Tnamed storage_page_values_const_iterator_name.

  Definition storage_page_values_allocator_name : name :=
    Ninst
      (Nscoped
         (Nscoped (Nglobal (Nid "boost")) (Nid "container"))
         (Nid "small_vector_allocator"))
      [Atype bytes32_ty;
       Atype
         (Tnamed
            (Ninst
               (Nscoped
                  (Nscoped (Nglobal (Nid "boost")) (Nid "container"))
                  (Nid "new_allocator"))
               [Atype Tvoid]));
       Atype Tvoid].

  Definition storage_page_values_holder_tag_name : name :=
    Ninst
      (Nscoped
         (Nscoped (Nglobal (Nid "boost")) (Nid "move_detail"))
         (Nid "integral_constant"))
      [Atype Tuint; Avalue (Eint 1%Z Tuint)].

  Definition storage_page_values_holder_name : name :=
    Ninst
      (Nscoped
         (Nscoped (Nglobal (Nid "boost")) (Nid "container"))
         (Nid "vector_alloc_holder"))
      [Atype (Tnamed storage_page_values_allocator_name);
       Atype Tulong;
       Atype (Tnamed storage_page_values_holder_tag_name)].

  Definition storage_page_values_holder_ty : type :=
    Tnamed storage_page_values_holder_name.

  Definition storage_page_values_vector_field : offset :=
    storage_page_values_field ,,
    o_base CU storage_page_values_name
      storage_page_values_small_vector_base_name ,,
    o_base CU storage_page_values_small_vector_base_name
      storage_page_values_vector_name.

  Definition scratch_array_ty : type :=
    Tarray bytes32_ty 64%N.

  Definition scratch_arg_ty : type :=
    Tdecay_type scratch_array_ty (Tptr bytes32_ty).

  Definition scratch_ref_arg_ty : type :=
    Tref scratch_array_ty.

  Definition merge_index_array_ty : type :=
    Tarray Tuchar 32%N.

  Definition merge_index_arg_ty : type :=
    Tptr Tuchar.

  Definition merge_const_index_array_ty : type :=
    Tarray (Qconst Tuchar) 32%N.

  Definition merge_const_index_arg_ty : type :=
    Tptr (Qconst Tuchar).

  Definition merge_block_row_ty : type :=
    Tarray Tuchar 64%N.

  Definition merge_blocks_array_ty : type :=
    Tarray merge_block_row_ty 32%N.

  Definition merge_blocks_arg_ty : type :=
    Tptr merge_block_row_ty.

  Definition merge_input_ptr_ty : type :=
    Tptr Tuchar.

  Definition merge_inputs_array_ty : type :=
    Tarray merge_input_ptr_ty 32%N.

  Definition merge_inputs_arg_ty : type :=
    Tptr merge_input_ptr_ty.

  Definition merge_const_inputs_arg_ty : type :=
    Tptr (Qconst merge_input_ptr_ty).

  Definition merge_output_array_ty : type :=
    Tarray bytes32_ty 32%N.

  Definition merge_output_arg_ty : type :=
    Tptr bytes32_ty.

  Definition merge_const_output_array_ty : type :=
    Tarray (Qconst bytes32_ty) 32%N.

  Definition merge_const_output_arg_ty : type :=
    Tptr (Qconst bytes32_ty).

  Definition init_leaves_name : name :=
    Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
      (Nfunction function_qualifiers.N "init_leaves"
        [Tref (Qconst storage_page_ty); Tulong; scratch_ref_arg_ty]).

  Definition merge_at_level_name : name :=
    Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
      (Nfunction function_qualifiers.N "merge_at_level"
        [Tuchar; Tulong; scratch_ref_arg_ty]).

  Definition compute_nonempty_subtree_root_name : name :=
    Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
      (Nfunction function_qualifiers.N "compute_nonempty_subtree_root"
        [Tref (Qconst storage_page_ty); Tulong]).

  Definition storage_SLOTS_name : name :=
    Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "storage_page_t"))
      (Nid "SLOTS").

  Definition storage_SLOT_SIZE_name : name :=
    Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "storage_page_t"))
      (Nid "SLOT_SIZE").

  Definition storage_NUM_PAIRS_name : name :=
    Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
      (Nid "NUM_PAIRS").

  Definition storage_page_NUM_PAIRS_name : name :=
    Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "storage_page_t"))
      (Nid "NUM_PAIRS").

  Definition storage_page_update_slot
      (offset : nat) (value : N) (page : list N) : list N :=
    firstn offset page ++ value :: skipn (S offset) page.

  Definition storage_page_set_model
      (offset : nat) (value : N) (page : list N) : list N :=
    storage_page_update_slot offset value page.

  Definition list_insert_at {A : Type}
      (offset : nat) (value : A) (values : list A) : list A :=
    firstn offset values ++ value :: skipn offset values.

  Definition list_erase_at {A : Type}
      (offset : nat) (values : list A) : list A :=
    firstn offset values ++ skipn (S offset) values.

  Definition list_replace_at {A : Type}
      (offset : nat) (value : A) (values : list A) : list A :=
    firstn offset values ++ value :: skipn (S offset) values.

  Definition ScratchR (q : Qp) (scratch : list N) : Rep :=
    arrayR bytes32_ty (bytes32R q) scratch
    ** [| length scratch = page_pair_count |].

  (* Storage keys are split exactly as in MIP 8: high bits choose the page, low
     7 bits choose the slot within the 128-slot page. *)
  Definition page_index_model (key : N) : N :=
    N.shiftr key 7.

  Definition slot_offset_model (key : N) : N :=
    N.land key 127.

  Definition slot_key_model (page_key slot_offset : N) : N :=
    N.lor
      (N.modulo (N.shiftl page_key 7) (2 ^ 256))
      (N.land slot_offset 127).

  (* The C++ implementation of [compute_slot_offset] reads the last byte and
     masks it.  This lemma connects that byte-level operation to the abstract
     low-7-bit model. *)
  Lemma slot_offset_low_byte key :
    N.land (N.land key 255) 127 = slot_offset_model key.
  Proof.
    unfold slot_offset_model.
    rewrite <- N.land_assoc.
    change (N.land 255 127) with 127.
    reflexivity.
  Qed.

  Lemma slot_offset_mask_small offset :
    (0 <= offset < 128)%Z ->
    N.land (Z.to_N offset) 127 = Z.to_N offset.
  Proof.
    intros Hoffset.
    change 127 with (N.ones 7).
    rewrite N.land_ones.
    apply N.mod_small.
    lia.
  Qed.

  (* The following bit-level functions model implementation helpers used by the
     page commitment code.  They are not cryptographic; they describe how the
     implementation finds live slots and live pairs before hashing. *)
  Fixpoint slot_bitmap_from (index : nat) (page : list N) : N :=
    match page with
    | [] => 0
    | slot :: rest =>
        (if N.eq_dec slot 0 then 0 else 2 ^ N.of_nat index)
        + slot_bitmap_from (S index) rest
    end.

  Definition slot_bitmap_word (page : list N) : N :=
    slot_bitmap_from 0 page.

  Definition storage_page_slot_present (slot : N) : bool :=
    negb (N.eqb slot 0).

  Definition storage_page_has_slot (page : list N) (offset : nat) : bool :=
    storage_page_slot_present (nth offset page 0).

  Definition storage_page_dense_values (page : list N) : list N :=
    List.filter storage_page_slot_present page.

  Definition storage_page_size (page : list N) : nat :=
    length (storage_page_dense_values page).

  Definition storage_page_dense_index (page : list N) (offset : nat) : nat :=
    length (List.filter storage_page_slot_present (firstn offset page)).

  Definition storage_page_empty_model : list N :=
    repeat 0%N page_slot_count.

  #[global] Arguments storage_page_empty_model : simpl never.
  #[global] Hint Opaque storage_page_empty_model : sl_opacity.

  Lemma storage_page_update_slot_cons_zero value slot rest :
    storage_page_update_slot 0 value (slot :: rest) = value :: rest.
  Proof.
    reflexivity.
  Qed.

  Lemma storage_page_update_slot_cons_succ offset value slot rest :
    storage_page_update_slot (S offset) value (slot :: rest) =
    slot :: storage_page_update_slot offset value rest.
  Proof.
    reflexivity.
  Qed.

  Lemma storage_page_update_slot_length offset value page :
    (offset < length page)%nat ->
    length (storage_page_update_slot offset value page) = length page.
  Proof.
    unfold storage_page_update_slot.
    intro Hoffset.
    rewrite app_length.
    rewrite firstn_length_le.
    2: {
      lia.
    }
    simpl.
    rewrite skipn_length.
    lia.
  Qed.

  Lemma storage_page_update_slot_nth_eq offset value page default :
    (offset < length page)%nat ->
    nth offset (storage_page_update_slot offset value page) default = value.
  Proof.
    unfold storage_page_update_slot.
    intro Hoffset.
    rewrite app_nth2.
    2: {
      rewrite firstn_length_le.
      2: {
        lia.
      }
      lia.
    }
    rewrite firstn_length_le.
    2: {
      lia.
    }
    replace (offset - offset)%nat with 0%nat by lia.
    reflexivity.
  Qed.

  Lemma storage_page_update_slot_Forall_range offset value page :
    (offset < length page)%nat ->
    (value < 2 ^ 256)%N ->
    List.Forall (fun word => (word < 2 ^ 256)%N) page ->
    List.Forall
      (fun word => (word < 2 ^ 256)%N)
      (storage_page_update_slot offset value page).
  Proof.
    revert page.
    induction offset as [| offset IH];
      intros [| slot rest] Hoffset Hvalue Hpage; simpl in Hoffset.
    { lia. }
    {
      rewrite storage_page_update_slot_cons_zero.
      inversion Hpage; subst.
      constructor; assumption.
    }
    { lia. }
    {
      rewrite storage_page_update_slot_cons_succ.
      inversion Hpage; subst.
      constructor.
      { assumption. }
      apply IH; [lia | exact Hvalue | assumption].
    }
  Qed.

  Lemma storage_page_dense_values_update_absent_zero
      page offset value :
    (offset < length page)%nat ->
    storage_page_slot_present (nth offset page 0) = false ->
    storage_page_slot_present value = false ->
    storage_page_dense_values
      (storage_page_update_slot offset value page) =
    storage_page_dense_values page.
  Proof.
    revert page.
    induction offset as [| offset IH];
      intros [| slot rest] Hoffset Hold Hvalue; simpl in Hoffset.
    { lia. }
    {
      rewrite storage_page_update_slot_cons_zero.
      unfold storage_page_dense_values.
      simpl.
      simpl in Hold.
      rewrite Hvalue.
      rewrite Hold.
      reflexivity.
    }
    { lia. }
    {
      rewrite storage_page_update_slot_cons_succ.
      unfold storage_page_dense_values in *.
      simpl.
      destruct (storage_page_slot_present slot); simpl;
        rewrite (IH rest); try reflexivity; try assumption; lia.
    }
  Qed.

  Lemma storage_page_dense_values_update_present_zero
      page offset value :
    (offset < length page)%nat ->
    storage_page_slot_present (nth offset page 0) = true ->
    storage_page_slot_present value = false ->
    storage_page_dense_values
      (storage_page_update_slot offset value page) =
    list_erase_at
      (storage_page_dense_index page offset)
      (storage_page_dense_values page).
  Proof.
    revert page.
    induction offset as [| offset IH];
      intros [| slot rest] Hoffset Hold Hvalue; simpl in Hoffset.
    { lia. }
    {
      rewrite storage_page_update_slot_cons_zero.
      unfold storage_page_dense_values, storage_page_dense_index,
        list_erase_at.
      simpl.
      simpl in Hold.
      rewrite Hvalue.
      rewrite Hold.
      reflexivity.
    }
    { lia. }
    {
      rewrite storage_page_update_slot_cons_succ.
      unfold storage_page_dense_values, storage_page_dense_index,
        list_erase_at in *.
      simpl.
      destruct (storage_page_slot_present slot) eqn:Hslot; simpl.
      {
        simpl.
        f_equal.
        rewrite IH; try assumption; try lia.
        reflexivity.
      }
      {
        rewrite IH; try assumption; try lia.
        reflexivity.
      }
    }
  Qed.

  Lemma storage_page_dense_values_update_present_nonzero
      page offset value :
    (offset < length page)%nat ->
    storage_page_slot_present (nth offset page 0) = true ->
    storage_page_slot_present value = true ->
    storage_page_dense_values
      (storage_page_update_slot offset value page) =
    list_replace_at
      (storage_page_dense_index page offset)
      value
      (storage_page_dense_values page).
  Proof.
    revert page.
    induction offset as [| offset IH];
      intros [| slot rest] Hoffset Hold Hvalue; simpl in Hoffset.
    { lia. }
    {
      rewrite storage_page_update_slot_cons_zero.
      unfold storage_page_dense_values, storage_page_dense_index,
        list_replace_at.
      simpl.
      simpl in Hold.
      rewrite Hvalue.
      rewrite Hold.
      reflexivity.
    }
    { lia. }
    {
      rewrite storage_page_update_slot_cons_succ.
      unfold storage_page_dense_values, storage_page_dense_index,
        list_replace_at in *.
      simpl.
      destruct (storage_page_slot_present slot) eqn:Hslot; simpl.
      {
        simpl.
        f_equal.
        rewrite IH; try assumption; try lia.
        reflexivity.
      }
      {
        rewrite IH; try assumption; try lia.
        reflexivity.
      }
    }
  Qed.

  Lemma storage_page_dense_values_update_absent_nonzero
      page offset value :
    (offset < length page)%nat ->
    storage_page_slot_present (nth offset page 0) = false ->
    storage_page_slot_present value = true ->
    storage_page_dense_values
      (storage_page_update_slot offset value page) =
    list_insert_at
      (storage_page_dense_index page offset)
      value
      (storage_page_dense_values page).
  Proof.
    revert page.
    induction offset as [| offset IH];
      intros [| slot rest] Hoffset Hold Hvalue; simpl in Hoffset.
    { lia. }
    {
      rewrite storage_page_update_slot_cons_zero.
      unfold storage_page_dense_values, storage_page_dense_index,
        list_insert_at.
      simpl.
      simpl in Hold.
      rewrite Hvalue.
      rewrite Hold.
      reflexivity.
    }
    { lia. }
    {
      rewrite storage_page_update_slot_cons_succ.
      unfold storage_page_dense_values, storage_page_dense_index,
        list_insert_at in *.
      simpl.
      destruct (storage_page_slot_present slot) eqn:Hslot; simpl.
      {
        simpl.
        f_equal.
        rewrite IH; try assumption; try lia.
        reflexivity.
      }
      {
        rewrite IH; try assumption; try lia.
        reflexivity.
      }
    }
  Qed.

  (* [StoragePageR] is the ownership-level view of a C++ storage page.  The
     current C++ object is sparse: [bitmap_] records which of the 128 logical
     slots are present, while [values_] stores the non-zero values densely in
     slot order.

     The Boost small-vector layout is abstracted by the library-level
     [boost_small_vector.SmallVectorR] view, but its logical contents are the
     dense non-zero values derived from the same 128-slot page model as
     [bitmap_]. *)
  Definition StoragePageR (q : Qp) (page : list N) : Rep :=
    storage_page_bitmap_field
      |-> primR Tuint128_t q (Vn (slot_bitmap_word page))
    ** storage_page_values_vector_field
      |-> boost_small_vector.SmallVectorR
        storage_page_values_ty storage_page_values_vector_ty
        storage_page_values_holder_ty bytes32_ty
        bytes32R q (storage_page_dense_values page)
    ** structR "monad::storage_page_t" q
    ** [| length page = page_slot_count |]
    ** [| List.Forall (fun word => (word < 2 ^ 256)%N) page |].

  #[global] Arguments StoragePageR : simpl never.
  #[global] Hint Opaque StoragePageR : sl_opacity.

  #[global] Instance observeStoragePageRType q page :
    Observe (type_ptrR storage_page_ty) (StoragePageR q page).
  Proof.
    unfold StoragePageR.
    apply _.
  Qed.

  Definition observeStoragePageRType_F :=
    ltac:(mk_at_obs_fwd observeStoragePageRType).

  #[global] Instance storage_page_BundledRep :
    concepts.BundledRep storage_page_ty (list N).
  Proof.
    constructor.
    exact StoragePageR.
  Defined.

  (** A moved-from storage page remains destructible, but its scalar bitmap and
      moved-from small vector no longer necessarily describe the same logical
      page.  This representation owns both members without asserting their
      ordinary [StoragePageR] coherence invariant. *)
  Definition StoragePageMoveResidualR (q : Qp) : Rep :=
    Exists (bitmap : N) (values : list N),
      storage_page_bitmap_field
        |-> primR Tuint128_t q (Vn bitmap)
      ** storage_page_values_vector_field
        |-> boost_small_vector.SmallVectorR
          storage_page_values_ty storage_page_values_vector_ty
          storage_page_values_holder_ty bytes32_ty
          bytes32R q values
      ** structR "monad::storage_page_t" q.

  #[global] Arguments StoragePageMoveResidualR : simpl never.
  #[global] Hint Opaque StoragePageMoveResidualR : sl_opacity.

  #[global] Instance observeStoragePageMoveResidualRType q :
    Observe (type_ptrR storage_page_ty) (StoragePageMoveResidualR q).
  Proof.
    unfold StoragePageMoveResidualR.
    apply _.
  Qed.

  Definition observeStoragePageMoveResidualRType_F :=
    ltac:(mk_at_obs_fwd observeStoragePageMoveResidualRType).

  Instance storage_page_MoveResidualRep :
    MoveResidualRep storage_page_ty (list N) :=
    {| move_residualR := fun _ => StoragePageMoveResidualR 1 |}.

  Lemma StoragePageR_move_residual (p : ptr) q page :
    p |-> StoragePageR q page
    |-- p |-> StoragePageMoveResidualR q.
  Proof.
    unfold StoragePageR, StoragePageMoveResidualR.
    rewrite <- (bi.exist_intro (slot_bitmap_word page)).
    rewrite <- (bi.exist_intro (storage_page_dense_values page)).
    go.
  Qed.

  Definition StoragePageR_move_residual_B p q page :=
    [BWD] (StoragePageR_move_residual p q page).

  Definition StoragePageR_move_residual_C :=
    [CANCEL] @StoragePageR_move_residual.

  Lemma StoragePageMoveResidualR_unpack (p : ptr) q :
    p |-> StoragePageMoveResidualR q
    |-- Exists (bitmap : N) (values : list N),
      p ,, storage_page_bitmap_field
        |-> primR Tuint128_t q$m (Vn bitmap)
      ** p ,, storage_page_values_vector_field
        |-> boost_small_vector.SmallVectorR
          storage_page_values_ty storage_page_values_vector_ty
          storage_page_values_holder_ty bytes32_ty
          bytes32R q values
      ** p |-> structR "monad::storage_page_t" q$m.
  Proof.
    unfold StoragePageMoveResidualR.
    go.
  Qed.

  Definition StoragePageMoveResidualR_unpack_F p q :=
    [FWD] (StoragePageMoveResidualR_unpack p q).

  Hint Resolve
    StoragePageR_move_residual_B
    StoragePageMoveResidualR_unpack_F : sl_opacity.

  Opaque bytes32R evmc_bytes32_wordR.
  #[global] Hint Opaque bytes32R evmc_bytes32_wordR : sl_opacity.

  Definition StoragePageBitmapR (q : Qp) (bitmap : N) : Rep :=
    storage_page_bitmap_field
      |-> primR Tuint128_t q (Vn bitmap)
    ** structR "monad::storage_page_t" q
    ** [| (bitmap < 2 ^ 128)%N |].

  #[global] Arguments StoragePageBitmapR : simpl never.
  #[global] Hint Opaque StoragePageBitmapR : sl_opacity.

  Definition storage_page_set_bit_model (bitmap : N) (offset : nat) : N :=
    N.setbit bitmap (N.of_nat offset).

  Definition storage_page_clear_bit_model (bitmap : N) (offset : nat) : N :=
    N.clearbit bitmap (N.of_nat offset).

  Definition pair_slot_mask (pair_index : nat) : N :=
    3 * 2 ^ (2 * N.of_nat pair_index).

  Definition pair_bit_mask (pair_index : nat) : N :=
    2 ^ N.of_nat pair_index.

  Fixpoint pair_bitmap_prefix (fuel : nat) (slot_bitmap : N) : N :=
    match fuel with
    | O => 0
    | S fuel' =>
        let prefix := pair_bitmap_prefix fuel' slot_bitmap in
        if N.eqb (N.land slot_bitmap (pair_slot_mask fuel')) 0
        then prefix
        else N.lor prefix (pair_bit_mask fuel')
    end.

  Fixpoint pair_bitmap_from
      (fuel : nat) (slot_bitmap pair_index : N) : N :=
    match fuel with
    | O => 0
    | S fuel' =>
        let lo := 2 ^ (2 * pair_index) in
        let hi := 2 ^ (2 * pair_index + 1) in
        (if N.eqb (N.land slot_bitmap (N.lor lo hi)) 0
         then 0
         else 2 ^ pair_index)
        + pair_bitmap_from fuel' slot_bitmap (N.succ pair_index)
    end.

  Definition pair_bitmap_word (slot_bitmap : N) : N :=
    pair_bitmap_prefix page_pair_count slot_bitmap.

  Lemma pair_bitmap_prefix_64_pair_bitmap_word slot_bitmap :
    pair_bitmap_prefix 64 slot_bitmap = pair_bitmap_word slot_bitmap.
  Proof.
    unfold pair_bitmap_word, page_pair_count.
    reflexivity.
  Qed.

  Opaque pair_bitmap_word.

  Definition storage_page_empty (page : list N) : bool :=
    forallb (N.eqb 0) page.

  Lemma slot_bitmap_from_zero_storage_page_empty index page :
    slot_bitmap_from index page = 0 <->
    storage_page_empty page = true.
  Proof.
    revert index.
    induction page as [| slot rest IH]; intro index; cbn.
    {
      split; reflexivity.
    }
    destruct (N.eq_dec slot 0) as [Hslot | Hslot].
    {
      subst slot.
      cbn.
      rewrite IH.
      reflexivity.
    }
    destruct slot as [| slot_pos].
    { contradiction Hslot; reflexivity. }
    cbn.
    split.
    {
      intro Hsum.
      pose proof (N.pow_nonzero 2 (N.of_nat index) ltac:(lia))
        as Hpow.
      lia.
    }
    {
      discriminate.
    }
  Qed.

  Lemma slot_bitmap_word_zero_storage_page_empty page :
    slot_bitmap_word page = 0 <-> storage_page_empty page = true.
  Proof.
    unfold slot_bitmap_word.
    apply slot_bitmap_from_zero_storage_page_empty.
  Qed.

  Lemma slot_bitmap_word_Z_zero_storage_page_empty page :
    Z.of_N (slot_bitmap_word page) = 0%Z <->
    storage_page_empty page = true.
  Proof.
    rewrite <- N2Z.inj_0.
    rewrite N2Z.inj_iff.
    apply slot_bitmap_word_zero_storage_page_empty.
  Qed.

  Lemma slot_bitmap_word_zero_asbool page :
    bool_decide (slot_bitmap_word page = 0) = storage_page_empty page.
  Proof.
    rewrite
      (bool_decide_ext
         (slot_bitmap_word page = 0)
         (storage_page_empty page = true)
         ltac:(apply slot_bitmap_word_zero_storage_page_empty)).
    destruct (storage_page_empty page); reflexivity.
  Qed.

  Definition bitmap_word_bit (bm : N) (index : nat) : bool :=
    negb (N.eqb (N.land bm (2 ^ N.of_nat index)) 0).

  Definition page_pair_leaf_model
      (page : list N) (pair_index : nat) : pair_leaf :=
    (bytes32_of_N (nth (2 * pair_index) page 0),
     bytes32_of_N (nth (2 * pair_index + 1) page 0)).

  Definition init_leaf_scratch_model
      (page : list N) (pair_bitmap : N) (old_scratch : list N) : list N :=
    map
      (fun pair_index =>
         if bitmap_word_bit pair_bitmap pair_index
         then
           bytes32_to_N
             (H64 leaf_mode (page_pair_leaf_model page pair_index))
         else nth pair_index old_scratch 0)
      (seq 0 page_pair_count).

  Definition page_subtree_root_model (page : list N) : digest :=
    match value_tree_from_slots (page_slots_model page) with
    | Some tree => eval_tree tree
    | None => bytes32_of_N 0
    end.

  Definition live_nodes_bitmap_word (nodes : list live_node) : N :=
    fold_left
      (fun bm node => N.lor bm (2 ^ N.of_nat node.(live_index)))
      nodes 0.

  (* [merge_at_level] scans the machine bitmap from low bits to high bits.
     The list view used by the Gallina [merge_level] model must therefore be
     canonical: strictly increasing by representative pair index, with every
     index inside the 64-pair page.  Without this side condition, two different
     lists can fold to the same bitmap while [merge_level] observes their
     different orders. *)
  Fixpoint live_nodes_well_formed_from
      (lower : nat) (nodes : list live_node) : Prop :=
    match nodes with
    | [] => True
    | node :: rest =>
        (lower <= node.(live_index) < page_pair_count)%nat /\
        live_nodes_well_formed_from (S node.(live_index)) rest
    end.

  Definition live_nodes_well_formed (nodes : list live_node) : Prop :=
    live_nodes_well_formed_from 0 nodes.

  Lemma live_nodes_well_formed_from_weaken lower lower' nodes :
    (lower' <= lower)%nat ->
    live_nodes_well_formed_from lower nodes ->
    live_nodes_well_formed_from lower' nodes.
  Proof.
    revert lower lower'.
    induction nodes as [| node rest IH]; intros lower lower' Hle Hwf.
    { exact I. }
    simpl in Hwf |- *.
    destruct Hwf as [Hnode Hrest].
    split; [lia | exact Hrest].
  Qed.

  Lemma merge_level_preserves_well_formed_from bit lower nodes :
    live_nodes_well_formed_from lower nodes ->
    live_nodes_well_formed_from lower (merge_level bit nodes).
  Proof.
    remember (length nodes) as fuel eqn:Hfuel.
    revert lower nodes Hfuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros lower nodes Hfuel Hwf.
    destruct nodes as [| current rest].
    { exact I. }
    simpl in Hwf |- *.
    destruct Hwf as [Hcurrent Hrest].
    destruct rest as [| next later].
    { simpl. split; [exact Hcurrent | exact I]. }
    simpl in Hrest.
    destruct Hrest as [Hnext Hlater].
    simpl.
    destruct (sibling_candidate bit (live_index current) (live_index next)).
    {
      split; [exact Hcurrent |].
      eapply live_nodes_well_formed_from_weaken.
      2: {
        refine
          (IH (length later) _
             (S (live_index next)) later eq_refl Hlater).
        rewrite Hfuel; simpl; lia.
      }
      simpl.
      lia.
    }
    {
      split; [exact Hcurrent |].
      change
        (live_nodes_well_formed_from
           (S (live_index current))
           (merge_level bit (next :: later))).
      refine
        (IH (length (next :: later)) _
           (S (live_index current)) (next :: later) eq_refl _).
      { rewrite Hfuel; simpl; lia. }
      {
        simpl.
        split; [exact Hnext | exact Hlater].
      }
    }
  Qed.

  Lemma merge_level_preserves_well_formed bit nodes :
    live_nodes_well_formed nodes ->
    live_nodes_well_formed (merge_level bit nodes).
  Proof.
    apply merge_level_preserves_well_formed_from.
  Qed.

  Definition scratch_represents_live_nodes
      (scratch : list N) (nodes : list live_node) : Prop :=
    length scratch = page_pair_count /\
    forall node,
      In node nodes ->
      nth node.(live_index) scratch 0 =
      bytes32_to_N (eval_tree node.(live_tree)).

  Record merge_job : Type := {
    merge_left : live_node;
    merge_right : live_node;
  }.

  Definition merge_job_node (job : merge_job) : live_node :=
    {|
      live_index := job.(merge_left).(live_index);
      live_tree :=
        TreeNode
          job.(merge_left).(live_tree)
          job.(merge_right).(live_tree);
    |}.

  Definition merge_job_input (job : merge_job) : bytes64 :=
    (eval_tree job.(merge_left).(live_tree),
     eval_tree job.(merge_right).(live_tree)).

  Definition merge_job_output (job : merge_job) : N :=
    bytes32_to_N (H64 merge_mode (merge_job_input job)).

  Definition merge_job_left_index (job : merge_job) : nat :=
    job.(merge_left).(live_index).

  Definition merge_job_right_index (job : merge_job) : nat :=
    job.(merge_right).(live_index).

  Record merge_scan_state : Type := {
    scan_pending : option live_node;
    scan_jobs : list merge_job;
  }.

  Definition initial_merge_scan_state : merge_scan_state :=
    {| scan_pending := None; scan_jobs := [] |}.

  Definition scan_one_node
      (bit : nat) (state : merge_scan_state) (node : live_node)
      : merge_scan_state :=
    match state.(scan_pending) with
    | None =>
        {|
          scan_pending := Some node;
          scan_jobs := state.(scan_jobs);
        |}
    | Some previous =>
        if sibling_candidate bit previous.(live_index) node.(live_index)
        then
          {|
            scan_pending := None;
            scan_jobs :=
              state.(scan_jobs) ++
              [{| merge_left := previous; merge_right := node |}];
          |}
        else
          {|
            scan_pending := Some node;
            scan_jobs := state.(scan_jobs);
          |}
    end.

  Fixpoint scan_nodes_from
      (bit : nat) (state : merge_scan_state) (nodes : list live_node)
      : merge_scan_state :=
    match nodes with
    | [] => state
    | node :: rest =>
        scan_nodes_from bit (scan_one_node bit state node) rest
    end.

  Definition scan_nodes (bit : nat) (nodes : list live_node)
      : merge_scan_state :=
    scan_nodes_from bit initial_merge_scan_state nodes.

  Definition merge_jobs (bit : nat) (nodes : list live_node)
      : list merge_job :=
    (scan_nodes bit nodes).(scan_jobs).

  Local Open Scope nat_scope.

  Definition merge_scan_pending_count
      (state : merge_scan_state) : nat :=
    match state.(scan_pending) with
    | Some _ => 1
    | None => 0
    end.

  Lemma scan_one_node_jobs_bound bit state node :
    2 * length (scan_one_node bit state node).(scan_jobs) +
      merge_scan_pending_count (scan_one_node bit state node) <=
    2 * length state.(scan_jobs) +
      merge_scan_pending_count state + 1.
  Proof.
    destruct state as [[pending |] jobs]; simpl.
    {
      destruct
        (sibling_candidate bit
           pending.(live_index) node.(live_index));
        simpl; rewrite ?app_length; simpl; lia.
    }
    lia.
  Qed.

  Lemma scan_nodes_from_jobs_bound bit nodes state :
    2 * length (scan_nodes_from bit state nodes).(scan_jobs) +
      merge_scan_pending_count (scan_nodes_from bit state nodes) <=
    2 * length state.(scan_jobs) +
      merge_scan_pending_count state + length nodes.
  Proof.
    revert state.
    induction nodes as [| node rest IH]; intro state.
    { simpl. lia. }
    simpl.
    specialize (IH (scan_one_node bit state node)).
    pose proof (scan_one_node_jobs_bound bit state node).
    lia.
  Qed.

  Lemma merge_jobs_two_for_one bit nodes :
    2 * length (merge_jobs bit nodes) <= length nodes.
  Proof.
    unfold merge_jobs, scan_nodes, initial_merge_scan_state.
    pose proof
      (scan_nodes_from_jobs_bound bit nodes
         {| scan_pending := None; scan_jobs := [] |}) as Hbound.
    simpl in Hbound.
    lia.
  Qed.

  Lemma live_nodes_well_formed_from_length lower nodes :
    live_nodes_well_formed_from lower nodes ->
    (lower <= page_pair_count)%nat ->
    (length nodes + lower <= page_pair_count)%nat.
  Proof.
    revert lower.
    induction nodes as [| node rest IH]; intros lower Hwf Hlower.
    { simpl. lia. }
    simpl in Hwf.
    destruct Hwf as [[Hindex_lower Hindex_upper] Hrest].
    specialize (IH (S node.(live_index)) Hrest).
    simpl.
    assert (S node.(live_index) <= page_pair_count)%nat by lia.
    specialize (IH H).
    lia.
  Qed.

  Lemma live_nodes_well_formed_length nodes :
    live_nodes_well_formed nodes ->
    (length nodes <= page_pair_count)%nat.
  Proof.
    intro Hwf.
    unfold live_nodes_well_formed in Hwf.
    pose proof (live_nodes_well_formed_from_length 0 nodes Hwf).
    unfold page_pair_count in *.
    lia.
  Qed.

  Lemma merge_jobs_length_le_32 bit nodes :
    live_nodes_well_formed nodes ->
    (length (merge_jobs bit nodes) <= 32)%nat.
  Proof.
    intro Hwf.
    pose proof (merge_jobs_two_for_one bit nodes).
    pose proof (live_nodes_well_formed_length nodes Hwf).
    unfold page_pair_count in *.
    lia.
  Qed.

  Local Close Scope nat_scope.

  Definition apply_merge_job_to_scratch
      (scratch : list N) (job : merge_job) : list N :=
    <[ job.(merge_left).(live_index) := merge_job_output job ]> scratch.

  Definition apply_merge_job_to_bitmap (bm : N) (job : merge_job) : N :=
    N.clearbit bm (N.of_nat job.(merge_right).(live_index)).

  Fixpoint apply_merge_jobs_to_scratch
      (scratch : list N) (jobs : list merge_job) : list N :=
    match jobs with
    | [] => scratch
    | job :: rest =>
        apply_merge_jobs_to_scratch
          (apply_merge_job_to_scratch scratch job) rest
    end.

  Fixpoint apply_merge_jobs_to_bitmap (bm : N) (jobs : list merge_job) : N :=
    match jobs with
    | [] => bm
    | job :: rest =>
        apply_merge_jobs_to_bitmap
          (apply_merge_job_to_bitmap bm job) rest
    end.

  Definition merge_hash_outputs
      (jobs : list merge_job) (old_outputs : list N) : list N :=
    blake3_hash_many_outputs merge_mode (map merge_job_input jobs) ++
    skipn (length jobs) old_outputs.

  Inductive merge_block_row : Type :=
  | MergeBlockUninit
  | MergeBlockLeft : digest -> merge_block_row
  | MergeBlockFull : bytes64 -> merge_block_row.

  Definition merge_block_rowR (row : merge_block_row) : Rep :=
    match row with
    | MergeBlockUninit =>
        arrayLR Tuchar 0 64
          (fun _ : unit => anyR Tuchar 1$m)
          (replicateN 64 ())
    | MergeBlockLeft lhs =>
        arrayLR Tuchar 0 32
          (fun byte : val => primR Tuchar 1$m byte)
          (blake3specs.bytes32_byte_values lhs)
        ** arrayLR Tuchar 32 64
          (fun _ : unit => uninitR Tuchar 1$m)
          (replicateN 32 ())
    | MergeBlockFull block =>
        blake3specs.Blake3BlockR 1 block
    end.

  Definition merge_block_rows (jobs : list merge_job)
      : list merge_block_row :=
    map (fun job => MergeBlockFull (merge_job_input job)) jobs ++
    replicateN
      (Z.to_N (32 - Z.of_nat (length jobs))) MergeBlockUninit.

  Definition merge_index_arrayR (indexes : list nat) : Rep :=
    as_Rep
      (fun base =>
         match indexes with
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
         end
       ).

  Definition merge_inputs_arrayR
      (blocksp : ptr) (jobs : list merge_job) : Rep :=
    as_Rep
      (fun base =>
         match jobs with
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
         end
       ).

  Definition merge_plan_arraysR
      (leftsp rightsp blocksp inputsp : ptr) (jobs : list merge_job)
      : mpred :=
    type_ptr merge_index_array_ty leftsp
    ** type_ptr merge_index_array_ty rightsp
    ** type_ptr merge_blocks_array_ty blocksp
    ** type_ptr merge_inputs_array_ty inputsp
    ** leftsp |-> merge_index_arrayR (map merge_job_left_index jobs)
    ** rightsp |-> merge_index_arrayR (map merge_job_right_index jobs)
    ** blocksp |-> arrayLR merge_block_row_ty 0 32
         merge_block_rowR (merge_block_rows jobs)
    ** inputsp |-> merge_inputs_arrayR blocksp jobs.

  Definition merge_plan_arrays_cleanupR
      (leftsp rightsp blocksp inputsp : ptr) (jobs : list merge_job)
      : mpred :=
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
         (fun _ : unit =>
            arrayLR Tuchar 0 64
              (fun _ : unit => anyR Tuchar 1$m)
              (replicateN 64 ()))
         (replicateN 32 ())
    ** inputsp |-> arrayLR merge_input_ptr_ty 0 32
         (fun _ : unit => anyR merge_input_ptr_ty 1$m)
         (replicateN 32 ()).

  Lemma storage_page_empty_page_slots page :
    storage_page_empty page = true ->
    page_slots_model page = repeat None (length page).
  Proof.
    unfold storage_page_empty.
    induction page as [| slot rest IH]; simpl.
    { reflexivity. }
    intros Hempty.
    apply andb_true_iff in Hempty as [Hslot Hrest].
    destruct slot as [| slot_pos]; [| discriminate].
    specialize (IH Hrest).
    rewrite IH.
    unfold page_slot_value_model.
    destruct (N.eq_dec 0 0) as [_ | Hneq].
    { reflexivity. }
    contradiction.
  Qed.

  Lemma bitmap_to_N_repeat_false bits :
    bitmap_to_N (repeat false bits) = 0.
  Proof.
    induction bits as [| bits IH]; simpl.
    { reflexivity. }
    now rewrite IH.
  Qed.

  Lemma bitmap_to_bytes16_repeat_false_page_slot_count :
    bitmap_to_bytes16 (repeat false page_slot_count) =
    bytes16_of_N 0.
  Proof.
    apply fin.t_eq.
    rewrite bitmap_to_bytes16_to_N.
    2: {
      rewrite repeat_length.
      unfold page_slot_count.
      lia.
    }
    change (fin.to_N (bytes16_of_N 0)) with 0.
    rewrite bitmap_to_N_repeat_false.
    reflexivity.
  Qed.

  Lemma page_commit_root_empty page :
    length page = page_slot_count ->
    storage_page_empty page = true ->
    bytes32_to_N (root (page_slots_model page)) = blake3_seal_model 0 None.
  Proof.
    intros Hlen Hempty.
    pose proof (storage_page_empty_page_slots page Hempty) as Hslots.
    rewrite Hslots.
    rewrite Hlen.
    unfold root, blake3_seal_model, blake3_seal_digest.
    change (value_tree_from_slots (repeat (@None slot_word) page_slot_count))
      with (@None value_tree).
    change (slot_bitmap (repeat (@None slot_word) page_slot_count))
      with (repeat false page_slot_count).
    rewrite bitmap_to_bytes16_repeat_false_page_slot_count.
    reflexivity.
  Qed.

  Lemma page_slots_model_length page :
    length (page_slots_model page) = length page.
  Proof.
    induction page as [| slot rest IH]; simpl; congruence.
  Qed.

  Lemma normalize_page_slots_model page :
    length page = page_slot_count ->
    normalize_slots (page_slots_model page) = page_slots_model page.
  Proof.
    intros Hlen.
    unfold normalize_slots.
    rewrite firstn_app.
    rewrite page_slots_model_length.
    rewrite Hlen.
    rewrite Nat.sub_diag.
    rewrite app_nil_r.
    rewrite firstn_all2.
    { reflexivity. }
    rewrite page_slots_model_length.
    lia.
  Qed.

  Lemma slot_bitmap_from_page_slots_model index page :
    slot_bitmap_from index page =
    (2 ^ N.of_nat index *
     bitmap_to_N (map slot_present (page_slots_model page)))%N.
  Proof.
    revert index.
    induction page as [| slot rest IH]; intro index; simpl.
    { nia. }
    rewrite IH.
    rewrite Nat2N.inj_succ.
    rewrite N.pow_succ_r'.
    unfold page_slot_value_model, slot_present.
    destruct (N.eq_dec slot 0) as [Hzero | Hnonzero].
    {
      subst slot.
      destruct (N.eq_dec 0 0) as [_ | Hneq]; [| contradiction].
      simpl.
      nia.
    }
    destruct (N.eq_dec slot 0) as [Hzero | _]; [contradiction |].
    simpl.
    nia.
  Qed.

  Lemma slot_bitmap_word_page_slots_model page :
    slot_bitmap_word page =
    bitmap_to_N (map slot_present (page_slots_model page)).
  Proof.
    unfold slot_bitmap_word.
    rewrite slot_bitmap_from_page_slots_model.
    simpl.
    nia.
  Qed.

  Lemma slot_bitmap_word_lt_128 page :
    length page = page_slot_count ->
    (slot_bitmap_word page < pow2N 128)%N.
  Proof.
    intro Hlen.
    rewrite slot_bitmap_word_page_slots_model.
    eapply N.lt_le_trans.
    { apply bitmap_to_N_lt_length. }
    rewrite length_map.
    rewrite page_slots_model_length.
    rewrite Hlen.
    unfold page_slot_count, pow2N.
    apply N.le_refl.
  Qed.

  Lemma page_slot_bitmap_bytes page :
    length page = page_slot_count ->
    bytes16_of_N (slot_bitmap_word page) =
    bitmap_to_bytes16 (slot_bitmap (page_slots_model page)).
  Proof.
    intro Hlen.
    apply fin.t_eq.
    unfold bytes16_of_N.
    rewrite fin.to_of_N'.
    2: {
      apply N.mod_upper_bound.
      discriminate.
    }
    rewrite bitmap_to_bytes16_to_N.
    2: {
      unfold slot_bitmap.
      rewrite length_map.
      rewrite normalize_slots_length.
      unfold page_slot_count.
      lia.
    }
    unfold slot_bitmap.
    rewrite (normalize_page_slots_model page Hlen).
    rewrite N.mod_small.
    2: now apply slot_bitmap_word_lt_128.
    rewrite slot_bitmap_word_page_slots_model.
    reflexivity.
  Qed.

  Lemma slots_from_bitmap_values_nil bm slots :
    slots_from_bitmap_values bm [] = Some slots ->
    slots = repeat None (length bm).
  Proof.
    intro H.
    assert
      (Hstrong :
        forall fuel bm slots,
          (length bm <= fuel)%nat ->
          slots_from_bitmap_values bm [] = Some slots ->
          slots = repeat None (length bm)).
    {
      induction fuel as [| fuel IH];
        intros bm' slots' Hfuel Hslots.
      {
        destruct bm' as [| first rest].
        { simpl in Hslots. inversion Hslots; reflexivity. }
        simpl in Hfuel. lia.
      }
      destruct bm' as [| first [| second rest]]; simpl in Hslots.
      { inversion Hslots; reflexivity. }
      { discriminate. }
      destruct (first || second) eqn:Hpair; [discriminate |].
      destruct (slots_from_bitmap_values rest [])
        as [rest_slots |] eqn:Hrest; [| discriminate].
      inversion Hslots; subst slots'; clear Hslots.
      rewrite (IH rest rest_slots).
      { reflexivity. }
      { simpl in Hfuel. lia. }
      { exact Hrest. }
    }
    exact (Hstrong (length bm) bm slots (Nat.le_refl (length bm)) H).
  Qed.

  Lemma page_slots_model_all_none_empty page :
    page_slots_model page = repeat None (length page) ->
    storage_page_empty page = true.
  Proof.
    induction page as [| slot rest IH]; simpl.
    { reflexivity. }
    intro Hslots.
    inversion Hslots as [[Hslot Hrest]].
    unfold page_slot_value_model in Hslot.
    destruct (N.eq_dec slot 0) as [Hzero | Hnonzero]; [subst slot | discriminate].
    simpl.
    rewrite (IH Hrest).
    reflexivity.
  Qed.

  Lemma value_tree_from_page_slots_nonempty page :
    length page = page_slot_count ->
    storage_page_empty page = false ->
    exists tree, value_tree_from_slots (page_slots_model page) = Some tree.
  Proof.
    intros Hlen Hnonempty.
    destruct (value_tree_from_slots (page_slots_model page))
      as [tree |] eqn:Htree.
    { now exists tree. }
    pose proof
      (value_tree_from_slots_empty_values (page_slots_model page) Htree)
      as Hactive.
    pose proof (slots_from_bitmap_values_roundtrip (page_slots_model page))
      as Hroundtrip.
    rewrite Hactive in Hroundtrip.
    apply slots_from_bitmap_values_nil in Hroundtrip.
    rewrite (normalize_page_slots_model page Hlen) in Hroundtrip.
    pose proof (page_slots_model_all_none_empty page) as Hall_empty.
    assert
      (Hbitmap_len :
        length (slot_bitmap (page_slots_model page)) = length page).
    {
      unfold slot_bitmap.
      rewrite length_map.
      rewrite (normalize_page_slots_model page Hlen).
      apply page_slots_model_length.
    }
    rewrite Hbitmap_len in Hroundtrip.
    specialize (Hall_empty Hroundtrip).
    rewrite Hnonempty in Hall_empty.
    discriminate.
  Qed.

  Lemma page_commit_root_nonempty page :
    length page = page_slot_count ->
    storage_page_empty page = false ->
    bytes32_to_N (root (page_slots_model page)) =
    blake3_seal_model
      (slot_bitmap_word page)
      (Some (page_subtree_root_model page)).
  Proof.
    intros Hlen Hnonempty.
    destruct (value_tree_from_page_slots_nonempty page Hlen Hnonempty)
      as [tree Htree].
    unfold root, page_subtree_root_model, blake3_seal_model,
      blake3_seal_digest.
    rewrite Htree.
    rewrite page_slot_bitmap_bytes.
    2: exact Hlen.
    reflexivity.
  Qed.

  Lemma page_commit_root_nonempty_digest page :
    length page = page_slot_count ->
    storage_page_empty page = false ->
    root (page_slots_model page) =
    seal_nonempty
      (bytes16_of_N (slot_bitmap_word page))
      (page_subtree_root_model page).
  Proof.
    intros Hlen Hnonempty.
    destruct (value_tree_from_page_slots_nonempty page Hlen Hnonempty)
      as [tree Htree].
    unfold root, page_subtree_root_model.
    rewrite Htree.
    rewrite page_slot_bitmap_bytes.
    2: exact Hlen.
    reflexivity.
  Qed.

  (*
    Dependency specs
    ----------------

    The specs below are summaries of library behavior needed by the generated
    storage-page AST.  They are deliberately small: enough to expose the MIP 8
    models, but not enough to verify libstdc++, Boost Outcome, intx, or BLAKE3
    themselves in this file.
  *)

  cpp.spec "monad::storage_page_t::storage_page_t()"
    from storage_page_cpp.source as storage_page_ctor_spec
    with (
      fun this : ptr =>
        \post this |-> StoragePageR 1 storage_page_empty_model
    ).

  cpp.spec "monad::storage_page_t::~storage_page_t()"
    from storage_page_cpp.source as storage_page_dtor_spec
    with (
      fun this : ptr =>
        \pre this |-> StoragePageMoveResidualR 1
        \post emp
    ).

  (* These storage-page object specs are the local API that the top-level
     encode/decode and commitment code relies on.  The page invariant remains a
     128-element pure list throughout. *)
  cpp.spec "monad::storage_page_t::is_empty() const"
    from storage_page_cpp.source as storage_page_is_empty_spec
    with (
      fun this : ptr =>
        \prepost{q page} this |-> StoragePageR q page
        \post [Vbool (storage_page_empty page)] emp
    ).

  cpp.spec "monad::storage_page_t::bitmap() const"
    from storage_page_cpp.source as storage_page_bitmap_spec
    with (
      fun this : ptr =>
        \prepost{q page} this |-> StoragePageR q page
        \post [Vn (slot_bitmap_word page)] emp
    ).

  cpp.spec "monad::storage_page_t::size() const"
    from storage_page_cpp.source as storage_page_size_spec
    with (
      fun this : ptr =>
        \prepost{q page} this |-> StoragePageR q page
        \post [Vn (N.of_nat (storage_page_size page))] emp
    ).

  cpp.spec "monad::storage_page_t::pair_bitmap() const"
    from storage_page_cpp.source as storage_page_pair_bitmap_spec
    with (
      fun this : ptr =>
        \prepost{qnum_pairs}
          _global storage_page_NUM_PAIRS_name
            |-> primR "unsigned long" qnum_pairs (Vn 64)
        \prepost{q page} this |-> StoragePageR q page
        \post [Vn (pair_bitmap_word (slot_bitmap_word page))] emp
    ).

  cpp.spec "monad::storage_page_t::has_bit_(const unsigned char) const"
    from storage_page_cpp.source as storage_page_has_bit_spec
    with (
      fun this : ptr =>
        \arg{i : Z} "i" (Vint i)
        \pre [| 0 <= i < Z.of_nat page_slot_count |]%Z
        \prepost{q page} this |-> StoragePageR q page
        \post [Vbool (storage_page_has_slot page (Z.to_nat i))] emp
    ).

  cpp.spec "monad::storage_page_t::dense_index_(const unsigned char) const"
    from storage_page_cpp.source as storage_page_dense_index_spec
    with (
      fun this : ptr =>
        \arg{i : Z} "i" (Vint i)
        \pre [| 0 <= i < Z.of_nat page_slot_count |]%Z
        \prepost{q page} this |-> StoragePageR q page
        \post [Vn (N.of_nat (storage_page_dense_index page (Z.to_nat i)))] emp
    ).

  cpp.spec "monad::storage_page_t::set_bit_(const unsigned char)"
    from storage_page_cpp.source as storage_page_set_bit_spec
    with (
      fun this : ptr =>
        \arg{i : Z} "i" (Vint i)
        \pre [| 0 <= i < Z.of_nat page_slot_count |]%Z
        \pre{bitmap} this |-> StoragePageBitmapR 1 bitmap
        \post this |-> StoragePageBitmapR 1
          (storage_page_set_bit_model bitmap (Z.to_nat i))
    ).

  cpp.spec "monad::storage_page_t::clear_bit_(const unsigned char)"
    from storage_page_cpp.source as storage_page_clear_bit_spec
    with (
      fun this : ptr =>
        \arg{i : Z} "i" (Vint i)
        \pre [| 0 <= i < Z.of_nat page_slot_count |]%Z
        \pre{bitmap} this |-> StoragePageBitmapR 1 bitmap
        \post this |-> StoragePageBitmapR 1
          (storage_page_clear_bit_model bitmap (Z.to_nat i))
    ).

  cpp.spec "monad::storage_page_t::set(const unsigned char, const monad::bytes32_t&)"
    from storage_page_cpp.source as storage_page_set_spec
    with (
      fun this : ptr =>
        \arg{offset : Z} "offset" (Vint offset)
        \arg{valuep : ptr} "value" (Vref valuep)
        \pre [| 0 <= offset < Z.of_nat page_slot_count |]%Z
        \prepost{qslots}
          _global storage_SLOTS_name
            |-> primR "unsigned long" qslots (Vn 128)
        \pre{page} this |-> StoragePageR 1 page
        \prepost{qvalue value} valuep |-> bytes32R qvalue value
        \post this |-> StoragePageR 1
          (storage_page_set_model (Z.to_nat offset) value page)
    ).

  Definition storage_page_values_index_const_spec : mpred :=
    boost_small_vector.index_const_spec
      storage_page_values_vector_name
      storage_page_values_ty
      storage_page_values_vector_ty
      storage_page_values_holder_ty
      bytes32_ty
      0%N
      bytes32R.

  Definition SpecFor_storage_page_values_index_const :=
    RegisterSpec storage_page_values_index_const_spec.
  #[global] Existing Instance SpecFor_storage_page_values_index_const.

  Definition storage_page_values_begin_spec : mpred :=
    boost_small_vector.begin_spec
      storage_page_values_vector_name
      storage_page_values_ty
      storage_page_values_vector_ty
      storage_page_values_holder_ty
      bytes32_ty
      storage_page_values_iterator_ty
      bytes32R.

  Definition SpecFor_storage_page_values_begin :=
    RegisterSpec storage_page_values_begin_spec.
  #[global] Existing Instance SpecFor_storage_page_values_begin.

  Definition storage_page_values_iterator_plus_spec : mpred :=
    boost_small_vector.iterator_plus_spec
      storage_page_values_iterator_ty
      bytes32_ty.

  Definition SpecFor_storage_page_values_iterator_plus :=
    RegisterSpec storage_page_values_iterator_plus_spec.
  #[global] Existing Instance SpecFor_storage_page_values_iterator_plus.

  Definition storage_page_values_const_iterator_ctor_spec : mpred :=
    boost_small_vector.const_iterator_from_iterator_ctor_spec
      storage_page_values_const_iterator_name
      storage_page_values_iterator_ty
      storage_page_values_const_iterator_ty
      bytes32_ty.

  Definition SpecFor_storage_page_values_const_iterator_ctor :=
    RegisterSpec storage_page_values_const_iterator_ctor_spec.
  #[global] Existing Instance SpecFor_storage_page_values_const_iterator_ctor.

  Definition storage_page_values_iterator_dtor_spec : mpred :=
    boost_small_vector.iterator_dtor_spec
      storage_page_values_iterator_name
      storage_page_values_iterator_ty
      bytes32_ty.

  Definition SpecFor_storage_page_values_iterator_dtor :=
    RegisterSpec storage_page_values_iterator_dtor_spec.
  #[global] Existing Instance SpecFor_storage_page_values_iterator_dtor.

  Definition storage_page_values_const_iterator_dtor_spec : mpred :=
    boost_small_vector.iterator_dtor_spec
      storage_page_values_const_iterator_name
      storage_page_values_const_iterator_ty
      bytes32_ty.

  Definition SpecFor_storage_page_values_const_iterator_dtor :=
    RegisterSpec storage_page_values_const_iterator_dtor_spec.
  #[global] Existing Instance SpecFor_storage_page_values_const_iterator_dtor.

  Definition storage_page_values_index_mut_spec : mpred :=
    boost_small_vector.index_mut_spec
      storage_page_values_vector_name
      storage_page_values_ty
      storage_page_values_vector_ty
      storage_page_values_holder_ty
      bytes32_ty
      0%N
      bytes32R.

  Definition SpecFor_storage_page_values_index_mut :=
    RegisterSpec storage_page_values_index_mut_spec.
  #[global] Existing Instance SpecFor_storage_page_values_index_mut.

  Definition storage_page_values_insert_spec : mpred :=
    boost_small_vector.insert_spec
      storage_page_values_vector_name
      storage_page_values_ty
      storage_page_values_vector_ty
      storage_page_values_holder_ty
      bytes32_ty
      storage_page_values_iterator_ty
      storage_page_values_const_iterator_ty
      bytes32R.

  Definition SpecFor_storage_page_values_insert :=
    RegisterSpec storage_page_values_insert_spec.
  #[global] Existing Instance SpecFor_storage_page_values_insert.

  Definition storage_page_values_erase_spec : mpred :=
    boost_small_vector.erase_spec
      storage_page_values_vector_name
      storage_page_values_ty
      storage_page_values_vector_ty
      storage_page_values_holder_ty
      bytes32_ty
      storage_page_values_iterator_ty
      storage_page_values_const_iterator_ty
      bytes32R.

  Definition SpecFor_storage_page_values_erase :=
    RegisterSpec storage_page_values_erase_spec.
  #[global] Existing Instance SpecFor_storage_page_values_erase.

  Definition storage_page_values_size_const_spec : mpred :=
    boost_small_vector.size_const_spec
      storage_page_values_vector_name
      storage_page_values_ty
      storage_page_values_vector_ty
      storage_page_values_holder_ty
      bytes32_ty
      bytes32R.

  Definition SpecFor_storage_page_values_size_const :=
    RegisterSpec storage_page_values_size_const_spec.
  #[global] Existing Instance SpecFor_storage_page_values_size_const.

  Definition storage_page_values_default_ctor_spec : mpred :=
    boost_small_vector.default_ctor_spec
      storage_page_values_name
      storage_page_values_small_vector_base_name
      storage_page_values_vector_name
      storage_page_values_ty
      storage_page_values_vector_ty
      storage_page_values_holder_ty
      bytes32_ty
      bytes32R.

  Definition SpecFor_storage_page_values_default_ctor :=
    RegisterSpec storage_page_values_default_ctor_spec.
  #[global] Existing Instance SpecFor_storage_page_values_default_ctor.

  Definition storage_page_values_dtor_spec : mpred :=
    boost_small_vector.dtor_spec
      storage_page_values_name
      storage_page_values_small_vector_base_name
      storage_page_values_vector_name
      storage_page_values_ty
      storage_page_values_vector_ty
      storage_page_values_holder_ty
      bytes32_ty
      bytes32R.

  Definition SpecFor_storage_page_values_dtor :=
    RegisterSpec storage_page_values_dtor_spec.
  #[global] Existing Instance SpecFor_storage_page_values_dtor.

  Definition storage_page_values_holder_start_const_spec : mpred :=
    boost_small_vector.holder_start_const_spec
      storage_page_values_holder_name
      storage_page_values_holder_ty
      bytes32_ty.

  Definition SpecFor_storage_page_values_holder_start_const :=
    RegisterSpec storage_page_values_holder_start_const_spec.
  #[global] Existing Instance SpecFor_storage_page_values_holder_start_const.

  cpp.spec "monad::storage_page_t::operator[](const unsigned char) const"
    from storage_page_cpp.source as storage_page_index_const_spec
    with (
      fun this : ptr =>
      \arg{offset : Z} "offset" (Vint offset)
      \pre [| 0 <= offset < Z.of_nat page_slot_count |]%Z
      \prepost{qslots}
        _global storage_SLOTS_name
          |-> primR "unsigned long" qslots (Vn 128)
      \prepost{q page} this |-> StoragePageR q page
      \post{retp : ptr} [Vptr retp]
        retp |-> bytes32R 1 (nth (Z.to_nat offset) page 0)
    ).

  (*
    Split page-commit helper specs
    ------------------------------

    These helpers are the proof-oriented decomposition of [page_commit].  The
    low-level scratch specs expose the intended loop invariant without forcing
    the top-level page-commit proof to symbolically execute the large merge
    loop.  The non-empty branch of [page_commit] now calls
    [compute_nonempty_subtree_root] and [blake3_seal] directly.
  *)

  cpp.spec
    (Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
       (Nfunction function_qualifiers.N "get_leaf_iv" nil))
    from storage_page_cpp.source as storage_get_leaf_iv_spec
    with (
      \pre{(ready : bool) (qcache : cQp.t) (qleafiv : Qp)}
        blake3specs.StorageLeafIvCacheR ready qcache qleafiv
      \pre{qiv qdomain}
        blake3specs.StorageLeafIvInitInputsR
          (negb ready) qiv qdomain
      \post
        [Vptr (_global blake3specs.storage_get_leaf_iv_static_iv_name)]
        blake3specs.StorageLeafIvCacheR
          true
          (blake3specs.storage_leaf_iv_cache_qcache_after
             ready qcache)
          (blake3specs.storage_leaf_iv_cache_qleaf_after
             ready qleafiv)
        ** blake3specs.StorageLeafIvInitInputsR
             (negb ready) qiv qdomain
    ).

  cpp.spec
    (Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
       (Nfunction function_qualifiers.N "blake3_seal"
          [Tuint128_t; Tptr (Qconst Tuchar)]))
    from storage_page_cpp.source as storage_blake3_seal_spec
    with (
      \arg{slot_bitmap : N} "slot_bitmap" (Vn slot_bitmap)
      \arg{rootp : ptr} "root_32" (Vptr rootp)
      \prepost type_ptr (Tarray Tuint 8) (_global "IV")
      \prepost{qiv}
        _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
          qiv model.blake3_iv_words
      \prepost{root} blake3specs.SealRootArgR rootp root
      \post{retp : ptr} [Vptr retp]
        retp |-> bytes32R 1
          (blake3specs.blake3_seal_model slot_bitmap root)
    ).

  cpp.spec
    (Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
       (Nfunction function_qualifiers.N "init_leaves"
          [Tref (Qconst storage_page_ty); Tulong; scratch_ref_arg_ty]))
    from storage_page_cpp.source as storage_init_leaves_spec
    with (
      \arg{pagep : ptr} "page" (Vref pagep)
      \arg{pair_bitmap : N} "pair_bitmap" (Vn pair_bitmap)
      \arg{scratchp : ptr} "scratch" (Vref scratchp)
      \prepost type_ptr (Tarray Tuint 8) (_global "IV")
      \pre{(ready : bool) (qleafcache : cQp.t) (qleafiv : Qp)}
        blake3specs.StorageLeafIvCacheR
          ready qleafcache qleafiv
      \prepost{qiv}
        _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
          qiv model.blake3_iv_words
      \pre{qdomain}
        blake3specs.StorageLeafDomainKeyMaybeR
          (negb ready) qdomain
      \prepost{qslot_size}
        _global storage_SLOT_SIZE_name
          |-> primR "unsigned long" qslot_size (Vn 32)
      \prepost{qslots}
        _global storage_SLOTS_name
          |-> primR "unsigned long" qslots (Vn 128)
      \prepost{q page} pagep |-> StoragePageR q page
      \pre{old_scratch}
        scratchp |-> ScratchR 1 old_scratch
      \post
        scratchp |-> ScratchR 1
          (init_leaf_scratch_model page pair_bitmap old_scratch)
        ** blake3specs.StorageLeafIvCacheR
             true
             (blake3specs.storage_leaf_iv_cache_qcache_after
                ready qleafcache)
             (blake3specs.storage_leaf_iv_cache_qleaf_after
                ready qleafiv)
        ** blake3specs.StorageLeafDomainKeyMaybeR
             (negb ready) qdomain
    ).

  cpp.spec
    (Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
       (Nfunction function_qualifiers.N "merge_at_level"
          [Tuchar; Tulong; scratch_ref_arg_ty]))
    from storage_page_cpp.source as storage_merge_at_level_spec
    with (
      \arg{bit : Z} "bit" (Vint bit)
      \arg{bm : N} "bm" (Vn bm)
      \arg{scratchp : ptr} "scratch" (Vref scratchp)
      \prepost{qiv}
        _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
          qiv model.blake3_iv_words
      \pre{nodes scratch}
        [| (0 <= bit < 6)%Z |]
        ** [| live_nodes_well_formed nodes |]
        ** [| bm = live_nodes_bitmap_word nodes |]
        ** [| scratch_represents_live_nodes scratch nodes |]
        ** scratchp |-> ScratchR 1 scratch
      \post{scratch'}
        [Vn (live_nodes_bitmap_word
               (merge_level (Z.to_nat bit) nodes))]
        scratchp |-> ScratchR 1 scratch'
        ** [| scratch_represents_live_nodes scratch'
              (merge_level (Z.to_nat bit) nodes) |]
    ).

  cpp.spec
    (Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
       (Nfunction function_qualifiers.N "compute_nonempty_subtree_root"
          [Tref (Qconst storage_page_ty); Tulong]))
    from storage_page_cpp.source as storage_compute_nonempty_subtree_root_spec
    with (
      \arg{pagep : ptr} "page" (Vref pagep)
      \arg{pair_bitmap : N} "pair_bitmap" (Vn pair_bitmap)
      \prepost type_ptr (Tarray Tuint 8) (_global "IV")
      \pre{(ready : bool) (qleafcache : cQp.t) (qleafiv : Qp)}
        blake3specs.StorageLeafIvCacheR
          ready qleafcache qleafiv
      \prepost{qslot_size}
        _global storage_SLOT_SIZE_name
          |-> primR "unsigned long" qslot_size (Vn 32)
      \prepost{qslots}
        _global storage_SLOTS_name
          |-> primR "unsigned long" qslots (Vn 128)
      \prepost{qiv}
        _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
          qiv model.blake3_iv_words
      \pre{qdomain}
        blake3specs.StorageLeafDomainKeyMaybeR
          (negb ready) qdomain
      \prepost{q page} pagep |-> StoragePageR q page
      \pre [| storage_page_empty page = false |]
      \pre [| pair_bitmap = pair_bitmap_word (slot_bitmap_word page) |]
      \post{retp : ptr} [Vptr retp]
        retp |-> bytes32R 1
          (bytes32_to_N (page_subtree_root_model page))
        ** blake3specs.StorageLeafIvCacheR
             true
             (blake3specs.storage_leaf_iv_cache_qcache_after
                ready qleafcache)
             (blake3specs.storage_leaf_iv_cache_qleaf_after
                ready qleafiv)
        ** blake3specs.StorageLeafDomainKeyMaybeR
             (negb ready) qdomain
    ).

  (*
    Top-level storage_page.cpp specs
    --------------------------------

    These are the obligations that [storage_page_proofs.v] proves against the
    generated AST.  They are intentionally stated in terms of the pure models
    above, so the C++ proof can be checked independently from the paper-level
    root uniqueness theorem.
  *)

  cpp.spec "monad::compute_page_key(const monad::bytes32_t&)"
    from storage_page_cpp.source as compute_page_key_spec
    with (
      \arg{storage_keyp : ptr} "storage_key" (Vref storage_keyp)
      \prepost{qshift}
        _global "monad::storage_page_t::PAGE_KEY_SHIFT"
          |-> primR "unsigned long" qshift (Vn 7)
      \prepost{q key} storage_keyp |-> bytes32R q key
      \post{retp : ptr} [Vptr retp]
        retp |-> bytes32R 1 (page_index_model key)
    ).

  cpp.spec "monad::compute_slot_offset(const monad::bytes32_t&)"
    from storage_page_cpp.source as compute_slot_offset_spec
    with (
      \arg{storage_keyp : ptr} "storage_key" (Vref storage_keyp)
      \prepost{qmask}
        _global "monad::storage_page_t::SLOT_OFFSET_MASK"
          |-> primR "unsigned char" qmask (Vint 127)
      \prepost{q key} storage_keyp |-> bytes32R q key
      \post{ret : Z} [Vint ret]
        [| ret = Z.of_N (slot_offset_model key) |]
    ).

  cpp.spec "monad::compute_slot_key(const monad::bytes32_t&, unsigned char)"
    from storage_page_cpp.source as compute_slot_key_spec
    with (
      \arg{page_keyp : ptr} "page_key" (Vref page_keyp)
      \arg{slot_offset : Z} "slot_offset" (Vint slot_offset)
      \prepost{qshift}
        _global "monad::storage_page_t::PAGE_KEY_SHIFT"
          |-> primR "unsigned long" qshift (Vn 7)
      \prepost{q page_key} page_keyp |-> bytes32R q page_key
      \pre [| 0 <= slot_offset < 128 |]%Z
      \post{retp : ptr} [Vptr retp]
        retp |-> bytes32R 1
             (slot_key_model page_key (Z.to_N slot_offset))
    ).

  (** For background on the style of the C++ specifications below, see
      #<a href="https://www.youtube.com/watch?v=zyyoWnF1QUE">this video</a>#. *)
  (** The global [IV] is an initialized [uint32_t[8]], not merely a span of
      eight cells. Its array [type_ptr] is a persistent initialization witness
      needed when [memcpy] reads its object representation. It is explicit
      here rather than silently assumed by a scalar-to-byte conversion axiom. *)
  (* begin show *)
  cpp.spec "monad::page_commit(const monad::storage_page_t&)"
    from storage_page_cpp.source as page_commit_spec
    with (
      \arg{pagep : ptr} "page" (Vref pagep)
      \prepost type_ptr (Tarray Tuint 8) (_global "IV")
      \prepost{qslot_size}
        _global storage_SLOT_SIZE_name
          |-> primR "unsigned long" qslot_size (Vn 32)
      \prepost{qslots}
        _global storage_SLOTS_name
          |-> primR "unsigned long" qslots (Vn 128)
      \prepost{qpage_num_pairs}
        _global storage_page_NUM_PAIRS_name
          |-> primR "unsigned long" qpage_num_pairs (Vn 64)
      \pre{(ready : bool) (qleafcache : cQp.t) (qleafiv : Qp)}
        blake3specs.StorageLeafIvCacheR
          ready qleafcache qleafiv
      \prepost{qiv}
        _global "IV" |-> blake3specs.Blake3ConstKeyWordsR
          qiv model.blake3_iv_words
      \prepost{q page} pagep |-> StoragePageR q page
      \pre{qdomain}
        blake3specs.StorageLeafDomainKeyMaybeR
          (negb ready && negb (storage_page_empty page)) qdomain
      \post{retp : ptr} [Vptr retp]
        retp |-> bytes32R 1 (bytes32_to_N (root (page_slots_model page)))
        ** blake3specs.StorageLeafIvCacheR
             (if storage_page_empty page then ready else true)
             (if storage_page_empty page
              then qleafcache
              else blake3specs.storage_leaf_iv_cache_qcache_after
                     ready qleafcache)
             (if storage_page_empty page
              then qleafiv
              else blake3specs.storage_leaf_iv_cache_qleaf_after
                     ready qleafiv)
        ** blake3specs.StorageLeafDomainKeyMaybeR
             (negb ready && negb (storage_page_empty page)) qdomain
    ).
  (* end show *)

  (** The [page_commit_spec] postcondition above is the C++ entry point for the
      abstract binding theorem in [commitment.v].  It returns the [N]-encoding
      of [root (page_slots_model page)], because [bytes32R] is the existing C++
      bytes32 representation predicate.

      The next two pure lemmas package the transfer step that is otherwise easy
      to miss.  If two verified C++ calls return the same bytes32 word, the
      spec gives equality of those two [bytes32_to_N] encodings.  Since digests
      are finite 256-bit words, [fin.t_eq] converts that back to equality of
      the digest roots used by [commitment.v].  The length hypotheses are the
      pure part of [StoragePageR]; they let us replace normalized slot lists by
      the concrete 128-slot views carried by storage pages. *)

  Theorem page_commit_return_eq_extracts_aligned_collision page page' :
    length page = page_slot_count ->
    length page' = page_slot_count ->
    bytes32_to_N (root (page_slots_model page)) =
    bytes32_to_N (root (page_slots_model page')) ->
    page_slots_model page <> page_slots_model page' ->
    exists_aligned_collision
      (root_with_trace (page_slots_model page))
      (root_with_trace (page_slots_model page')).
  Proof.
    intros Hlen Hlen' Hret Hdistinct.
    eapply Root_binding_break_extracts_aligned_collision.
    {
      rewrite !root_with_trace_root.
      apply fin.t_eq.
      exact Hret.
    }
    {
      intro Hnormalized.
      apply Hdistinct.
      rewrite <- (normalize_page_slots_model page Hlen).
      rewrite <- (normalize_page_slots_model page' Hlen').
      exact Hnormalized.
    }
  Qed.

  Theorem page_commit_return_eq_no_aligned_collision_same_view page page' :
    length page = page_slot_count ->
    length page' = page_slot_count ->
    no_aligned_collisions
      (root_with_trace (page_slots_model page))
      (root_with_trace (page_slots_model page')) ->
    bytes32_to_N (root (page_slots_model page)) =
    bytes32_to_N (root (page_slots_model page')) ->
    page_slots_model page = page_slots_model page'.
  Proof.
    intros Hlen Hlen' Hno_collision Hret.
    assert
      (Hroot :
        root (page_slots_model page) =
        root (page_slots_model page')).
    {
      apply fin.t_eq.
      exact Hret.
    }
    pose proof
      (Root_injective_no_collision
         (page_slots_model page)
         (page_slots_model page')
         Hno_collision
         Hroot) as Hnormalized.
    rewrite (normalize_page_slots_model page Hlen) in Hnormalized.
    rewrite (normalize_page_slots_model page' Hlen') in Hnormalized.
    exact Hnormalized.
  Qed.

  (* begin show *)
  cpp.spec "monad::encode_storage_page(const monad::storage_page_t&)"
    from storage_page_cpp.source as encode_storage_page_spec
    with (
      \arg{pagep : ptr} "page" (Vref pagep)
      \prepost{qslots}
        _global storage_SLOTS_name
          |-> primR "unsigned long" qslots (Vn 128)
      \prepost{q page} pagep |-> StoragePageR q page
      \post{retp : ptr} [Vptr retp]
        retp |-> ByteStringR 1$m (encode_storage_page_model page)
    ).
  (* end show *)

  (* begin show *)
  cpp.spec "monad::decode_storage_page(std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>)"
    from storage_page_cpp.source as decode_storage_page_spec
    with (
      \arg{encp : ptr} "enc" (Vptr encp)
      \prepost{qslots}
        _global storage_SLOTS_name
          |-> primR "unsigned long" qslots (Vn 128)
      \pre{(bytes : list Z) (data : ptr)}
        encp |-> ByteStringViewSpineR 1 data
          (N.of_nat (length bytes))
      \pre{qbytes}
        data |-> array_sliceR Tuchar 0 (Z.of_nat (length bytes))
          (fun byte => ucharR (cQp.const qbytes) byte) bytes
      \pre [| storage_encoded_bytes_in_range bytes |]
      \post{retp : ptr} [Vptr retp]
        data |-> array_sliceR Tuchar 0 (Z.of_nat (length bytes))
          (fun byte => ucharR (cQp.const qbytes) byte) bytes
        ** retp |-> ResultR storage_page_ty 1
             (decode_storage_page_result_model bytes)
        ** match decode_storage_page_result_model bytes with
           | Result.Ok _ =>
               Exists final_data : ptr,
                 encp |-> ByteStringViewSpineR 1 final_data 0
                 ** [| byte_string_view_suffix
                           data bytes final_data [] |]
           | Result.Err _ =>
               Exists (final_data : ptr) (final_length : N),
                 encp |-> ByteStringViewSpineR 1
                    final_data final_length
                 ** [| byte_string_view_suffix_length
                         data bytes final_data final_length |]
           end
    ).
  (* end show *)

  (** The two specs above are tied together by the pure model theorem
      [decode_encode_storage_page_result_model].

      Concretely, if [page] has exactly the 128 storage slots expected by
      MIP-8 and is already canonical as a list of bytes32 words, then encoding
      it with [encode_storage_page_model] and immediately decoding those bytes
      with [decode_storage_page_result_model] returns [Result.Ok page].  The
      canonicality
      side condition rules out differences that are only artifacts of the
      model's bytes32 normalization.  Internally,
      [decode_storage_page_result_model] enforces strictly increasing indices
      below 128, compact RLP strings, nonzero slot values, and complete input
      consumption as the C++ decoder; rejection returns the corresponding
      [DecodeError.DecodeError.t].

      Thus, once the C++ encoder is proved against [encode_storage_page_spec]
      and the C++ decoder is proved against [decode_storage_page_spec], their
      composition inherits this pure model roundtrip property. *)
End with_Sigma.

#[global] Existing Instance storage_page_MoveResidualRep.

#[global] Hint Resolve
  observeStoragePageRType_F
  observeStoragePageMoveResidualRType_F
  StoragePageR_move_residual_C | 10 : sl_opacity.
