Set Default Goal Selector "!".
Set Nested Proofs Allowed.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.wand.
Require Import skylabs.auto.cpp.tactics.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.auto.cpp.Arith.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.libspecs.byte_string_specs.
Require Import monad.proofs.libspecs.evmc_specs.
Require Import monad.proofs.libspecs.result_model.
Require Import monad.proofs.libspecs.rlp_decode_error_model.
Require Import monad.proofs.libspecs.rlp_decode_error_specs.
Require Import monad.proofs.libspecs.rlp_specs.
Require Import monad.proofs.execproofs.mip8.storage_page_specs.
Require Import monad.proofs.execproofs.mip8.storage_page_encoding.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_ctor.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_dtor.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_index_const.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_set.
Require Import monad.proofs.disableIPMtacs_use_go_instead.
Require Import monad.proofs.execproofs.mip8.storage_page_indexed_encoding.

Import linearity.
Import wand_fupd.

#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

Lemma storage_encoded_bytes_in_range_skipn n bytes :
  storage_encoded_bytes_in_range bytes ->
  storage_encoded_bytes_in_range (skipn n bytes).
Proof.
  revert bytes.
  induction n as [| n IHn];
    intros [| byte rest] Hrange;
    cbn [skipn];
    eauto using storage_encoded_bytes_in_range_cons_tail.
Qed.

Lemma rlp_decode_string_model_rest_range encoded payload rest :
  storage_encoded_bytes_in_range encoded ->
  rlp_decode_string_model encoded = Some (payload, rest) ->
  storage_encoded_bytes_in_range rest.
Proof.
  intros Hrange Hdecode.
  destruct encoded as [| header encoded_rest];
    cbn [rlp_decode_string_model] in Hdecode;
    try discriminate.
  destruct (header <=? 127)%Z eqn:Hsingle.
  {
    injection Hdecode as _ <-.
    eauto using storage_encoded_bytes_in_range_cons_tail.
  }
  destruct ((128 <=? header)%Z && (header <=? 183)%Z) eqn:Hshort.
  {
    destruct
      (rlp_short_string_is_noncanonical
         (Z.to_nat (header - 128)) encoded_rest);
      try discriminate.
    destruct (Z.to_nat (header - 128) <=? length encoded_rest)%nat;
      try discriminate.
    injection Hdecode as _ <-.
    apply storage_encoded_bytes_in_range_skipn.
    eauto using storage_encoded_bytes_in_range_cons_tail.
  }
  destruct ((184 <=? header)%Z && (header <=? 191)%Z);
    try discriminate.
  destruct
    (Z.to_nat (header - 183) <? length encoded_rest)%nat;
    try discriminate.
  destruct
    (rlp_decode_long_string_length
       (firstn (Z.to_nat (header - 183)) encoded_rest)) as [len |];
    try discriminate.
  destruct (len <? 56)%nat; try discriminate.
  destruct
    (len <=? length
       (skipn (Z.to_nat (header - 183)) encoded_rest))%nat;
    try discriminate.
  injection Hdecode as _ <-.
  apply storage_encoded_bytes_in_range_skipn.
  apply storage_encoded_bytes_in_range_skipn.
  eauto using storage_encoded_bytes_in_range_cons_tail.
Qed.

Lemma rlp_decode_bytes32_compact_model_rest_range encoded value rest :
  storage_encoded_bytes_in_range encoded ->
  rlp_decode_bytes32_compact_model encoded = Some (value, rest) ->
  storage_encoded_bytes_in_range rest.
Proof.
  intros Hrange Hdecode.
  unfold rlp_decode_bytes32_compact_model in Hdecode.
  destruct (rlp_decode_string_model encoded) as [[payload after_payload] |]
    eqn:Hshort; try discriminate.
  destruct (32 <? length payload)%nat; try discriminate.
  destruct (compact_payload_has_leading_zero payload); try discriminate.
  injection Hdecode as _ <-.
  eauto using rlp_decode_string_model_rest_range.
Qed.

#[local] Hint Resolve rlp_decode_bytes32_compact_model_rest_range : pure.

#[local] Hint Resolve
  storage_encoded_bytes_in_range_cons_head
  storage_encoded_bytes_in_range_cons_tail
  : pure.
#[local] Hint Unfold storage_encoded_byte_in_range : pure.
#[local] Hint Extern 1
  (byte_string_view_suffix_length ?base ?backing ?view_data ?view_length) =>
    match goal with
    | Hsuffix :
        byte_string_view_suffix base backing view_data ?visible |- _ =>
        exists visible;
        split; [reflexivity | exact Hsuffix]
    end
  : pure.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Instance learn_byte_string_view_spine :
    LearnEq3 ByteStringViewSpineR :=
    ltac:(solve_learnable).

  #[local] Instance learn_storage_page :
    LearnEq2 StoragePageR :=
    ltac:(solve_learnable).

  #[local] Hint Resolve wp_init_implicit_B_local : sl_opacity.
  #[local] Hint Resolve
    ResultR_unpack_F ResultR_pack_B : sl_opacity.

  Definition type_ptr_reference_to_B_local ty p :=
    [BWD] (type_ptr_reference_to ty p).

#[local] Hint Resolve
  observeStoragePageTypePtr_index_F
  type_ptr_reference_to_B_local : sl_opacity.

	  Lemma keep_and_gather_frame
      (I R : mpred) (Q : mpred -> mpred) :
    (R |-- Q (R ** emp)) ->
    I ** R |-- I ** gather_all.Spatial.gather (Q:=Q).
  Proof.
    intro HQ.
    apply bi.sep_mono.
    {
      reflexivity.
    }
    {
      apply (gather_all.prove_gather_spatial R
               (GS:=bunch_pers.BunchBaseNonPer R)).
      simpl.
      exact HQ.
    }
  Qed.

  (** The page contains a completed prefix and a zero suffix. [next] is one
      past the last accepted index, so increasing indices never overwrite
      previously accepted values. The input backing array is unchanged. *)
  Definition decode_loop_running
      (enc_addr : ptr) (qslots : cQp.t)
      (backing_q : Qp) (backing_base : ptr) (bytes : list Z)
      (page_addr prev_index_addr first_addr : ptr) : mpred :=
    Exists (fuel next : nat) (prefix : list N)
      (current_data : ptr) (current_bytes : list Z),
      [| next <= page_slot_count |]
      ** [| page_slot_count <= next + fuel |]
      ** [| length prefix = next |]
      ** [| storage_encoded_bytes_in_range current_bytes |]
      ** [| byte_string_view_suffix
                backing_base bytes current_data current_bytes |]
      ** [| match decode_slots_from fuel next current_bytes with
            | Result.Ok suffix => Result.Ok (prefix ++ suffix)
            | Result.Err error => Result.Err error
            end = decode_storage_page_result_model bytes |]
      ** enc_addr |-> ByteStringViewSpineR 1 current_data
           (N.of_nat (length current_bytes))
      ** backing_base |-> array_sliceR Tuchar 0
           (Z.of_nat (length bytes))
           (fun byte => ucharR (cQp.const backing_q) byte) bytes
      ** _global storage_SLOTS_name
           |-> primR "unsigned long" qslots (Vn 128)
      ** page_addr |-> StoragePageR 1
           (prefix ++ repeat 0%N (page_slot_count - next))
      ** prev_index_addr |-> ucharR 1$m (Z.of_nat (Nat.pred next))
      ** first_addr |-> boolR 1$m (Nat.eqb next 0).

  Lemma decode_loop_running_initial
      (enc_addr : ptr) (qslots : cQp.t)
      (backing_q : Qp) (data : ptr) (bytes : list Z)
      (page_addr prev_index_addr first_addr : ptr) :
    storage_encoded_bytes_in_range bytes ->
    enc_addr |-> ByteStringViewSpineR 1 data
      (N.of_nat (length bytes))
    ** data |-> array_sliceR Tuchar 0
         (Z.of_nat (length bytes))
         (fun byte => ucharR (cQp.const backing_q) byte) bytes
    ** _global storage_SLOTS_name
         |-> primR "unsigned long" qslots (Vn 128)
    ** page_addr |-> StoragePageR 1 storage_page_empty_model
    ** prev_index_addr |-> ucharR 1$m 0
    ** first_addr |-> boolR 1$m true
    |-- decode_loop_running enc_addr qslots backing_q data bytes
          page_addr prev_index_addr first_addr.
  Proof using MODd.
    intro Hrange.
    unfold decode_loop_running.
    rewrite <- (bi.exist_intro page_slot_count).
    rewrite <- (bi.exist_intro 0%nat).
    rewrite <- (bi.exist_intro ([] : list N)).
    rewrite <- (bi.exist_intro data).
    rewrite <- (bi.exist_intro bytes).
    assert (Hmodel :
      match decode_slots_from page_slot_count 0 bytes with
      | Result.Ok suffix => Result.Ok ([] ++ suffix)
      | Result.Err error => Result.Err error
      end = decode_storage_page_result_model bytes).
    {
      unfold decode_storage_page_result_model.
      destruct (decode_slots_from page_slot_count 0 bytes); reflexivity.
    }
    assert (Hsuffix : byte_string_view_suffix data bytes data bytes).
    {
      exists []. cbn [List.app length].
      split; [reflexivity |].
      rewrite offset_ptr_sub_0; [reflexivity | vm_compute; eauto].
    }
    change ([] ++ repeat 0%N (page_slot_count - 0))
      with storage_page_empty_model.
    go.
  Qed.

  Definition decode_loop_running_initial_B
      enc_addr qslots backing_q data bytes
      page_addr prev_index_addr first_addr Hrange :=
    [BWD] (decode_loop_running_initial
      enc_addr qslots backing_q data bytes
      page_addr prev_index_addr first_addr Hrange).

  Opaque decode_storage_page_model decode_storage_page_result_model.

  Lemma prf_decode_storage_page :
    verify[source] decode_storage_page_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    go using storage_page_ctor_spec.
    wp_while (fun _ =>
      decode_loop_running enc_addr qslots qbytes data bytes
        page_addr prev_index_addr first_addr).
    match goal with
    | Hrange : storage_encoded_bytes_in_range bytes |- _ =>
        pose (initial_loop_B := decode_loop_running_initial_B
          enc_addr qslots qbytes data bytes
          page_addr prev_index_addr first_addr Hrange)
    end.
    go using initial_loop_B.
    go using string_view_empty_spec.
    wp_if.
    {
      intro Hnonempty.
      destruct current_bytes as [| header rest].
      { discriminate. }
      assert (Hheader_range : storage_encoded_byte_in_range header)
        by eauto using storage_encoded_bytes_in_range_cons_head.
      unfold storage_encoded_byte_in_range in Hheader_range.
      replace header with (trim 8 header) in * by arith_solve.
      assert (Hheader_index :
        (0 < N.of_nat (length (trim 8 header :: rest)))%N)
        by (cbn; lia).
      match goal with
      | Hsuffix : byte_string_view_suffix
          data bytes current_data (trim 8 header :: rest) |- _ =>
          pose proof (byte_string_view_suffix_tail
            data bytes current_data (trim 8 header) rest Hsuffix)
            as Hsuffix_tail;
          destruct Hsuffix as [consumed [Hbacking Hcurrent_data]]
      end.
      subst bytes current_data.
      go using
        (byte_string_view_suffix_range_C
          data qbytes (consumed ++ trim 8 header :: rest)
          (data .[ Tuchar ! Z.of_nat (length consumed) ])
          (trim 8 header :: rest)
          (ex_intro _ consumed (conj eq_refl eq_refl))),
        string_view_index_spec.
      wapply (byte_string_view_suffix_head_extract
        data qbytes (consumed ++ trim 8 header :: rest)
        (data .[ Tuchar ! Z.of_nat (length consumed) ])
        consumed (trim 8 header) rest eq_refl eq_refl).
      go.
      normalize_ptrs.
      replace (Z.of_nat (length consumed) + 0)%Z
        with (Z.of_nat (length consumed)) by lia.
      go.
      wapply (byte_string_view_suffix_head_join
        data qbytes (consumed ++ trim 8 header :: rest)
        (data .[ Tuchar ! Z.of_nat (length consumed) ])
        consumed (trim 8 header) rest eq_refl eq_refl).
      go using
        (byte_string_view_suffix_range_C
          data qbytes (consumed ++ trim 8 header :: rest)
          (data .[ Tuchar ! Z.of_nat (length consumed) ])
          (trim 8 header :: rest)
          (ex_intro _ consumed (conj eq_refl eq_refl))).
      change (drop (N.to_nat 1) (trim 8 header :: rest)) with rest.
      assert (Hsuffix_after_header_exact :
        byte_string_view_suffix
          data (consumed ++ trim 8 header :: rest)
          (data .[ Tuchar ! Z.of_nat (length consumed) ] .[ Tuchar ! 1 ])
          rest).
      { rewrite o_sub_sub. exact Hsuffix_tail. }
      assert (Hsuffix_after_header_cpp :
        byte_string_view_suffix_length
          data (consumed ++ trim 8 header :: rest)
          (data .[ Tuchar ! Z.of_nat (length consumed) ] .[ Tuchar ! 1 ])
          (N.of_nat (S (length rest)) - 1)%N).
      {
        replace (N.of_nat (S (length rest)) - 1)%N
          with (N.of_nat (length rest)) by lia.
        apply byte_string_view_suffix_length_intro.
        exact Hsuffix_after_header_exact.
      }
      wp_if.
      {
        intro Hindex_ge.
        assert (Hbad : decode_slots_from fuel (length prefix)
          (trim 8 header :: rest) =
          Result.Err DecodeError.DecodeError.NonCanonical).
        {
          assert ((Z.of_nat page_slot_count <=? trim 8 header)%Z = true)
            as Hge by (apply Z.leb_le; exact Hindex_ge).
          destruct fuel; cbn [decode_slots_from]; rewrite Hge orb_true_r;
            reflexivity.
        }
        match goal with
        | Hmodel : context[decode_slots_from fuel _ _] |- _ =>
            rewrite Hbad in Hmodel; cbn in Hmodel; rewrite <- Hmodel
        end.
        go.
        rewrite <- (bi.exist_intro DecodeError.DecodeError.NonCanonical).
        go.
      }
      {
        intro Hindex_lt.
        Import skylabs.auto.cpp.hints.join.manual_expr_condition.
        go.
        wpe_spec (fun _ =>
          \prepost first_addr |-> boolR 1$m (Nat.eqb (length prefix) 0)
          \prepost prev_index_addr |-> ucharR 1$m
            (Z.of_nat (Nat.pred (length prefix)))
          \prepost index_addr |-> ucharR 1$c (trim 8 header)
          \post [Vbool (Z.ltb (trim 8 header) (Z.of_nat (length prefix)))] emp).
        go.
        {
          destruct (length prefix) as [| previous] eqn:Hprefix_length.
          {
            replace (trim 8 header <? Z.of_nat 0)%Z with false
              by (symmetry; apply Z.ltb_ge; arith_solve).
            go using skylabs.auto.cpp.hints.join.wp_operand_seqand_B.
          }
          {
            go using skylabs.auto.cpp.hints.join.wp_operand_seqand_B.
            assert (Hcmp :
              (trim 8 header <? Z.of_nat (S previous))%Z =
              bool_decide (trim 8 header <= Z.of_nat previous)%Z).
            {
              apply Bool.eq_true_iff_eq.
              rewrite Z.ltb_lt bool_decide_eq_true. lia.
            }
            rewrite Hcmp. go.
          }
        }
        go.
        wp_if.
        {
          intro Horder_bad.
          assert (Hbad : decode_slots_from fuel (length prefix)
            (trim 8 header :: rest) =
            Result.Err DecodeError.DecodeError.NonCanonical).
          {
            destruct fuel; cbn [decode_slots_from];
              rewrite Horder_bad; reflexivity.
          }
          match goal with
          | Hmodel : context[decode_slots_from fuel _ _] |- _ =>
              rewrite Hbad in Hmodel; cbn in Hmodel; rewrite <- Hmodel
          end.
          go.
          rewrite <- (bi.exist_intro DecodeError.DecodeError.NonCanonical).
          go.
        }
        {
          intro Horder_ok.
          assert (Hindex_lower : (Z.of_nat (length prefix) <= trim 8 header)%Z)
            by (apply Z.ltb_ge; exact Horder_ok).
          assert (Hindex_upper :
            (Z.of_nat page_slot_count <=? trim 8 header)%Z = false)
            by (apply Z.leb_gt; exact Hindex_lt).
          match goal with
          | Hresult : context[decode_slots_from fuel _ _] |- _ =>
              rename Hresult into Hmodel
          end.
          destruct fuel as [| fuel']; [unfold page_slot_count in *; lia |].
          cbn [decode_slots_from] in Hmodel.
          rewrite Horder_ok Hindex_upper in Hmodel.
          cbn [orb] in Hmodel.
          go.
          destruct (rlp_decode_bytes32_compact_result_model rest)
            as [[value decoded_rest] | error] eqn:Hdecode_result.
          {
            assert (Hdecode : rlp_decode_bytes32_compact_model rest =
              Some (value, decoded_rest)).
            {
              rewrite <- rlp_decode_bytes32_compact_result_to_option.
              rewrite Hdecode_result. reflexivity.
            }
            rewrite <- (bi.exist_intro qbytes).
            match goal with
            | |- context[bi_exist ?P] =>
                rewrite <- (bi.exist_intro (Ψ := P) data)
            end.
            match goal with
            | |- context[bi_exist ?P] =>
                rewrite <- (bi.exist_intro (Ψ := P)
                  (consumed ++ trim 8 header :: rest))
            end.
            match goal with
            | |- context[bi_exist ?P] =>
                rewrite <- (bi.exist_intro (Ψ := P) rest)
            end.
            go using OutcomeResultR_pack_B.
            rewrite Hdecode_result.
            go using OutcomeResultR_pack_B.
            rewrite <- (bi.exist_intro
              (@OutcomeValue N outcome_status_code value)).
            go using OutcomeResultR_pack_B.
            wp_if.
            {
              intro Hzero.
              apply N.eqb_eq in Hzero.
              destruct (N.eq_dec value 0%N) as [Hz | Hnz]; [|contradiction].
              cbn in Hmodel.
              rewrite <- Hmodel.
              go using OutcomeResultR_pack_B.
              rewrite <- (bi.exist_intro DecodeError.DecodeError.NonCanonical).
              go.
              rewrite <- (bi.exist_intro
                (@OutcomeValue N outcome_status_code 0%N)).
              go using OutcomeResultR_pack_B.
            }
            {
              intro Hnonzero.
              apply N.eqb_neq in Hnonzero.
              destruct (N.eq_dec value 0%N) as [Hz | Hnz]; [contradiction |].
              go.
              rewrite <- (bi.exist_intro
                (@OutcomeValue N outcome_status_code value)).
              go.
              assert (Hnext :
                match decode_slots_from fuel' (S (Z.to_nat (trim 8 header)))
                    decoded_rest with
                | Result.Ok suffix => Result.Ok
                    ((prefix ++ repeat 0%N
                      (Z.to_nat (trim 8 header) - length prefix) ++ [value]) ++ suffix)
                | Result.Err error => Result.Err error
                end = decode_storage_page_result_model
                  (consumed ++ trim 8 header :: rest)).
              {
                destruct (BinNat.N.eq_dec value 0%N) in Hmodel; [contradiction |].
                destruct (decode_slots_from fuel'
                  (S (Z.to_nat (trim 8 header))) decoded_rest);
                  cbn [List.app] in Hmodel |- *.
                { rewrite <- !app_assoc. exact Hmodel. }
                { exact Hmodel. }
              }
              assert (Hdecoded_rest_range :
                storage_encoded_bytes_in_range decoded_rest)
                by eauto using rlp_decode_bytes32_compact_model_rest_range,
                  storage_encoded_bytes_in_range_cons_tail.
              match goal with
              | Hview : byte_string_view_suffix _ _ _
                  (rlp_decode_string_final_view rest) |- _ =>
                  rewrite (rlp_decode_bytes32_compact_final_view_success
                    _ _ _ Hdecode) in Hview
              end.
              rewrite (rlp_decode_bytes32_compact_final_view_success
                _ _ _ Hdecode).
              change storage_page_set_model with decode_storage_page_update_slot.
              rewrite decode_storage_page_update_slot_gap.
              2: { unfold page_slot_count. lia. }
              unfold decode_loop_running.
              rewrite <- (bi.exist_intro fuel').
              rewrite <- (bi.exist_intro (S (Z.to_nat (trim 8 header)))).
              rewrite <- (bi.exist_intro
                (prefix ++ repeat 0%N
                  (Z.to_nat (trim 8 header) - length prefix) ++ [value])).
              rewrite <- (bi.exist_intro t).
              rewrite <- (bi.exist_intro decoded_rest).
              go.
              rewrite !app_length repeat_length /=.
              go.
            }
          }
          {
            cbn in Hmodel.
            rewrite <- Hmodel.
            rewrite <- (bi.exist_intro qbytes).
            match goal with
            | |- context[bi_exist ?P] =>
                rewrite <- (bi.exist_intro (Ψ := P) data)
            end.
            match goal with
            | |- context[bi_exist ?P] =>
                rewrite <- (bi.exist_intro (Ψ := P)
                  (consumed ++ trim 8 header :: rest))
            end.
            match goal with
            | |- context[bi_exist ?P] =>
                rewrite <- (bi.exist_intro (Ψ := P) rest)
            end.
            go using later_spec_bwd,
              OutcomeResultR_unpack_F, OutcomeResultR_pack_B.
            rewrite Hdecode_result.
            go using later_spec_bwd,
              OutcomeResultR_unpack_F, OutcomeResultR_pack_B.
            rewrite <- (bi.exist_intro (@OutcomeError N outcome_status_code
              (decode_error_status_code error))).
            go.
            go using StatusCodeR_as_cfractional, _at_split_specific_cfrac_C.
            go.
            rewrite <- (bi.exist_intro (decode_error_status_code error)).
            go.
            rewrite <- (bi.exist_intro (decode_error_status_code error)).
            go.
            rewrite <- (bi.exist_intro (@OutcomeFailureMoved outcome_status_code)).
            rewrite <- (bi.exist_intro (@OutcomeMoved N outcome_status_code)).
            go.
          }
        }
      }
    }
    {
      intro Hempty.
      destruct current_bytes as [| header rest]; [|cbn in Hempty; discriminate].
      match goal with
      | Hmodel : context[decode_slots_from fuel _ []] |- _ =>
          rewrite decode_slots_from_empty in Hmodel;
          cbn in Hmodel; rewrite <- Hmodel
      end.
      go.
    }
  Qed.
End with_Sigma.
