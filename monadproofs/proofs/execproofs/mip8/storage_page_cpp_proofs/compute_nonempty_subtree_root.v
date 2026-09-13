Set Default Goal Selector "!".

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.

Lemma popcount_fuel_le fuel word :
  popcount_fuel fuel word <= N.of_nat fuel.
Proof.
  revert word.
  induction fuel as [| fuel IH]; intro word; simpl.
  { lia. }
  destruct (N.odd word);
    specialize (IH (N.shiftr word 1)); simpl; lia.
Qed.

Lemma popcount64_int_bound :
  forall word,
  bitsize.bound (int_rank.bitsize int_rank.Iint) Signed
    (Z.of_N (popcount64 word)).
Proof.
  intro word.
  pose proof (popcount_fuel_le 64 word).
  unfold popcount64 in *.
  change (bitsize.bound (int_rank.bitsize int_rank.Iint)
            Signed (Z.of_N (popcount_fuel 64 word)))
    with (-2147483648 <= Z.of_N (popcount_fuel 64 word)
          <= 2147483647)%Z.
  lia.
Qed.

Lemma countr_zero_fuel_le fuel word :
  countr_zero_fuel fuel word <= 64 + N.of_nat fuel.
Proof.
  revert word.
  induction fuel as [| fuel IH]; intro word; simpl.
  { lia. }
  destruct (N.eqb word 0).
  { lia. }
  destruct (N.odd word);
    specialize (IH (N.shiftr word 1)); simpl; lia.
Qed.

Lemma countr_zero64_int_bound :
  forall word,
  bitsize.bound (int_rank.bitsize int_rank.Iint) Signed
    (Z.of_N (countr_zero64 word)).
Proof.
  intro word.
  pose proof (countr_zero_fuel_le 64 word).
  unfold countr_zero64 in *.
  change (bitsize.bound (int_rank.bitsize int_rank.Iint)
            Signed (Z.of_N (countr_zero_fuel 64 word)))
    with (-2147483648 <= Z.of_N (countr_zero_fuel 64 word)
          <= 2147483647)%Z.
  lia.
Qed.

#[local] Hint Resolve
  popcount64_int_bound countr_zero64_int_bound : typeclass_instances pure.
#[local] Hint Opaque
  popcount64 popcount_fuel countr_zero64 countr_zero_fuel
  : typeclass_instances sl_opacity.

Opaque popcount64 popcount_fuel countr_zero64 countr_zero_fuel.

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.init_leaf_scratch_support.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  #[local] Hint Resolve
    wp_init_implicit_B_local
    wp.wp_init_initlist_struct_B
    wp_operand_initlist_default_B
    wp_init_default_array_B
    wp_init_bytes32_array_zero_local_B
    observeStoragePageLength_F
    UNSAFE_read_prim_cancel : sl_opacity.
  #[local] Hint Opaque
    StoragePageR ScratchR root page_slots_model page_subtree_root_model
    pair_bitmap_word pair_bitmap_prefix live_nodes_bitmap_word
    scratch_represents_live_nodes : sl_opacity.

  Opaque pair_bitmap_word live_nodes_bitmap_word.
  Transparent pair_bitmap_word pair_bitmap_prefix live_nodes_bitmap_word.

  Definition page_initial_live_nodes (page : list N) : list live_node :=
    match active_leaf_nodes
            (pair_bitmap (page_slots_model page))
            (active_pair_values (page_slots_model page)) with
    | Some nodes => nodes
    | None => []
    end.

  Fixpoint merge_prefix (bit : nat) (nodes : list live_node)
      : list live_node :=
    match bit with
    | O => nodes
    | S bit' => merge_level bit' (merge_prefix bit' nodes)
    end.

  Lemma merge_prefix_succ bit nodes :
    merge_level bit (merge_prefix bit nodes) =
    merge_prefix (S bit) nodes.
  Proof.
    reflexivity.
  Qed.

  Lemma merge_prefix_preserves_well_formed bit nodes :
    live_nodes_well_formed nodes ->
    live_nodes_well_formed (merge_prefix bit nodes).
  Proof.
    induction bit as [| bit IH]; intro Hwf; simpl.
    { exact Hwf. }
    apply merge_level_preserves_well_formed.
    now apply IH.
  Qed.

  #[local] Hint Resolve
    merge_level_preserves_well_formed
    merge_prefix_preserves_well_formed : pure.

  Fixpoint initial_nodes_from_pair_options
      (next_index : nat)
      (pairs : list (option blake3model.pair_leaf))
      : list live_node :=
    match pairs with
    | [] => []
    | Some pair_value :: rest =>
        {|
          live_index := next_index;
          live_tree := TreeLeaf pair_value;
        |} :: initial_nodes_from_pair_options (S next_index) rest
    | None :: rest =>
        initial_nodes_from_pair_options (S next_index) rest
    end.

  Lemma active_leaf_nodes_from_pair_options next_index pairs :
    active_leaf_nodes_from
      next_index
      (pair_option_bitmap pairs)
      (pair_option_values pairs) =
    Some (initial_nodes_from_pair_options next_index pairs, []).
  Proof.
    revert next_index.
    induction pairs as [| [pair_value |] rest IH]; intro next_index;
      simpl.
    { reflexivity. }
    {
      rewrite IH.
      reflexivity.
    }
    { apply IH. }
  Qed.

  Lemma active_leaf_nodes_pair_options pairs :
    active_leaf_nodes
      (pair_option_bitmap pairs)
      (pair_option_values pairs) =
    Some (initial_nodes_from_pair_options 0 pairs).
  Proof.
    unfold active_leaf_nodes.
    rewrite active_leaf_nodes_from_pair_options.
    reflexivity.
  Qed.

  Lemma page_initial_live_nodes_eq page :
    page_initial_live_nodes page =
    initial_nodes_from_pair_options
      0 (pair_options (page_slots_model page)).
  Proof.
    unfold page_initial_live_nodes.
    rewrite <- pair_options_bitmap.
    rewrite <- pair_options_values.
    rewrite active_leaf_nodes_pair_options.
    reflexivity.
  Qed.

  Lemma initial_nodes_well_formed_from next_index pairs :
    (next_index + length pairs <= page_pair_count)%nat ->
    live_nodes_well_formed_from
      next_index
      (initial_nodes_from_pair_options next_index pairs).
  Proof.
    revert next_index.
    induction pairs as [| [pair_value |] rest IH]; intros next_index Hlen;
      simpl in *.
    { exact I. }
    {
      split.
      { lia. }
      apply IH.
      lia.
    }
    {
      eapply live_nodes_well_formed_from_weaken.
      2: {
        apply IH.
        lia.
      }
      lia.
    }
  Qed.

  Lemma initial_nodes_well_formed pairs :
    length pairs = page_pair_count ->
    live_nodes_well_formed
      (initial_nodes_from_pair_options 0 pairs).
  Proof.
    intro Hlen.
    unfold live_nodes_well_formed.
    apply initial_nodes_well_formed_from.
    lia.
  Qed.

  Lemma bitmap_to_N_testbit_nat bm index :
    N.testbit (bitmap_to_N bm) (N.of_nat index) =
    nth index bm false.
  Proof.
    revert index.
    induction bm as [| bit rest IH]; intro index.
    { destruct index; reflexivity. }
    destruct index as [| index].
    {
      simpl.
      destruct bit.
      { replace (1 + 2 * bitmap_to_N rest)%N
          with (2 * bitmap_to_N rest + 1)%N by lia.
        apply N.testbit_odd_0. }
      rewrite N.add_0_l.
      apply N.testbit_even_0.
    }
    simpl.
    replace (N.pos (Pos.of_succ_nat index))
      with (N.succ (N.of_nat index))
      by lia.
    replace
      ((if bit then 1 else 0) + 2 * bitmap_to_N rest)%N
      with (2 * bitmap_to_N rest + N.b2n bit)%N
      by (destruct bit; simpl; lia).
    rewrite N.testbit_succ_r.
    apply IH.
  Qed.

  Lemma bitmap_word_bit_of_bitmap_to_N bm index :
    nth index bm false = true ->
    bitmap_word_bit (bitmap_to_N bm) index = true.
  Proof.
    intro Hbit.
    unfold bitmap_word_bit.
    destruct
      (N.eqb (N.land (bitmap_to_N bm) (2 ^ N.of_nat index)) 0)
      eqn:Hland; [| reflexivity].
    apply N.eqb_eq in Hland.
    pose proof
      (f_equal
         (fun word => N.testbit word (N.of_nat index))
         Hland) as Htest.
    rewrite N.land_spec in Htest.
    rewrite N.pow2_bits_true in Htest.
    rewrite Bool.andb_true_r in Htest.
    rewrite bitmap_to_N_testbit_nat in Htest.
    rewrite Hbit in Htest.
    discriminate.
  Qed.

  Lemma N_testbit_3_high (bit : N) :
    (2 <= bit)%N ->
    N.testbit 3 bit = false.
  Proof.
    intro Hbit.
    apply N.bits_above_log2.
    change (N.log2 3) with 1%N.
    lia.
  Qed.

  Lemma pair_slot_mask_testbit_true_low index :
    N.testbit
      (pair_slot_mask index)
      (2 * N.of_nat index)%N = true.
  Proof.
    unfold pair_slot_mask.
    replace (2 * N.of_nat index)%N
      with (0 + 2 * N.of_nat index)%N by lia.
    rewrite N.mul_pow2_bits_add.
    reflexivity.
  Qed.

  Lemma pair_slot_mask_testbit_true_high index :
    N.testbit
      (pair_slot_mask index)
      (2 * N.of_nat index + 1)%N = true.
  Proof.
    unfold pair_slot_mask.
    replace (2 * N.of_nat index + 1)%N
      with (1 + 2 * N.of_nat index)%N by lia.
    rewrite N.mul_pow2_bits_add.
    reflexivity.
  Qed.

  Lemma pair_slot_mask_testbit_other index (bit : N) :
    bit <> (2 * N.of_nat index)%N ->
    bit <> (2 * N.of_nat index + 1)%N ->
    N.testbit (pair_slot_mask index) bit = false.
  Proof.
    intros Hlow Hhigh.
    unfold pair_slot_mask.
    destruct (N.ltb bit (2 * N.of_nat index)) eqn:Hlt.
    {
      apply N.ltb_lt in Hlt.
      now rewrite N.mul_pow2_bits_low.
    }
    apply N.ltb_ge in Hlt.
    rewrite N.mul_pow2_bits_high.
    2: {
      exact Hlt.
    }
    apply N_testbit_3_high.
    lia.
  Qed.

  Lemma pair_slot_mask_occupied_bit word index :
    negb
      (N.eqb
         (N.land word (pair_slot_mask index))
         0) =
    (N.testbit word (2 * N.of_nat index)%N ||
     N.testbit word (2 * N.of_nat index + 1)%N).
  Proof.
    destruct (N.testbit word (2 * N.of_nat index)%N) eqn:Hlow;
      destruct (N.testbit word (2 * N.of_nat index + 1)%N) eqn:Hhigh;
      simpl.
    all: unfold pair_slot_mask at 1.
    all: fold (pair_slot_mask index).
    all: destruct
      (N.eqb (N.land word (pair_slot_mask index)) 0) eqn:Hland;
      try reflexivity.
    all: try
      (apply N.eqb_eq in Hland;
       pose proof
         (f_equal
            (fun value =>
               N.testbit value (2 * N.of_nat index)%N)
            Hland) as Htest;
       rewrite N.land_spec in Htest;
       rewrite pair_slot_mask_testbit_true_low in Htest;
       rewrite Bool.andb_true_r in Htest;
       rewrite Hlow in Htest;
       discriminate).
    all: try
      (apply N.eqb_eq in Hland;
       pose proof
         (f_equal
            (fun value =>
               N.testbit value (2 * N.of_nat index + 1)%N)
            Hland) as Htest;
       rewrite N.land_spec in Htest;
       rewrite pair_slot_mask_testbit_true_high in Htest;
       rewrite Bool.andb_true_r in Htest;
       rewrite Hhigh in Htest;
       discriminate).
    assert (Hzero : N.land word (pair_slot_mask index) = 0%N).
    {
      apply N.bits_inj_0.
      intro bit.
      rewrite N.land_spec.
      destruct (N.eq_dec bit (2 * N.of_nat index)%N) as [Heq | Hneq].
      { subst bit. now rewrite Hlow. }
      destruct (N.eq_dec bit (2 * N.of_nat index + 1)%N) as [Heq | Hneq'].
      { subst bit. now rewrite Hhigh. }
      rewrite pair_slot_mask_testbit_other.
      2: {
        exact Hneq.
      }
      2: {
        exact Hneq'.
      }
      now rewrite Bool.andb_false_r.
    }
    rewrite Hzero in Hland.
    rewrite N.eqb_refl in Hland.
    discriminate.
  Qed.

  Lemma bitmap_word_bit_testbit word index :
    bitmap_word_bit word index =
    N.testbit word (N.of_nat index).
  Proof.
    unfold bitmap_word_bit.
    destruct (N.testbit word (N.of_nat index)) eqn:Hbit.
    {
      destruct (N.eqb (N.land word (2 ^ N.of_nat index)) 0)
        eqn:Hland; [| reflexivity].
      apply N.eqb_eq in Hland.
      pose proof
        (f_equal
           (fun value => N.testbit value (N.of_nat index))
           Hland) as Htest.
      rewrite N.land_spec in Htest.
      rewrite N.pow2_bits_true in Htest.
      rewrite Bool.andb_true_r in Htest.
      rewrite Hbit in Htest.
      discriminate.
    }
    destruct (N.eqb (N.land word (2 ^ N.of_nat index)) 0)
      eqn:Hland; [reflexivity |].
    exfalso.
    apply N.eqb_neq in Hland.
    apply Hland.
    apply N.bits_inj_0.
    intro bit.
    rewrite N.land_spec.
    rewrite N.pow2_bits_eqb.
    destruct (N.eqb (N.of_nat index) bit) eqn:Heq.
    {
      apply N.eqb_eq in Heq.
      subst bit.
      now rewrite Hbit.
    }
    now rewrite Bool.andb_false_r.
  Qed.

  Lemma bitmap_to_N_testbit_N bm bit :
    N.testbit (bitmap_to_N bm) bit =
    nth (N.to_nat bit) bm false.
  Proof.
    rewrite <- (N2Nat.id bit) at 1.
    apply bitmap_to_N_testbit_nat.
  Qed.

  Lemma pair_bit_mask_testbit index bit :
    N.testbit (pair_bit_mask index) bit =
    N.eqb (N.of_nat index) bit.
  Proof.
    unfold pair_bit_mask.
    apply N.pow2_bits_eqb.
  Qed.

  Lemma pair_bitmap_prefix_testbit fuel slot_bitmap bit :
    N.testbit (pair_bitmap_prefix fuel slot_bitmap) bit =
    if N.ltb bit (N.of_nat fuel)
    then
      negb
        (N.eqb
           (N.land slot_bitmap
              (pair_slot_mask (N.to_nat bit)))
           0)
    else false.
  Proof.
    revert bit.
    induction fuel as [| fuel IH]; intro bit.
    {
      simpl.
      destruct (N.ltb bit 0) eqn:Hlt; [| reflexivity].
      apply N.ltb_lt in Hlt.
      lia.
    }
    simpl.
    destruct
      (N.eqb
         (N.land slot_bitmap (pair_slot_mask fuel))
         0) eqn:Hoccupied.
    {
      rewrite IH.
      destruct (N.ltb bit (N.of_nat fuel)) eqn:Hlt_fuel.
      {
        apply N.ltb_lt in Hlt_fuel.
        replace
          (bit <?
           N.pos (Pos.of_succ_nat fuel))%N
          with true.
        2: {
          symmetry.
          apply N.ltb_lt.
          replace (N.pos (Pos.of_succ_nat fuel))
            with (N.succ (N.of_nat fuel)) by lia.
          lia.
        }
        reflexivity.
      }
      apply N.ltb_ge in Hlt_fuel.
      destruct (N.eq_dec bit (N.of_nat fuel)) as [Heq | Hneq].
      {
        subst bit.
        rewrite Nat2N.id.
        rewrite Hoccupied.
        replace
          (N.of_nat fuel <?
           N.pos (Pos.of_succ_nat fuel))%N
          with true.
        2: {
          symmetry.
          apply N.ltb_lt.
          replace (N.pos (Pos.of_succ_nat fuel))
            with (N.succ (N.of_nat fuel)) by lia.
          lia.
        }
        reflexivity.
      }
      replace
        (bit <?
         N.pos (Pos.of_succ_nat fuel))%N
        with false.
      2: {
        symmetry.
        apply N.ltb_ge.
        replace (N.pos (Pos.of_succ_nat fuel))
          with (N.succ (N.of_nat fuel)) by lia.
        lia.
      }
      reflexivity.
    }
    rewrite N.lor_spec.
    rewrite IH.
    rewrite pair_bit_mask_testbit.
    destruct (N.ltb bit (N.of_nat fuel)) eqn:Hlt_fuel.
    {
      apply N.ltb_lt in Hlt_fuel.
      replace (N.of_nat fuel =? bit)%N with false
        by (symmetry; apply N.eqb_neq; lia).
      rewrite Bool.orb_false_r.
      replace
        (bit <?
         N.pos (Pos.of_succ_nat fuel))%N
        with true.
      2: {
        symmetry.
        apply N.ltb_lt.
        replace (N.pos (Pos.of_succ_nat fuel))
          with (N.succ (N.of_nat fuel)) by lia.
        lia.
      }
      reflexivity.
    }
    apply N.ltb_ge in Hlt_fuel.
    destruct (N.eq_dec bit (N.of_nat fuel)) as [Heq | Hneq].
    {
      subst bit.
      rewrite N.eqb_refl.
      simpl.
      rewrite Nat2N.id.
      rewrite Hoccupied.
      replace
        (N.of_nat fuel <?
         N.pos (Pos.of_succ_nat fuel))%N
        with true.
      2: {
        symmetry.
        apply N.ltb_lt.
        replace (N.pos (Pos.of_succ_nat fuel))
          with (N.succ (N.of_nat fuel)) by lia.
        lia.
      }
      reflexivity.
    }
    replace (N.of_nat fuel =? bit)%N with false
      by (symmetry; apply N.eqb_neq; lia).
    simpl.
    replace
      (bit <?
       N.pos (Pos.of_succ_nat fuel))%N
      with false.
    2: {
      symmetry.
      apply N.ltb_ge.
      replace (N.pos (Pos.of_succ_nat fuel))
        with (N.succ (N.of_nat fuel)) by lia.
      lia.
    }
    reflexivity.
  Qed.

  Lemma pair_bitmap_from_slot_bitmap_length_even bm n :
    length bm = (2 * n)%nat ->
    length (pair_bitmap_from_slot_bitmap bm) = n.
  Proof.
    revert bm.
    induction n as [| n IH]; intros bm Hlen.
    { destruct bm as [| first [| second rest]]; simpl in *; lia. }
    destruct bm as [| first [| second rest]];
      simpl in Hlen; [lia | lia |].
    simpl.
    rewrite IH.
    2: {
      lia.
    }
    lia.
  Qed.

  Lemma pair_bitmap_from_slot_bitmap_nth bm index :
    nth index (pair_bitmap_from_slot_bitmap bm) false =
    (nth (2 * index) bm false ||
     nth (2 * index + 1) bm false)%bool.
  Proof.
    revert bm index.
    fix IH 1.
    intros bm index.
    destruct bm as [| first [| second rest]];
      destruct index as [| index]; simpl.
    { reflexivity. }
    { reflexivity. }
    { destruct first; reflexivity. }
    { destruct index; reflexivity. }
    { reflexivity. }
    replace (2 * S index)%nat with (S (S (2 * index))) by lia.
    replace (2 * S index + 1)%nat
      with (S (S (2 * index + 1))) by lia.
    simpl.
    replace (index + S (index + 0))%nat
      with (S (2 * index)) by lia.
    replace (index + S (index + 0) + 1)%nat
      with (S (2 * index + 1)) by lia.
    simpl.
    apply IH.
  Qed.

  Lemma pair_bitmap_word_bitmap_to_N bm :
    length bm = page_slot_count ->
    pair_bitmap_word (bitmap_to_N bm) =
    bitmap_to_N (pair_bitmap_from_slot_bitmap bm).
  Proof.
    intro Hlen.
    apply N.bits_inj.
    intro bit.
    unfold pair_bitmap_word.
    rewrite pair_bitmap_prefix_testbit.
    destruct (N.ltb bit (N.of_nat page_pair_count)) eqn:Hlt.
    {
      apply N.ltb_lt in Hlt.
      rewrite bitmap_to_N_testbit_N.
      rewrite pair_bitmap_from_slot_bitmap_nth.
      rewrite pair_slot_mask_occupied_bit.
      rewrite !bitmap_to_N_testbit_N.
      replace (N.to_nat (2 * N.of_nat (N.to_nat bit)))%nat
        with (2 * N.to_nat bit)%nat by lia.
      replace (N.to_nat (2 * N.of_nat (N.to_nat bit) + 1))%nat
        with (2 * N.to_nat bit + 1)%nat by lia.
      reflexivity.
    }
    {
      rewrite bitmap_to_N_testbit_N.
      symmetry.
      apply nth_overflow.
      pose proof
        (pair_bitmap_from_slot_bitmap_length_even
           bm page_pair_count) as Hpair_len.
      assert (Hbm_len : length bm = (2 * page_pair_count)%nat).
      {
        unfold page_slot_count, page_pair_count in *.
        lia.
      }
      specialize (Hpair_len Hbm_len).
      rewrite Hpair_len.
      apply N.ltb_ge in Hlt.
      lia.
    }
  Qed.

  Lemma fold_live_nodes_bitmap_word_testbit_nat nodes acc index :
    N.testbit
      (fold_left
         (fun bm node => N.lor bm (2 ^ N.of_nat node.(live_index)))
         nodes acc)
      (N.of_nat index) =
    N.testbit acc (N.of_nat index) ||
    existsb
      (fun node => Nat.eqb index node.(live_index))
      nodes.
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
        (N.of_nat node.(live_index) =? N.of_nat index)%N =
        Nat.eqb index node.(live_index)).
    {
      destruct (Nat.eqb index node.(live_index)) eqn:Hnat.
      {
        apply Nat.eqb_eq in Hnat.
        subst index.
        now rewrite N.eqb_refl.
      }
      apply Nat.eqb_neq in Hnat.
      apply N.eqb_neq.
      lia.
    }
    rewrite Heqb.
    destruct (N.testbit acc (N.of_nat index));
      destruct (Nat.eqb index node.(live_index));
      destruct
        (existsb
           (fun node0 : live_node =>
              Nat.eqb index node0.(live_index)) rest);
      reflexivity.
  Qed.

  Lemma live_nodes_bitmap_word_testbit_nat nodes index :
    N.testbit (live_nodes_bitmap_word nodes) (N.of_nat index) =
    existsb
      (fun node => Nat.eqb index node.(live_index))
      nodes.
  Proof.
    unfold live_nodes_bitmap_word.
    rewrite fold_live_nodes_bitmap_word_testbit_nat.
    reflexivity.
  Qed.

  Lemma nat_ltb_true n m :
    (n < m)%nat -> (n <? m)%nat = true.
  Proof.
    apply (proj2 (Nat.ltb_lt n m)).
  Qed.

  Lemma nat_ltb_false n m :
    (m <= n)%nat -> (n <? m)%nat = false.
  Proof.
    apply (proj2 (Nat.ltb_ge n m)).
  Qed.

  Lemma nat_eqb_false n m :
    n <> m -> (n =? m)%nat = false.
  Proof.
    apply (proj2 (Nat.eqb_neq n m)).
  Qed.

  Lemma initial_nodes_existsb_nat next_index pairs index :
    existsb
      (fun node => Nat.eqb index node.(live_index))
      (initial_nodes_from_pair_options next_index pairs) =
    if Nat.ltb index next_index
    then false
    else nth (index - next_index) (pair_option_bitmap pairs) false.
  Proof.
    revert next_index index.
    induction pairs as [| [pair_value |] rest IH];
      intros next_index index; simpl.
    {
      destruct (Nat.ltb index next_index);
        destruct (index - next_index)%nat; reflexivity.
    }
    {
      destruct (Nat.lt_ge_cases index next_index) as [Hlt | Hge].
      {
        destruct (Nat.ltb index next_index) eqn:Hltb;
          [| pose proof (proj2 (Nat.ltb_lt index next_index) Hlt)
               as Hlt_true;
             rewrite Hltb in Hlt_true;
             discriminate].
        destruct (index =? next_index)%nat eqn:Heqb.
        { pose proof (proj2 (Nat.eqb_neq index next_index) ltac:(lia))
            as Heq_false;
          rewrite Heqb in Heq_false;
          discriminate. }
        rewrite IH.
        destruct (Nat.ltb index (S next_index)) eqn:Hltb';
          [reflexivity |].
        pose proof (proj2 (Nat.ltb_lt index (S next_index)) ltac:(lia))
          as Hlt_true;
        rewrite Hltb' in Hlt_true;
        discriminate.
      }
      destruct (Nat.eq_dec index next_index) as [Heq | Hneq].
      {
        subst index.
        rewrite Nat.eqb_refl.
        simpl.
        destruct (Nat.ltb next_index next_index) eqn:Hltb.
        {
          pose proof
            (proj2 (Nat.ltb_ge next_index next_index) ltac:(lia))
            as Hlt_false;
          rewrite Hltb in Hlt_false;
          discriminate.
        }
        replace (next_index - next_index)%nat with 0%nat by lia.
        reflexivity.
      }
      assert (Hgt : (next_index < index)%nat) by lia.
      destruct (Nat.ltb index next_index) eqn:Hltb.
      {
        pose proof (proj2 (Nat.ltb_ge index next_index) ltac:(lia))
          as Hlt_false;
        rewrite Hltb in Hlt_false;
        discriminate.
      }
      destruct (index =? next_index)%nat eqn:Heqb.
      { pose proof (proj2 (Nat.eqb_neq index next_index) ltac:(lia))
          as Heq_false;
        rewrite Heqb in Heq_false;
        discriminate. }
      rewrite IH.
      destruct (Nat.ltb index (S next_index)) eqn:Hltb'.
      {
        pose proof
          (proj2 (Nat.ltb_ge index (S next_index)) ltac:(lia))
          as Hlt_false;
        rewrite Hltb' in Hlt_false;
        discriminate.
      }
      replace (index - next_index)%nat
        with (S (index - S next_index)) by lia.
      reflexivity.
    }
    {
      destruct (Nat.lt_ge_cases index next_index) as [Hlt | Hge].
      {
        destruct (Nat.ltb index next_index) eqn:Hltb;
          [| pose proof (proj2 (Nat.ltb_lt index next_index) Hlt)
               as Hlt_true;
             rewrite Hltb in Hlt_true;
             discriminate].
        rewrite IH.
        destruct (Nat.ltb index (S next_index)) eqn:Hltb';
          [reflexivity |].
        pose proof (proj2 (Nat.ltb_lt index (S next_index)) ltac:(lia))
          as Hlt_true;
        rewrite Hltb' in Hlt_true;
        discriminate.
      }
      destruct (Nat.eq_dec index next_index) as [Heq | Hneq].
      {
        subst index.
        rewrite IH.
        destruct (Nat.ltb next_index (S next_index)) eqn:Hltb;
          [| pose proof
               (proj2 (Nat.ltb_lt next_index (S next_index))
                  ltac:(lia)) as Hlt_true;
             rewrite Hltb in Hlt_true;
             discriminate].
        destruct (Nat.ltb next_index next_index) eqn:Hltb'.
        {
          pose proof
            (proj2 (Nat.ltb_ge next_index next_index) ltac:(lia))
            as Hlt_false;
          rewrite Hltb' in Hlt_false;
          discriminate.
        }
        replace (next_index - next_index)%nat with 0%nat by lia.
        reflexivity.
      }
      assert (Hgt : (next_index < index)%nat) by lia.
      destruct (Nat.ltb index next_index) eqn:Hltb.
      {
        pose proof (proj2 (Nat.ltb_ge index next_index) ltac:(lia))
          as Hlt_false;
        rewrite Hltb in Hlt_false;
        discriminate.
      }
      rewrite IH.
      destruct (Nat.ltb index (S next_index)) eqn:Hltb'.
      {
        pose proof
          (proj2 (Nat.ltb_ge index (S next_index)) ltac:(lia))
          as Hlt_false;
        rewrite Hltb' in Hlt_false;
        discriminate.
      }
      replace (index - next_index)%nat
        with (S (index - S next_index)) by lia.
      reflexivity.
    }
  Qed.

  Lemma live_nodes_bitmap_word_initial_nodes pairs :
    live_nodes_bitmap_word
      (initial_nodes_from_pair_options 0 pairs) =
    bitmap_to_N (pair_option_bitmap pairs).
  Proof.
    apply N.bits_inj.
    intro bit.
    rewrite <- (N2Nat.id bit).
    rewrite live_nodes_bitmap_word_testbit_nat.
    rewrite initial_nodes_existsb_nat.
    simpl.
    rewrite Nat.sub_0_r.
    symmetry.
    apply bitmap_to_N_testbit_nat.
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

  Lemma init_leaf_scratch_model_length page pair_bitmap old_scratch :
    length (init_leaf_scratch_model page pair_bitmap old_scratch) =
    page_pair_count.
  Proof.
    unfold init_leaf_scratch_model.
    rewrite length_map.
    apply seq_length.
  Qed.

  Lemma initial_nodes_from_pair_options_in
      next_index pairs node :
    In node (initial_nodes_from_pair_options next_index pairs) ->
    exists offset pair_value,
      nth_error pairs offset = Some (Some pair_value) /\
      node.(live_index) = (next_index + offset)%nat /\
      node.(live_tree) = TreeLeaf pair_value.
  Proof.
    revert next_index node.
    induction pairs as [| [pair_value |] rest IH];
      intros next_index node Hnode; simpl in Hnode.
    { contradiction. }
    {
      destruct Hnode as [Hhead | Hrest].
      {
        subst node.
        exists 0%nat, pair_value.
        simpl.
        repeat split.
        lia.
      }
      destruct (IH (S next_index) node Hrest)
        as [offset [rest_pair [Hnth [Hindex Htree]]]].
      exists (S offset), rest_pair.
      simpl.
      repeat split; try exact Htree; try exact Hnth.
      lia.
    }
    {
      destruct (IH (S next_index) node Hnode)
        as [offset [rest_pair [Hnth [Hindex Htree]]]].
      exists (S offset), rest_pair.
      simpl.
      repeat split; try exact Htree; try exact Hnth.
      lia.
    }
  Qed.

  Lemma initial_nodes_index_bound pairs node :
    length pairs = page_pair_count ->
    In node (initial_nodes_from_pair_options 0 pairs) ->
    (node.(live_index) < page_pair_count)%nat.
  Proof.
    intros Hlen Hnode.
    pose proof
      (initial_nodes_from_pair_options_in 0 pairs node Hnode)
      as [offset [pair_value [Hnth [Hindex _Htree]]]].
    simpl in Hindex.
    subst offset.
    apply nth_error_split in Hnth
      as [prefix [suffix [Hpairs Hprefix]]].
    subst pairs.
    rewrite app_length in Hlen.
    simpl in Hlen.
    lia.
  Qed.

  Lemma pair_options_page_slots_nth page pair_index pair_value :
    length page = page_slot_count ->
    nth_error (pair_options (page_slots_model page)) pair_index =
    Some (Some pair_value) ->
    pair_value = page_pair_leaf_model page pair_index.
  Proof.
    intro Hlen.
    unfold pair_options.
    rewrite normalize_page_slots_model.
    2: {
      exact Hlen.
    }
    clear Hlen.
    revert page.
    induction pair_index as [| pair_index IH];
      intros page Hnth.
    {
      destruct page as [| first page_rest].
      { simpl in Hnth. discriminate. }
      destruct page_rest as [| second rest].
      { simpl in Hnth. discriminate. }
      simpl in Hnth.
      unfold page_pair_leaf_model.
      simpl.
      unfold page_slot_value_model, slot_present, slot_payload in Hnth.
      destruct (N.eq_dec first 0%N) as [Hfirst | Hfirst];
        destruct (N.eq_dec second 0%N) as [Hsecond | Hsecond];
        simpl in Hnth; try discriminate;
        inversion Hnth; subst pair_value; clear Hnth;
        subst; reflexivity.
    }
    destruct page as [| first page_rest].
    { simpl in Hnth. discriminate. }
    destruct page_rest as [| second rest].
    { simpl in Hnth. discriminate. }
    simpl in Hnth.
    unfold page_slot_value_model, slot_present, slot_payload in Hnth.
    destruct (N.eq_dec first 0%N);
      destruct (N.eq_dec second 0%N);
      simpl in Hnth.
    all:
      specialize (IH rest Hnth);
      unfold page_pair_leaf_model in *;
      replace (2 * S pair_index)%nat
        with (S (S (2 * pair_index))) by lia;
      replace (2 * S pair_index + 1)%nat
        with (S (S (2 * pair_index + 1))) by lia;
      exact IH.
  Qed.

  Definition combine_live_nodes
      (lhs rhs : option live_node) : option live_node :=
    match lhs, rhs with
    | None, None => None
    | Some node, None => Some node
    | None, Some node => Some node
    | Some lhs_node, Some rhs_node =>
        Some
          {|
            live_index := lhs_node.(live_index);
            live_tree :=
              TreeNode lhs_node.(live_tree) rhs_node.(live_tree);
          |}
    end.

  Fixpoint build_live_tree
      (depth start : nat)
      (pairs : list (option blake3model.pair_leaf))
      : option live_node :=
    match depth with
    | O =>
        match pairs with
        | [Some pair_value] =>
            Some
              {|
                live_index := start;
                live_tree := TreeLeaf pair_value;
              |}
        | _ => None
        end
    | S depth' =>
        let width := subtree_width depth' in
        combine_live_nodes
          (build_live_tree depth' start (firstn width pairs))
          (build_live_tree
             depth' (start + width)%nat (skipn width pairs))
    end.

  Lemma combine_live_nodes_tree lhs rhs :
    option_map live_tree (combine_live_nodes lhs rhs) =
    combine_value_trees
      (option_map live_tree lhs)
      (option_map live_tree rhs).
  Proof.
    destruct lhs as [[lhs_index lhs_tree] |];
      destruct rhs as [[rhs_index rhs_tree] |];
      reflexivity.
  Qed.

  Lemma build_live_tree_value_tree depth start pairs :
    option_map live_tree (build_live_tree depth start pairs) =
    build_value_tree depth pairs.
  Proof.
    revert start pairs.
    induction depth as [| depth IH]; intros start pairs.
    {
      destruct pairs as [| [pair_value |] [| extra rest]];
        reflexivity.
    }
    simpl.
    rewrite <- (IH start (firstn (subtree_width depth) pairs)).
    rewrite <-
      (IH (start + subtree_width depth)%nat
         (skipn (subtree_width depth) pairs)).
    apply combine_live_nodes_tree.
  Qed.

  Lemma build_live_tree_some_value_tree
      depth start pairs node :
    build_live_tree depth start pairs = Some node ->
    build_value_tree depth pairs = Some node.(live_tree).
  Proof.
    intro Hlive.
    pose proof (build_live_tree_value_tree depth start pairs) as Htree.
    rewrite Hlive in Htree.
    symmetry.
    exact Htree.
  Qed.

  Lemma subtree_width_pos depth :
    (0 < subtree_width depth)%nat.
  Proof.
    induction depth; simpl; lia.
  Qed.

  Lemma subtree_width_succ depth :
    subtree_width (S depth) = (2 * subtree_width depth)%nat.
  Proof.
    reflexivity.
  Qed.

  Lemma div_exact_interval base width quotient index :
    width <> 0%nat ->
    base = (width * quotient)%nat ->
    (base <= index < base + width)%nat ->
    (index / width = quotient)%nat.
  Proof.
    intros Hwidth Hbase Hbounds.
    symmetry.
    eapply Nat.div_unique with (r := (index - base)%nat).
    { lia. }
    rewrite Hbase.
    lia.
  Qed.

  Lemma build_live_tree_index_bounds depth start pairs node :
    length pairs = subtree_width depth ->
    build_live_tree depth start pairs = Some node ->
    (start <= node.(live_index) <
     start + subtree_width depth)%nat.
  Proof.
    revert start pairs node.
    induction depth as [| depth IH]; intros start pairs node Hlen Hbuild.
    {
      destruct pairs as [| [pair_value |] [| extra rest]];
        simpl in *; try lia; try discriminate.
      inversion Hbuild; subst node; simpl; lia.
    }
    simpl in Hlen, Hbuild.
    set (width := subtree_width depth).
    fold width in Hlen, Hbuild.
    assert (Hleft_len : length (firstn width pairs) = width).
    { rewrite length_firstn. lia. }
    assert (Hright_len : length (skipn width pairs) = width).
    { rewrite length_skipn. lia. }
    destruct (build_live_tree depth start (firstn width pairs))
      as [lhs |] eqn:Hlhs;
      destruct (build_live_tree depth (start + width)%nat (skipn width pairs))
        as [rhs |] eqn:Hrhs;
      simpl in Hbuild; inversion Hbuild; subst node; clear Hbuild.
    all: try (pose proof (IH start (firstn width pairs) lhs Hleft_len Hlhs)
               as Hlhs_bounds; simpl; lia).
    pose proof
      (IH (start + width)%nat (skipn width pairs) rhs Hright_len Hrhs)
      as Hrhs_bounds.
    simpl.
    lia.
  Qed.

  Definition aligned_at (depth start : nat) : Prop :=
    exists quotient,
      start = (subtree_width depth * quotient)%nat.

  Lemma aligned_at_zero depth :
    aligned_at depth 0.
  Proof.
    exists 0%nat.
    lia.
  Qed.

  Lemma aligned_at_next depth start :
    aligned_at (S depth) start ->
    aligned_at (S depth)
      (start + subtree_width (S depth))%nat.
  Proof.
    intros [quotient Hstart].
    exists (S quotient).
    rewrite Hstart.
    lia.
  Qed.

  Lemma build_live_tree_sibling_candidate_true
      depth start lhs_pairs rhs_pairs lhs rhs :
    aligned_at (S depth) start ->
    length lhs_pairs = subtree_width depth ->
    length rhs_pairs = subtree_width depth ->
    build_live_tree depth start lhs_pairs = Some lhs ->
    build_live_tree depth
      (start + subtree_width depth)%nat rhs_pairs = Some rhs ->
    sibling_candidate depth lhs.(live_index) rhs.(live_index) = true.
  Proof.
    intros [quotient Hstart] Hlhs_len Hrhs_len Hlhs Hrhs.
    pose proof
      (build_live_tree_index_bounds depth start lhs_pairs lhs
         Hlhs_len Hlhs) as Hlhs_bounds.
    pose proof
      (build_live_tree_index_bounds
         depth (start + subtree_width depth)%nat rhs_pairs rhs
         Hrhs_len Hrhs) as Hrhs_bounds.
    unfold sibling_candidate, same_parent_at_level,
      index_bit_is_zero.
    set (width := subtree_width depth).
    assert (Hwidth_pos : width <> 0%nat)
      by (subst width; pose proof (subtree_width_pos depth); lia).
    assert
      (Hparent_width :
        subtree_width (S depth) = (2 * width)%nat)
      by (subst width; reflexivity).
    assert
      (Hparent_nonzero : subtree_width (S depth) <> 0%nat)
      by (rewrite Hparent_width; lia).
    assert
      (Hstart_parent :
        start = (subtree_width (S depth) * quotient)%nat)
      by exact Hstart.
    assert
      (Hlhs_parent :
        (lhs.(live_index) / subtree_width (S depth) = quotient)%nat).
    {
      change ((lhs.(live_index) / subtree_width (S depth))%nat = quotient).
      eapply
        (div_exact_interval
           start (subtree_width (S depth)) quotient
           lhs.(live_index)); eauto.
      rewrite Hparent_width.
      lia.
    }
    assert
      (Hrhs_parent :
        (rhs.(live_index) / subtree_width (S depth) = quotient)%nat).
    {
      change ((rhs.(live_index) / subtree_width (S depth))%nat = quotient).
      eapply
        (div_exact_interval
           start (subtree_width (S depth)) quotient
           rhs.(live_index)); eauto.
      rewrite Hparent_width.
      lia.
    }
    assert
      (Hlhs_bit :
        (lhs.(live_index) / width = 2 * quotient)%nat).
    {
      change ((lhs.(live_index) / width)%nat = (2 * quotient)%nat).
      eapply
        (div_exact_interval
           start width (2 * quotient) lhs.(live_index)).
      { exact Hwidth_pos. }
      {
        rewrite Hstart_parent.
        rewrite Hparent_width.
        nia.
      }
      lia.
    }
    rewrite Hlhs_parent.
    rewrite Hrhs_parent.
    rewrite Nat.eqb_refl.
    rewrite Hlhs_bit.
    rewrite Nat.even_even.
    reflexivity.
  Qed.

  Lemma build_live_tree_no_sibling_with_later
      depth start current_pairs current later :
    aligned_at (S depth) start ->
    length current_pairs = subtree_width (S depth) ->
    build_live_tree (S depth) start current_pairs = Some current ->
    (start + subtree_width (S depth) <= later.(live_index))%nat ->
    sibling_candidate depth current.(live_index) later.(live_index) =
    false.
  Proof.
    intros [quotient Hstart] Hcurrent_len Hcurrent Hlater_lower.
    pose proof
      (build_live_tree_index_bounds
         (S depth) start current_pairs current Hcurrent_len Hcurrent)
      as Hcurrent_bounds.
    unfold sibling_candidate, same_parent_at_level.
    set (parent_width := subtree_width (S depth)).
    assert (Hparent_pos : parent_width <> 0%nat)
      by (subst parent_width; pose proof (subtree_width_pos (S depth)); lia).
    assert
      (Hcurrent_parent :
        (current.(live_index) / parent_width = quotient)%nat).
    {
      change ((current.(live_index) / parent_width)%nat = quotient).
      eapply
        (div_exact_interval
           start parent_width quotient current.(live_index)).
      { exact Hparent_pos. }
      { subst parent_width. exact Hstart. }
      lia.
    }
    assert
      (Hlater_parent :
        (S quotient <= later.(live_index) / parent_width)%nat).
    {
      eapply Nat.div_le_lower_bound.
      { exact Hparent_pos. }
      subst parent_width.
      rewrite Hstart in Hlater_lower.
      lia.
    }
    rewrite Hcurrent_parent.
    replace (quotient =? later.(live_index) / parent_width)%nat
      with false.
    { reflexivity. }
    symmetry.
    apply Nat.eqb_neq.
    lia.
  Qed.

  Fixpoint build_live_forest
      (fuel depth start : nat)
      (pairs : list (option blake3model.pair_leaf))
      : list live_node :=
    match fuel with
    | O => []
    | S fuel' =>
        let width := subtree_width depth in
        let rest :=
          build_live_forest
            fuel' depth (start + width)%nat (skipn width pairs) in
        match build_live_tree depth start (firstn width pairs) with
        | Some node => node :: rest
        | None => rest
        end
    end.

  Lemma build_live_forest_zero pairs depth start :
    build_live_forest 0 depth start pairs = [].
  Proof.
    reflexivity.
  Qed.

 Lemma initial_nodes_from_pair_options_app start lhs rhs :
    initial_nodes_from_pair_options start (lhs ++ rhs) =
    initial_nodes_from_pair_options start lhs ++
    initial_nodes_from_pair_options (start + length lhs)%nat rhs.
  Proof.
    revert start.
    induction lhs as [| [pair_value |] rest IH]; intro start; simpl.
    { replace (start + 0)%nat with start by lia.
      reflexivity. }
    {
      rewrite IH.
      replace (start + S (length rest))%nat
        with (S start + length rest)%nat by lia.
      reflexivity.
    }
    {
      rewrite IH.
      replace (start + S (length rest))%nat
        with (S start + length rest)%nat by lia.
      reflexivity.
    }
  Qed.

  Lemma build_live_forest_depth_zero fuel start pairs :
    length pairs = fuel ->
    build_live_forest fuel 0 start pairs =
    initial_nodes_from_pair_options start pairs.
  Proof.
    revert start pairs.
    induction fuel as [| fuel IH]; intros start pairs Hlen.
    { destruct pairs; simpl in *; [reflexivity | lia]. }
    destruct pairs as [| [pair_value |] rest]; simpl in Hlen; [lia | |].
    {
      simpl.
      change (skipn 0 rest) with rest.
      replace (start + 1)%nat with (S start) by lia.
      rewrite (IH (S start) rest ltac:(lia)).
      reflexivity.
    }
    {
      simpl.
      change (skipn 0 rest) with rest.
      replace (start + 1)%nat with (S start) by lia.
      rewrite (IH (S start) rest ltac:(lia)).
      reflexivity.
    }
  Qed.

  Lemma build_live_forest_in_bounds
      fuel depth start pairs node :
    length pairs = (fuel * subtree_width depth)%nat ->
    In node (build_live_forest fuel depth start pairs) ->
    (start <= node.(live_index) <
     start + fuel * subtree_width depth)%nat.
  Proof.
    revert start pairs node.
    induction fuel as [| fuel IH]; intros start pairs node Hlen Hin.
    { simpl in Hin; contradiction. }
    simpl in Hin.
    set (width := subtree_width depth).
    set (head := build_live_tree depth start (firstn width pairs)) in *.
    set
      (tail :=
         build_live_forest fuel depth (start + width)%nat
           (skipn width pairs)) in *.
    fold width in Hlen, Hin.
    fold head in Hin.
    fold tail in Hin.
    destruct head as [head_node |] eqn:Hhead.
    {
      destruct Hin as [Hnode | Htail].
      {
        subst node.
        subst head.
        eapply build_live_tree_index_bounds in Hhead.
        2: {
          rewrite length_firstn.
          subst width.
          pose proof (subtree_width_pos depth).
          lia.
        }
        simpl in Hhead.
        lia.
      }
      subst tail.
      eapply IH in Htail.
      2: {
        rewrite length_skipn.
        subst width.
        pose proof (subtree_width_pos depth).
        lia.
      }
      lia.
    }
    subst tail.
    eapply IH in Hin.
    2: {
      rewrite length_skipn.
      subst width.
      pose proof (subtree_width_pos depth).
      lia.
    }
    lia.
  Qed.

  Lemma build_live_tree_first_parent_chunk depth start pairs :
    build_live_tree
      (S depth) start (firstn (subtree_width (S depth)) pairs) =
    combine_live_nodes
      (build_live_tree depth start
         (firstn (subtree_width depth) pairs))
      (build_live_tree depth
         (start + subtree_width depth)%nat
         (firstn (subtree_width depth)
            (skipn (subtree_width depth) pairs))).
  Proof.
    simpl.
    set (width := subtree_width depth).
    fold width.
    replace (subtree_width (S depth)) with (width + width)%nat.
    2: {
      subst width.
      simpl.
      lia.
    }
    replace (width + (width + 0))%nat with (width + width)%nat
      by lia.
    rewrite firstn_firstn.
    replace (Nat.min width (width + width)) with width by lia.
    rewrite skipn_firstn_comm.
    replace (width + width - width)%nat with width by lia.
    reflexivity.
  Qed.

  Lemma build_live_forest_step
      fuel depth start pairs :
    aligned_at (S depth) start ->
    length pairs =
      (fuel * subtree_width (S depth))%nat ->
    merge_level depth
      (build_live_forest (2 * fuel) depth start pairs) =
    build_live_forest fuel (S depth) start pairs.
  Proof.
    revert start pairs.
    induction fuel as [| fuel IH]; intros start pairs Haligned Hlen.
    {
      simpl.
      reflexivity.
    }
    simpl.
    set (width := subtree_width depth).
    assert (Hwidth_pos : (0 < width)%nat)
      by (subst width; apply subtree_width_pos).
    assert
      (Hparent_width :
        subtree_width (S depth) = (2 * width)%nat)
      by (subst width; reflexivity).
    assert
      (Hleft_len : length (firstn width pairs) = width).
    { rewrite length_firstn. rewrite Hparent_width in Hlen. lia. }
    assert
      (Hright_len :
        length (firstn width (skipn width pairs)) = width).
    {
      rewrite length_firstn.
      rewrite length_skipn.
      rewrite Hparent_width in Hlen.
      lia.
    }
    assert
      (Hcurrent_len :
        length (firstn (subtree_width (S depth)) pairs) =
        subtree_width (S depth)).
    {
      rewrite length_firstn.
      lia.
    }
    assert
      (Htail_len :
        length (skipn (subtree_width (S depth)) pairs) =
        (fuel * subtree_width (S depth))%nat).
    {
      rewrite length_skipn.
      lia.
    }
    pose proof (aligned_at_next depth start Haligned) as Haligned_tail.
    replace (width + (width + 0))%nat with (width + width)%nat
      by lia.
    rewrite firstn_firstn.
    replace (Nat.min width (width + width)) with width by lia.
    rewrite skipn_firstn_comm.
    replace (width + width - width)%nat with width by lia.
    rewrite <- skipn_skipn.
    replace (width + width)%nat with (subtree_width (S depth))
      by (rewrite Hparent_width; lia).
    set
      (lhs :=
         build_live_tree depth start
           (firstn width pairs)).
    set
      (rhs :=
         build_live_tree depth (start + width)%nat
           (firstn width (skipn width pairs))).
    set
      (tail_pairs := skipn (subtree_width (S depth)) pairs).
    set
      (tail :=
         build_live_forest (2 * fuel) depth
           (start + subtree_width (S depth))%nat tail_pairs).
    replace (fuel + S (fuel + 0))%nat with (S (2 * fuel))%nat
      by lia.
    simpl.
    fold width.
    replace (fuel + (fuel + 0))%nat with (2 * fuel)%nat
      by lia.
    replace (start + width + width)%nat
      with (start + subtree_width (S depth))%nat
      by (rewrite Hparent_width; lia).
    rewrite skipn_skipn.
    replace (width + width)%nat with (subtree_width (S depth))
      by (rewrite Hparent_width; lia).
    fold rhs.
    fold tail_pairs.
    fold tail.
    assert
      (Htail_step :
        merge_level depth tail =
        build_live_forest fuel (S depth)
          (start + subtree_width (S depth))%nat tail_pairs).
    {
      subst tail tail_pairs.
      apply IH.
      { exact Haligned_tail. }
      { exact Htail_len. }
    }
    destruct lhs as [lhs_node |] eqn:Hlhs;
      destruct rhs as [rhs_node |] eqn:Hrhs; simpl.
    {
      rewrite
        (build_live_tree_sibling_candidate_true
           depth start
           (firstn width pairs)
           (firstn width (skipn width pairs))
           lhs_node rhs_node Haligned Hleft_len Hright_len).
      2: {
        subst lhs.
        exact Hlhs.
      }
      2: {
        subst rhs.
        exact Hrhs.
      }
      simpl.
      rewrite Htail_step.
      reflexivity.
    }
    {
      destruct tail as [| next rest] eqn:Htail_cases.
      {
        simpl in Htail_step.
        replace (start + (width + (width + 0)))%nat
          with (start + subtree_width (S depth))%nat
          by (rewrite Hparent_width; lia).
        replace (start + (width + (width + 0)))%nat
          with (start + subtree_width (S depth))%nat in Htail_step
          by (rewrite Hparent_width; lia).
        replace
          (start + (subtree_width depth + (subtree_width depth + 0)))%nat
          with (start + subtree_width (S depth))%nat in Htail_step
          by (simpl; lia).
        rewrite <- Htail_step.
        reflexivity.
      }
      simpl.
      replace
        (sibling_candidate depth lhs_node.(live_index)
           next.(live_index))
        with false.
      2: {
        symmetry.
        eapply build_live_tree_no_sibling_with_later.
        { exact Haligned. }
        { exact Hcurrent_len. }
        {
          rewrite build_live_tree_first_parent_chunk.
          subst lhs rhs.
          rewrite Hlhs.
          rewrite Hrhs.
          reflexivity.
        }
        subst tail.
        pose proof
          (build_live_forest_in_bounds
             (2 * fuel) depth
             (start + subtree_width (S depth))%nat
             tail_pairs next) as Hnext.
        rewrite Htail_cases in Hnext.
        assert
          (Htail_len_child :
            length tail_pairs =
            (2 * fuel * subtree_width depth)%nat).
        {
          subst tail_pairs.
          rewrite Htail_len.
          rewrite Hparent_width.
          nia.
        }
        specialize (Hnext Htail_len_child).
        assert (Hin_next : In next (next :: rest)) by (simpl; auto).
        specialize (Hnext Hin_next).
        lia.
      }
      replace (start + (width + (width + 0)))%nat
        with (start + subtree_width (S depth))%nat
        by (rewrite Hparent_width; lia).
      change
        (lhs_node :: merge_level depth (next :: rest) =
         lhs_node ::
         build_live_forest fuel (S depth)
           (start + subtree_width (S depth))%nat tail_pairs).
      rewrite Htail_step.
      reflexivity.
    }
    {
      destruct tail as [| next rest] eqn:Htail_cases.
      {
        simpl in Htail_step.
        replace (start + (width + (width + 0)))%nat
          with (start + subtree_width (S depth))%nat
          by (rewrite Hparent_width; lia).
        replace (start + (width + (width + 0)))%nat
          with (start + subtree_width (S depth))%nat in Htail_step
          by (rewrite Hparent_width; lia).
        replace
          (start + (subtree_width depth + (subtree_width depth + 0)))%nat
          with (start + subtree_width (S depth))%nat in Htail_step
          by (simpl; lia).
        rewrite <- Htail_step.
        reflexivity.
      }
      simpl.
      replace
        (sibling_candidate depth rhs_node.(live_index)
           next.(live_index))
        with false.
      2: {
        symmetry.
        eapply build_live_tree_no_sibling_with_later.
        { exact Haligned. }
        { exact Hcurrent_len. }
        {
          rewrite build_live_tree_first_parent_chunk.
          subst lhs rhs.
          rewrite Hlhs.
          rewrite Hrhs.
          reflexivity.
        }
        subst tail.
        pose proof
          (build_live_forest_in_bounds
             (2 * fuel) depth
             (start + subtree_width (S depth))%nat
             tail_pairs next) as Hnext.
        rewrite Htail_cases in Hnext.
        assert
          (Htail_len_child :
            length tail_pairs =
            (2 * fuel * subtree_width depth)%nat).
        {
          subst tail_pairs.
          rewrite Htail_len.
          rewrite Hparent_width.
          nia.
        }
        specialize (Hnext Htail_len_child).
        assert (Hin_next : In next (next :: rest)) by (simpl; auto).
        specialize (Hnext Hin_next).
        lia.
      }
      replace (start + (width + (width + 0)))%nat
        with (start + subtree_width (S depth))%nat
        by (rewrite Hparent_width; lia).
      change
        (rhs_node :: merge_level depth (next :: rest) =
         rhs_node ::
         build_live_forest fuel (S depth)
           (start + subtree_width (S depth))%nat tail_pairs).
      rewrite Htail_step.
      reflexivity.
    }
    {
      exact Htail_step.
    }
  Qed.

  Lemma merge_prefix_initial_nodes_build_live_forest
      depth fuel start pairs :
    aligned_at depth start ->
    length pairs = (fuel * subtree_width depth)%nat ->
    merge_prefix depth (initial_nodes_from_pair_options start pairs) =
    build_live_forest fuel depth start pairs.
  Proof.
    revert fuel start pairs.
    induction depth as [| depth IH]; intros fuel start pairs Haligned Hlen.
    {
      simpl.
      symmetry.
      apply build_live_forest_depth_zero.
      simpl in Hlen.
      lia.
    }
    simpl in Hlen.
    rewrite <- merge_prefix_succ.
    assert
      (Hprefix :
        merge_prefix depth
          (initial_nodes_from_pair_options start pairs) =
        build_live_forest (2 * fuel) depth start pairs).
    {
      apply IH.
      {
        destruct Haligned as [quotient Hstart].
        exists (2 * quotient)%nat.
        rewrite Hstart.
        simpl.
        nia.
      }
      nia.
    }
    rewrite Hprefix.
    apply build_live_forest_step.
    { exact Haligned. }
    { exact Hlen. }
  Qed.

  Lemma build_live_forest_one depth start pairs :
    length pairs = subtree_width depth ->
    build_live_forest 1 depth start pairs =
    match build_live_tree depth start pairs with
    | Some node => [node]
    | None => []
    end.
  Proof.
    intro Hlen.
    simpl.
    rewrite firstn_all2.
    2: {
      lia.
    }
    destruct (build_live_tree depth start pairs); reflexivity.
  Qed.

  Lemma merge_prefix_page_initial_build_live_tree page :
    length page = page_slot_count ->
    merge_prefix 6 (page_initial_live_nodes page) =
    match
      build_live_tree 6 0
        (pair_options (page_slots_model page))
    with
    | Some node => [node]
    | None => []
    end.
  Proof.
    intro Hlen.
    rewrite page_initial_live_nodes_eq.
    rewrite
      (merge_prefix_initial_nodes_build_live_forest
         6 1 0 (pair_options (page_slots_model page))).
    {
      apply build_live_forest_one.
      apply pair_options_length.
    }
    { apply aligned_at_zero. }
    rewrite pair_options_length.
    reflexivity.
  Qed.

  Lemma build_live_tree_from_value_tree depth start pairs tree :
    build_value_tree depth pairs = Some tree ->
    exists node,
      build_live_tree depth start pairs = Some node /\
      node.(live_tree) = tree.
  Proof.
    intro Htree.
    pose proof (build_live_tree_value_tree depth start pairs) as Hlive_tree.
    destruct (build_live_tree depth start pairs) as [node |] eqn:Hlive.
    {
      exists node.
      split; [reflexivity |].
      rewrite Htree in Hlive_tree.
      now inversion Hlive_tree.
    }
    rewrite Htree in Hlive_tree.
    discriminate.
  Qed.

  Transparent
    countr_zero64 countr_zero_fuel popcount64 popcount_fuel.

  Lemma countr_zero64_pow2_small index :
    (index < 64)%nat ->
    countr_zero64 (2 ^ N.of_nat index)%N = N.of_nat index.
  Proof.
    intro Hindex.
    unfold countr_zero64.
    do 64
      (destruct index as [| index];
       [vm_compute; reflexivity | simpl in Hindex]).
    lia.
  Qed.

  Lemma live_nodes_bitmap_word_singleton node :
    live_nodes_bitmap_word [node] =
    (2 ^ N.of_nat node.(live_index))%N.
  Proof.
    unfold live_nodes_bitmap_word.
    simpl.
    apply N.lor_0_l.
  Qed.

  Lemma popcount_fuel_testbit_one fuel word index :
    (index < fuel)%nat ->
    N.testbit word (N.of_nat index) = true ->
    (1 <= popcount_fuel fuel word)%N.
  Proof.
    revert word index.
    induction fuel as [| fuel IH]; intros word index Hindex Hbit.
    { lia. }
    destruct index as [| index].
    {
      simpl in Hbit |- *.
      rewrite N.bit0_odd in Hbit.
      rewrite Hbit.
      lia.
    }
    simpl in Hindex |- *.
    assert
      (Hshift_bit :
        N.testbit (N.shiftr word 1) (N.of_nat index) = true).
    {
      rewrite N.shiftr_spec'.
      replace (N.of_nat index + 1)%N
        with (N.of_nat (S index)) by lia.
      exact Hbit.
    }
    pose proof (IH (N.shiftr word 1) index ltac:(lia) Hshift_bit)
      as Hone.
    destruct (N.odd word); lia.
  Qed.

  Lemma popcount_fuel_testbit_two fuel word lhs rhs :
    (lhs < fuel)%nat ->
    (rhs < fuel)%nat ->
    lhs <> rhs ->
    N.testbit word (N.of_nat lhs) = true ->
    N.testbit word (N.of_nat rhs) = true ->
    (2 <= popcount_fuel fuel word)%N.
  Proof.
    revert word lhs rhs.
    induction fuel as [| fuel IH];
      intros word lhs rhs Hlhs Hrhs Hneq Hlhs_bit Hrhs_bit.
    { lia. }
    destruct lhs as [| lhs]; destruct rhs as [| rhs].
    { contradiction. }
    {
      simpl in Hlhs_bit.
      rewrite N.bit0_odd in Hlhs_bit.
      simpl in Hrhs.
      assert
        (Hshift_rhs :
          N.testbit (N.shiftr word 1) (N.of_nat rhs) = true).
      {
        rewrite N.shiftr_spec'.
        replace (N.of_nat rhs + 1)%N
          with (N.of_nat (S rhs)) by lia.
        exact Hrhs_bit.
      }
      pose proof
        (popcount_fuel_testbit_one
           fuel (N.shiftr word 1) rhs ltac:(lia) Hshift_rhs)
        as Hone.
      simpl.
      rewrite Hlhs_bit.
      lia.
    }
    {
      simpl in Hrhs_bit.
      rewrite N.bit0_odd in Hrhs_bit.
      simpl in Hlhs.
      assert
        (Hshift_lhs :
          N.testbit (N.shiftr word 1) (N.of_nat lhs) = true).
      {
        rewrite N.shiftr_spec'.
        replace (N.of_nat lhs + 1)%N
          with (N.of_nat (S lhs)) by lia.
        exact Hlhs_bit.
      }
      pose proof
        (popcount_fuel_testbit_one
           fuel (N.shiftr word 1) lhs ltac:(lia) Hshift_lhs)
        as Hone.
      simpl.
      rewrite Hrhs_bit.
      destruct (N.odd word); lia.
    }
    simpl in Hlhs, Hrhs.
    assert
      (Hshift_lhs :
        N.testbit (N.shiftr word 1) (N.of_nat lhs) = true).
    {
      rewrite N.shiftr_spec'.
      replace (N.of_nat lhs + 1)%N
        with (N.of_nat (S lhs)) by lia.
      exact Hlhs_bit.
    }
    assert
      (Hshift_rhs :
        N.testbit (N.shiftr word 1) (N.of_nat rhs) = true).
    {
      rewrite N.shiftr_spec'.
      replace (N.of_nat rhs + 1)%N
        with (N.of_nat (S rhs)) by lia.
      exact Hrhs_bit.
    }
    pose proof
      (IH (N.shiftr word 1) lhs rhs
         ltac:(lia) ltac:(lia) ltac:(lia)
         Hshift_lhs Hshift_rhs) as Htwo.
    simpl.
    destruct (N.odd word); lia.
  Qed.

  Lemma live_nodes_well_formed_popcount_le1_length_le1 nodes :
    live_nodes_well_formed nodes ->
    (popcount64 (live_nodes_bitmap_word nodes) <= 1)%N ->
    (length nodes <= 1)%nat.
  Proof.
    intros Hwf Hpop.
    destruct nodes as [| first [| second rest]]; simpl; [lia.. |].
    unfold live_nodes_well_formed in Hwf.
    simpl in Hwf.
    destruct Hwf as [[Hfirst_lower Hfirst_upper] Hrest].
    simpl in Hrest.
    destruct Hrest as [[Hsecond_lower Hsecond_upper] _].
    pose proof
      (live_nodes_bitmap_word_in
         first (first :: second :: rest) ltac:(simpl; auto))
      as Hfirst_bit.
    pose proof
      (live_nodes_bitmap_word_in
         second (first :: second :: rest)
         ltac:(simpl; auto))
      as Hsecond_bit.
    unfold popcount64 in Hpop.
    pose proof
      (popcount_fuel_testbit_two
         64 (live_nodes_bitmap_word (first :: second :: rest))
         first.(live_index) second.(live_index)
         ltac:(unfold page_pair_count in *; lia)
         ltac:(unfold page_pair_count in *; lia)
         ltac:(lia)
         Hfirst_bit Hsecond_bit) as Htwo.
    lia.
  Qed.

  Lemma merge_level_length_le1 bit nodes :
    (length nodes <= 1)%nat ->
    merge_level bit nodes = nodes.
  Proof.
    destruct nodes as [| first [| second rest]]; simpl; intro Hlen;
      try reflexivity; lia.
  Qed.

  Lemma merge_prefix_noop_after target bit initial nodes :
    (bit <= target)%nat ->
    nodes = merge_prefix bit initial ->
    (length nodes <= 1)%nat ->
    merge_prefix target initial = nodes.
  Proof.
    revert bit nodes.
    induction target as [| target IH]; intros bit nodes Hle Hnodes Hlen.
    {
      destruct bit; [symmetry; exact Hnodes | lia].
    }
    destruct (Nat.eq_dec bit (S target)) as [Heq | Hneq].
    {
      subst bit.
      symmetry.
      exact Hnodes.
    }
    assert (Hbit_le_target : (bit <= target)%nat) by lia.
    rewrite <- merge_prefix_succ.
    rewrite (IH bit nodes Hbit_le_target Hnodes Hlen).
    apply merge_level_length_le1.
    exact Hlen.
  Qed.

  (* Pure bridge facts for the loop invariant.  The C++ proof below shows that
     the body maintains the scratch/bitmap invariant using the already-specified
     helpers [init_leaf_scratch] and [merge_scratch_level].  These facts connect
     that invariant back to the Section-1 commitment model in [commitment.v]:
     once the live-node bitmap has at most one bit, the selected scratch cell is
     the nonempty page subtree root. *)
  Lemma page_initial_live_nodes_ok :
    forall page,
      length page = page_slot_count ->
      storage_page_empty page = false ->
      let nodes := page_initial_live_nodes page in
      live_nodes_well_formed nodes /\
      pair_bitmap_word (slot_bitmap_word page) =
        live_nodes_bitmap_word nodes /\
      scratch_represents_live_nodes
        (init_leaf_scratch_model page
           (pair_bitmap_word (slot_bitmap_word page))
           (replicateN 64 0%N))
        nodes.
  Proof.
    intros page Hlen _Hnonempty.
    unfold page_initial_live_nodes.
    rewrite <- pair_options_bitmap.
    rewrite <- pair_options_values.
    rewrite active_leaf_nodes_pair_options.
    set (pairs := pair_options (page_slots_model page)).
    split.
    {
      apply initial_nodes_well_formed.
      subst pairs.
      apply pair_options_length.
    }
    assert
      (Hbitmap :
        pair_bitmap_word (slot_bitmap_word page) =
        live_nodes_bitmap_word
          (initial_nodes_from_pair_options 0 pairs)).
    {
      subst pairs.
      rewrite live_nodes_bitmap_word_initial_nodes.
      rewrite slot_bitmap_word_page_slots_model.
      rewrite pair_bitmap_word_bitmap_to_N.
      2: {
        rewrite length_map.
        rewrite page_slots_model_length.
        exact Hlen.
      }
      rewrite pair_options_bitmap.
      unfold pair_bitmap, slot_bitmap.
      rewrite normalize_page_slots_model.
      2: {
        exact Hlen.
      }
      reflexivity.
    }
    split; [exact Hbitmap |].
    split.
    { apply init_leaf_scratch_model_length. }
    intros node Hnode.
    pose proof
      (initial_nodes_from_pair_options_in 0 pairs node Hnode)
      as [offset [pair_value [Hnth [Hindex Htree]]]].
    simpl in Hindex.
    subst offset.
    subst pairs.
    assert (Hindex_bound : (node.(live_index) < page_pair_count)%nat).
    {
      eapply initial_nodes_index_bound.
      { apply pair_options_length. }
      { exact Hnode. }
    }
    assert
      (Hpair :
        pair_value = page_pair_leaf_model page node.(live_index)).
    {
      eapply pair_options_page_slots_nth; eauto.
    }
    unfold init_leaf_scratch_model.
    set
      (leaf_at :=
         fun pair_index : nat =>
           if
             bitmap_word_bit
               (pair_bitmap_word (slot_bitmap_word page))
               pair_index
           then
             blake3model.bytes32_to_N
               (blake3model.H64 blake3model.leaf_mode
                  (page_pair_leaf_model page pair_index))
           else nth pair_index (replicateN 64 0%N) 0%N).
    change
      (nth node.(live_index)
         (map leaf_at (seq 0 page_pair_count)) 0%N =
       blake3model.bytes32_to_N (eval_tree node.(live_tree))).
    rewrite
      (@nth_indep
         N (map leaf_at (seq 0 page_pair_count))
         node.(live_index) 0%N (leaf_at 0%nat)).
    2: {
      rewrite length_map.
      rewrite seq_length.
      exact Hindex_bound.
    }
    rewrite map_nth.
    rewrite seq_nth.
    2: {
      exact Hindex_bound.
    }
    simpl.
    unfold leaf_at.
    clear leaf_at.
    rewrite bitmap_word_bit_testbit.
    rewrite Hbitmap.
    rewrite live_nodes_bitmap_word_in.
    2: {
      exact Hnode.
    }
    rewrite Htree.
    simpl.
    now rewrite Hpair.
  Qed.

  Lemma compute_nonempty_subtree_root_done_at_depth :
    forall page bm scratch nodes,
      length page = page_slot_count ->
      storage_page_empty page = false ->
      nodes = merge_prefix 6 (page_initial_live_nodes page) ->
      live_nodes_well_formed nodes ->
      bm = live_nodes_bitmap_word nodes ->
      scratch_represents_live_nodes scratch nodes ->
      nth_error scratch (N.to_nat (countr_zero64 bm)) =
      Some (blake3model.bytes32_to_N (page_subtree_root_model page)).
  Proof.
    intros page bm scratch nodes Hlen Hnonempty Hnodes Hwf Hbm Hscratch.
    subst nodes.
    destruct (value_tree_from_page_slots_nonempty page Hlen Hnonempty)
      as [tree Htree].
    unfold value_tree_from_slots in Htree.
    set (pairs := pair_options (page_slots_model page)) in *.
    destruct
      (build_live_tree_from_value_tree 6 0 pairs tree Htree)
      as [root_node [Hlive Hroot_tree]].
    pose proof (merge_prefix_page_initial_build_live_tree page Hlen)
      as Hmerge.
    fold pairs in Hmerge.
    rewrite Hlive in Hmerge.
    rewrite Hmerge in Hwf, Hscratch, Hbm.
    subst bm.
    simpl in Hwf.
    destruct Hwf as [Hroot_index _].
    destruct Hscratch as [Hscratch_len Hscratch].
    specialize
      (Hscratch root_node ltac:(simpl; auto)) as Hscratch_root.
    rewrite live_nodes_bitmap_word_singleton.
    assert (Hroot_index_lt : (root_node.(live_index) < 64)%nat)
      by (unfold page_pair_count in *; lia).
    rewrite
      (countr_zero64_pow2_small
         root_node.(live_index) Hroot_index_lt).
    rewrite Nat2N.id.
    assert
      (Hnth_root :
        nth_error scratch root_node.(live_index) =
        Some (nth root_node.(live_index) scratch 0%N)).
    {
      apply nth_error_nth'.
      rewrite Hscratch_len.
      unfold page_pair_count in *.
      lia.
    }
    rewrite Hnth_root.
    rewrite Hscratch_root.
    rewrite Hroot_tree.
    unfold page_subtree_root_model.
    unfold value_tree_from_slots.
    fold pairs.
    rewrite Htree.
    reflexivity.
  Qed.

  Lemma compute_nonempty_subtree_root_done :
    forall page bit bm scratch nodes,
      length page = page_slot_count ->
      storage_page_empty page = false ->
      (0 <= bit <= 6)%Z ->
      nodes = merge_prefix (Z.to_nat bit)
        (page_initial_live_nodes page) ->
      live_nodes_well_formed nodes ->
      bm = live_nodes_bitmap_word nodes ->
      scratch_represents_live_nodes scratch nodes ->
      (bit < 6)%Z ->
      (popcount64 bm <= 1)%N ->
      nth_error scratch (N.to_nat (countr_zero64 bm)) =
      Some (blake3model.bytes32_to_N (page_subtree_root_model page)).
  Proof.
    intros page bit bm scratch nodes Hlen Hnonempty Hbit_range
      Hnodes Hwf Hbm Hscratch Hbit_lt Hpop.
    assert (Hnodes_len : (length nodes <= 1)%nat).
    {
      eapply live_nodes_well_formed_popcount_le1_length_le1.
      { exact Hwf. }
      rewrite <- Hbm.
      exact Hpop.
    }
    assert
      (Hfinal :
        merge_prefix 6 (page_initial_live_nodes page) = nodes).
    {
      eapply
        (merge_prefix_noop_after
           6 (Z.to_nat bit)
           (page_initial_live_nodes page) nodes).
      { lia. }
      { exact Hnodes. }
      { exact Hnodes_len. }
    }
    eapply compute_nonempty_subtree_root_done_at_depth.
    { exact Hlen. }
    { exact Hnonempty. }
    { symmetry. exact Hfinal. }
    { exact Hwf. }
    { exact Hbm. }
    { exact Hscratch. }
  Qed.

  Opaque pair_bitmap_word live_nodes_bitmap_word.
  Opaque countr_zero64 countr_zero_fuel popcount64 popcount_fuel.

  Lemma scratchR_replicate64_zero_pack (base : ptr) :
    base |-> arrayR bytes32_ty (exec_specs.bytes32R 1)
      (replicateN 64 0%N)
    |-- base |-> ScratchR 1 (replicateN 64 0%N).
  Proof.
    unfold ScratchR.
    go.
  Qed.

  Definition scratchR_replicate64_zero_pack_F base :=
    [FWD] (scratchR_replicate64_zero_pack base).

  Lemma arrayR_cellN_recombine_with_type_ptr
      {T : Type} (i : N) (l : list T) ty (R : T -> Rep)
      (base : ptr) (v : T)
      (Hnth : nth_error l (N.to_nat i) = Some v) :
    base |-> arrayR ty R (take (N.to_nat i) l)
    ** □ type_ptr ty (base .[ ty ! i])
    ** base .[ ty ! i] |-> R v
    ** base .[ ty ! i + 1]
         |-> arrayR ty R (drop (N.to_nat (i + 1)) l)
    |-- base |-> arrayR ty R l.
  Proof.
    rewrite -(_at_arrayR_cellN i l ty R base v Hnth).
    go.
  Qed.

  Definition arrayR_cellN_recombine_with_type_ptr_C
      {T : Type} i l ty R base (v : T) Hnth :=
    [CANCEL]
      (arrayR_cellN_recombine_with_type_ptr
         i l ty R base v Hnth).

  Lemma bytes32_array_cellN_recombine_with_type_ptr
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
  Proof.
    rewrite -(_at_arrayR_cellN
                i l bytes32_ty (exec_specs.bytes32R 1)
                base v Hnth).
    go.
  Qed.

  Definition bytes32_array_cellN_recombine_with_type_ptr_F
      i l base v Hnth :=
    [FWD]
      (bytes32_array_cellN_recombine_with_type_ptr
         i l base v Hnth).

  Lemma prf_compute_nonempty_subtree_root :
    verify[source] storage_compute_nonempty_subtree_root_spec.
  Proof using MODd.
    verify_spec.
    name_locals.
    match goal with
    | Hnonempty : storage_page_empty page = false |- _ =>
        pose proof Hnonempty as Hpage_nonempty
    end.
    match goal with
    | Hlen : length page = page_slot_count |- _ =>
        pose proof Hlen as Hpage_len
    end.
    go.
    rewrite <- (bi.exist_intro ready).
    rewrite <- (bi.exist_intro qleafcache).
    rewrite <- (bi.exist_intro qleafiv).
    rewrite <- (bi.exist_intro qdomain).
    rewrite <- (bi.exist_intro q).
    rewrite <- (bi.exist_intro page).
    rewrite <- (bi.exist_intro (replicateN 64 0%N)).
    go using (leaf_output_words64_zero_pack_cells_F scratch_addr).
    unfold blake3specs.Blake3OutputWordsR,
      blake3_impl_h_specs.Blake3OutputWordsR.
    go using scratchR_replicate64_zero_pack_F.
    pose proof
      (page_initial_live_nodes_ok page Hpage_len Hpage_nonempty)
      as (Hinitial_wf & Hinitial_bm & Hinitial_scratch).
    wp_for (fun _ =>
      Exists bit_model bm_model scratch_model nodes_model,
        [| (0 <= bit_model <= 6)%Z |]
        ** [| nodes_model =
              merge_prefix (Z.to_nat bit_model)
                (page_initial_live_nodes page) |]
        ** [| live_nodes_well_formed nodes_model |]
        ** [| bm_model = live_nodes_bitmap_word nodes_model |]
        ** [| scratch_represents_live_nodes scratch_model nodes_model |]
        ** page_addr
             |-> refR<storage_page_ty> 1$m pagep
        ** pagep |-> StoragePageR q page
        ** pair_bitmap_addr
             |-> ulongR 1$c
                   (pair_bitmap_word (slot_bitmap_word page))
        ** scratch_addr |-> ScratchR 1 scratch_model
        ** bm_addr |-> ulongR 1$m bm_model
        ** level_addr |-> ucharR 1$m bit_model).
    rewrite <- (bi.exist_intro 0%Z).
    rewrite <- (bi.exist_intro
      (pair_bitmap_word (slot_bitmap_word page))).
    rewrite <- (bi.exist_intro
      (init_leaf_scratch_model page
         (pair_bitmap_word (slot_bitmap_word page))
         (replicateN 64 0%N))).
    rewrite <- (bi.exist_intro (page_initial_live_nodes page)).
    go.
    match goal with
    | |- context[if asbool (?bit_model < 6)%Z then _ else _] =>
        destruct (asbool (bit_model < 6)%Z) eqn:Hbit_guard
    end.
    {
      pose proof Hbit_guard as Hbit_lt.
      apply bool_decide_eq_true_1 in Hbit_lt.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      go1.
      wp_if.
      {
        intro Hpop_gt.
        go.
        match goal with
        | Hscratch :
            scratch_represents_live_nodes
              ?scratch_model ?nodes_model |- _ =>
            rewrite <- (bi.exist_intro nodes_model);
            rewrite <- (bi.exist_intro scratch_model)
        end.
        go.
        match goal with
        | Hscratch :
            scratch_represents_live_nodes
              ?scratch_model
              (merge_level (Z.to_nat ?bit_model)
                 (merge_prefix (Z.to_nat ?bit_model)
                    (page_initial_live_nodes page))) |- _ =>
            rewrite <- (bi.exist_intro scratch_model)
        end.
        match goal with
        | Hbit_lt' : ?bit_model < 6 |- _ =>
            assert
              (Hbit_succ :
                Z.to_nat (bit_model + 1) = S (Z.to_nat bit_model))
              by lia;
            assert
              (Hbit_range : (0 <= bit_model + 1 <= 6)%Z)
              by lia
        end.
        rewrite Hbit_succ.
        rewrite <- merge_prefix_succ.
        go.
      }
      {
        intro Hpop_done.
        lazymatch goal with
        | Hpop_done' :
            context[
              live_nodes_bitmap_word
                (merge_prefix (Z.to_nat ?bit_model)
                   (page_initial_live_nodes page))] |- _ =>
            let nodes_model :=
              constr:(merge_prefix (Z.to_nat bit_model)
                        (page_initial_live_nodes page)) in
            lazymatch goal with
            | Hscratch :
                scratch_represents_live_nodes ?scratch_model nodes_model,
              Hwf : live_nodes_well_formed nodes_model,
              Hbit_lt' : Z.lt bit_model 6 |- _ =>
                assert
                  (Hpop_done_N :
                    (popcount64 (live_nodes_bitmap_word nodes_model) <= 1)%N)
                  by lia;
                pose proof
                  (compute_nonempty_subtree_root_done
                     page bit_model (live_nodes_bitmap_word nodes_model)
                     scratch_model nodes_model
                     Hpage_len Hpage_nonempty
                     ltac:(lia) eq_refl Hwf eq_refl Hscratch
                     Hbit_lt' Hpop_done_N)
                  as Hroot
            end
        end.
        unfold ScratchR.
        go.
        lazymatch goal with
        | Hroot :
            nth_error ?scratch (N.to_nat ?root_idx) = Some ?root |- _ =>
            rewrite (_at_arrayR_cellN
                       root_idx scratch bytes32_ty
                       (exec_specs.bytes32R 1) scratch_addr
                       root Hroot)
        end.
        go1.
        go1 using bytes32_array_cellN_recombine_with_type_ptr_F.
        match goal with
        | Hlen : length ?scratch = page_pair_count |- _ =>
            assert (Hscratch_len64 : length scratch = N.to_nat 64)
            by (change page_pair_count with 64%nat in Hlen; exact Hlen)
        end.
        go1.
        go1 using wp_destroy_bytes32_array_local_B.
      }
    }
    {
      pose proof Hbit_guard as Hbit_done.
      apply bool_decide_eq_false_1 in Hbit_done.
      go.
      lazymatch goal with
      | Hscratch :
          scratch_represents_live_nodes ?scratch_model
            (merge_prefix (Z.to_nat ?bit_model)
               (page_initial_live_nodes page)) |- _ =>
          let nodes_model :=
            constr:(merge_prefix (Z.to_nat bit_model)
                      (page_initial_live_nodes page)) in
          lazymatch goal with
          | Hwf : live_nodes_well_formed nodes_model,
            Hbit_done' : ~ Z.lt bit_model 6 |- _ =>
              assert (Hbit_eq : bit_model = 6%Z) by lia;
              assert
                (Hnodes_eq :
                  nodes_model =
                  merge_prefix 6 (page_initial_live_nodes page))
                by (rewrite Hbit_eq; reflexivity);
              assert
                (Hwf6 :
                  live_nodes_well_formed
                    (merge_prefix 6 (page_initial_live_nodes page)))
                by (rewrite <- Hnodes_eq; exact Hwf);
              assert
                (Hscratch6 :
                  scratch_represents_live_nodes scratch_model
                    (merge_prefix 6 (page_initial_live_nodes page)))
                by (rewrite <- Hnodes_eq; exact Hscratch);
              pose proof
                (compute_nonempty_subtree_root_done_at_depth
                   page
                   (live_nodes_bitmap_word
                      (merge_prefix 6 (page_initial_live_nodes page)))
                   scratch_model
                   (merge_prefix 6 (page_initial_live_nodes page))
                   Hpage_len Hpage_nonempty
                   eq_refl Hwf6 eq_refl Hscratch6)
                as Hroot
          end
      end.
      unfold ScratchR.
      go.
      lazymatch goal with
      | Hroot :
          nth_error ?scratch (N.to_nat ?root_idx) = Some ?root |- _ =>
          rewrite (_at_arrayR_cellN
                     root_idx scratch bytes32_ty
                     (exec_specs.bytes32R 1) scratch_addr
                     root Hroot)
      end.
      go1.
      go1 using bytes32_array_cellN_recombine_with_type_ptr_F.
      match goal with
      | Hlen : length ?scratch = page_pair_count |- _ =>
          assert (Hscratch_len64 : length scratch = N.to_nat 64)
          by (change page_pair_count with 64%nat in Hlen; exact Hlen)
      end.
      go1.
      go1 using wp_destroy_bytes32_array_local_B.
    }
  Qed.
End with_Sigma.

#[global] Opaque
  pair_bitmap_word
  pair_bitmap_prefix
  live_nodes_bitmap_word
  countr_zero64
  countr_zero_fuel
  popcount64
  popcount_fuel.

#[global] Hint Opaque
  pair_bitmap_word
  pair_bitmap_prefix
  live_nodes_bitmap_word
  countr_zero64
  countr_zero_fuel
  popcount64
  popcount_fuel : sl_opacity.
