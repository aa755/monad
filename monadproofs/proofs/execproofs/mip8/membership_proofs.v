Set Default Goal Selector "!".

(** * Inclusion and exclusion proofs for induced-subtree commitments

    This file models the proof objects discussed in the two MIP-8 documents.

    The
    Merkle Commitments via Induced Subtrees
    note explains the generic construction: a bitmap selects active leaves in a
    complete binary tree, the induced subtree skips empty branches, and an
    inclusion proof for one active leaf contains exactly the sibling subtree
    hashes that are needed along the leaf-to-root path.  It also states the
    proof-size bound: if [k] leaves are active in a height-[n] tree, then an
    inclusion proof contains at most [min (k - 1) n] sibling hashes.

    The
    MIP-8 page-ified storage-state
    note specializes this to storage pages.  A word inclusion proof carries the
    full 128-bit slot bitmap plus at most [min (k - 1) 6] 32-byte sibling
    hashes, because the merge tree has 64 pair leaves.  A word exclusion proof
    carries only the 128-bit bitmap plus the 32-byte committed root.

    The models below deliberately separate two concerns.

    - The geometric part is proved here: what an inclusion/exclusion proof
      means, why it is sound for the bitmap it carries, and why the hash-count
      bounds hold.

    - The root-level security part is linked to [commitment].  That file proves
      that two different normalized MIP-8 page views with the same root expose
      an aligned hash collision.  The MIP-8 bridge section below reuses that
      theorem to explain what a false opened membership view would have to
      break.
*)

From Stdlib Require Import Bool List Lia NArith PeanoNat.
Require Import monad.proofs.execproofs.mip8.blake3model.
Require Import monad.proofs.execproofs.mip8.induced_subtree.
Require Import monad.proofs.execproofs.mip8.commitment.
Import ListNotations.

(** ** Tree geometry used by membership proofs *)

(** We reuse the path representation from [induced_subtree]: a node is a list
    of left/right decisions from the root.  Here the bitmap is boolean and
    executable, because proof-size bounds are stated by counting active leaves. *)
Definition leaf_bitmap : Type := node -> bool.

Definition child (prefix : node) (bit : bool) : node :=
  prefix ++ [bit].

(** [active_count_in depth bm prefix] counts active leaves in the complete
    subtree of remaining height [depth] rooted at [prefix].  This is the
    quantity that the PDF calls [k] when [prefix] is the root. *)
Fixpoint active_count_in
    (depth : nat) (bm : leaf_bitmap) (prefix : node) : nat :=
  match depth with
  | O => if bm prefix then 1 else 0
  | S depth' =>
      active_count_in depth' bm (child prefix false) +
      active_count_in depth' bm (child prefix true)
  end.

Definition active_count (depth : nat) (bm : leaf_bitmap) : nat :=
  active_count_in depth bm [].

Definition subtree_nonempty
    (depth : nat) (bm : leaf_bitmap) (prefix : node) : bool :=
  0 <? active_count_in depth bm prefix.

(** [inclusion_sibling_count_from] follows a requested leaf path.  At each
    branch, the proof needs one sibling hash exactly when the opposite subtree
    is nonempty.  Empty siblings are omitted because the induced subtree does
    not contain them; unary nodes are bypassed. *)
Fixpoint inclusion_sibling_count_from
    (depth : nat) (bm : leaf_bitmap) (prefix suffix : node) : nat :=
  match depth, suffix with
  | O, [] => 0
  | S depth', bit :: rest =>
      (if subtree_nonempty depth' bm (child prefix (negb bit)) then 1 else 0) +
      inclusion_sibling_count_from depth' bm (child prefix bit) rest
  | _, _ => 0
  end.

Definition inclusion_sibling_count
    (depth : nat) (bm : leaf_bitmap) (leaf : node) : nat :=
  inclusion_sibling_count_from depth bm [] leaf.

Lemma nonempty_indicator_le_count count :
  (if 0 <? count then 1 else 0) <= count.
Proof.
  destruct count; simpl; lia.
Qed.

Lemma nonempty_indicator_le_one depth bm prefix :
  (if subtree_nonempty depth bm prefix then 1 else 0) <= 1.
Proof.
  destruct (subtree_nonempty depth bm prefix); lia.
Qed.

Lemma child_suffix_eq prefix bit suffix :
  child prefix bit ++ suffix = prefix ++ bit :: suffix.
Proof.
  unfold child.
  rewrite <- app_assoc.
  reflexivity.
Qed.

(** A path has at most one sibling at each level, hence at most [depth] sibling
    hashes.  This is the obvious half of the [min (k - 1) depth] bound. *)
Lemma inclusion_sibling_count_from_depth_bound depth bm prefix suffix :
  length suffix = depth ->
  inclusion_sibling_count_from depth bm prefix suffix <= depth.
Proof.
  revert prefix suffix.
  induction depth as [|depth IH]; intros prefix suffix Hlen.
  {
    destruct suffix; simpl in *; lia.
  }
  {
    destruct suffix as [|bit rest]; simpl in Hlen; [lia |].
    apply Nat.succ_inj in Hlen.
    simpl.
    pose proof
      (nonempty_indicator_le_one depth bm (child prefix (negb bit)))
      as Hsibling.
    pose proof (IH (child prefix bit) rest Hlen) as Hrest.
    lia.
  }
Qed.

Lemma active_count_in_positive_of_leaf_true depth bm prefix suffix :
  length suffix = depth ->
  bm (prefix ++ suffix) = true ->
  0 < active_count_in depth bm prefix.
Proof.
  revert prefix suffix.
  induction depth as [|depth IH]; intros prefix suffix Hlen Hactive.
  {
    destruct suffix; simpl in *; [|lia].
    rewrite app_nil_r in Hactive.
    destruct (bm prefix); simpl in *; congruence || lia.
  }
  {
    destruct suffix as [|bit rest]; simpl in Hlen; [lia |].
    apply Nat.succ_inj in Hlen.
    simpl.
    assert (Hactive_rest : bm (child prefix bit ++ rest) = true).
    {
      rewrite child_suffix_eq.
      exact Hactive.
    }
    pose proof (IH (child prefix bit) rest Hlen Hactive_rest) as Hcurrent.
    destruct bit; simpl in *; lia.
  }
Qed.

(** The less superficial half of the bound is that every sibling hash must be
    justified by at least one active leaf outside the opened leaf's own branch.
    Inductively, the current branch contributes the opened leaf plus whatever
    siblings occur below it, while the opposite branch can pay for the one hash
    that summarizes that whole branch. *)
Lemma inclusion_sibling_count_from_active_bound depth bm prefix suffix :
  length suffix = depth ->
  bm (prefix ++ suffix) = true ->
  inclusion_sibling_count_from depth bm prefix suffix <=
    active_count_in depth bm prefix - 1.
Proof.
  revert prefix suffix.
  induction depth as [|depth IH]; intros prefix suffix Hlen Hactive.
  {
    destruct suffix; simpl in *; [|lia].
    rewrite app_nil_r in Hactive.
    destruct (bm prefix); simpl in *; congruence || lia.
  }
  {
    destruct suffix as [|bit rest]; simpl in Hlen; [lia |].
    apply Nat.succ_inj in Hlen.
    simpl.
    assert (Hactive_rest : bm (child prefix bit ++ rest) = true).
    {
      rewrite child_suffix_eq.
      exact Hactive.
    }
    pose proof (IH (child prefix bit) rest Hlen Hactive_rest) as Hrest.
    pose proof
      (active_count_in_positive_of_leaf_true
         depth bm (child prefix bit) rest Hlen Hactive_rest)
      as Hcurrent.
    pose proof
      (nonempty_indicator_le_count
         (active_count_in depth bm (child prefix (negb bit))))
      as Hsibling.
    unfold subtree_nonempty in *.
    destruct bit; simpl in *; lia.
  }
Qed.

Theorem inclusion_sibling_count_bound depth bm leaf :
  length leaf = depth ->
  bm leaf = true ->
  inclusion_sibling_count depth bm leaf <=
    Nat.min (active_count depth bm - 1) depth.
Proof.
  intros Hlength Hmember.
  unfold inclusion_sibling_count, active_count.
  apply Nat.min_glb.
  {
    eapply inclusion_sibling_count_from_active_bound;
      [exact Hlength | simpl; exact Hmember].
  }
  {
    eapply inclusion_sibling_count_from_depth_bound; exact Hlength.
  }
Qed.

(** ** Inclusion proof model and size bounds *)

Definition digest_bytes : nat := 32.

Record ismc_inclusion_proof : Type := {
  inclusion_sibling_hashes : list digest;
}.

(** This validity predicate treats sibling hash *values* abstractly.  The shape
    obligation is the important point here: a valid proof contains exactly the
    hashes for the nonempty sibling subtrees along the opened leaf's path. *)
Definition valid_ismc_inclusion_proof
    (depth : nat) (bm : leaf_bitmap) (leaf : node)
    (proof : ismc_inclusion_proof) : Prop :=
  length leaf = depth /\
  bm leaf = true /\
  length proof.(inclusion_sibling_hashes) =
    inclusion_sibling_count depth bm leaf.

(** The verifier rebuilds the induced-subtree digest bottom-up.  It hashes the
    opened pair value itself before consuming any sibling hashes, so the proof
    authenticates the value at the opened pair leaf rather than merely proving
    that an already-computed digest appears somewhere in the tree.  The bitmap
    and leaf path tell the verifier where sibling hashes are required and
    whether a consumed sibling is the left or right child. *)
Section InclusionVerifier.
  Variable leaf_digest : pair_leaf -> digest.
  Variable merge_digest : digest -> digest -> digest.
  Variable seal_digest : leaf_bitmap -> digest -> digest.

  Fixpoint fold_inclusion_from
      (depth : nat) (bm : leaf_bitmap) (prefix suffix : node)
      (current : digest) (siblings : list digest)
      : option (digest * list digest) :=
    match depth, suffix with
    | O, [] => Some (current, siblings)
    | S depth', bit :: rest =>
        match
          fold_inclusion_from
            depth' bm (child prefix bit) rest current siblings
        with
        | None => None
        | Some (child_digest, remaining) =>
            if subtree_nonempty depth' bm (child prefix (negb bit))
            then
              match remaining with
              | [] => None
              | sibling_digest :: remaining' =>
                  let parent_digest :=
                    if bit
                    then merge_digest sibling_digest child_digest
                    else merge_digest child_digest sibling_digest in
                  Some (parent_digest, remaining')
              end
            else Some (child_digest, remaining)
        end
    | _, _ => None
    end.

  Definition recompute_ismc_inclusion_root
      (depth : nat) (bm : leaf_bitmap) (leaf : node)
      (opened_leaf : pair_leaf) (proof : ismc_inclusion_proof)
      : option digest :=
    match
      fold_inclusion_from
        depth bm [] leaf (leaf_digest opened_leaf)
        proof.(inclusion_sibling_hashes)
    with
    | Some (tree_digest, []) => Some (seal_digest bm tree_digest)
    | _ => None
    end.

  Definition verifies_ismc_inclusion_proof
      (root : digest) (depth : nat) (bm : leaf_bitmap) (leaf : node)
      (opened_leaf : pair_leaf) (proof : ismc_inclusion_proof) : Prop :=
    length leaf = depth /\
    bm leaf = true /\
    recompute_ismc_inclusion_root depth bm leaf opened_leaf proof =
      Some root.

  Lemma fold_inclusion_from_consumes_count
      depth bm prefix suffix current siblings result remaining :
    length suffix = depth ->
    fold_inclusion_from
      depth bm prefix suffix current siblings =
      Some (result, remaining) ->
    length siblings =
      inclusion_sibling_count_from depth bm prefix suffix +
      length remaining.
  Proof.
    revert prefix suffix current siblings result remaining.
    induction depth as [|depth IH];
      intros prefix suffix current siblings result remaining Hlen Hfold.
    {
      destruct suffix; simpl in *; [|lia].
      inversion Hfold; subst.
      lia.
    }
    {
      destruct suffix as [|bit rest]; simpl in Hlen; [lia |].
      apply Nat.succ_inj in Hlen.
      simpl in Hfold |- *.
      destruct
        (fold_inclusion_from
           depth bm (child prefix bit) rest current siblings)
        as [[child_digest siblings_after_child] |] eqn:Hchild;
        [|discriminate].
      pose proof
        (IH (child prefix bit) rest current siblings
           child_digest siblings_after_child Hlen Hchild)
        as Hchild_count.
      destruct (subtree_nonempty depth bm (child prefix (negb bit)))
        eqn:Hsibling.
      {
        destruct siblings_after_child as [|sibling_digest remaining'];
          [discriminate |].
        inversion Hfold; subst.
        simpl in *.
        lia.
      }
      {
        inversion Hfold; subst.
        lia.
      }
    }
  Qed.

  Lemma verified_ismc_inclusion_proof_valid_shape
      root depth bm leaf opened_leaf proof :
    verifies_ismc_inclusion_proof
      root depth bm leaf opened_leaf proof ->
    valid_ismc_inclusion_proof depth bm leaf proof.
  Proof.
    intros [Hlength [Hmember Hroot]].
    unfold recompute_ismc_inclusion_root in Hroot.
    destruct
      (fold_inclusion_from
         depth bm [] leaf (leaf_digest opened_leaf)
         proof.(inclusion_sibling_hashes))
      as [[tree_digest remaining] |] eqn:Hfold;
      [|discriminate].
    destruct remaining as [|extra remaining']; [|discriminate].
    pose proof
      (fold_inclusion_from_consumes_count
         depth bm [] leaf (leaf_digest opened_leaf)
         proof.(inclusion_sibling_hashes)
         tree_digest [] Hlength Hfold) as Hcount.
    simpl in Hcount.
    repeat split; try assumption.
    unfold inclusion_sibling_count.
    rewrite Nat.add_0_r in Hcount.
    exact Hcount.
  Qed.

  Theorem verified_ismc_inclusion_proof_sound
      root depth bm leaf opened_leaf proof :
    verifies_ismc_inclusion_proof
      root depth bm leaf opened_leaf proof ->
    bm leaf = true.
  Proof.
    intros [_ [Hmember _]].
    exact Hmember.
  Qed.
End InclusionVerifier.

Definition ismc_inclusion_proof_hash_count
    (proof : ismc_inclusion_proof) : nat :=
  length proof.(inclusion_sibling_hashes).

Definition ismc_inclusion_proof_size_bytes
    (bitmap_bytes : nat) (proof : ismc_inclusion_proof) : nat :=
  bitmap_bytes + digest_bytes * ismc_inclusion_proof_hash_count proof.

Theorem valid_ismc_inclusion_proof_sound depth bm leaf proof :
  valid_ismc_inclusion_proof depth bm leaf proof ->
  bm leaf = true.
Proof.
  intros [_ [Hmember _]].
  exact Hmember.
Qed.

Theorem valid_ismc_inclusion_proof_hash_count_bound depth bm leaf proof :
  valid_ismc_inclusion_proof depth bm leaf proof ->
  ismc_inclusion_proof_hash_count proof <=
    Nat.min (active_count depth bm - 1) depth.
Proof.
  intros [Hlength [Hmember Hhashes]].
  unfold ismc_inclusion_proof_hash_count.
  rewrite Hhashes.
  now apply inclusion_sibling_count_bound.
Qed.

Theorem valid_ismc_inclusion_proof_size_bound
    bitmap_bytes depth bm leaf proof :
  valid_ismc_inclusion_proof depth bm leaf proof ->
  ismc_inclusion_proof_size_bytes bitmap_bytes proof <=
    bitmap_bytes + digest_bytes *
      Nat.min (active_count depth bm - 1) depth.
Proof.
  intros Hvalid.
  unfold ismc_inclusion_proof_size_bytes.
  pose proof
    (valid_ismc_inclusion_proof_hash_count_bound
       depth bm leaf proof Hvalid) as Hhash_bound.
  cbv [digest_bytes].
  lia.
Qed.

Theorem verified_ismc_inclusion_proof_size_bound
    leaf_digest merge_digest seal_digest root
    bitmap_bytes depth bm leaf opened_leaf proof :
  verifies_ismc_inclusion_proof
    leaf_digest merge_digest seal_digest
    root depth bm leaf opened_leaf proof ->
  ismc_inclusion_proof_size_bytes bitmap_bytes proof <=
    bitmap_bytes + digest_bytes *
      Nat.min (active_count depth bm - 1) depth.
Proof.
  intros Hverified.
  pose proof
    (verified_ismc_inclusion_proof_valid_shape
       leaf_digest merge_digest seal_digest
       root depth bm leaf opened_leaf proof
       Hverified) as Hvalid.
  exact
    (valid_ismc_inclusion_proof_size_bound
       bitmap_bytes depth bm leaf proof Hvalid).
Qed.

(** ** Exclusion proof model and size bounds *)

Record ismc_exclusion_proof : Type := {
  exclusion_committed_root : digest;
}.

(** An exclusion proof carries the bitmap and the committed root.  Since the
    bitmap is part of the witness, bitmap-level soundness is just the statement
    that the queried leaf bit is absent.  The final section explains how this
    becomes a root-level security property once the commitment binds bitmaps. *)
Definition valid_ismc_exclusion_proof
    (depth : nat) (bm : leaf_bitmap) (leaf : node)
    (_proof : ismc_exclusion_proof) : Prop :=
  length leaf = depth /\ bm leaf = false.

Definition verifies_ismc_exclusion_proof
    (root : digest) (depth : nat) (bm : leaf_bitmap) (leaf : node)
    (proof : ismc_exclusion_proof) : Prop :=
  valid_ismc_exclusion_proof depth bm leaf proof /\
  proof.(exclusion_committed_root) = root.

Definition ismc_exclusion_proof_size_bytes
    (bitmap_bytes : nat) (_proof : ismc_exclusion_proof) : nat :=
  bitmap_bytes + digest_bytes.

Theorem valid_ismc_exclusion_proof_sound depth bm leaf proof :
  valid_ismc_exclusion_proof depth bm leaf proof ->
  bm leaf = false.
Proof.
  intros [_ Habsent].
  exact Habsent.
Qed.

Theorem verified_ismc_exclusion_proof_sound root depth bm leaf proof :
  verifies_ismc_exclusion_proof root depth bm leaf proof ->
  bm leaf = false.
Proof.
  intros [Hvalid _].
  now apply valid_ismc_exclusion_proof_sound in Hvalid.
Qed.

Theorem ismc_exclusion_proof_size_constant bitmap_bytes proof :
  ismc_exclusion_proof_size_bytes bitmap_bytes proof =
    bitmap_bytes + digest_bytes.
Proof.
  reflexivity.
Qed.

(** ** MIP-8 byte-size corollaries *)

Definition mip8_pair_tree_depth : nat := 6.
Definition mip8_slot_tree_depth : nat := 7.
Definition mip8_slot_bitmap_bytes : nat := 16.

(** The MIP-8 inclusion path is through the 64-leaf pair tree, but the proof
    still carries the full 128-bit slot bitmap.  This is the stated
    [16 + 32 * min(k - 1, 6)] byte bound. *)
Corollary mip8_valid_inclusion_proof_size_bound bm leaf proof :
  valid_ismc_inclusion_proof mip8_pair_tree_depth bm leaf proof ->
  ismc_inclusion_proof_size_bytes mip8_slot_bitmap_bytes proof <=
    mip8_slot_bitmap_bytes + digest_bytes *
      Nat.min
        (active_count mip8_pair_tree_depth bm - 1)
        mip8_pair_tree_depth.
Proof.
  apply valid_ismc_inclusion_proof_size_bound.
Qed.

Corollary mip8_verified_inclusion_proof_size_bound
    leaf_digest merge_digest seal_digest root bm leaf opened_leaf proof :
  verifies_ismc_inclusion_proof
    leaf_digest merge_digest seal_digest root
    mip8_pair_tree_depth bm leaf opened_leaf proof ->
  ismc_inclusion_proof_size_bytes mip8_slot_bitmap_bytes proof <=
    mip8_slot_bitmap_bytes + digest_bytes *
      Nat.min
        (active_count mip8_pair_tree_depth bm - 1)
        mip8_pair_tree_depth.
Proof.
  apply verified_ismc_inclusion_proof_size_bound.
Qed.

(** A MIP-8 word exclusion proof consists of the 16-byte slot bitmap and the
    32-byte root digest, for a total of 48 bytes. *)
Corollary mip8_exclusion_proof_size_exact proof :
  ismc_exclusion_proof_size_bytes mip8_slot_bitmap_bytes proof = 48.
Proof.
  reflexivity.
Qed.

Corollary mip8_slot_exclusion_proof_sound bm leaf proof :
  valid_ismc_exclusion_proof mip8_slot_tree_depth bm leaf proof ->
  bm leaf = false.
Proof.
  apply valid_ismc_exclusion_proof_sound.
Qed.

(** ** MIP-8 opened views and root binding *)

(** The generic membership proof geometry addresses leaves by a root-to-leaf
    path.  The page commitment in [commitment] addresses pair leaves by their
    complete-tree index.  [path_to_nat] is the root-first binary encoding that
    connects the two presentations: going left contributes zero at that level,
    and going right contributes the width of the remaining subtree. *)
Fixpoint path_to_nat (path : node) : nat :=
  match path with
  | [] => 0
  | bit :: rest =>
      (if bit then Nat.pow 2 (length rest) else 0) + path_to_nat rest
  end.

Definition empty_pair_leaf : pair_leaf :=
  (bytes32_of_N 0%N, bytes32_of_N 0%N).

Definition pair_leaf_at_path
    (slots : slot_values) (leaf : node) : pair_leaf :=
  nth (path_to_nat leaf) (pair_leaves slots) empty_pair_leaf.

Definition pair_bitmap_at_path
    (slots : slot_values) (leaf : node) : bool :=
  nth (path_to_nat leaf) (pair_bitmap slots) false.

Definition pair_bitmap_as_leaf_bitmap
    (slots : slot_values) : leaf_bitmap :=
  pair_bitmap_at_path slots.

Definition mip8_leaf_digest (opened_pair : pair_leaf) : digest :=
  H64 leaf_mode opened_pair.

Definition mip8_merge_digest (lhs rhs : digest) : digest :=
  H64 merge_mode (lhs, rhs).

(** The inclusion verifier seals with the 128-bit slot bitmap, not the 64-bit
    pair bitmap used to route the induced merge tree.  This is the step that
    prevents moving an otherwise identical pair leaf to a different slot
    position without changing the root. *)
Definition mip8_seal_digest
    (slots : slot_values) (_pair_bm : leaf_bitmap)
    (tree_root : digest) : digest :=
  seal_nonempty (bitmap_to_bytes16 (slot_bitmap slots)) tree_root.

(** A verified inclusion for a full page view opens the pair value at the
    requested path and recomputes that view's root from the opened value plus
    sibling hashes.  This is intentionally a statement about an opened *view*:
    arbitrary sibling hashes do not by themselves determine the values of the
    other committed leaves. *)
Definition verifies_mip8_pair_inclusion_for_view
    (slots : slot_values) (leaf : node) (opened_pair : pair_leaf)
    (proof : ismc_inclusion_proof) : Prop :=
  pair_leaf_at_path slots leaf = opened_pair /\
  verifies_ismc_inclusion_proof
    mip8_leaf_digest mip8_merge_digest (mip8_seal_digest slots)
    (root slots) mip8_pair_tree_depth
    (pair_bitmap_as_leaf_bitmap slots) leaf opened_pair proof.

Definition verifies_mip8_pair_exclusion_for_view
    (slots : slot_values) (leaf : node)
    (proof : ismc_exclusion_proof) : Prop :=
  verifies_ismc_exclusion_proof
    (root slots) mip8_pair_tree_depth
    (pair_bitmap_as_leaf_bitmap slots) leaf proof.

(** If an opened inclusion view verifies against the root of a different
    committed page view, the MIP-8 binding theorem turns that mismatch into the
    aligned collision event from [commitment]. *)
Theorem mip8_false_inclusion_view_extracts_aligned_collision
    committed_slots claimed_slots leaf opened_pair proof :
  verifies_mip8_pair_inclusion_for_view
    claimed_slots leaf opened_pair proof ->
  root claimed_slots = root committed_slots ->
  normalize_slots committed_slots <> normalize_slots claimed_slots ->
  exists_aligned_collision
    (root_with_trace committed_slots)
    (root_with_trace claimed_slots).
Proof.
  intros _ Hroot Hdistinct.
  apply Root_binding_break_extracts_aligned_collision.
  {
    rewrite !root_with_trace_root.
    symmetry.
    exact Hroot.
  }
  exact Hdistinct.
Qed.

(** This is the value-facing form of the previous theorem.  If the opened pair
    value differs from the pair value in the committed page view, then a proof
    for the claimed view can verify against the committed root only by inducing
    an aligned hash collision. *)
Corollary mip8_false_inclusion_value_extracts_aligned_collision
    committed_slots claimed_slots leaf opened_pair proof :
  verifies_mip8_pair_inclusion_for_view
    claimed_slots leaf opened_pair proof ->
  root claimed_slots = root committed_slots ->
  pair_leaf_at_path committed_slots leaf <> opened_pair ->
  exists_aligned_collision
    (root_with_trace committed_slots)
    (root_with_trace claimed_slots).
Proof.
  intros Hverified Hroot Hfalse_value.
  destruct Hverified as [Hclaimed_value Hverified].
  eapply mip8_false_inclusion_view_extracts_aligned_collision.
  { exact (conj Hclaimed_value Hverified). }
  { exact Hroot. }
  intro Hsame.
  apply Hfalse_value.
  unfold pair_leaf_at_path, pair_leaves in *.
  rewrite Hsame.
  exact Hclaimed_value.
Qed.

(** The exclusion analogue is the same root-binding argument.  A false
    exclusion proof is represented here as a proof for a claimed page view whose
    normalized slots differ from the committed page view. *)
Theorem mip8_false_exclusion_view_extracts_aligned_collision
    committed_slots claimed_slots leaf proof :
  verifies_mip8_pair_exclusion_for_view claimed_slots leaf proof ->
  root claimed_slots = root committed_slots ->
  normalize_slots committed_slots <> normalize_slots claimed_slots ->
  exists_aligned_collision
    (root_with_trace committed_slots)
    (root_with_trace claimed_slots).
Proof.
  intros _ Hroot Hdistinct.
  apply Root_binding_break_extracts_aligned_collision.
  {
    rewrite !root_with_trace_root.
    symmetry.
    exact Hroot.
  }
  exact Hdistinct.
Qed.

(** Conversely, if the two traced computations have no aligned collision, a
    verified inclusion view with the same root must be the committed normalized
    page view. *)
Corollary mip8_verified_inclusion_view_sound_no_collision
    committed_slots claimed_slots leaf opened_pair proof :
  no_aligned_collisions
    (root_with_trace committed_slots)
    (root_with_trace claimed_slots) ->
  root claimed_slots = root committed_slots ->
  verifies_mip8_pair_inclusion_for_view
    claimed_slots leaf opened_pair proof ->
  normalize_slots committed_slots = normalize_slots claimed_slots.
Proof.
  intros Hno_collision Hroot _.
  apply Root_injective_no_collision; [exact Hno_collision |].
  symmetry.
  exact Hroot.
Qed.

Corollary mip8_verified_inclusion_value_sound_no_collision
    committed_slots claimed_slots leaf opened_pair proof :
  no_aligned_collisions
    (root_with_trace committed_slots)
    (root_with_trace claimed_slots) ->
  root claimed_slots = root committed_slots ->
  verifies_mip8_pair_inclusion_for_view
    claimed_slots leaf opened_pair proof ->
  pair_leaf_at_path committed_slots leaf = opened_pair.
Proof.
  intros Hno_collision Hroot Hverified.
  destruct Hverified as [Hclaimed_value Hverified].
  pose proof
    (mip8_verified_inclusion_view_sound_no_collision
       committed_slots claimed_slots leaf opened_pair proof
       Hno_collision Hroot (conj Hclaimed_value Hverified))
    as Hsame.
  unfold pair_leaf_at_path, pair_leaves.
  rewrite Hsame.
  exact Hclaimed_value.
Qed.

Corollary mip8_verified_exclusion_view_sound_no_collision
    committed_slots claimed_slots leaf proof :
  no_aligned_collisions
    (root_with_trace committed_slots)
    (root_with_trace claimed_slots) ->
  root claimed_slots = root committed_slots ->
  verifies_mip8_pair_exclusion_for_view claimed_slots leaf proof ->
  normalize_slots committed_slots = normalize_slots claimed_slots.
Proof.
  intros Hno_collision Hroot _.
  apply Root_injective_no_collision; [exact Hno_collision |].
  symmetry.
  exact Hroot.
Qed.

(** ** Root-level security from bitmap binding *)

Section BindingSecurity.
  Variable committed_view : Type.
  Variable bit_at : committed_view -> leaf_bitmap.
  Variable root : committed_view -> digest.

  (** This is the exact commitment property needed by membership proofs: equal
      roots must expose the same bitmap bits.  The stronger MIP-8 theorem in
      [commitment] binds the whole normalized committed view; this section only
      needs the bitmap projection of that fact. *)
  Definition root_binds_bitmap : Prop :=
    forall view view',
      root view = root view' ->
      forall leaf, bit_at view leaf = bit_at view' leaf.

  Definition valid_inclusion_for_view
      depth view leaf proof : Prop :=
    valid_ismc_inclusion_proof depth (bit_at view) leaf proof.

  Definition valid_exclusion_for_view
      depth view leaf proof : Prop :=
    valid_ismc_exclusion_proof depth (bit_at view) leaf proof.

  Section VerifiedViews.
    Variable leaf_digest : pair_leaf -> digest.
    Variable merge_digest : digest -> digest -> digest.
    Variable seal_digest : leaf_bitmap -> digest -> digest.

    Definition verifies_inclusion_for_view
        depth view leaf opened_leaf proof : Prop :=
      verifies_ismc_inclusion_proof
        leaf_digest merge_digest seal_digest (root view)
        depth (bit_at view) leaf opened_leaf proof.

    Definition verifies_exclusion_for_view
        depth view leaf proof : Prop :=
      verifies_ismc_exclusion_proof
        (root view) depth (bit_at view) leaf proof.

    Theorem same_root_verified_inclusion_exclusion_conflict
        depth view view' leaf opened_leaf inclusion exclusion :
      root_binds_bitmap ->
      root view = root view' ->
      verifies_inclusion_for_view
        depth view leaf opened_leaf inclusion ->
      verifies_exclusion_for_view depth view' leaf exclusion ->
      False.
    Proof.
      intros Hbind Hroot Hinclude Hexclude.
      pose proof
        (verified_ismc_inclusion_proof_sound
           leaf_digest merge_digest seal_digest (root view)
           depth (bit_at view) leaf opened_leaf inclusion Hinclude)
        as Hmember.
      pose proof
        (verified_ismc_exclusion_proof_sound
           (root view') depth (bit_at view') leaf exclusion Hexclude)
        as Habsent.
      rewrite (Hbind view view' Hroot leaf) in Hmember.
      congruence.
    Qed.
  End VerifiedViews.

  Theorem same_root_preserves_inclusion_membership
      depth view view' leaf proof :
    root_binds_bitmap ->
    root view = root view' ->
    valid_inclusion_for_view depth view leaf proof ->
    bit_at view' leaf = true.
  Proof.
    intros Hbind Hroot Hvalid.
    pose proof
      (valid_ismc_inclusion_proof_sound
         depth (bit_at view) leaf proof Hvalid) as Hmember.
    rewrite <- (Hbind view view' Hroot leaf).
    exact Hmember.
  Qed.

  Theorem same_root_preserves_exclusion_nonmembership
      depth view view' leaf proof :
    root_binds_bitmap ->
    root view = root view' ->
    valid_exclusion_for_view depth view leaf proof ->
    bit_at view' leaf = false.
  Proof.
    intros Hbind Hroot Hvalid.
    pose proof
      (valid_ismc_exclusion_proof_sound
         depth (bit_at view) leaf proof Hvalid) as Habsent.
    rewrite <- (Hbind view view' Hroot leaf).
    exact Habsent.
  Qed.

  (** Therefore, under bitmap binding, an inclusion proof and an exclusion
      proof for the same queried leaf cannot both verify against equal roots.
      Equivalently, producing such a pair is a binding break, and in the MIP-8
      commitment model that binding break is reduced to an aligned hash
      collision in [commitment]. *)
  Theorem same_root_inclusion_exclusion_conflict
      depth view view' leaf inclusion exclusion :
    root_binds_bitmap ->
    root view = root view' ->
    valid_inclusion_for_view depth view leaf inclusion ->
    valid_exclusion_for_view depth view' leaf exclusion ->
    False.
  Proof.
    intros Hbind Hroot Hinclude Hexclude.
    pose proof
      (valid_ismc_inclusion_proof_sound
         depth (bit_at view) leaf inclusion Hinclude) as Hmember.
    pose proof
      (valid_ismc_exclusion_proof_sound
         depth (bit_at view') leaf exclusion Hexclude) as Habsent.
    rewrite (Hbind view view' Hroot leaf) in Hmember.
    congruence.
  Qed.
End BindingSecurity.
