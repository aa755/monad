(** * MIP-8 page commitments

    This file formalizes
    Merkle Commitments via Induced Subtrees by
    defining a Gallina (Coq) model of the scheme and proving the main security property about the model.

    In subsequent files, the #<a href="https://github.com/category-labs/monad/blob/9f7005e8ae0c8a073da24189b545e58f40a1287e/category/execution/monad/db/storage_page.cpp&#35;L136">C++ implementation</a>#
    is specified against this model.  Once that implementation proof is
    complete, the security properties proved here transfer to the actual C++
    code.


    The commitment is for a 128-slot storage page.  Each slot is a 32-byte
    value or empty.  The algorithm groups adjacent slots into 64-byte pair
    leaves, builds the induced subtree over the nonempty pairs, hashes that
    compact tree, and finally seals the result with the full 128-bit slot
    bitmap.  Empty pages have no merge root; their root is just a hash of the
    bitmap seal.

    The file is organized in the same order a reader should understand the
    construction.

    - Section [Algorithm] defines the compact commitment algorithm.  This is
      the simplest presentation: normalize the slot list, form optional pair
      leaves, recursively build the induced value tree, hash it, and seal it.

    - Section [CorrectnessStatement] adds the extra vocabulary needed for the
      security theorem: semantic hash-call locations, located traces, and the
      aligned-collision assumption.
      This machinery can be avoided if we only care about a weaker security property
      which assumes a too strong property about lack of collision on inputs.

    - Section [CorrectnessProof] proves the statement. You do not need to read it unless you want to: Coq has checked that there are no holes in the proof.
      It also contains the
      lower-level reducer facts needed to connect the compact Section 1
      presentation with the C++ scratch-array intuition.

    The concrete byte types use [skylabs.prelude.fin]: [fin.t n] is the type of natural
    numbers less than [n].  Internally it is represented as a dependent pair of
    a number and a proof that the number is below [n], but that detail can be
    ignored here.

    - [byte] is [fin.t 2^8].
    - [bytes16] is [fin.t 2^128].
    - [bytes32] and [digest] are [fin.t 2^256].
    - [bytes64] and [pair_leaf] are pairs of 32-byte words.

    The BLAKE3 compression behavior is abstracted by three parameters.  [H64]
    hashes one 64-byte block and carries a mode bit so the model can distinguish
    the C++ leaf-mode calls from merge-mode calls.  [seal_empty] models the
    16-byte empty-page seal.  [seal_nonempty] models the 48-byte seal containing
    the bitmap and a 32-byte induced-subtree root.
*)

(* begin hide *)
Set Default Goal Selector "!".

From Stdlib Require Import Bool List Arith PeanoNat Lia NArith.
Require Import stdpp.decidable.
Require Import skylabs.prelude.fin.
Require Import monad.proofs.execproofs.mip8.blake3model.
Import ListNotations.
(* end hide *)

(** ** Section 1: Algorithm model

    This section contains only the objects needed to understand what the MIP-8
    page commitment computes. 
*)
Section Algorithm.

Definition page_slot_count : nat := 128.
Definition page_pair_count : nat := 64.
Definition page_pair_tree_depth : nat := 6.

(**  The public input is a list of optional slot values.  Position [n] is slot
    [n]; [None] means the slot is absent.  Inputs shorter than 128 slots are
    padded with [None], and longer inputs are truncated.  This canonical
    128-slot view is what the commitment binds. *)

Definition slot_values : Type := list (option slot_word).

Definition normalize_slots (slots : slot_values) : slot_values :=
  firstn page_slot_count (slots ++ repeat None page_slot_count).

(** Bitmaps are little-endian bit lists here.  [bitmap_to_bytes16] packs the
    128-slot seal bitmap into the 16 bytes used by the page commitment. *)
Definition bitmap := list bool.

Definition slot_present (slot : option slot_word) : bool :=
  match slot with
  | Some _ => true
  | None => false
  end.

Definition slot_payload (slot : option slot_word) : slot_word :=
  match slot with
  | Some value => value
  | None => bytes32_of_N 0
  end.

Local Open Scope N_scope.

Fixpoint bitmap_to_N (bm : bitmap) : N :=
  match bm with
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + 2 * bitmap_to_N rest
  end.

Local Close Scope N_scope.

(** if [bm >= 2^128], this returns 0 *)
Definition bitmap_to_bytes16 (bm : bitmap) : bytes16 :=
  @fin.of_N' (pow2N 128) ltac:(solve_pow2N_pos) (bitmap_to_N bm).

Definition slot_bitmap (slots : slot_values) : bitmap :=
  map slot_present (normalize_slots slots).

(** pair adjacent slots *)
Fixpoint pair_options_raw
    (slots : slot_values) : list (option pair_leaf) :=
  match slots with
  | first :: second :: rest =>
      if slot_present first || slot_present second
      then Some (slot_payload first, slot_payload second) ::
           pair_options_raw rest
      else None :: pair_options_raw rest
  | _ => []
  end.

Definition pair_options (slots : slot_values)
    : list (option pair_leaf) :=
  pair_options_raw (normalize_slots slots).

(** [subtree_width depth] is the number of pair positions below a complete
    subtree at [depth].  A leaf-level subtree has width 1, and each parent
    level doubles the width.  The full storage page uses
    [page_pair_tree_depth = 6], so its complete tree has 64 pair positions. *)
Fixpoint subtree_width (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => 2 * subtree_width n'
  end.

(** The Coq algorithm is designed for ease of understanding, not efficiency, so
    it is organized differently from the C++ loop.  We first pair adjacent
    slots, then construct the minimal binary tree with the occupied slot pairs
    as leaves.  [value_tree] represents that compact tree.  After that, the
    pre-seal root hash is just a simple tree recursion. *)
Inductive value_tree : Type :=
| TreeLeaf (leaf : pair_leaf)
| TreeNode (lchild rchild : value_tree).

(** just a helper used below to build a tree from slot pairs *)
Definition combine_value_trees
    (lhs rhs : option value_tree) : option value_tree :=
  match lhs, rhs with
  | None, None => None
  | Some tree, None => Some tree
  | None, Some tree => Some tree
  | Some lhs_tree, Some rhs_tree =>
      Some (TreeNode lhs_tree rhs_tree)
  end.

(** this can be considered the heart of the Coq model: *)
Fixpoint build_value_tree
    (depth : nat) (pairs : list (option pair_leaf))
    : option value_tree :=
  match depth with
  | O =>
      match pairs with
      | [Some value] => Some (TreeLeaf value)
      | _ => None
      end
  | S depth' =>
      let width := subtree_width depth' in
      combine_value_trees
        (build_value_tree depth' (firstn width pairs))
        (build_value_tree depth' (skipn width pairs))
  end.

Definition value_tree_from_slots
    (slots : slot_values) : option value_tree :=
  build_value_tree page_pair_tree_depth (pair_options slots).

Section value_tree_demo.
  Variables (v0 v1 v8 v32 v32' : slot_word).

  Let zero : slot_word := bytes32_of_N 0.
  Let singleton_pair_slot (value : slot_word) : slot_values :=
    [Some value; None].
  Let demo_slots : slot_values :=
    singleton_pair_slot v0 ++
    singleton_pair_slot v1 ++
    repeat None 12 ++
    singleton_pair_slot v8 ++
    repeat None 46 ++
    [Some v32; Some v32'].
  Let pair0 : pair_leaf := (v0, zero).
  Let pair1 : pair_leaf := (v1, zero).
  Let pair8 : pair_leaf := (v8, zero).
  Let pair32 : pair_leaf := (v32, v32').
  Let demo_tree : value_tree :=
    TreeNode
      (TreeNode
        (TreeNode
          (TreeLeaf pair0)
          (TreeLeaf pair1))
        (TreeLeaf pair8))
      (TreeLeaf pair32).

  (** This example helps build intuition for [build_value_tree].  The input
      [demo_slots] has occupied pair leaves [0], [1], [8], and [32].  The many
      [None] slots are deliberate: they show that the compact [value_tree]
      skips every complete-tree node whose other side is empty.

<<
slot sketch:
  pair 0  = (v0, 0)
  pair 1  = (v1, 0)
  pairs 2..7 are empty
  pair 8  = (v8, 0)
  pairs 9..31 are empty
  pair 32 = (v32, v32')

value tree:

                 TreeNode
                /        \
           TreeNode     TreeLeaf (v32, v32')
          /        \
     TreeNode     TreeLeaf (v8, 0)
     /      \
TreeLeaf   TreeLeaf
 (v0, 0)   (v1, 0)
>>

      In the ambient complete tree, there are unary stretches from pair [8] up
      to the [0..15] region and from pair [32] up to the [32..63] half.  They
      do not become [TreeNode] constructors because they do not correspond to
      hash merges.  The example lemma [value_tree_from_slots_demo] proves that the
      algorithm returns exactly this compact tree. *)
  Example value_tree_from_slots_demo :
    value_tree_from_slots demo_slots = Some demo_tree.
  (* begin show *)
  Proof.
    reflexivity.
  Qed.
  (* end show *)
End value_tree_demo.

(** Later, the file induced_subtree_bridge.v proves that the complete-tree
    denotation of a tree built by [build_value_tree] satisfies the notion page's
    [minimal_connected_subtree] predicate: the lemma
    [build_value_tree_paper_minimal_connected_subtree] and the uniqueness
    corollary [build_value_tree_unique_paper_minimal_connected_subtree]: but these lemmas
    are not necessary to understand the content of this file.

    Once we have the value tree, a simple tree recursion suffices to produce
    the pre-seal root hash:
 *)
  Fixpoint eval_tree (tree : value_tree) : digest :=
    match tree with
    | TreeLeaf value => H64 leaf_mode value
    | TreeNode lhs rhs =>
        H64 merge_mode (eval_tree lhs, eval_tree rhs)
    end.

  (** Final seal step. This is the main algorithm whose security properties we
      prove below. *)
  Definition root (slots : slot_values) : digest :=
    match value_tree_from_slots slots with
    | None => seal_empty (bitmap_to_bytes16 (slot_bitmap slots))
    | Some tree =>
        seal_nonempty
          (bitmap_to_bytes16 (slot_bitmap slots))
          (eval_tree tree)
    end.

End Algorithm.

(** ** Section 2: Correctness statement

    At this point, we can already state a somewhat weak correctness property like:
[[
  Theorem Root_binding_break_extracts_aligned_collision slots slots' :
    Root slots = Root slots' ->
    normalize_slots slots <> normalize_slots slots' ->
    exists_hash_collision (closure slots) (closure slots').
]]
    where [exists_hash_collision sl sr] says that there is a hash_input (e.g. pair of values) in the set [sl] and there is a hash_input in the set [sr], such that their hash outputs are the same. [closure s] produces a set closed under the hash operations: e.g. calling hash with merge mode on any 2 values in [s].


    But such a property is unnecessarily weak because it treats every hash
    collision in the closure as equally relevant. Hash collisions
    are only problematic if they happen at the same spot in the tree.
    Next, we build some machinery to be able to define "same spot".
    The main step here is to define [root_with_trace], which is like the
    Section 1 root function above, but
    also traces the calls to the hash function and the tree address where each hash happened.
    To make that easy, we first define a slightly augmented version of [value_tree], where
    each node stores its tree address (merge level and horizontal index in the corresponding complete binary tree).

    Intuitively, the proof goes as follows: if two roots are equal, compare
    the two seal hashes first.  If the seal inputs differ, the binding break is
    already a seal collision.  If the seal inputs agree, then the slot bitmap
    agrees, so both computations have the same induced pair-tree shape.  The
    proof can then walk corresponding leaves and internal merge nodes.  At each
    corresponding position, equality of child digests either gives equal inputs
    or exposes a hash collision at that same semantic position.

*)
Section CorrectnessStatement.

(** *** Located hash calls *)

(** Locations are geometric MIP-8 tree positions, not positions in the C++ loop
    trace.  We use [merge_level], not root-depth: [merge_level = 0] merges
    adjacent pair leaves, [merge_level = 1] merges groups of two pairs, and so
    on upward through the complete 64-pair tree.  [parent_index] is the
    horizontal index of that merge at the given level. *)
Inductive call_loc : Type :=
| LocSeal
| LocPairLeaf (pair_index : nat)
| LocNode (merge_level parent_index : nat).

Inductive call_input : Type :=
| InputLeaf (leaf : pair_leaf)
| InputMerge (left_digest right_digest : digest)
| InputSealEmpty (bitmap_bytes : bytes16)
| InputSealNonempty (bitmap_bytes : bytes16) (tree_root : digest).

Record located_call : Type := mk_located_call {
  located_call_loc : call_loc;
  located_call_input : call_input;
}.

(** *** Annotating the compact tree *)

(** Section 1's [value_tree] deliberately omits locations.  This proof-only
    tree is the same tree after annotation: it remembers where each retained
    pair leaf and merge came from in the complete 64-pair tree. *)
Inductive located_value_tree : Type :=
| LocatedTreeLeaf (pair_index : nat) (leaf : pair_leaf)
| LocatedTreeNode
    (merge_level parent_index : nat)
    (left_child right_child : located_value_tree).

(** A compact induced tree cannot recover locations by itself.  If one side of
    a split is empty, [combine_value_trees] erased that side, so the compact
    tree no longer says whether a surviving leaf came from the left or right
    half of the complete tree.

    [annotate_value_tree] therefore walks the compact tree together with the
    original pair-position list.  The list supplies only the missing left/right
    occupancy information; the values and hash shape still come from the
    already-built tree. *)
Fixpoint annotate_value_tree
    (depth start : nat)
    (pairs : list (option pair_leaf)) (tree : value_tree)
    : option located_value_tree :=
  match depth with
  | O =>
      match pairs, tree with
      | [Some _], TreeLeaf value => Some (LocatedTreeLeaf start value)
      | _, _ => None
      end
  | S depth' =>
      let width := subtree_width depth' in
      let lhs_pairs := firstn width pairs in
      let rhs_pairs := skipn width pairs in
      match build_value_tree depth' lhs_pairs,
            build_value_tree depth' rhs_pairs with
      | None, None => None
      | Some _, None =>
          annotate_value_tree depth' start lhs_pairs tree
      | None, Some _ =>
          annotate_value_tree depth' (start + width) rhs_pairs tree
      | Some _, Some _ =>
          match tree with
          | TreeNode lhs rhs =>
              match annotate_value_tree depth' start lhs_pairs lhs,
                    annotate_value_tree
                      depth' (start + width) rhs_pairs rhs with
              | Some lhs_loc, Some rhs_loc =>
                  Some
                    (LocatedTreeNode
                       depth'
                       (start / subtree_width (S depth'))
                       lhs_loc
                       rhs_loc)
              | _, _ => None
              end
          | TreeLeaf _ => None
          end
      end
  end.

Definition annotate_tree_from_slots
    (slots : slot_values) (tree : value_tree)
    : option located_value_tree :=
  annotate_value_tree page_pair_tree_depth 0 (pair_options slots) tree.

(** Annotation recovers the semantic positions erased by the compact tree.
    These positions are the nodes of the ambient complete 64-pair tree.  A
    location [LocNode level parent] covers this pair interval:

<<
parent * 2^(level+1)  through  (parent + 1) * 2^(level+1) - 1
>>

    The level says how wide the complete-tree region is, and the parent index
    says where that region sits horizontally.  A compact [TreeNode] receives a
    [LocNode] exactly when both children of that complete-tree region are
    occupied; unary complete-tree steps are skipped because no hash merge
    happens there.

    These are the locations later used by the aligned-collision statement. *)
Section annotate_tree_demo.
  Variables (v0 v1 v4 v5 : slot_word).

  Let zero : slot_word := bytes32_of_N 0.
  Let singleton_pair_slot (value : slot_word) : slot_values :=
    [Some value; None].
  Let demo_slots : slot_values :=
    singleton_pair_slot v0 ++
    singleton_pair_slot v1 ++
    repeat None 4 ++
    singleton_pair_slot v4 ++
    singleton_pair_slot v5.
  Let pair0 : pair_leaf := (v0, zero).
  Let pair1 : pair_leaf := (v1, zero).
  Let pair4 : pair_leaf := (v4, zero).
  Let pair5 : pair_leaf := (v5, zero).

  Let demo_tree : value_tree :=
    match value_tree_from_slots demo_slots with
    | Some tree => tree
    | None => TreeLeaf pair0
    end.
  Let demo_located_tree : located_value_tree :=
    LocatedTreeNode 2 0
      (LocatedTreeNode 0 0
        (LocatedTreeLeaf 0 pair0)
        (LocatedTreeLeaf 1 pair1))
      (LocatedTreeNode 0 2
        (LocatedTreeLeaf 4 pair4)
        (LocatedTreeLeaf 5 pair5)).

  (** This example shows how [annotate_tree_from_slots] adds ambient
      complete-tree locations to the output of [build_value_tree].

<<
occupied pair leaves:
  0, 1, 4, 5

located merge skeleton:

             LocNode 2 0
            /           \
     LocNode 0 0     LocNode 0 2
      /       \       /       \
 0:(v0,0) 1:(v1,0) 4:(v4,0) 5:(v5,0)
>>

      [LocNode 0 1] does not exist because there were no leaves for positions
      [2] and [3].  No [LocNode] exists at level [1] either: those complete-tree
      nodes are unary stretches, so [build_value_tree] optimized them away.
      The lemma [annotate_tree_from_slots_demo] proves the displayed located
      tree.  The helper lemma [annotate_demo_tree_from_slots] first records
      that the compact tree for [demo_slots] is [demo_tree]. *)
  Example annotate_demo_tree_from_slots :
    value_tree_from_slots demo_slots = Some demo_tree.
  (* begin show *)
  Proof.
    reflexivity.
  Qed.
  (* end show *)

  Example annotate_tree_from_slots_demo :
    annotate_tree_from_slots demo_slots demo_tree =
    Some demo_located_tree.
  (* begin show *)
  Proof.
    reflexivity.
  Qed.
  (* end show *)
End annotate_tree_demo.

  Definition call_digest (input : call_input) : digest :=
    match input with
    | InputLeaf value => H64 leaf_mode value
    | InputMerge lhs rhs => H64 merge_mode (lhs, rhs)
    | InputSealEmpty bm => seal_empty bm
    | InputSealNonempty bm root => seal_nonempty bm root
    end.

  Record root_trace : Type := {
    traced_root : digest;
    traced_calls : list located_call;
  }.

  (** [eval_tree_with_trace] is similar to [eval_tree] above, except it also
      records the semantic locations and inputs for the hash calls. *)
  Fixpoint eval_tree_with_trace (tree : located_value_tree) : root_trace :=
    match tree with
    | LocatedTreeLeaf index value =>
        let input := InputLeaf value in
        {|
          traced_root := call_digest input;
          traced_calls :=
            [mk_located_call (LocPairLeaf index) input];
        |}
    | LocatedTreeNode level parent lhs rhs =>
        let lhs_trace := eval_tree_with_trace lhs in
        let rhs_trace := eval_tree_with_trace rhs in
        let input :=
          InputMerge
            lhs_trace.(traced_root)
            rhs_trace.(traced_root) in
        {|
          traced_root := call_digest input;
          traced_calls :=
            lhs_trace.(traced_calls) ++
            rhs_trace.(traced_calls) ++
            [mk_located_call
               (LocNode level parent)
               input];
        |}
    end.

  (** *** root with trace *)

  (** The traced computation is the proof-facing counterpart of Section 1's
      root function.  It computes the digest and the semantic hash-call trace together,
      so the seal call in the trace visibly uses the same digest returned as
      the root.

      The fallback branch under [Some tree] is unreachable for public
      [slot_values]: Section 3 proves [annotate_tree_from_slots_some].  It is
      present only so this proof-facing function is total without making the
      reader carry an impossible [option] case. *)
  Definition root_with_trace (slots : slot_values)
      : root_trace :=
    match value_tree_from_slots slots with
    | None =>
        let bitmap_bytes := bitmap_to_bytes16 (slot_bitmap slots) in
        {|
          traced_root := seal_empty bitmap_bytes;
          traced_calls :=
            [mk_located_call
               LocSeal
               (InputSealEmpty bitmap_bytes)];
        |}
    | Some tree =>
        let bitmap_bytes := bitmap_to_bytes16 (slot_bitmap slots) in
        match annotate_tree_from_slots slots tree with
        | Some located_tree =>
            let tree_trace := eval_tree_with_trace located_tree in
            let tree_root := tree_trace.(traced_root) in
            {|
              traced_root := seal_nonempty bitmap_bytes tree_root;
              traced_calls :=
                tree_trace.(traced_calls) ++
                [mk_located_call
                   LocSeal
                   (InputSealNonempty bitmap_bytes tree_root)];
            |}
        | None =>
            {|
              traced_root := seal_nonempty bitmap_bytes (eval_tree tree);
              traced_calls :=
                [mk_located_call
                   LocSeal
                   (InputSealNonempty bitmap_bytes (eval_tree tree))];
            |}
        end
    end.

  Section root_with_trace_demo.
    Variables (v1 v2 v3 : slot_word).

    Let zero : slot_word := bytes32_of_N 0.
    Let leaf0 : pair_leaf := (v1, zero).
    Let leaf1 : pair_leaf := (v2, v1).
    Let leaf2 : pair_leaf := (v3, zero).
    Let demo_slots : slot_values :=
      [Some v1; None; Some v2; Some v1; Some v3].
    Let demo_located_tree : located_value_tree :=
      LocatedTreeNode 1 0
        (LocatedTreeNode 0 0
          (LocatedTreeLeaf 0 leaf0)
          (LocatedTreeLeaf 1 leaf1))
        (LocatedTreeLeaf 2 leaf2).
    Let demo_bitmap : bytes16 :=
      bitmap_to_bytes16 (slot_bitmap demo_slots).
    Let leaf0_digest : digest := call_digest (InputLeaf leaf0).
    Let leaf1_digest : digest := call_digest (InputLeaf leaf1).
    Let leaf2_digest : digest := call_digest (InputLeaf leaf2).
    Let merge01_input : call_input :=
      InputMerge leaf0_digest leaf1_digest.
    Let merge01_digest : digest := call_digest merge01_input.
    Let merge012_input : call_input :=
      InputMerge merge01_digest leaf2_digest.
    Let merge012_digest : digest := call_digest merge012_input.

    (** The example lemma proves the result of [root_with_trace] on [demo_slots] *)
    Example root_with_trace_demo :
      root_with_trace demo_slots =
      {|
        traced_root := seal_nonempty demo_bitmap merge012_digest;
        traced_calls :=
          [mk_located_call (LocPairLeaf 0) (InputLeaf leaf0);
           mk_located_call (LocPairLeaf 1) (InputLeaf leaf1);
           mk_located_call (LocNode 0 0) merge01_input;
           mk_located_call (LocPairLeaf 2) (InputLeaf leaf2);
           mk_located_call (LocNode 1 0) merge012_input;
           mk_located_call
             LocSeal
             (InputSealNonempty demo_bitmap merge012_digest)];
      |}.
    (* begin show *)
    Proof.
      reflexivity.
    Qed.
    (* end show *)
  End root_with_trace_demo.

  (** An [exists_aligned_collision] is the precise bad event for binding.  It does not
      say that some two hash calls anywhere collided.  It says that the two
      compared traces contain calls at the same semantic location, with
      different inputs and equal hash outputs. *)
  Definition exists_aligned_collision
      (trace trace' : root_trace) : Prop :=
    exists loc input input',
      In (mk_located_call loc input)
        trace.(traced_calls) /\
      In (mk_located_call loc input')
        trace'.(traced_calls) /\
      input <> input' /\
      call_digest input = call_digest input'.

  (** *** Main theorem statements *)

  (** The first theorem says that [root_with_trace] is only proof
      instrumentation.  Adding semantic call locations and a trace does not
      change the root computed by the compact Section 1 algorithm.
      We have aborted this theorem proof here and will prove it later in the file.
   *)
  Theorem root_with_trace_root_statement slots :
    (root_with_trace slots).(traced_root) = root slots.
  Proof.
  Abort.

  (** [Root_binding_break_extracts_aligned_collision] is the binding theorem in
      its most informative form.  It does not assume collision freedom.  It
      says that if two normalized page views are different but their traced
      computations return the same digest, then the two traces contain an
      aligned collision.

      The statement is phrased directly with [root_with_trace] because the
      trace is part of the evidence: [exists_aligned_collision] refers directly to the
      two traced computations produced by [root_with_trace]. The above theorem
      anyway proves that [root_with_trace] and the Section 1 root function
      produce the same root hash.
   *)
  Theorem Root_binding_break_extracts_aligned_collision_statement
      slots slots' :
    (root_with_trace slots).(traced_root) = (root_with_trace slots').(traced_root) ->
    normalize_slots slots <> normalize_slots slots' ->
    exists_aligned_collision (root_with_trace slots) (root_with_trace slots').
  Proof.
  Abort.

(** Forward reference: the C++ proof layer uses this file's Section 1 root function as
    the pure model for [monad::page_commit].  The exact C++ postcondition is in
    [page_commit_spec]. *)

End CorrectnessStatement.

(** ** Section 3: Correctness proof

    The rest of the file is proof machinery.  The first group of lemmas shows
    that the compact recursive algorithm has the expected bitmap and value
    properties.  Later lemmas show that annotation preserves the compact tree
    root, that located traces line up with root computation, and that equality
    of roots can be pushed down through aligned locations.

    Some definitions in this section look closer to the C++ implementation than
    Section 1 does.  They are proof instrumentation, not the primary
    specification.  Their job is to justify the same induced-tree intuition that
    the C++ scratch-array reducer implements.
*)
Section CorrectnessProof.

  #[local] Instance call_loc_eq_decision : EqDecision call_loc.
  Proof.
    solve_decision.
  Defined.

  Definition call_loc_eq_dec
      (loc loc' : call_loc) : {loc = loc'} + {loc <> loc'} :=
    decide (loc = loc').

  #[local] Instance call_input_eq_decision : EqDecision call_input.
  Proof.
    solve_decision.
  Defined.

  Definition call_input_eq_dec
      (input input' : call_input) : {input = input'} + {input <> input'} :=
    decide (input = input').

  (** These are proof-only views of the traced located tree.  Section 2 keeps
      only [eval_tree_with_trace], where root computation and trace construction
      happen together; the projections below make later inductions shorter. *)
  Fixpoint erase_located_tree (tree : located_value_tree) : value_tree :=
    match tree with
    | LocatedTreeLeaf _ value => TreeLeaf value
    | LocatedTreeNode _ _ lhs rhs =>
        TreeNode (erase_located_tree lhs) (erase_located_tree rhs)
    end.

  Definition eval_located_tree (tree : located_value_tree) : digest :=
    (eval_tree_with_trace tree).(traced_root).

  Fixpoint located_tree_values
      (tree : located_value_tree) : list pair_leaf :=
    match tree with
    | LocatedTreeLeaf _ value => [value]
    | LocatedTreeNode _ _ lhs rhs =>
        located_tree_values lhs ++ located_tree_values rhs
    end.

  Definition tree_located_calls (tree : located_value_tree)
      : list located_call :=
    (eval_tree_with_trace tree).(traced_calls).

  Definition slot_from_bit (present : bool) (value : slot_word)
      : option slot_word :=
    if present then Some value else None.

  Fixpoint pair_bitmap_from_slot_bitmap
      (bm : bitmap) : bitmap :=
    match bm with
    | first :: second :: rest =>
        (first || second) :: pair_bitmap_from_slot_bitmap rest
    | [last] => [last]
    | [] => []
    end.

  Fixpoint pair_leaves_raw (slots : slot_values) : list pair_leaf :=
    match slots with
    | first :: second :: rest =>
        (slot_payload first, slot_payload second) :: pair_leaves_raw rest
    | _ => []
    end.

  Fixpoint select_by_bitmap {A : Type}
      (bm : bitmap) (values : list A) : list A :=
    match bm, values with
    | occupied :: bm_rest, value :: values_rest =>
        if occupied
        then value :: select_by_bitmap bm_rest values_rest
        else select_by_bitmap bm_rest values_rest
    | _, _ => []
    end.

  Definition pair_bitmap (slots : slot_values) : bitmap :=
    pair_bitmap_from_slot_bitmap (slot_bitmap slots).

  Definition pair_leaves (slots : slot_values) : list pair_leaf :=
    pair_leaves_raw (normalize_slots slots).

  Definition active_pair_values (slots : slot_values) : list pair_leaf :=
    select_by_bitmap (pair_bitmap slots) (pair_leaves slots).

  Definition pair_option_present (pair_value : option pair_leaf) : bool :=
    match pair_value with
    | Some _ => true
    | None => false
    end.

  Definition pair_option_bitmap (pairs : list (option pair_leaf))
      : bitmap :=
    map pair_option_present pairs.

  Fixpoint pair_option_values
      (pairs : list (option pair_leaf)) : list pair_leaf :=
    match pairs with
    | [] => []
    | Some pair_value :: rest => pair_value :: pair_option_values rest
    | None :: rest => pair_option_values rest
    end.

  Definition index_bit_is_zero (bit index : nat) : bool :=
    Nat.even (index / subtree_width bit).

  Definition same_parent_at_level (bit lhs rhs : nat) : bool :=
    Nat.eqb (lhs / subtree_width (S bit)) (rhs / subtree_width (S bit)).

  Definition sibling_candidate (bit lhs rhs : nat) : bool :=
    same_parent_at_level bit lhs rhs &&
    index_bit_is_zero bit lhs.

  (** The following reducer mirrors the C++ scratch/live-bitmap loop.  It is
      proof instrumentation: Section 1 already gave the readable recursive
      value-tree algorithm. *)
  Record live_node : Type := {
    live_index : nat;
    live_tree : value_tree;
  }.

  Fixpoint active_leaf_nodes_from
      (next_index : nat) (bm : bitmap) (values : list pair_leaf)
      : option (list live_node * list pair_leaf) :=
    match bm with
    | [] => Some ([], values)
    | occupied :: rest =>
        if occupied
        then
          match values with
          | [] => None
          | value :: values_rest =>
              match active_leaf_nodes_from
                      (S next_index) rest values_rest with
              | Some (nodes, leftover) =>
                  Some
                    ({|
                       live_index := next_index;
                       live_tree := TreeLeaf value;
                     |} :: nodes, leftover)
              | None => None
              end
          end
        else active_leaf_nodes_from (S next_index) rest values
    end.

  Definition active_leaf_nodes
      (bm : bitmap) (values : list pair_leaf) : option (list live_node) :=
    match active_leaf_nodes_from 0 bm values with
    | Some (nodes, []) => Some nodes
    | _ => None
    end.

  Fixpoint merge_level (bit : nat) (nodes : list live_node)
      : list live_node :=
    match nodes with
    | [] => []
    | current :: rest_nodes =>
        match rest_nodes with
        | [] => [current]
        | next :: later =>
            if sibling_candidate bit
                 current.(live_index) next.(live_index)
            then
              {|
                live_index := current.(live_index);
                live_tree :=
                  TreeNode current.(live_tree) next.(live_tree);
              |} :: merge_level bit later
            else current :: merge_level bit rest_nodes
        end
    end.

  Fixpoint reduce_levels
      (fuel bit : nat) (nodes : list live_node) : list live_node :=
    match fuel with
    | O => nodes
    | S fuel' =>
        if length nodes <=? 1
        then nodes
        else reduce_levels fuel' (S bit) (merge_level bit nodes)
    end.

  Inductive commit_result : Type :=
  | CommitMalformed
  | CommitEmpty
  | CommitNonempty (tree : value_tree).

  Definition reducer_result
      (depth : nat) (bm : bitmap) (values : list pair_leaf)
      : commit_result :=
    match active_leaf_nodes bm values with
    | None => CommitMalformed
    | Some [] => CommitEmpty
    | Some nodes =>
        match reduce_levels depth 0 nodes with
        | [root] => CommitNonempty root.(live_tree)
        | _ => CommitMalformed
        end
    end.

  Fixpoint tree_values (tree : value_tree) : list pair_leaf :=
    match tree with
    | TreeLeaf value => [value]
    | TreeNode lhs rhs => tree_values lhs ++ tree_values rhs
    end.

  Definition live_values (nodes : list live_node) : list pair_leaf :=
    concat (map (fun node => tree_values node.(live_tree)) nodes).

  Inductive same_tree_shape : value_tree -> value_tree -> Prop :=
  | SameTreeLeaf (lhs_value rhs_value : pair_leaf) :
        same_tree_shape
          (TreeLeaf lhs_value)
          (TreeLeaf rhs_value)
  | SameTreeNode
      (lhs lhs' rhs rhs' : value_tree) :
        same_tree_shape lhs lhs' ->
        same_tree_shape rhs rhs' ->
        same_tree_shape
          (TreeNode lhs rhs)
          (TreeNode lhs' rhs').

  Inductive same_located_tree_shape :
      located_value_tree -> located_value_tree -> Prop :=
  | SameLocatedTreeLeaf
      (index : nat) (lhs_value rhs_value : pair_leaf) :
        same_located_tree_shape
          (LocatedTreeLeaf index lhs_value)
          (LocatedTreeLeaf index rhs_value)
  | SameLocatedTreeNode
      (level parent : nat)
      (lhs lhs' rhs rhs' : located_value_tree) :
        same_located_tree_shape lhs lhs' ->
        same_located_tree_shape rhs rhs' ->
        same_located_tree_shape
          (LocatedTreeNode level parent lhs rhs)
          (LocatedTreeNode level parent lhs' rhs').

  Definition same_live_shape (lhs rhs : live_node) : Prop :=
    live_index lhs = live_index rhs /\
    same_tree_shape (live_tree lhs) (live_tree rhs).

  Definition valid_seal_bitmap (bm : bitmap) : Prop :=
    length bm = 128.

  Fixpoint slots_from_bitmap_values
      (bm : bitmap) (values : list pair_leaf) : option slot_values :=
    match bm with
    | [] =>
        match values with
        | [] => Some []
        | _ :: _ => None
        end
    | first :: second :: bm_rest =>
        if first || second
        then
          match values with
          | (first_value, second_value) :: values_rest =>
              match slots_from_bitmap_values bm_rest values_rest with
              | Some slots_rest =>
                  Some
                    (slot_from_bit first first_value ::
                     slot_from_bit second second_value ::
                     slots_rest)
              | None => None
              end
          | [] => None
          end
        else
          match slots_from_bitmap_values bm_rest values with
          | Some slots_rest => Some (None :: None :: slots_rest)
          | None => None
          end
    | [_] => None
    end.

  (** Basic facts about the algorithmic definitions from Section 1. *)
  Lemma normalize_slots_length slots :
    length (normalize_slots slots) = page_slot_count.
  Proof.
    unfold normalize_slots, page_slot_count.
    rewrite length_firstn, length_app, repeat_length.
    lia.
  Qed.

  Lemma normalize_slots_even slots :
    Nat.even (length (normalize_slots slots)) = true.
  Proof.
    rewrite normalize_slots_length.
    reflexivity.
  Qed.

  Lemma slot_from_present_payload slot :
    slot_from_bit (slot_present slot) (slot_payload slot) = slot.
  Proof.
    destruct slot; reflexivity.
  Qed.

  Lemma bitmap_to_N_lt_length bm :
    (bitmap_to_N bm < 2 ^ N.of_nat (length bm))%N.
  Proof.
    induction bm as [| bit rest IH]; simpl.
    { lia. }
    change
      (((if bit then 1 else 0) + 2 * bitmap_to_N rest <
        2 ^ N.of_nat (S (length rest)))%N).
    rewrite Nat2N.inj_succ.
    rewrite N.pow_succ_r'.
    destruct bit; nia.
  Qed.

  Lemma bitmap_to_N_lt_128 bm :
    length bm <= 128 -> (bitmap_to_N bm < pow2N 128)%N.
  Proof.
    intro Hlen.
    eapply N.lt_le_trans.
    { apply bitmap_to_N_lt_length. }
    unfold pow2N.
    apply N.pow_le_mono_r; [discriminate | lia].
  Qed.

  Lemma bitmap_to_bytes16_to_N bm :
    length bm <= 128 ->
    fin.to_N (bitmap_to_bytes16 bm) = bitmap_to_N bm.
  Proof.
    intro Hlen.
    unfold bitmap_to_bytes16.
    apply fin.to_of_N'.
    now apply bitmap_to_N_lt_128.
  Qed.

  Lemma bitmap_to_N_inj_same_length bm bm' :
    length bm = length bm' ->
    bitmap_to_N bm = bitmap_to_N bm' ->
    bm = bm'.
  Proof.
    revert bm'.
    induction bm as [| bit rest IH]; intros bm' Hlen Henc.
    { destruct bm'; [reflexivity | discriminate]. }
    destruct bm' as [| bit' rest']; [discriminate |].
    simpl in Henc.
    inversion Hlen as [Hlen_tail].
    destruct bit, bit'; simpl in Henc.
    { f_equal; eapply IH; eauto; nia. }
    { exfalso; nia. }
    { exfalso; nia. }
    { f_equal; eapply IH; eauto; nia. }
  Qed.

  Lemma bitmap_to_bytes16_inj bm bm' :
    valid_seal_bitmap bm ->
    valid_seal_bitmap bm' ->
    bitmap_to_bytes16 bm = bitmap_to_bytes16 bm' ->
    bm = bm'.
  Proof.
    intros Hlen Hlen' Hbytes.
    apply bitmap_to_N_inj_same_length.
    { unfold valid_seal_bitmap in *; lia. }
    pose proof (f_equal fin.to_N Hbytes) as HN.
    rewrite !bitmap_to_bytes16_to_N in HN
      by (unfold valid_seal_bitmap in *; lia).
    exact HN.
  Qed.

  Lemma pair_options_raw_length_exact slots n :
    length slots = 2 * n ->
    length (pair_options_raw slots) = n.
  Proof.
    revert slots.
    induction n as [| n IH]; intros slots Hlen.
    { destruct slots as [| first [| second rest]]; simpl in *; lia. }
    destruct slots as [| first [| second rest]]; simpl in Hlen; [lia | lia |].
    simpl.
    destruct (slot_present first || slot_present second); simpl;
      rewrite IH by lia; reflexivity.
  Qed.

  Lemma pair_options_length slots :
    length (pair_options slots) = page_pair_count.
  Proof.
    unfold pair_options, page_pair_count.
    apply pair_options_raw_length_exact.
    rewrite normalize_slots_length.
    reflexivity.
  Qed.

  Lemma pair_options_bitmap_raw_even slots :
    Nat.even (length slots) = true ->
    pair_option_bitmap (pair_options_raw slots) =
    pair_bitmap_from_slot_bitmap (map slot_present slots).
  Proof.
    revert slots.
    fix IH 1.
    intros slots Heven.
    destruct slots as [| first [| second rest]]; simpl in *;
      [reflexivity | discriminate |].
    destruct (slot_present first || slot_present second); simpl;
      now rewrite IH.
  Qed.

  Lemma pair_options_bitmap slots :
    pair_option_bitmap (pair_options slots) = pair_bitmap slots.
  Proof.
    unfold pair_options, pair_bitmap, slot_bitmap.
    apply pair_options_bitmap_raw_even.
    apply normalize_slots_even.
  Qed.

  Lemma pair_options_values_raw slots :
    pair_option_values (pair_options_raw slots) =
    select_by_bitmap
      (pair_bitmap_from_slot_bitmap (map slot_present slots))
      (pair_leaves_raw slots).
  Proof.
    revert slots.
    fix IH 1.
    intros slots.
    destruct slots as [| first [| second rest]]; simpl; [reflexivity.. |].
    destruct (slot_present first || slot_present second); simpl;
      now rewrite IH.
  Qed.

  Lemma pair_options_values slots :
    pair_option_values (pair_options slots) = active_pair_values slots.
  Proof.
    unfold pair_options, active_pair_values, pair_bitmap, pair_leaves,
      slot_bitmap.
    apply pair_options_values_raw.
  Qed.

  Lemma slots_from_bitmap_values_roundtrip_even slots :
    Nat.even (length slots) = true ->
    slots_from_bitmap_values
      (map slot_present slots)
      (select_by_bitmap
         (pair_bitmap_from_slot_bitmap (map slot_present slots))
         (pair_leaves_raw slots)) =
    Some slots.
  Proof.
    revert slots.
    fix IH 1.
    intros slots Heven.
    destruct slots as [| first rest].
    { reflexivity. }
    destruct rest as [| second rest].
    { discriminate. }
    simpl in Heven.
    simpl.
    destruct first as [first_value |];
      destruct second as [second_value |]; simpl;
      rewrite IH by exact Heven;
      rewrite ?slot_from_present_payload;
      reflexivity.
  Qed.

  Lemma slots_from_bitmap_values_roundtrip slots :
    slots_from_bitmap_values
      (slot_bitmap slots)
      (active_pair_values slots) =
    Some (normalize_slots slots).
  Proof.
    unfold slot_bitmap, active_pair_values, pair_bitmap, pair_leaves.
    apply slots_from_bitmap_values_roundtrip_even.
    apply normalize_slots_even.
  Qed.

  Lemma slot_bitmap_valid slots :
    valid_seal_bitmap (slot_bitmap slots).
  Proof.
    unfold valid_seal_bitmap, slot_bitmap.
    rewrite length_map.
    now rewrite normalize_slots_length.
  Qed.

  Lemma tree_values_nonempty tree :
    tree_values tree <> [].
  Proof.
    induction tree as [value | lhs IHlhs rhs IHrhs]; simpl.
    { discriminate. }
    intro Hempty.
    apply app_eq_nil in Hempty as [Hlhs _].
    exact (IHlhs Hlhs).
  Qed.

  Lemma eval_located_tree_erase tree :
    eval_tree (erase_located_tree tree) = eval_located_tree tree.
  Proof.
    induction tree as [index value | level parent lhs IHlhs rhs IHrhs];
      simpl; [reflexivity |].
    now rewrite IHlhs, IHrhs.
  Qed.

  Lemma located_tree_values_erase tree :
    tree_values (erase_located_tree tree) = located_tree_values tree.
  Proof.
    induction tree as [index value | level parent lhs IHlhs rhs IHrhs];
      simpl; [reflexivity |].
    now rewrite IHlhs, IHrhs.
  Qed.

  Lemma pair_option_values_app lhs rhs :
    pair_option_values (lhs ++ rhs) =
    pair_option_values lhs ++ pair_option_values rhs.
  Proof.
    induction lhs as [| [pair_value |] rest IH]; simpl; [reflexivity | |];
      now rewrite IH.
  Qed.

  Lemma pair_option_values_firstn_skipn width pairs :
    pair_option_values pairs =
    pair_option_values (firstn width pairs) ++
    pair_option_values (skipn width pairs).
  Proof.
    rewrite <- pair_option_values_app.
    now rewrite firstn_skipn.
  Qed.

  Lemma build_tree_values_or_empty depth pairs :
    length pairs = subtree_width depth ->
    match build_value_tree depth pairs with
    | Some tree => tree_values tree = pair_option_values pairs
    | None => pair_option_values pairs = []
    end.
  Proof.
    revert pairs.
    induction depth as [| depth IHdepth]; intros pairs Hlen.
    { destruct pairs as [| [pair_value |] [| extra rest]]; simpl in *;
        try lia; reflexivity. }
    simpl in Hlen.
    simpl.
    set (width := subtree_width depth).
    assert (Hleft_len : length (firstn width pairs) = subtree_width depth).
    { subst width.
      rewrite length_firstn.
      lia. }
    assert (Hright_len : length (skipn width pairs) = subtree_width depth).
    { subst width.
      rewrite length_skipn.
      lia. }
    pose proof (IHdepth (firstn width pairs) Hleft_len)
      as Hleft_values.
    pose proof (IHdepth (skipn width pairs) Hright_len)
      as Hright_values.
    destruct (build_value_tree depth (firstn width pairs))
      as [lhs |] eqn:Hlhs;
      destruct (build_value_tree depth (skipn width pairs))
        as [rhs |] eqn:Hrhs; simpl in *.
    { rewrite Hleft_values, Hright_values.
      rewrite (pair_option_values_firstn_skipn width pairs).
      reflexivity. }
    { rewrite Hleft_values.
      rewrite (pair_option_values_firstn_skipn width pairs).
      rewrite Hright_values, app_nil_r.
      reflexivity. }
    { rewrite Hright_values.
      rewrite (pair_option_values_firstn_skipn width pairs).
      now rewrite Hleft_values.
    }
    { rewrite (pair_option_values_firstn_skipn width pairs).
      now rewrite Hleft_values, Hright_values.
    }
  Qed.

  Lemma value_tree_from_slots_values slots tree :
    value_tree_from_slots slots = Some tree ->
    tree_values tree = active_pair_values slots.
  Proof.
    unfold value_tree_from_slots.
    pose proof
      (build_tree_values_or_empty
         page_pair_tree_depth (pair_options slots)
         (pair_options_length slots))
      as Hvalues.
    destruct (build_value_tree page_pair_tree_depth (pair_options slots))
      as [tree' |] eqn:Hbuild; [| discriminate].
    intro Htree.
    inversion Htree; subst tree'; clear Htree.
    now rewrite Hvalues, pair_options_values.
  Qed.

  Lemma value_tree_from_slots_empty_values slots :
    value_tree_from_slots slots = None ->
    active_pair_values slots = [].
  Proof.
    unfold value_tree_from_slots.
    pose proof
      (build_tree_values_or_empty
         page_pair_tree_depth (pair_options slots)
         (pair_options_length slots))
      as Hvalues.
    destruct (build_value_tree page_pair_tree_depth (pair_options slots))
      as [tree |] eqn:Hbuild; [discriminate |].
    intro Hnone.
    now rewrite <- pair_options_values.
  Qed.

  Lemma build_tree_same_bitmap depth pairs pairs' :
    length pairs = subtree_width depth ->
    length pairs' = subtree_width depth ->
    pair_option_bitmap pairs = pair_option_bitmap pairs' ->
    match build_value_tree depth pairs,
          build_value_tree depth pairs' with
    | Some tree, Some tree' => same_tree_shape tree tree'
    | None, None => True
    | _, _ => False
    end.
  Proof.
    revert pairs pairs'.
    induction depth as [| depth IH]; intros pairs pairs'
      Hlen Hlen' Hbitmap.
    { destruct pairs as [| [pair |] [| extra rest]];
        destruct pairs' as [| [pair' |] [| extra' rest']];
        simpl in *; try lia; try discriminate; constructor. }
    simpl in Hlen, Hlen'.
    simpl.
    set (width := subtree_width depth).
    assert (Hleft_len : length (firstn width pairs) = subtree_width depth).
    { subst width; rewrite length_firstn; lia. }
    assert (Hright_len : length (skipn width pairs) = subtree_width depth).
    { subst width; rewrite length_skipn; lia. }
    assert (Hleft_len' : length (firstn width pairs') = subtree_width depth).
    { subst width; rewrite length_firstn; lia. }
    assert (Hright_len' : length (skipn width pairs') = subtree_width depth).
    { subst width; rewrite length_skipn; lia. }
    assert
      (Hbitmap_left :
         pair_option_bitmap (firstn width pairs) =
         pair_option_bitmap (firstn width pairs')).
    { unfold pair_option_bitmap in *.
      rewrite <- !firstn_map.
      now rewrite Hbitmap. }
    assert
      (Hbitmap_right :
         pair_option_bitmap (skipn width pairs) =
         pair_option_bitmap (skipn width pairs')).
    { unfold pair_option_bitmap in *.
      rewrite <- !skipn_map.
      now rewrite Hbitmap. }
    pose proof
      (IH (firstn width pairs) (firstn width pairs')
         Hleft_len Hleft_len' Hbitmap_left)
      as Hleft.
    pose proof
      (IH (skipn width pairs) (skipn width pairs')
         Hright_len Hright_len' Hbitmap_right)
      as Hright.
    destruct (build_value_tree depth (firstn width pairs))
      as [lhs |];
      destruct (build_value_tree depth (firstn width pairs'))
        as [lhs' |];
      destruct (build_value_tree depth (skipn width pairs))
        as [rhs |];
      destruct (build_value_tree depth (skipn width pairs'))
        as [rhs' |];
      simpl in *; try contradiction; auto; constructor; assumption.
  Qed.

  Lemma annotate_value_tree_build_some depth start pairs tree :
    length pairs = subtree_width depth ->
    build_value_tree depth pairs = Some tree ->
    exists located_tree,
      annotate_value_tree depth start pairs tree = Some located_tree /\
      erase_located_tree located_tree = tree.
  Proof.
    revert start pairs tree.
    induction depth as [| depth IH]; intros start pairs tree Hlen Hbuild.
    { destruct pairs as [| [pair |] [| extra rest]]; simpl in *;
        try lia; try discriminate.
      inversion Hbuild; subst; clear Hbuild.
      exists (LocatedTreeLeaf start pair).
      split; reflexivity. }
    simpl in Hlen, Hbuild.
    simpl.
    assert
      (Hleft_len :
         length (firstn (subtree_width depth) pairs) =
         subtree_width depth).
    { rewrite length_firstn; lia. }
    assert
      (Hright_len :
         length (skipn (subtree_width depth) pairs) =
         subtree_width depth).
    { rewrite length_skipn; lia. }
    destruct (build_value_tree depth (firstn (subtree_width depth) pairs))
      as [lhs |] eqn:Hlhs;
      destruct (build_value_tree depth (skipn (subtree_width depth) pairs))
        as [rhs |] eqn:Hrhs; simpl in Hbuild.
    { inversion Hbuild; subst; clear Hbuild.
      destruct
        (IH start
           (firstn (subtree_width depth) pairs) lhs Hleft_len Hlhs)
        as [lhs_loc [Hlhs_loc Herase_lhs]].
      destruct
        (IH
           (start + subtree_width depth)
           (skipn (subtree_width depth) pairs)
           rhs Hright_len Hrhs)
        as [rhs_loc [Hrhs_loc Herase_rhs]].
      rewrite Hlhs_loc, Hrhs_loc.
      exists
        (LocatedTreeNode
           depth
           (start / subtree_width (S depth))
           lhs_loc
           rhs_loc).
      simpl.
      split; [reflexivity |].
      now rewrite Herase_lhs, Herase_rhs. }
    { inversion Hbuild; subst; clear Hbuild.
      exact
        (IH start
           (firstn (subtree_width depth) pairs) tree Hleft_len Hlhs). }
    { inversion Hbuild; subst; clear Hbuild.
      exact
        (IH
           (start + subtree_width depth)
           (skipn (subtree_width depth) pairs)
           tree Hright_len Hrhs). }
    discriminate.
  Qed.

  Lemma annotate_tree_from_slots_some slots tree :
    value_tree_from_slots slots = Some tree ->
    exists located_tree,
      annotate_tree_from_slots slots tree = Some located_tree /\
      erase_located_tree located_tree = tree.
  Proof.
    unfold value_tree_from_slots, annotate_tree_from_slots.
    intro Htree.
    eapply annotate_value_tree_build_some; eauto.
    apply pair_options_length.
  Qed.

  (** First main theorem: the traced computation agrees with the small
      algorithmic specification from Section 1.  The proof is intentionally simple: it
      unfolds both computations and checks that the trace records the same seal
      digest that the Section 1 root function returns. *)
  Theorem root_with_trace_root slots :
    (root_with_trace slots).(traced_root) = root slots.
  Proof.
    unfold root_with_trace, root.
    destruct (value_tree_from_slots slots) as [tree |] eqn:Htree;
      simpl.
    { destruct (annotate_tree_from_slots_some slots tree Htree)
        as [located [Hannot Herase]].
      rewrite Hannot.
      fold (eval_located_tree located).
      rewrite <- eval_located_tree_erase.
      rewrite Herase.
      reflexivity. }
    reflexivity.
  Qed.

  Lemma annotate_value_tree_same_shape
      depth start pairs pairs' tree tree' located located' :
    length pairs = subtree_width depth ->
    length pairs' = subtree_width depth ->
    pair_option_bitmap pairs = pair_option_bitmap pairs' ->
    annotate_value_tree depth start pairs tree = Some located ->
    annotate_value_tree depth start pairs' tree' = Some located' ->
    same_located_tree_shape located located'.
  Proof.
    revert start pairs pairs' tree tree' located located'.
    induction depth as [| depth IH]; intros start pairs pairs'
      tree tree' located located' Hlen Hlen' Hbitmap Hannot Hannot'.
    { destruct pairs as [| [pair |] [| extra rest]];
        destruct pairs' as [| [pair' |] [| extra' rest']];
        destruct tree as [value | lhs rhs];
        destruct tree' as [value' | lhs' rhs'];
        simpl in *; try lia; try discriminate.
      inversion Hannot; inversion Hannot'; subst.
      constructor. }
    simpl in Hlen, Hlen'.
    simpl in Hannot, Hannot'.
    assert
      (Hleft_len :
         length (firstn (subtree_width depth) pairs) =
         subtree_width depth).
    { rewrite length_firstn; lia. }
    assert
      (Hright_len :
         length (skipn (subtree_width depth) pairs) =
         subtree_width depth).
    { rewrite length_skipn; lia. }
    assert
      (Hleft_len' :
         length (firstn (subtree_width depth) pairs') =
         subtree_width depth).
    { rewrite length_firstn; lia. }
    assert
      (Hright_len' :
         length (skipn (subtree_width depth) pairs') =
         subtree_width depth).
    { rewrite length_skipn; lia. }
    assert
      (Hbitmap_left :
         pair_option_bitmap (firstn (subtree_width depth) pairs) =
         pair_option_bitmap (firstn (subtree_width depth) pairs')).
    { unfold pair_option_bitmap in *.
      rewrite <- !firstn_map.
      now rewrite Hbitmap. }
    assert
      (Hbitmap_right :
         pair_option_bitmap (skipn (subtree_width depth) pairs) =
         pair_option_bitmap (skipn (subtree_width depth) pairs')).
    { unfold pair_option_bitmap in *.
      rewrite <- !skipn_map.
      now rewrite Hbitmap. }
    pose proof
      (build_tree_same_bitmap
         depth
         (firstn (subtree_width depth) pairs)
         (firstn (subtree_width depth) pairs')
         Hleft_len Hleft_len' Hbitmap_left)
      as Hleft_status.
    pose proof
      (build_tree_same_bitmap
         depth
         (skipn (subtree_width depth) pairs)
         (skipn (subtree_width depth) pairs')
         Hright_len Hright_len' Hbitmap_right)
      as Hright_status.
    destruct (build_value_tree depth (firstn (subtree_width depth) pairs))
      as [lhs |] eqn:Hlhs;
      destruct (build_value_tree depth (firstn (subtree_width depth) pairs'))
        as [lhs' |] eqn:Hlhs';
      destruct (build_value_tree depth (skipn (subtree_width depth) pairs))
        as [rhs |] eqn:Hrhs;
      destruct (build_value_tree depth (skipn (subtree_width depth) pairs'))
        as [rhs' |] eqn:Hrhs';
      simpl in Hleft_status, Hright_status;
      try contradiction.
    { destruct tree as [value | tree_lhs tree_rhs]; [discriminate |].
      destruct tree' as [value' | tree_lhs' tree_rhs']; [discriminate |].
      destruct
        (annotate_value_tree
           depth start
           (firstn (subtree_width depth) pairs) tree_lhs)
        as [located_lhs |] eqn:Hannot_lhs; [| discriminate].
      destruct
        (annotate_value_tree
           depth (start + subtree_width depth)
           (skipn (subtree_width depth) pairs) tree_rhs)
        as [located_rhs |] eqn:Hannot_rhs; [| discriminate].
      destruct
        (annotate_value_tree
           depth start
           (firstn (subtree_width depth) pairs') tree_lhs')
        as [located_lhs' |] eqn:Hannot_lhs'; [| discriminate].
      destruct
        (annotate_value_tree
           depth (start + subtree_width depth)
           (skipn (subtree_width depth) pairs') tree_rhs')
        as [located_rhs' |] eqn:Hannot_rhs'; [| discriminate].
      inversion Hannot; inversion Hannot'; subst.
      pose proof
        (IH
           start
           (firstn (subtree_width depth) pairs)
           (firstn (subtree_width depth) pairs')
           tree_lhs tree_lhs'
           located_lhs located_lhs'
           Hleft_len Hleft_len' Hbitmap_left
           Hannot_lhs Hannot_lhs')
        as Hsame_lhs.
      pose proof
        (IH
           (start + subtree_width depth)
           (skipn (subtree_width depth) pairs)
           (skipn (subtree_width depth) pairs')
           tree_rhs tree_rhs'
           located_rhs located_rhs'
           Hright_len Hright_len' Hbitmap_right
           Hannot_rhs Hannot_rhs')
        as Hsame_rhs.
      exact
        (SameLocatedTreeNode
           depth
           (start / subtree_width (S depth))
           located_lhs located_lhs'
           located_rhs located_rhs'
           Hsame_lhs Hsame_rhs). }
    { exact
        (IH
           start
           (firstn (subtree_width depth) pairs)
           (firstn (subtree_width depth) pairs')
           tree tree'
           located located'
           Hleft_len Hleft_len' Hbitmap_left
           Hannot Hannot'). }
    { exact
        (IH
           (start + subtree_width depth)
           (skipn (subtree_width depth) pairs)
           (skipn (subtree_width depth) pairs')
           tree tree'
           located located'
           Hright_len Hright_len' Hbitmap_right
           Hannot Hannot'). }
    { discriminate. }
  Qed.

  Lemma annotate_tree_from_slots_same_shape
      slots slots' tree tree' located located' :
    slot_bitmap slots = slot_bitmap slots' ->
    annotate_tree_from_slots slots tree = Some located ->
    annotate_tree_from_slots slots' tree' = Some located' ->
    same_located_tree_shape located located'.
  Proof.
    intros Hslot_bitmap Hannot Hannot'.
    unfold annotate_tree_from_slots in Hannot, Hannot'.
    eapply
      (annotate_value_tree_same_shape
         page_pair_tree_depth 0
         (pair_options slots) (pair_options slots')
         tree tree' located located'); eauto.
    { apply pair_options_length. }
    { apply pair_options_length. }
    rewrite !pair_options_bitmap.
    unfold pair_bitmap.
    now rewrite Hslot_bitmap.
  Qed.

  Lemma value_tree_from_slots_same_shape slots slots' tree tree' :
    slot_bitmap slots = slot_bitmap slots' ->
    value_tree_from_slots slots = Some tree ->
    value_tree_from_slots slots' = Some tree' ->
    same_tree_shape tree tree'.
  Proof.
    intros Hslot_bitmap Htree Htree'.
    unfold value_tree_from_slots in Htree, Htree'.
    pose proof
      (build_tree_same_bitmap
         page_pair_tree_depth (pair_options slots) (pair_options slots')
         (pair_options_length slots) (pair_options_length slots'))
      as Hshape.
    rewrite !pair_options_bitmap in Hshape.
    assert (pair_bitmap slots = pair_bitmap slots') as Hpair_bitmap.
    { unfold pair_bitmap.
      now rewrite Hslot_bitmap. }
    specialize (Hshape Hpair_bitmap).
    rewrite Htree, Htree' in Hshape.
    exact Hshape.
  Qed.

  Lemma normalize_slots_from_same_commit_parts slots slots' :
    slot_bitmap slots = slot_bitmap slots' ->
    active_pair_values slots = active_pair_values slots' ->
    normalize_slots slots = normalize_slots slots'.
  Proof.
    intros Hslot_bitmap Hactive_values.
    pose proof (slots_from_bitmap_values_roundtrip slots) as Hroundtrip.
    pose proof (slots_from_bitmap_values_roundtrip slots') as Hroundtrip'.
    rewrite <- Hslot_bitmap, <- Hactive_values in Hroundtrip'.
    rewrite Hroundtrip in Hroundtrip'.
    now inversion Hroundtrip'.
  Qed.

  Definition hash64_call : Set := (hash_mode * bytes64)%type.

  Fixpoint tree_hash_inputs (tree : value_tree) : list hash64_call :=
    match tree with
    | TreeLeaf value => [(leaf_mode, value)]
    | TreeNode lhs rhs =>
        tree_hash_inputs lhs ++
        tree_hash_inputs rhs ++
        [(merge_mode, (eval_tree lhs, eval_tree rhs))]
    end.

  Definition hash64_input_set := hash64_call -> Prop.

  Definition collision_free_on (allowed : hash64_input_set) : Prop :=
    forall lhs rhs,
      allowed lhs ->
      allowed rhs ->
      H64 (fst lhs) (snd lhs) = H64 (fst rhs) (snd rhs) ->
      lhs = rhs.

  Definition Root_from_bitmaps
      (depth : nat)
      (tree_bm seal_bm : bitmap)
      (values : list pair_leaf)
      : option digest :=
    match reducer_result depth tree_bm values with
    | CommitMalformed => None
    | CommitEmpty => Some (seal_empty (bitmap_to_bytes16 seal_bm))
    | CommitNonempty tree =>
        Some (seal_nonempty (bitmap_to_bytes16 seal_bm) (eval_tree tree))
    end.

  Definition root_hash_inputs_from_bitmaps
      (depth : nat) (tree_bm : bitmap) (values : list pair_leaf)
      : list hash64_call :=
    match reducer_result depth tree_bm values with
    | CommitMalformed => []
    | CommitEmpty => []
    | CommitNonempty tree => tree_hash_inputs tree
    end.

  Definition root_empty_seal_inputs_from_bitmaps
      (depth : nat)
      (tree_bm seal_bm : bitmap)
      (values : list pair_leaf)
      : list bytes16 :=
    match reducer_result depth tree_bm values with
    | CommitEmpty => [bitmap_to_bytes16 seal_bm]
    | _ => []
    end.

  Definition root_nonempty_seal_inputs_from_bitmaps
      (depth : nat)
      (tree_bm seal_bm : bitmap)
      (values : list pair_leaf)
      : list (bytes16 * digest) :=
    match reducer_result depth tree_bm values with
    | CommitNonempty tree => [(bitmap_to_bytes16 seal_bm, eval_tree tree)]
    | _ => []
    end.

  Definition valid_bitmap_tuple
      (depth : nat) (bm : bitmap) (values : list pair_leaf) : Prop :=
    reducer_result depth bm values <> CommitMalformed.

  Lemma active_leaf_nodes_from_values
      next bm values nodes leftover :
    active_leaf_nodes_from next bm values = Some (nodes, leftover) ->
    values = live_values nodes ++ leftover.
  Proof.
    revert next values nodes leftover.
    induction bm as [| occupied rest IH];
      intros next values nodes leftover Hactive; simpl in Hactive.
    { inversion Hactive; reflexivity. }
    destruct occupied.
    { destruct values as [| value values_rest]; [discriminate |].
      destruct (active_leaf_nodes_from (S next) rest values_rest)
        as [[rest_nodes rest_leftover] |] eqn:Hrest; [| discriminate].
      pose proof
        (IH (S next) values_rest rest_nodes rest_leftover Hrest)
        as Hvalues.
      inversion Hactive; subst nodes leftover; clear Hactive.
      simpl.
      now rewrite Hvalues. }
    exact (IH (S next) values nodes leftover Hactive).
  Qed.

  Lemma active_leaf_nodes_values bm values nodes :
    active_leaf_nodes bm values = Some nodes ->
    live_values nodes = values.
  Proof.
    unfold active_leaf_nodes.
    destruct (active_leaf_nodes_from 0 bm values)
      as [[nodes0 leftover] |] eqn:Hactive; [| discriminate].
    destruct leftover as [| extra leftover']; [| discriminate].
    pose proof
      (active_leaf_nodes_from_values 0 bm values nodes0 [] Hactive)
      as Hvalues.
    intro Hnodes; inversion Hnodes; subst nodes; clear Hnodes.
    now rewrite app_nil_r in Hvalues.
  Qed.

  Lemma active_leaf_nodes_from_same_shape
      next bm values values' nodes leftover nodes' leftover' :
    active_leaf_nodes_from next bm values = Some (nodes, leftover) ->
    active_leaf_nodes_from next bm values' = Some (nodes', leftover') ->
    Forall2 same_live_shape nodes nodes'.
  Proof.
    revert next values values' nodes leftover nodes' leftover'.
    induction bm as [| occupied rest IH];
      intros next values values' nodes leftover nodes' leftover'
        Hactive Hactive'; simpl in Hactive, Hactive'.
    { inversion Hactive; inversion Hactive'; subst.
      constructor. }
    destruct occupied.
    { destruct values as [| value values_rest]; [discriminate |].
      destruct values' as [| value' values_rest']; [discriminate |].
      destruct (active_leaf_nodes_from (S next) rest values_rest)
        as [[rest_nodes rest_leftover] |] eqn:Hrest; [| discriminate].
      destruct (active_leaf_nodes_from (S next) rest values_rest')
        as [[rest_nodes' rest_leftover'] |] eqn:Hrest'; [| discriminate].
      inversion Hactive; inversion Hactive'; subst; clear Hactive Hactive'.
      constructor.
      { split; [reflexivity | constructor]. }
      eapply IH; eauto. }
    eapply IH; eauto.
  Qed.

  Lemma active_leaf_nodes_same_shape bm values values' nodes nodes' :
    active_leaf_nodes bm values = Some nodes ->
    active_leaf_nodes bm values' = Some nodes' ->
    Forall2 same_live_shape nodes nodes'.
  Proof.
    unfold active_leaf_nodes.
    destruct (active_leaf_nodes_from 0 bm values)
      as [[nodes0 leftover] |] eqn:Hactive; [| discriminate].
    destruct leftover as [| extra leftover']; [| discriminate].
    destruct (active_leaf_nodes_from 0 bm values')
      as [[nodes0' leftover'] |] eqn:Hactive'; [| discriminate].
    destruct leftover' as [| extra' leftover'']; [| discriminate].
    intros Hnodes Hnodes'; inversion Hnodes; inversion Hnodes'; subst.
    eapply active_leaf_nodes_from_same_shape; eauto.
  Qed.

  Lemma Forall2_same_live_shape_length lhs rhs :
    Forall2 same_live_shape lhs rhs ->
    length lhs = length rhs.
  Proof.
    intro Hsame.
    now apply Forall2_length in Hsame.
  Qed.

  Lemma merge_level_values_strong nodes :
    (forall bit, live_values (merge_level bit nodes) = live_values nodes) /\
    (forall bit current,
        live_values (merge_level bit (current :: nodes)) =
        live_values (current :: nodes)).
  Proof.
    induction nodes as [| next later IH].
    { split; intros; reflexivity. }
    destruct IH as [IH_later IH_cons_later].
    split.
    { intro bit.
      apply IH_cons_later. }
    intros bit current.
    simpl.
    destruct (sibling_candidate
                bit (live_index current) (live_index next)).
    { unfold live_values; simpl.
      pose proof (IH_later bit) as Hlater_values.
      unfold live_values in Hlater_values.
      rewrite Hlater_values.
      now rewrite app_assoc. }
    unfold live_values; simpl.
    pose proof (IH_cons_later bit next) as Hrest_values.
    unfold live_values in Hrest_values.
    simpl in Hrest_values.
    now rewrite Hrest_values.
  Qed.

  Lemma merge_level_values bit nodes :
    live_values (merge_level bit nodes) = live_values nodes.
  Proof.
    now apply (proj1 (merge_level_values_strong nodes)).
  Qed.

  Lemma reduce_levels_values fuel bit nodes :
    live_values (reduce_levels fuel bit nodes) = live_values nodes.
  Proof.
    revert bit nodes.
    induction fuel as [| fuel IH]; intros bit nodes; [reflexivity |].
    simpl.
    destruct (length nodes <=? 1) eqn:Hlen; [reflexivity |].
    rewrite IH.
    apply merge_level_values.
  Qed.

  Lemma merge_level_same_shape_strong nodes :
    (forall bit nodes',
        Forall2 same_live_shape nodes nodes' ->
        Forall2 same_live_shape
          (merge_level bit nodes) (merge_level bit nodes')) /\
    (forall bit current current' nodes',
        same_live_shape current current' ->
        Forall2 same_live_shape nodes nodes' ->
        Forall2 same_live_shape
          (merge_level bit (current :: nodes))
          (merge_level bit (current' :: nodes'))).
  Proof.
    induction nodes as [| next later IH].
    { split.
      { intros bit nodes' Hsame.
        inversion Hsame; constructor. }
      intros bit current current' nodes' Hcurrent Hsame.
      inversion Hsame; subst.
      constructor; [exact Hcurrent | constructor]. }
    destruct IH as [IH_later IH_cons_later].
    split.
    { intros bit nodes' Hsame.
      inversion Hsame as [| ? next' ? later' Hnext Hlater]; subst.
      eapply IH_cons_later; eauto. }
    intros bit current current' nodes' Hcurrent Hsame.
    inversion Hsame as [| ? next' ? later' Hnext Hlater]; subst.
    destruct Hcurrent as [Hcurrent_index Hcurrent_shape].
    destruct Hnext as [Hnext_index Hnext_shape].
    assert
      (sibling_candidate bit
         (live_index current) (live_index next) =
       sibling_candidate bit
         (live_index current') (live_index next')) as Hsibling.
    { now rewrite Hcurrent_index, Hnext_index. }
    simpl.
    rewrite Hsibling.
    destruct (sibling_candidate
                bit (live_index current') (live_index next')).
    { constructor.
      { split; [exact Hcurrent_index |].
        rewrite Hcurrent_index.
        constructor; assumption. }
      eapply IH_later; eauto. }
    constructor.
    { split; assumption. }
    eapply IH_cons_later; eauto.
    split; assumption.
  Qed.

  Lemma merge_level_same_shape bit nodes nodes' :
    Forall2 same_live_shape nodes nodes' ->
    Forall2 same_live_shape
      (merge_level bit nodes) (merge_level bit nodes').
  Proof.
    apply (proj1 (merge_level_same_shape_strong nodes)).
  Qed.

  Lemma reduce_levels_same_shape fuel bit nodes nodes' :
    Forall2 same_live_shape nodes nodes' ->
    Forall2 same_live_shape
      (reduce_levels fuel bit nodes)
      (reduce_levels fuel bit nodes').
  Proof.
    revert bit nodes nodes'.
    induction fuel as [| fuel IH]; intros bit nodes nodes' Hsame;
      [exact Hsame |].
    simpl.
    pose proof (Forall2_same_live_shape_length _ _ Hsame) as Hlen.
    rewrite <- Hlen.
    destruct (length nodes <=? 1) eqn:Hsmall.
    { exact Hsame. }
    apply IH.
    now apply merge_level_same_shape.
  Qed.

  Lemma reducer_result_values depth bm values tree :
    reducer_result depth bm values = CommitNonempty tree ->
    tree_values tree = values.
  Proof.
    unfold reducer_result.
    destruct (active_leaf_nodes bm values) as [nodes |] eqn:Hactive;
      [| discriminate].
    destruct nodes as [| node rest_nodes]; [discriminate |].
    intro Hcommit.
    pose proof (active_leaf_nodes_values bm values _ Hactive) as Hactive_values.
    destruct (reduce_levels depth 0 (node :: rest_nodes))
      as [| root rest] eqn:Hreduced; try discriminate.
    destruct rest as [| extra rest']; try discriminate.
    inversion Hcommit; subst tree; clear Hcommit.
    rewrite <- Hactive_values.
    pose proof (reduce_levels_values depth 0 (node :: rest_nodes))
      as Hvalues.
    rewrite Hreduced in Hvalues.
    unfold live_values in Hvalues; simpl in Hvalues.
    rewrite app_nil_r in Hvalues.
    change
      (tree_values (live_tree node) ++
       concat
         (map (fun node : live_node => tree_values (live_tree node))
            rest_nodes))
      with (live_values (node :: rest_nodes)) in Hvalues.
    exact Hvalues.
  Qed.

  Lemma reducer_result_same_shape
      depth bm values values' tree tree' :
    reducer_result depth bm values = CommitNonempty tree ->
    reducer_result depth bm values' = CommitNonempty tree' ->
    same_tree_shape tree tree'.
  Proof.
    unfold reducer_result.
    destruct (active_leaf_nodes bm values) as [nodes |] eqn:Hactive;
      [| discriminate].
    destruct nodes as [| node rest_nodes]; [discriminate |].
    destruct (active_leaf_nodes bm values') as [nodes' |] eqn:Hactive';
      [| discriminate].
    destruct nodes' as [| node' rest_nodes']; [discriminate |].
    intros Hcommit Hcommit'.
    pose proof
      (active_leaf_nodes_same_shape
         bm values values' _ _ Hactive Hactive')
      as Hactive_shape.
    pose proof
      (reduce_levels_same_shape
         depth 0 (node :: rest_nodes) (node' :: rest_nodes')
         Hactive_shape)
      as Hreduced_shape.
    destruct (reduce_levels depth 0 (node :: rest_nodes))
      as [| root rest] eqn:Hreduced; [discriminate |].
    destruct rest as [| extra rest']; [| discriminate].
    inversion Hcommit; subst tree; clear Hcommit.
    destruct (reduce_levels depth 0 (node' :: rest_nodes'))
      as [| root' rest] eqn:Hreduced'; [discriminate |].
    destruct rest as [| extra' rest']; [| discriminate].
    inversion Hcommit'; subst tree'; clear Hcommit'.
    inversion Hreduced_shape as [| ? ? ? ? Hroot_shape Htail_shape].
    destruct Hroot_shape as [_ Htree_shape].
    exact Htree_shape.
  Qed.

  Lemma tree_hash_inputs_contains_eval tree :
    In
      match tree with
      | TreeLeaf value => (leaf_mode, value)
      | TreeNode lhs rhs =>
          (merge_mode, (eval_tree lhs, eval_tree rhs))
      end
      (tree_hash_inputs tree).
  Proof.
    destruct tree as [value | lhs rhs]; simpl.
    { now left. }
    apply in_or_app; right.
    apply in_or_app; right.
    now left.
  Qed.

  Lemma eval_tree_same_shape_no_collision
      allowed tree tree' :
    collision_free_on allowed ->
    (forall input, In input (tree_hash_inputs tree) -> allowed input) ->
    (forall input, In input (tree_hash_inputs tree') -> allowed input) ->
    same_tree_shape tree tree' ->
    eval_tree tree = eval_tree tree' ->
    tree_values tree = tree_values tree'.
  Proof.
    intros Hfree Hallowed Hallowed' Hshape.
    induction Hshape; simpl; intro Heval.
    { assert ((leaf_mode, lhs_value) = (leaf_mode, rhs_value)) as Heq_input.
      { eapply Hfree.
        { apply Hallowed. simpl; now left. }
        { apply Hallowed'. simpl; now left. }
        exact Heval. }
      injection Heq_input as Hvalue_eq.
      now rewrite Hvalue_eq. }
    assert
      ((merge_mode, (eval_tree lhs, eval_tree rhs)) =
       (merge_mode, (eval_tree lhs', eval_tree rhs'))) as Heq_input.
    { eapply Hfree.
      { apply Hallowed.
        simpl.
        apply in_or_app; right.
        apply in_or_app; right.
        now left. }
      { apply Hallowed'.
        simpl.
        apply in_or_app; right.
        apply in_or_app; right.
        now left. }
      exact Heval. }
    injection Heq_input as Heq_lhs Heq_rhs.
    rewrite
      (IHHshape1
         (fun input Hin =>
            Hallowed input
              (in_or_app _ _ _ (or_introl Hin)))
         (fun input Hin =>
            Hallowed' input
              (in_or_app _ _ _ (or_introl Hin)))
         Heq_lhs).
    rewrite
      (IHHshape2
         (fun input Hin =>
            Hallowed input
              (in_or_app _ _ _
                 (or_intror
                    (in_or_app _ _ _ (or_introl Hin)))))
         (fun input Hin =>
            Hallowed' input
              (in_or_app _ _ _
                 (or_intror
                    (in_or_app _ _ _ (or_introl Hin)))))
         Heq_rhs).
    reflexivity.
  Qed.

  Lemma eval_located_tree_same_shape_no_aligned_collision tree tree' :
    (forall loc input input',
        In (mk_located_call loc input)
          (tree_located_calls tree) ->
        In (mk_located_call loc input')
          (tree_located_calls tree') ->
        call_digest input = call_digest input' ->
        input = input') ->
    same_located_tree_shape tree tree' ->
    eval_located_tree tree = eval_located_tree tree' ->
    located_tree_values tree = located_tree_values tree'.
  Proof.
    intros Hfree Hshape.
    induction Hshape; simpl; intro Heval.
    { assert (InputLeaf lhs_value = InputLeaf rhs_value) as Heq_input.
      { eapply Hfree with (loc := LocPairLeaf index).
        { simpl; now left. }
        { simpl; now left. }
        exact Heval. }
      injection Heq_input as Hvalue_eq.
      now rewrite Hvalue_eq. }
    assert
      (InputMerge (eval_located_tree lhs) (eval_located_tree rhs) =
       InputMerge (eval_located_tree lhs') (eval_located_tree rhs'))
      as Heq_input.
    { eapply Hfree with (loc := LocNode level parent).
      { simpl.
        apply in_or_app; right.
        apply in_or_app; right.
        now left. }
      { simpl.
        apply in_or_app; right.
        apply in_or_app; right.
        now left. }
      exact Heval. }
    injection Heq_input as Heq_lhs Heq_rhs.
    rewrite
      (IHHshape1
         (fun loc input input' Hin Hin' Heq =>
            Hfree loc input input'
              (in_or_app _ _ _ (or_introl Hin))
              (in_or_app _ _ _ (or_introl Hin'))
              Heq)
         Heq_lhs).
    rewrite
      (IHHshape2
         (fun loc input input' Hin Hin' Heq =>
            Hfree loc input input'
              (in_or_app _ _ _
                 (or_intror
                    (in_or_app _ _ _ (or_introl Hin))))
              (in_or_app _ _ _
                 (or_intror
                    (in_or_app _ _ _ (or_introl Hin'))))
              Heq)
         Heq_rhs).
    reflexivity.
  Qed.

  Definition root_inputs_for_bitmap_pair
      depth tree_bm values tree_bm' values' : list hash64_call :=
    root_hash_inputs_from_bitmaps depth tree_bm values ++
    root_hash_inputs_from_bitmaps depth tree_bm' values'.

  Definition empty_seal_inputs_for_bitmap_pair
      depth tree_bm seal_bm values tree_bm' seal_bm' values'
      : list bytes16 :=
    root_empty_seal_inputs_from_bitmaps depth tree_bm seal_bm values ++
    root_empty_seal_inputs_from_bitmaps depth tree_bm' seal_bm' values'.

  Definition nonempty_seal_inputs_for_bitmap_pair
      depth tree_bm seal_bm values tree_bm' seal_bm' values'
      : list (bytes16 * digest) :=
    root_nonempty_seal_inputs_from_bitmaps depth tree_bm seal_bm values ++
    root_nonempty_seal_inputs_from_bitmaps depth tree_bm' seal_bm' values'.

  Definition seal_empty_collision_free_on
      (allowed : bytes16 -> Prop) : Prop :=
    forall lhs rhs,
      allowed lhs ->
      allowed rhs ->
      seal_empty lhs = seal_empty rhs ->
      lhs = rhs.

  Definition seal_nonempty_collision_free_on
      (allowed : (bytes16 * digest) -> Prop) : Prop :=
    forall lhs rhs,
      allowed lhs ->
      allowed rhs ->
      seal_nonempty (fst lhs) (snd lhs) =
      seal_nonempty (fst rhs) (snd rhs) ->
      lhs = rhs.

  Definition seal_empty_nonempty_disjoint_on
      (allowed_empty : bytes16 -> Prop)
      (allowed_nonempty : (bytes16 * digest) -> Prop) : Prop :=
    forall empty_input nonempty_input,
      allowed_empty empty_input ->
      allowed_nonempty nonempty_input ->
      seal_empty empty_input <>
      seal_nonempty (fst nonempty_input) (snd nonempty_input).

  Theorem Root_from_bitmaps_injective_no_collision
      depth tree_bm seal_bm values tree_bm' seal_bm' values' :
    valid_bitmap_tuple depth tree_bm values ->
    valid_bitmap_tuple depth tree_bm' values' ->
    valid_seal_bitmap seal_bm ->
    valid_seal_bitmap seal_bm' ->
    (seal_bm = seal_bm' -> tree_bm = tree_bm') ->
    collision_free_on
      (fun input =>
         In input
           (root_inputs_for_bitmap_pair depth tree_bm values tree_bm' values')) ->
    seal_empty_collision_free_on
      (fun input =>
         In input
           (empty_seal_inputs_for_bitmap_pair
              depth tree_bm seal_bm values tree_bm' seal_bm' values')) ->
    seal_nonempty_collision_free_on
      (fun input =>
         In input
           (nonempty_seal_inputs_for_bitmap_pair
              depth tree_bm seal_bm values tree_bm' seal_bm' values')) ->
    seal_empty_nonempty_disjoint_on
      (fun input =>
         In input
           (empty_seal_inputs_for_bitmap_pair
              depth tree_bm seal_bm values tree_bm' seal_bm' values'))
      (fun input =>
         In input
           (nonempty_seal_inputs_for_bitmap_pair
              depth tree_bm seal_bm values tree_bm' seal_bm' values')) ->
    Root_from_bitmaps depth tree_bm seal_bm values =
    Root_from_bitmaps depth tree_bm' seal_bm' values' ->
    seal_bm = seal_bm' /\ tree_bm = tree_bm' /\ values = values'.
  Proof.
    intros Hvalid Hvalid' Hbm_valid Hbm'_valid Htree_from_seal
      Hfree_hash Hfree_empty Hfree_nonempty Hseal_disjoint Hroot.
    destruct (reducer_result depth tree_bm values)
      as [| | tree] eqn:Hresult;
      destruct (reducer_result depth tree_bm' values')
        as [| | tree'] eqn:Hresult';
      try contradiction;
      unfold Root_from_bitmaps in Hroot;
      rewrite Hresult, Hresult' in Hroot.
    { inversion Hroot as [Hseal_eq]; clear Hroot.
      assert
        (bitmap_to_bytes16 seal_bm =
         bitmap_to_bytes16 seal_bm') as Hbitmap_eq.
      { eapply Hfree_empty.
        { unfold empty_seal_inputs_for_bitmap_pair.
          apply in_or_app; left.
          unfold root_empty_seal_inputs_from_bitmaps.
          rewrite Hresult.
          now left. }
        { unfold empty_seal_inputs_for_bitmap_pair.
          apply in_or_app; right.
          unfold root_empty_seal_inputs_from_bitmaps.
          rewrite Hresult'.
          now left. }
        exact Hseal_eq. }
      pose proof
        (bitmap_to_bytes16_inj
           seal_bm seal_bm' Hbm_valid Hbm'_valid Hbitmap_eq)
        as Hseal_bm.
      pose proof (Htree_from_seal Hseal_bm) as Htree_bm.
      subst seal_bm' tree_bm'.
      split; [reflexivity |].
      split; [reflexivity |].
      unfold reducer_result in Hresult, Hresult'.
      destruct (active_leaf_nodes tree_bm values) as [nodes |] eqn:Hactive;
        [| discriminate].
      destruct nodes as [| node rest].
      2: {
        destruct (reduce_levels depth 0 (node :: rest)) as [| root tail];
          [discriminate |].
        destruct tail; discriminate.
      }
      destruct (active_leaf_nodes tree_bm values') as [nodes' |] eqn:Hactive';
        [| discriminate].
      destruct nodes' as [| node' rest'].
      2: {
        destruct (reduce_levels depth 0 (node' :: rest')) as [| root' tail'];
          [discriminate |].
        destruct tail'; discriminate.
      }
      pose proof
        (active_leaf_nodes_values tree_bm values [] Hactive)
        as Hvalues.
      pose proof
        (active_leaf_nodes_values tree_bm values' [] Hactive')
        as Hvalues'.
      now rewrite <- Hvalues, <- Hvalues'. }
    { inversion Hroot as [Hseal_eq]; clear Hroot.
      exfalso.
      eapply Hseal_disjoint.
      { unfold empty_seal_inputs_for_bitmap_pair.
        apply in_or_app; left.
        unfold root_empty_seal_inputs_from_bitmaps.
        rewrite Hresult.
        now left. }
      { unfold nonempty_seal_inputs_for_bitmap_pair.
        apply in_or_app; right.
        unfold root_nonempty_seal_inputs_from_bitmaps.
        rewrite Hresult'.
        now left. }
      exact Hseal_eq. }
    { inversion Hroot as [Hseal_eq]; clear Hroot.
      exfalso.
      eapply Hseal_disjoint.
      { unfold empty_seal_inputs_for_bitmap_pair.
        apply in_or_app; right.
        unfold root_empty_seal_inputs_from_bitmaps.
        rewrite Hresult'.
        now left. }
      { unfold nonempty_seal_inputs_for_bitmap_pair.
        apply in_or_app; left.
        unfold root_nonempty_seal_inputs_from_bitmaps.
        rewrite Hresult.
        now left. }
      exact (eq_sym Hseal_eq). }
    { inversion Hroot as [Hseal_eq]; clear Hroot.
      assert
        ((bitmap_to_bytes16 seal_bm, eval_tree tree) =
         (bitmap_to_bytes16 seal_bm', eval_tree tree')) as Hseal_input_eq.
      { eapply Hfree_nonempty.
        { unfold nonempty_seal_inputs_for_bitmap_pair.
          apply in_or_app; left.
          unfold root_nonempty_seal_inputs_from_bitmaps.
          rewrite Hresult.
          now left. }
        { unfold nonempty_seal_inputs_for_bitmap_pair.
          apply in_or_app; right.
          unfold root_nonempty_seal_inputs_from_bitmaps.
          rewrite Hresult'.
          now left. }
        exact Hseal_eq. }
      inversion Hseal_input_eq as [[Hbitmap_eq Heval]].
      pose proof
        (bitmap_to_bytes16_inj
           seal_bm seal_bm' Hbm_valid Hbm'_valid Hbitmap_eq)
        as Hseal_bm.
      pose proof (Htree_from_seal Hseal_bm) as Htree_bm.
      subst seal_bm' tree_bm'.
      split; [reflexivity |].
      split; [reflexivity |].
      pose proof
        (reducer_result_same_shape
           depth tree_bm values values' tree tree' Hresult Hresult')
        as Hshape.
      pose proof
        (reducer_result_values depth tree_bm values tree Hresult)
        as Hvalues.
      pose proof
        (reducer_result_values depth tree_bm values' tree' Hresult')
        as Hvalues'.
      rewrite <- Hvalues, <- Hvalues'.
      eapply eval_tree_same_shape_no_collision; eauto.
      { intros input Hin.
        unfold root_inputs_for_bitmap_pair.
        apply in_or_app; left.
        unfold root_hash_inputs_from_bitmaps.
        rewrite Hresult.
        exact Hin. }
      { intros input Hin.
        unfold root_inputs_for_bitmap_pair.
        apply in_or_app; right.
        unfold root_hash_inputs_from_bitmaps.
        rewrite Hresult'.
        exact Hin. } }
  Qed.

  Theorem Root_from_bitmaps_distinct_no_collision
      depth tree_bm seal_bm values tree_bm' seal_bm' values' :
    valid_bitmap_tuple depth tree_bm values ->
    valid_bitmap_tuple depth tree_bm' values' ->
    valid_seal_bitmap seal_bm ->
    valid_seal_bitmap seal_bm' ->
    (seal_bm = seal_bm' -> tree_bm = tree_bm') ->
    collision_free_on
      (fun input =>
         In input
           (root_inputs_for_bitmap_pair depth tree_bm values tree_bm' values')) ->
    seal_empty_collision_free_on
      (fun input =>
         In input
           (empty_seal_inputs_for_bitmap_pair
              depth tree_bm seal_bm values tree_bm' seal_bm' values')) ->
    seal_nonempty_collision_free_on
      (fun input =>
         In input
           (nonempty_seal_inputs_for_bitmap_pair
              depth tree_bm seal_bm values tree_bm' seal_bm' values')) ->
    seal_empty_nonempty_disjoint_on
      (fun input =>
         In input
           (empty_seal_inputs_for_bitmap_pair
              depth tree_bm seal_bm values tree_bm' seal_bm' values'))
      (fun input =>
         In input
           (nonempty_seal_inputs_for_bitmap_pair
              depth tree_bm seal_bm values tree_bm' seal_bm' values')) ->
    (seal_bm, values) <> (seal_bm', values') ->
    Root_from_bitmaps depth tree_bm seal_bm values <>
    Root_from_bitmaps depth tree_bm' seal_bm' values'.
  Proof.
    intros Hvalid Hvalid' Hbm_valid Hbm'_valid Htree_from_seal
      Hfree_hash Hfree_empty Hfree_nonempty Hseal_disjoint
      Hdistinct Hroot.
    destruct
      (Root_from_bitmaps_injective_no_collision
         depth tree_bm seal_bm values tree_bm' seal_bm' values'
         Hvalid Hvalid' Hbm_valid Hbm'_valid Htree_from_seal
         Hfree_hash Hfree_empty
         Hfree_nonempty Hseal_disjoint Hroot)
      as [Hseal_bm [Htree_bm Hvalues]].
    apply Hdistinct.
    now subst.
  Qed.

  Definition root_hash_inputs (slots : slot_values) : list hash64_call :=
    match value_tree_from_slots slots with
    | None => []
    | Some tree => tree_hash_inputs tree
    end.

  Definition root_inputs_for_pair
      (slots slots' : slot_values) : list hash64_call :=
    root_hash_inputs slots ++ root_hash_inputs slots'.

  Definition empty_seal_inputs (slots : slot_values) : list bytes16 :=
    match value_tree_from_slots slots with
    | None => [bitmap_to_bytes16 (slot_bitmap slots)]
    | Some _ => []
    end.

  Definition empty_seal_inputs_for_pair
      (slots slots' : slot_values) : list bytes16 :=
    empty_seal_inputs slots ++ empty_seal_inputs slots'.

  Definition nonempty_seal_inputs
      (slots : slot_values) : list (bytes16 * digest) :=
    match value_tree_from_slots slots with
    | None => []
    | Some tree =>
        [(bitmap_to_bytes16 (slot_bitmap slots), eval_tree tree)]
    end.

  Definition nonempty_seal_inputs_for_pair
      (slots slots' : slot_values) : list (bytes16 * digest) :=
    nonempty_seal_inputs slots ++ nonempty_seal_inputs slots'.

  Definition located_aligned_collision
      (call call' : located_call) : Prop :=
    located_call_loc call = located_call_loc call' /\
    located_call_input call <> located_call_input call' /\
    call_digest (located_call_input call) =
    call_digest (located_call_input call').

  Definition digest_eq_dec
      (lhs rhs : digest) : {lhs = rhs} + {lhs <> rhs} :=
    decide (lhs = rhs).

  Definition located_aligned_collision_dec call call' :
    {located_aligned_collision call call'} +
    {~ located_aligned_collision call call'}.
  Proof.
    unfold located_aligned_collision.
    destruct
      (call_loc_eq_dec
         (located_call_loc call)
         (located_call_loc call')) as [Hloc | Hloc].
    { destruct
        (call_input_eq_dec
           (located_call_input call)
           (located_call_input call')) as [Hinput | Hinput].
      { right.
        intros (_ & Hneq & _).
        exact (Hneq Hinput). }
      destruct
        (digest_eq_dec
           (call_digest (located_call_input call))
           (call_digest (located_call_input call'))) as [Hdigest | Hdigest].
      { left.
        repeat split; assumption. }
      right.
      intros (_ & _ & Heq_digest).
      exact (Hdigest Heq_digest). }
    right.
    intros (Heq_loc & _ & _).
    exact (Hloc Heq_loc).
  Defined.

  Fixpoint list_exists_sig_dec {A : Type}
      (P : A -> Prop)
      (P_dec : forall value, {P value} + {~ P value})
      (values : list A)
      : {value : A & In value values /\ P value} +
        {~ exists value, In value values /\ P value}.
  Proof.
    destruct values as [| value values].
    { right.
      intros (value & Hin & _).
      inversion Hin. }
    destruct (P_dec value) as [HP | HnotP].
    { left.
      exists value.
      split; [now left | exact HP]. }
    destruct (@list_exists_sig_dec A P P_dec values)
      as [(found & Hin & HP) | Hnone].
    { left.
      exists found.
      split; [now right | exact HP]. }
    right.
    intros (found & [Heq | Hin] & HP).
    { subst found.
      exact (HnotP HP). }
    apply Hnone.
    exists found.
    split; assumption.
  Defined.

  Definition aligned_collision_calls
      (calls calls' : list located_call) : Prop :=
    exists call call',
      In call calls /\
      In call' calls' /\
      located_aligned_collision call call'.

  Definition aligned_collision_calls_witness
      (calls calls' : list located_call) : Type :=
    {call : located_call &
      {call' : located_call &
        In call calls /\
        In call' calls' /\
        located_aligned_collision call call'}}.

  Fixpoint aligned_collision_calls_sig_dec calls calls' :
    aligned_collision_calls_witness calls calls' +
    {~ aligned_collision_calls calls calls'}.
  Proof.
    destruct calls as [| call calls].
    { right.
      intros (call & call' & Hin & _).
      inversion Hin. }
    destruct
      (list_exists_sig_dec
         (fun call' => located_aligned_collision call call')
         (fun call' => located_aligned_collision_dec call call')
         calls') as [(call' & Hin' & Hcollision) | Hnone_head].
    { left.
      exists call, call'.
      split; [now left |].
      split; assumption. }
    destruct (aligned_collision_calls_sig_dec calls calls')
      as [(tail_call & call' & Hin & Hin' & Hcollision) | Hnone_tail].
    { left.
      exists tail_call, call'.
      split; [now right |].
      split; assumption. }
    right.
    intros (found & call' & [Heq | Hin] & Hin' & Hcollision).
    { subst found.
      apply Hnone_head.
      exists call'.
      split; assumption. }
    apply Hnone_tail.
    exists found, call'.
    split; [exact Hin |].
    split; assumption.
  Defined.

  Definition aligned_collision_calls_dec calls calls' :
    {aligned_collision_calls calls calls'} +
    {~ aligned_collision_calls calls calls'}.
  Proof.
    destruct (aligned_collision_calls_sig_dec calls calls')
      as [(call & call' & Hin & Hin' & Hcollision) | Hnone].
    { left.
      exists call, call'.
      split; [exact Hin |].
      split; assumption. }
    right; exact Hnone.
  Defined.

  Lemma exists_aligned_collision_iff_calls trace trace' :
    exists_aligned_collision trace trace' <->
    aligned_collision_calls
      trace.(traced_calls)
      trace'.(traced_calls).
  Proof.
    unfold
      exists_aligned_collision,
      aligned_collision_calls,
      located_aligned_collision.
    split.
    { intros (loc & input & input' & Hin & Hin' & Hneq & Hdigest).
      exists (mk_located_call loc input),
        (mk_located_call loc input').
      repeat split; simpl; try assumption; reflexivity. }
    intros (call & call' & Hin & Hin' & Hloc & Hneq & Hdigest).
    destruct call as [loc input].
    destruct call' as [loc' input'].
    simpl in *.
    subst loc'.
    exists loc, input, input'.
    repeat split; assumption.
  Qed.

  Definition exists_aligned_collision_dec trace trace' :
    {exists_aligned_collision trace trace'} + {~ exists_aligned_collision trace trace'}.
  Proof.
    destruct
      (aligned_collision_calls_dec
         trace.(traced_calls)
         trace'.(traced_calls)) as
      [Hcollision | Hno_collision].
    { left.
      now apply exists_aligned_collision_iff_calls. }
    right.
    intro Hcollision.
    apply Hno_collision.
    now apply exists_aligned_collision_iff_calls.
  Defined.

  (** This corollary-facing predicate is just the negation of the bad event in
      the main extractor theorem.  It lives in the proof section because the
      Section 2 statement only needs the positive collision event. *)
  Definition no_aligned_collisions
      (trace trace' : root_trace) : Prop :=
    ~ exists_aligned_collision trace trace'.

  Lemma no_aligned_collisions_pointwise trace trace' :
    no_aligned_collisions trace trace' ->
    forall loc input input',
      In (mk_located_call loc input)
        trace.(traced_calls) ->
      In (mk_located_call loc input')
        trace'.(traced_calls) ->
      call_digest input = call_digest input' ->
      input = input'.
  Proof.
    unfold no_aligned_collisions.
    intros Hno_collision loc input input' Hin Hin' Hdigest.
    destruct (call_input_eq_dec input input') as [Heq_input | Hneq_input].
    { exact Heq_input. }
    exfalso.
    apply Hno_collision.
    exists loc, input, input'.
    repeat split; assumption.
  Qed.

  Theorem Root_injective_no_collision slots slots' :
    no_aligned_collisions
      (root_with_trace slots)
      (root_with_trace slots') ->
    root slots = root slots' ->
    normalize_slots slots = normalize_slots slots'.
  Proof.
    intros Hno_collision Hroot.
    pose proof
      (no_aligned_collisions_pointwise
         (root_with_trace slots)
         (root_with_trace slots')
         Hno_collision)
      as Hno_aligned.
    unfold root in Hroot.
    destruct (value_tree_from_slots slots) as [tree |] eqn:Htree;
      destruct (value_tree_from_slots slots') as [tree' |] eqn:Htree';
      simpl in Hroot.
    { pose proof Hroot as Hseal_eq.
      destruct (annotate_tree_from_slots_some slots tree Htree)
        as [located_tree [Hannot Herase]].
      destruct (annotate_tree_from_slots_some slots' tree' Htree')
        as [located_tree' [Hannot' Herase']].
      assert
        (eval_located_tree located_tree = eval_tree tree)
        as Hlocated_eval.
      { rewrite <- eval_located_tree_erase.
        now rewrite Herase. }
      assert
        (eval_located_tree located_tree' = eval_tree tree')
        as Hlocated_eval'.
      { rewrite <- eval_located_tree_erase.
        now rewrite Herase'. }
      assert
        (InputSealNonempty
           (bitmap_to_bytes16 (slot_bitmap slots))
           (eval_tree tree) =
         InputSealNonempty
           (bitmap_to_bytes16 (slot_bitmap slots'))
           (eval_tree tree'))
        as Hseal_input_eq.
      { eapply Hno_aligned with (loc := LocSeal).
        { change
            (In
              (mk_located_call
                LocSeal
                (InputSealNonempty
                  (bitmap_to_bytes16 (slot_bitmap slots))
                  (eval_tree tree)))
              ((root_with_trace slots).(traced_calls))).
          unfold root_with_trace.
          rewrite Htree, Hannot.
          apply in_or_app; right.
          fold (eval_located_tree located_tree).
          rewrite Hlocated_eval.
          now left. }
        { change
            (In
              (mk_located_call
                LocSeal
                (InputSealNonempty
                  (bitmap_to_bytes16 (slot_bitmap slots'))
                  (eval_tree tree')))
              ((root_with_trace slots').(traced_calls))).
          unfold root_with_trace.
          rewrite Htree', Hannot'.
          apply in_or_app; right.
          fold (eval_located_tree located_tree').
          rewrite Hlocated_eval'.
          now left. }
        exact Hseal_eq. }
      injection Hseal_input_eq as Hbitmap_eq Heval.
      pose proof
        (bitmap_to_bytes16_inj
           (slot_bitmap slots) (slot_bitmap slots')
           (slot_bitmap_valid slots) (slot_bitmap_valid slots')
           Hbitmap_eq)
        as Hslot_bitmap.
      pose proof
        (annotate_tree_from_slots_same_shape
           slots slots' tree tree' located_tree located_tree'
           Hslot_bitmap Hannot Hannot')
        as Hshape.
      pose proof (value_tree_from_slots_values slots tree Htree)
        as Hvalues.
      pose proof (value_tree_from_slots_values slots' tree' Htree')
        as Hvalues'.
      assert
        (active_pair_values slots = active_pair_values slots')
        as Hactive_values.
      { rewrite <- Hvalues, <- Hvalues'.
        assert
          (eval_located_tree located_tree =
           eval_located_tree located_tree') as Heval_located.
        { rewrite <- !eval_located_tree_erase.
          now rewrite Herase, Herase'. }
        rewrite <- Herase, <- Herase'.
        rewrite !located_tree_values_erase.
        eapply eval_located_tree_same_shape_no_aligned_collision.
        { intros loc input input' Hin Hin' Heq.
          eapply Hno_aligned with (loc := loc).
          { change
              (In
                (mk_located_call loc input)
                ((root_with_trace slots).(traced_calls))).
            unfold root_with_trace.
            rewrite Htree, Hannot.
            apply in_or_app; left.
            fold (tree_located_calls located_tree).
            exact Hin. }
          { change
              (In
                (mk_located_call loc input')
                ((root_with_trace slots').(traced_calls))).
            unfold root_with_trace.
            rewrite Htree', Hannot'.
            apply in_or_app; left.
            fold (tree_located_calls located_tree').
            exact Hin'. }
          exact Heq. }
        { exact Hshape. }
        { exact Heval_located. } }
      now apply normalize_slots_from_same_commit_parts. }
    { pose proof Hroot as Hseal_eq.
      destruct (annotate_tree_from_slots_some slots tree Htree)
        as [located_tree [Hannot Herase]].
      assert
        (eval_located_tree located_tree = eval_tree tree)
        as Hlocated_eval.
      { rewrite <- eval_located_tree_erase.
        now rewrite Herase. }
      assert
        (InputSealNonempty
           (bitmap_to_bytes16 (slot_bitmap slots))
           (eval_tree tree) =
         InputSealEmpty
           (bitmap_to_bytes16 (slot_bitmap slots')))
        as Hseal_input_eq.
      { eapply Hno_aligned with (loc := LocSeal).
        { change
            (In
              (mk_located_call
                LocSeal
                (InputSealNonempty
                  (bitmap_to_bytes16 (slot_bitmap slots))
                  (eval_tree tree)))
              ((root_with_trace slots).(traced_calls))).
          unfold root_with_trace.
          rewrite Htree, Hannot.
          apply in_or_app; right.
          fold (eval_located_tree located_tree).
          rewrite Hlocated_eval.
          now left. }
        { change
            (In
              (mk_located_call
                LocSeal
                (InputSealEmpty
                  (bitmap_to_bytes16 (slot_bitmap slots'))))
              ((root_with_trace slots').(traced_calls))).
          unfold root_with_trace.
          rewrite Htree'.
          now left. }
        exact Hseal_eq. }
      discriminate Hseal_input_eq. }
    { pose proof Hroot as Hseal_eq.
      destruct (annotate_tree_from_slots_some slots' tree' Htree')
        as [located_tree' [Hannot' Herase']].
      assert
        (eval_located_tree located_tree' = eval_tree tree')
        as Hlocated_eval'.
      { rewrite <- eval_located_tree_erase.
        now rewrite Herase'. }
      assert
        (InputSealEmpty
           (bitmap_to_bytes16 (slot_bitmap slots)) =
         InputSealNonempty
           (bitmap_to_bytes16 (slot_bitmap slots'))
           (eval_tree tree'))
        as Hseal_input_eq.
      { eapply Hno_aligned with (loc := LocSeal).
        { change
            (In
              (mk_located_call
                LocSeal
                (InputSealEmpty
                  (bitmap_to_bytes16 (slot_bitmap slots))))
              ((root_with_trace slots).(traced_calls))).
          unfold root_with_trace.
          rewrite Htree.
          now left. }
        { change
            (In
              (mk_located_call
                LocSeal
                (InputSealNonempty
                  (bitmap_to_bytes16 (slot_bitmap slots'))
                  (eval_tree tree')))
              ((root_with_trace slots').(traced_calls))).
          unfold root_with_trace.
          rewrite Htree', Hannot'.
          apply in_or_app; right.
          fold (eval_located_tree located_tree').
          rewrite Hlocated_eval'.
          now left. }
        exact Hseal_eq. }
      discriminate Hseal_input_eq. }
    { pose proof Hroot as Hseal_eq.
      assert
        (InputSealEmpty (bitmap_to_bytes16 (slot_bitmap slots)) =
         InputSealEmpty (bitmap_to_bytes16 (slot_bitmap slots')))
        as Hseal_input_eq.
      { eapply Hno_aligned with (loc := LocSeal).
        { change
            (In
              (mk_located_call
                LocSeal
                (InputSealEmpty
                  (bitmap_to_bytes16 (slot_bitmap slots))))
              ((root_with_trace slots).(traced_calls))).
          unfold root_with_trace.
          rewrite Htree.
          now left. }
        { change
            (In
              (mk_located_call
                LocSeal
                (InputSealEmpty
                  (bitmap_to_bytes16 (slot_bitmap slots'))))
              ((root_with_trace slots').(traced_calls))).
          unfold root_with_trace.
          rewrite Htree'.
          now left. }
        exact Hseal_eq. }
      injection Hseal_input_eq as Hbitmap_eq.
      pose proof
        (bitmap_to_bytes16_inj
           (slot_bitmap slots) (slot_bitmap slots')
           (slot_bitmap_valid slots) (slot_bitmap_valid slots')
           Hbitmap_eq)
        as Hslot_bitmap.
      pose proof (value_tree_from_slots_empty_values slots Htree)
        as Hvalues.
      pose proof (value_tree_from_slots_empty_values slots' Htree')
        as Hvalues'.
      assert
        (active_pair_values slots = active_pair_values slots')
        as Hactive_values.
      { now rewrite Hvalues, Hvalues'. }
      now apply normalize_slots_from_same_commit_parts. }
  Qed.

  (** This is the main security theorem: every binding break produces an
      aligned collision in the two traced computations.  The proof searches the
      two finite traces with [exists_aligned_collision_dec].  If no bad pair exists,
      [no_aligned_collisions_pointwise] turns that absence into the local rule
      needed to push root equality through the seal and tree locations, forcing
      the normalized page views to agree and contradicting distinctness. *)
  Theorem Root_binding_break_extracts_aligned_collision slots slots' :
    (root_with_trace slots).(traced_root) =
    (root_with_trace slots').(traced_root) ->
    normalize_slots slots <> normalize_slots slots' ->
    exists_aligned_collision (root_with_trace slots) (root_with_trace slots').
  Proof.
    intros Hroot Hdistinct.
    destruct
      (exists_aligned_collision_dec
         (root_with_trace slots)
         (root_with_trace slots'))
      as [Hcollision | Hno_collision].
    { exact Hcollision. }
    exfalso.
    apply Hdistinct.
    eapply Root_injective_no_collision.
    { exact Hno_collision. }
    rewrite <- !root_with_trace_root.
    exact Hroot.
  Qed.

  (** The no-collision theorem is a corollary of the extractor.  It is the
      form a caller usually wants after separately assuming that the compared
      traces contain no aligned collision. *)
  Theorem Root_distinct_no_collision slots slots' :
    no_aligned_collisions
      (root_with_trace slots)
      (root_with_trace slots') ->
    normalize_slots slots <> normalize_slots slots' ->
    root slots <> root slots'.
  Proof.
    intros Hno_aligned Hdistinct Hroot.
    apply Hdistinct.
    eapply Root_injective_no_collision; eauto.
  Qed.
End CorrectnessProof.
