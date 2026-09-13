Set Default Goal Selector "!".

(*
  Purpose of this file
  --------------------

  This is the paper-level proof for the
  Merkle Commitments via Induced Subtrees
  PDF.  It intentionally avoids hashes, storage pages, and generated C++ ASTs.
  The only object here is the finite complete binary tree and the subset of
  leaves selected by a bitmap.

  The main theorem, [merkle_commitments_induced_subtree_lemma], is the Coq
  version of the PDF lemma saying that a nonempty set of selected leaves induces
  a unique minimal rooted connected subtree: exactly the nodes that lie on a
  path from the root to a selected leaf.

  The MIP 8 PDF uses this result indirectly: page commitments commit only to
  nonzero storage slots, so the implementation needs a canonical compact tree
  that is determined by the occupancy bitmap.  This file proves that such a
  tree is not a choice made by the implementation; it is forced by the selected
  leaves.
*)

From Stdlib Require Import List Lia
  Logic.FunctionalExtensionality Logic.PropExtensionality.
Import ListNotations.

(* Nodes are root-to-node paths.  A [false]/[true] step is a left/right branch.
   This representation makes ancestry just list-prefix, which keeps the proof
   about the tree itself separate from any later bitmap encoding. *)
Definition node := list bool.

Definition isleaf (height : nat) (p : node) : Prop :=
  length p = height.

Definition in_complete_tree (height : nat) (p : node) : Prop :=
  length p <= height.

Definition prefix (p q : node) : Prop :=
  exists r, q = p ++ r.

(* The prefix lemmas below are the whole "geometry" of the complete binary tree.
   Once ancestry is prefix, connectedness and path membership become list facts
   rather than graph-search facts. *)
Lemma prefix_refl (p : node) : prefix p p.
Proof.
  exists []; now rewrite app_nil_r.
Qed.

Lemma prefix_nil (p : node) : prefix [] p.
Proof.
  exists p; reflexivity.
Qed.

Lemma prefix_trans (p q r : node) :
  prefix p q -> prefix q r -> prefix p r.
Proof.
  intros [pq_tail Hq] [qr_tail Hr].
  subst q r.
  exists (pq_tail ++ qr_tail).
  now rewrite app_assoc.
Qed.

Lemma prefix_length_le (p q : node) :
  prefix p q -> length p <= length q.
Proof.
  intros [tail ->].
  rewrite length_app; lia.
Qed.

Lemma prefix_eq_of_equal_length (p q : node) :
  prefix p q -> length p = length q -> p = q.
Proof.
  intros [tail ->] Hlen.
  rewrite length_app in Hlen.
  assert (tail = []) as ->.
  { destruct tail; simpl in Hlen; [reflexivity | lia]. }
  now rewrite app_nil_r.
Qed.

Definition occupied_leaf
    (height : nat) (bitmap : node -> Prop) (p : node) : Prop :=
  isleaf height p /\ bitmap p.

Definition nonempty_bitmap (height : nat) (bitmap : node -> Prop) : Prop :=
  exists p, occupied_leaf height bitmap p.

(* The induced subtree is defined extensionally: a node belongs exactly when it
   is an ancestor of some occupied leaf.  This is the key construction in the
   PDF.  The rest of the file proves that this direct definition is equivalent
   to the more semantic "unique minimal connected subtree" phrasing. *)
Definition induced_nodes
    (height : nat) (bitmap : node -> Prop) (p : node) : Prop :=
  exists l, isleaf height l /\ bitmap l /\ prefix p l.

(* A rooted connected subtree is represented as a predicate over nodes, not as
   an explicit edge set.  Ancestor-closure is enough because the ambient tree is
   already complete and rooted: if a node is present, the path back to the root
   is forced to be present. *)
Record rooted_connected_subtree
    (height : nat) (subtree : node -> Prop) : Prop := {
  subtree_in_tree :
    forall p, subtree p -> in_complete_tree height p;
  subtree_root :
    subtree [];
  subtree_ancestor_closed :
    forall p q, prefix p q -> subtree q -> subtree p;
}.

Definition contains_occupied_leaves
    (height : nat) (bitmap subtree : node -> Prop) : Prop :=
  forall l, isleaf height l -> bitmap l -> subtree l.

Definition contains_exactly_occupied_leaves
    (height : nat) (bitmap subtree : node -> Prop) : Prop :=
  forall l, isleaf height l -> (subtree l <-> bitmap l).

Definition every_node_on_occupied_path
    (height : nat) (bitmap subtree : node -> Prop) : Prop :=
  forall p, subtree p -> exists l, isleaf height l /\ bitmap l /\ prefix p l.

(* The four conjuncts mirror the PDF statement:
   rooted/connected, exact selected leaves, every node justified by an occupied
   path, and minimality against any other rooted connected candidate. *)
Definition minimal_connected_subtree
    (height : nat) (bitmap subtree : node -> Prop) : Prop :=
  rooted_connected_subtree height subtree /\
  contains_exactly_occupied_leaves height bitmap subtree /\
  every_node_on_occupied_path height bitmap subtree /\
  forall candidate,
    rooted_connected_subtree height candidate ->
    contains_occupied_leaves height bitmap candidate ->
    forall p, subtree p -> candidate p.

Lemma induced_nodes_in_tree height bitmap :
  forall p, induced_nodes height bitmap p -> in_complete_tree height p.
Proof.
  intros p [l [Hleaf [_ Hprefix]]].
  unfold isleaf, in_complete_tree in *.
  apply prefix_length_le in Hprefix; lia.
Qed.

Lemma induced_nodes_root height bitmap :
  nonempty_bitmap height bitmap ->
  induced_nodes height bitmap [].
Proof.
  intros [l [Hleaf Hbitmap]].
  exists l; repeat split; auto using prefix_nil.
Qed.

Lemma induced_nodes_ancestor_closed height bitmap :
  forall p q,
    prefix p q ->
    induced_nodes height bitmap q ->
    induced_nodes height bitmap p.
Proof.
  intros p q Hpq [l [Hleaf [Hbitmap Hql]]].
  exists l; repeat split; eauto using prefix_trans.
Qed.

Lemma induced_nodes_rooted_connected height bitmap :
  nonempty_bitmap height bitmap ->
  rooted_connected_subtree height (induced_nodes height bitmap).
Proof.
  intro Hnonempty.
  split.
  - apply induced_nodes_in_tree.
  - now apply induced_nodes_root.
  - apply induced_nodes_ancestor_closed.
Qed.

Lemma induced_nodes_exact_leaves height bitmap :
  contains_exactly_occupied_leaves height bitmap
    (induced_nodes height bitmap).
Proof.
  intros l Hleaf.
  split.
  - intros [l' [Hleaf' [Hbitmap Hprefix]]].
    assert (l = l') as ->.
    { apply prefix_eq_of_equal_length; auto.
      unfold isleaf in *; lia. }
    exact Hbitmap.
  - intro Hbitmap.
    exists l; repeat split; auto using prefix_refl.
Qed.

Lemma induced_nodes_path_property height bitmap :
  every_node_on_occupied_path height bitmap
    (induced_nodes height bitmap).
Proof.
  intros p Hp; exact Hp.
Qed.

Lemma induced_nodes_minimal height bitmap :
  forall candidate,
    rooted_connected_subtree height candidate ->
    contains_occupied_leaves height bitmap candidate ->
    forall p,
      induced_nodes height bitmap p -> candidate p.
Proof.
  intros candidate Hconnected Hcontains p [l [Hleaf [Hbitmap Hprefix]]].
  (* Minimality is the whole reason for defining [induced_nodes] by paths: any
     candidate that contains all selected leaves and is ancestor-closed must also
     contain every ancestor on those selected paths. *)
  destruct Hconnected as [_ _ Hancestor].
  eapply Hancestor; eauto.
Qed.

Theorem induced_nodes_minimal_connected_subtree height bitmap :
  nonempty_bitmap height bitmap ->
  minimal_connected_subtree height bitmap
    (induced_nodes height bitmap).
Proof.
  intro Hnonempty.
  unfold minimal_connected_subtree.
  split.
  - now apply induced_nodes_rooted_connected.
  - split.
    + apply induced_nodes_exact_leaves.
    + split.
      * apply induced_nodes_path_property.
      * eapply induced_nodes_minimal; eauto.
Qed.

Lemma minimal_connected_subtree_iff_induced height bitmap subtree :
  minimal_connected_subtree height bitmap subtree ->
  forall p, subtree p <-> induced_nodes height bitmap p.
Proof.
  intros (Hconnected & Hexact & Hpath & _) p.
  split.
  (* One direction uses the "no irrelevant nodes" clause.  The other uses exact
     leaf containment plus ancestor-closure.  Together they say every valid
     minimal subtree has the same node predicate as [induced_nodes]. *)
  - apply Hpath.
  - intros [l [Hleaf [Hbitmap Hprefix]]].
    destruct Hconnected as [_ _ Hancestor].
    eapply Hancestor; eauto.
    now apply (proj2 (Hexact l Hleaf)).
Qed.

Theorem induced_subtree_exists_unique height bitmap :
  nonempty_bitmap height bitmap ->
  exists! subtree,
    minimal_connected_subtree height bitmap subtree.
Proof.
  intro Hnonempty.
  (* Existence is by the explicit induced construction; uniqueness is
     extensional equality of node predicates.  This avoids committing to a
     concrete tree data structure, which is useful later when the commitment
     shape is encoded as bitmaps and merge queues instead. *)
  exists (induced_nodes height bitmap).
  split.
  - now apply induced_nodes_minimal_connected_subtree.
  - intros candidate Hcandidate.
    (* The standard [exists!] connective uses Leibniz equality.  Since subtrees
       are represented as predicates over nodes, the path-based uniqueness
       theorem gives pointwise iff first; functional and propositional
       extensionality turn that into predicate equality. *)
    apply functional_extensionality; intro p.
    apply propositional_extensionality.
    pose proof
      (minimal_connected_subtree_iff_induced
         height bitmap candidate Hcandidate p) as Hiff.
    symmetry.
    exact Hiff.
Qed.

Theorem merkle_commitments_induced_subtree_lemma height bitmap :
  nonempty_bitmap height bitmap ->
  exists! subtree,
    rooted_connected_subtree height subtree /\
    contains_exactly_occupied_leaves height bitmap subtree /\
    every_node_on_occupied_path height bitmap subtree /\
    (forall candidate,
      rooted_connected_subtree height candidate ->
      contains_occupied_leaves height bitmap candidate ->
      forall p, subtree p -> candidate p).
Proof.
  intro Hnonempty.
  destruct (induced_subtree_exists_unique height bitmap Hnonempty)
    as [subtree [Hminimal Hunique]].
  exists subtree.
  split; [exact Hminimal |].
  intros candidate Hcandidate.
  apply Hunique.
  exact Hcandidate.
Qed.
