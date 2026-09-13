(** * Bridge from MIP-8 value trees to induced subtrees

    [induced_subtree.v] proves the paper theorem over complete binary trees:
    nodes are root-to-node paths and a subtree is a predicate on those paths.

    [commitment.v] uses a more compact executable tree.  A [value_tree]
    contains only occupied pair leaves and binary merge nodes that are actually
    hashed.  Unary stretches of the complete tree are collapsed because they do
    not produce hashes.

    This file connects the two views.  Given the original pair-position list
    used by [build_value_tree], [compact_value_tree_nodes] expands the compact
    tree back into the complete-tree nodes that lie on paths to occupied pair
    leaves.  The main theorems are stated directly with the paper-level
    [minimal_connected_subtree] predicate rather than introducing a second,
    compact-tree-specific minimality notion.
*)

(* begin hide *)
Set Default Goal Selector "!".

From Stdlib Require Import Bool List Lia.
Import ListNotations.

Require Import monad.proofs.execproofs.mip8.induced_subtree.
Require Import monad.proofs.execproofs.mip8.blake3model.
Require Import monad.proofs.execproofs.mip8.commitment.
(* end hide *)

(** ** Occupied pair leaves as a paper bitmap *)

(** [occupied_leaf_path depth pairs path] means that [path] names an occupied
    pair leaf in the complete tree whose leaves are represented by [pairs].
    The recursion follows the same bisection as [build_value_tree]: [false]
    selects the left half and [true] selects the right half. *)
Fixpoint occupied_leaf_path
    (depth : nat) (pairs : list (option pair_leaf)) (path : node) : Prop :=
  match depth with
  | O =>
      path = [] /\ exists value, pairs = [Some value]
  | S depth' =>
      let width := subtree_width depth' in
      match path with
      | false :: rest =>
          occupied_leaf_path depth' (firstn width pairs) rest
      | true :: rest =>
          occupied_leaf_path depth' (skipn width pairs) rest
      | [] => False
      end
  end.

Definition pair_leaf_bitmap
    (depth : nat) (pairs : list (option pair_leaf)) : node -> Prop :=
  occupied_leaf_path depth pairs.

(** ** Expanding the compact value tree *)

(** [compact_value_tree_nodes depth pairs tree] is the complete-tree node
    predicate denoted by a compact [value_tree] built from [pairs].  Every
    recursive subtree includes its local root [[]].  If only one child side is
    occupied, the compact tree has no unary constructor, so the original
    [pairs] list is used to decide whether to continue through the left or
    right branch. *)
Fixpoint compact_value_tree_nodes
    (depth : nat) (pairs : list (option pair_leaf)) (tree : value_tree)
    (path : node) : Prop :=
  match depth with
  | O =>
      path = [] /\ exists value, pairs = [Some value]
  | S depth' =>
      let width := subtree_width depth' in
      let lhs_pairs := firstn width pairs in
      let rhs_pairs := skipn width pairs in
      match build_value_tree depth' lhs_pairs,
            build_value_tree depth' rhs_pairs,
            tree with
      | Some _, None, _ =>
          path = [] \/
          exists rest,
            path = false :: rest /\
            compact_value_tree_nodes depth' lhs_pairs tree rest
      | None, Some _, _ =>
          path = [] \/
          exists rest,
            path = true :: rest /\
            compact_value_tree_nodes depth' rhs_pairs tree rest
      | Some _, Some _, TreeNode lhs rhs =>
          path = [] \/
          (exists rest,
            path = false :: rest /\
            compact_value_tree_nodes depth' lhs_pairs lhs rest) \/
          (exists rest,
            path = true :: rest /\
            compact_value_tree_nodes depth' rhs_pairs rhs rest)
      | _, _, _ => False
      end
  end.

(** ** Path lemmas *)

Lemma prefix_to_nil path :
  prefix path [] -> path = [].
Proof.
  intros [tail Htail].
  destruct path as [| bit rest]; [reflexivity | discriminate Htail].
Qed.

Lemma prefix_cons bit path leaf :
  prefix path leaf ->
  prefix (bit :: path) (bit :: leaf).
Proof.
  intros [tail ->].
  exists tail.
  reflexivity.
Qed.

Lemma prefix_of_cons_inv bit path leaf :
  prefix path (bit :: leaf) ->
  path = [] \/
  exists rest,
    path = bit :: rest /\ prefix rest leaf.
Proof.
  intros [tail Hprefix].
  destruct path as [| head rest].
  { now left. }
  right.
  inversion Hprefix; subst head.
  exists rest.
  split; [reflexivity |].
  exists tail.
  reflexivity.
Qed.

Lemma isleaf_cons bit depth leaf :
  isleaf depth leaf ->
  isleaf (S depth) (bit :: leaf).
Proof.
  unfold isleaf.
  simpl.
  congruence.
Qed.

Lemma occupied_leaf_path_length depth pairs path :
  occupied_leaf_path depth pairs path ->
  length path = depth.
Proof.
  revert pairs path.
  induction depth as [| depth IH]; intros pairs path Hoccupied.
  { destruct Hoccupied as [-> _].
    reflexivity. }
  destruct path as [| bit rest]; simpl in Hoccupied; [contradiction |].
  destruct bit.
  { simpl.
    f_equal.
    eapply IH; eauto. }
  simpl.
  f_equal.
  eapply IH; eauto.
Qed.

Lemma occupied_leaf_path_build_value_tree
    depth pairs path :
  length pairs = subtree_width depth ->
  occupied_leaf_path depth pairs path ->
  exists tree, build_value_tree depth pairs = Some tree.
Proof.
  revert pairs path.
  induction depth as [| depth IH]; intros pairs path Hlen Hoccupied.
  { destruct Hoccupied as [_ [value ->]].
    exists (TreeLeaf value).
    reflexivity. }
  simpl in Hlen.
  destruct path as [| bit rest]; simpl in Hoccupied; [contradiction |].
  set (width := subtree_width depth).
  assert (Hleft_len : length (firstn width pairs) = width).
  { subst width. rewrite length_firstn. lia. }
  assert (Hright_len : length (skipn width pairs) = width).
  { subst width. rewrite length_skipn. lia. }
  destruct bit.
  { destruct (IH (skipn width pairs) rest Hright_len Hoccupied)
      as [rhs Hrhs].
    simpl.
    change (subtree_width depth) with width.
    rewrite Hrhs.
    destruct (build_value_tree depth (firstn width pairs)) as [lhs |].
    { exists (TreeNode lhs rhs). reflexivity. }
    exists rhs. reflexivity. }
  destruct (IH (firstn width pairs) rest Hleft_len Hoccupied)
    as [lhs Hlhs].
  simpl.
  change (subtree_width depth) with width.
  rewrite Hlhs.
  destruct (build_value_tree depth (skipn width pairs)) as [rhs |].
  { exists (TreeNode lhs rhs). reflexivity. }
  exists lhs. reflexivity.
Qed.

Lemma no_occupied_leaf_path_of_no_tree depth pairs :
  length pairs = subtree_width depth ->
  build_value_tree depth pairs = None ->
  forall path, ~ occupied_leaf_path depth pairs path.
Proof.
  intros Hlen Hnone path Hoccupied.
  destruct (occupied_leaf_path_build_value_tree depth pairs path Hlen Hoccupied)
    as [tree Htree].
  rewrite Htree in Hnone.
  discriminate.
Qed.

Lemma compact_value_tree_nodes_root depth pairs tree :
  length pairs = subtree_width depth ->
  build_value_tree depth pairs = Some tree ->
  compact_value_tree_nodes depth pairs tree [].
Proof.
  revert pairs tree.
  induction depth as [| depth IH]; intros pairs tree Hlen Hbuild.
  { simpl in Hbuild.
    destruct pairs as [| [value |] [| extra rest]];
      try discriminate.
    inversion Hbuild; subst tree.
    split; [reflexivity |].
    exists value.
    reflexivity. }
  simpl in Hlen, Hbuild.
  set (width := subtree_width depth).
  change (subtree_width depth) with width in Hbuild.
  destruct (build_value_tree depth (firstn width pairs)) as [lhs |] eqn:Hlhs;
    destruct (build_value_tree depth (skipn width pairs)) as [rhs |] eqn:Hrhs;
    simpl in Hbuild; try discriminate.
  { inversion Hbuild; subst tree.
    simpl.
    change (subtree_width depth) with width.
    rewrite Hlhs, Hrhs.
    now left. }
  { inversion Hbuild; subst tree.
    simpl.
    change (subtree_width depth) with width.
    rewrite Hlhs, Hrhs.
    now left. }
  inversion Hbuild; subst tree.
  simpl.
  change (subtree_width depth) with width.
  rewrite Hlhs, Hrhs.
  now left.
Qed.

(** ** The bridge theorem *)

Lemma compact_value_tree_nodes_are_induced
    depth pairs tree :
  length pairs = subtree_width depth ->
  build_value_tree depth pairs = Some tree ->
  forall path,
    compact_value_tree_nodes depth pairs tree path <->
    induced_nodes depth (pair_leaf_bitmap depth pairs) path.
Proof.
  revert pairs tree.
  induction depth as [| depth IH]; intros pairs tree Hlen Hbuild path.
  { simpl in Hbuild.
    destruct pairs as [| [value |] [| extra rest]];
      try discriminate.
    inversion Hbuild; subst tree.
    simpl.
    split.
    { intros [Hpath Hoccupied].
      subst path.
      exists [].
      split; [reflexivity |].
      split.
      { split; [reflexivity | exact Hoccupied]. }
      apply prefix_refl. }
    intros [leaf [Hleaf [Hbitmap Hprefix]]].
    unfold isleaf in Hleaf.
    destruct leaf as [| bit rest]; [| discriminate Hleaf].
    apply prefix_to_nil in Hprefix.
    destruct Hbitmap as [_ Hoccupied].
    split; [exact Hprefix | exact Hoccupied]. }
  simpl in Hlen, Hbuild.
  set (width := subtree_width depth).
  change (subtree_width depth) with width in Hbuild.
  assert (Hleft_len : length (firstn width pairs) = width).
  { subst width. rewrite length_firstn. lia. }
  assert (Hright_len : length (skipn width pairs) = width).
  { subst width. rewrite length_skipn. lia. }
  destruct (build_value_tree depth (firstn width pairs)) as [lhs |] eqn:Hlhs;
    destruct (build_value_tree depth (skipn width pairs)) as [rhs |] eqn:Hrhs;
    simpl in Hbuild; try discriminate.
  { inversion Hbuild; subst tree.
    simpl.
    change (subtree_width depth) with width.
    rewrite Hlhs, Hrhs.
    split.
    { intros [Hroot | [[rest [Hpath Hnodes]] | [rest [Hpath Hnodes]]]].
      { subst path.
        pose proof (compact_value_tree_nodes_root
                    depth (firstn width pairs) lhs Hleft_len Hlhs)
          as Hleft_root.
        apply (proj1 (IH (firstn width pairs) lhs Hleft_len Hlhs []))
          in Hleft_root.
        destruct Hleft_root as [leaf [Hleaf [Hbitmap Hprefix]]].
        exists (false :: leaf).
        repeat split.
        { now apply isleaf_cons. }
        { exact Hbitmap. }
        apply prefix_nil. }
      { subst path.
        apply (proj1 (IH (firstn width pairs) lhs Hleft_len Hlhs rest))
          in Hnodes.
        destruct Hnodes as [leaf [Hleaf [Hbitmap Hprefix]]].
        exists (false :: leaf).
        repeat split.
        { now apply isleaf_cons. }
        { exact Hbitmap. }
        now apply prefix_cons. }
      subst path.
      apply (proj1 (IH (skipn width pairs) rhs Hright_len Hrhs rest))
        in Hnodes.
      destruct Hnodes as [leaf [Hleaf [Hbitmap Hprefix]]].
      exists (true :: leaf).
      repeat split.
      { now apply isleaf_cons. }
      { exact Hbitmap. }
      now apply prefix_cons. }
    intros [leaf [Hleaf [Hbitmap Hprefix]]].
    destruct leaf as [| bit leaf_rest].
    { discriminate Hleaf. }
    destruct (prefix_of_cons_inv bit path leaf_rest)
      as [Hpath_root | [rest [Hpath Hprefix_rest]]].
    { exact Hprefix. }
    { now left. }
    subst path.
    destruct bit.
    { right; right.
      exists rest.
      split; [reflexivity |].
      apply (proj2 (IH (skipn width pairs) rhs Hright_len Hrhs rest)).
      exists leaf_rest.
      repeat split.
      { unfold isleaf in Hleaf |- *.
        simpl in Hleaf.
        lia. }
      { exact Hbitmap. }
      { exact Hprefix_rest. } }
    right; left.
    exists rest.
    split; [reflexivity |].
    apply (proj2 (IH (firstn width pairs) lhs Hleft_len Hlhs rest)).
    exists leaf_rest.
    repeat split.
    { unfold isleaf in Hleaf |- *.
      simpl in Hleaf.
      lia. }
    { exact Hbitmap. }
    { exact Hprefix_rest. } }
  { inversion Hbuild; subst tree.
    simpl.
    change (subtree_width depth) with width.
    rewrite Hlhs, Hrhs.
    split.
    { intros [Hroot | [rest [Hpath Hnodes]]].
      { subst path.
        pose proof (compact_value_tree_nodes_root
                    depth (firstn width pairs) lhs Hleft_len Hlhs)
          as Hleft_root.
        apply (proj1 (IH (firstn width pairs) lhs Hleft_len Hlhs []))
          in Hleft_root.
        destruct Hleft_root as [leaf [Hleaf [Hbitmap Hprefix]]].
        exists (false :: leaf).
        repeat split.
        { now apply isleaf_cons. }
        { exact Hbitmap. }
        apply prefix_nil. }
      subst path.
      apply (proj1 (IH (firstn width pairs) lhs Hleft_len Hlhs rest))
        in Hnodes.
      destruct Hnodes as [leaf [Hleaf [Hbitmap Hprefix]]].
      exists (false :: leaf).
      repeat split.
      { now apply isleaf_cons. }
      { exact Hbitmap. }
      now apply prefix_cons. }
    intros [leaf [Hleaf [Hbitmap Hprefix]]].
    destruct leaf as [| bit leaf_rest].
    { discriminate Hleaf. }
    destruct bit.
    { exfalso.
      eapply (no_occupied_leaf_path_of_no_tree
                depth (skipn width pairs)); eauto. }
    destruct (prefix_of_cons_inv false path leaf_rest)
      as [Hpath_root | [rest [Hpath Hprefix_rest]]].
    { exact Hprefix. }
    { now left. }
    subst path.
    right.
    exists rest.
    split; [reflexivity |].
    apply (proj2 (IH (firstn width pairs) lhs Hleft_len Hlhs rest)).
    exists leaf_rest.
    repeat split.
    { unfold isleaf in Hleaf |- *.
      simpl in Hleaf.
      lia. }
    { exact Hbitmap. }
    { exact Hprefix_rest. } }
  inversion Hbuild; subst tree.
  simpl.
  change (subtree_width depth) with width.
  rewrite Hlhs, Hrhs.
  split.
  { intros [Hroot | [rest [Hpath Hnodes]]].
    { subst path.
      pose proof (compact_value_tree_nodes_root
                  depth (skipn width pairs) rhs Hright_len Hrhs)
        as Hright_root.
      apply (proj1 (IH (skipn width pairs) rhs Hright_len Hrhs []))
        in Hright_root.
      destruct Hright_root as [leaf [Hleaf [Hbitmap Hprefix]]].
      exists (true :: leaf).
      repeat split.
      { now apply isleaf_cons. }
      { exact Hbitmap. }
      apply prefix_nil. }
    subst path.
    apply (proj1 (IH (skipn width pairs) rhs Hright_len Hrhs rest))
      in Hnodes.
    destruct Hnodes as [leaf [Hleaf [Hbitmap Hprefix]]].
    exists (true :: leaf).
    repeat split.
    { now apply isleaf_cons. }
    { exact Hbitmap. }
    now apply prefix_cons. }
  intros [leaf [Hleaf [Hbitmap Hprefix]]].
  destruct leaf as [| bit leaf_rest].
  { discriminate Hleaf. }
  destruct bit.
  { destruct (prefix_of_cons_inv true path leaf_rest)
      as [Hpath_root | [rest [Hpath Hprefix_rest]]].
    { exact Hprefix. }
    { now left. }
    subst path.
    right.
    exists rest.
    split; [reflexivity |].
    apply (proj2 (IH (skipn width pairs) rhs Hright_len Hrhs rest)).
    exists leaf_rest.
    repeat split.
    { unfold isleaf in Hleaf |- *.
      simpl in Hleaf.
      lia. }
    { exact Hbitmap. }
    { exact Hprefix_rest. } }
  exfalso.
  eapply (no_occupied_leaf_path_of_no_tree
            depth (firstn width pairs)); eauto.
Qed.

Lemma minimal_connected_subtree_ext
    height bitmap subtree subtree' :
  (forall path, subtree path <-> subtree' path) ->
  minimal_connected_subtree height bitmap subtree ->
  minimal_connected_subtree height bitmap subtree'.
Proof.
  intros Hequiv (Hconnected & Hexact & Hpath & Hminimal).
  split.
  { destruct Hconnected as [Hin_tree Hroot Hancestor].
    split.
    { intros path Hsubtree'.
      apply Hin_tree.
      now apply Hequiv. }
    { now apply Hequiv. }
    intros path leaf Hprefix Hleaf.
    apply Hequiv.
    eapply Hancestor; eauto.
    now apply Hequiv. }
  split.
  { intros leaf Hleaf.
    rewrite <- Hequiv.
    apply Hexact; exact Hleaf. }
  split.
  { intros path Hsubtree'.
    apply Hpath.
    now apply Hequiv. }
  intros candidate Hcandidate Hcontains path Hsubtree'.
  eapply Hminimal; eauto.
  now apply Hequiv.
Qed.

Theorem build_value_tree_paper_minimal_connected_subtree
    depth pairs tree :
  length pairs = subtree_width depth ->
  build_value_tree depth pairs = Some tree ->
  minimal_connected_subtree depth (pair_leaf_bitmap depth pairs)
    (compact_value_tree_nodes depth pairs tree).
Proof.
  intros Hlen Hbuild.
  assert
    (Hroot :
       compact_value_tree_nodes depth pairs tree []).
  { now apply compact_value_tree_nodes_root. }
  pose proof
    (compact_value_tree_nodes_are_induced
       depth pairs tree Hlen Hbuild) as Hbridge.
  assert (Hnonempty : nonempty_bitmap depth (pair_leaf_bitmap depth pairs)).
  { apply Hbridge in Hroot.
    destruct Hroot as [leaf [Hleaf [Hbitmap _]]].
    exists leaf.
    split; assumption. }
  eapply minimal_connected_subtree_ext.
  { intro path.
    symmetry.
    apply Hbridge. }
  now apply induced_nodes_minimal_connected_subtree.
Qed.

(** The compact tree is therefore not just a valid minimal subtree.  Its
    complete-tree denotation is exactly the unique subtree satisfying the
    paper-level minimality specification. *)
Corollary build_value_tree_unique_paper_minimal_connected_subtree
    depth pairs tree :
  length pairs = subtree_width depth ->
  build_value_tree depth pairs = Some tree ->
  forall subtree,
    minimal_connected_subtree depth (pair_leaf_bitmap depth pairs) subtree <->
    subtree = compact_value_tree_nodes depth pairs tree.
Proof.
  intros Hlen Hbuild subtree.
  pose proof
    (build_value_tree_paper_minimal_connected_subtree
       depth pairs tree Hlen Hbuild) as Hminimal.
  assert (Hnonempty : nonempty_bitmap depth (pair_leaf_bitmap depth pairs)).
  { pose proof Hminimal as Hminimal_copy.
    destruct Hminimal_copy as [[_ Hroot _] [_ [Hpath _]]].
    destruct (Hpath [] Hroot) as [leaf [Hleaf [Hbitmap _]]].
    exists leaf.
    split; assumption. }
  destruct (induced_subtree_exists_unique
              depth (pair_leaf_bitmap depth pairs) Hnonempty)
    as [unique [Hunique Hunique_is_unique]].
  split.
  { intro Hsubtree.
    transitivity unique.
    { symmetry.
      now apply Hunique_is_unique. }
    now apply Hunique_is_unique. }
  intro Hsubtree.
  subst subtree.
  exact Hminimal.
Qed.
