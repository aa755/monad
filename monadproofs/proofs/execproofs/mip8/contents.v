Set Default Goal Selector "!".

(** * MIP-8 Proof Directory Contents

    This file is a Coqdoc landing page for the MIP-8 proof directory.  It is
    intentionally light on Gallina: its job is to tell a reader which file to
    open next and why.  The [Require Import] commands at the end are kept
    visible on purpose, because Coqdoc turns imported module names into
    hyperlinks to the generated pages for those files.

    The directory has three conceptual layers.

    - The first layer is the paper argument from
      Merkle Commitments via Induced Subtrees:
      selected leaves in a complete binary tree determine a unique minimal
      connected induced subtree.

    - The second layer is the MIP-8 page-commitment model from the
      MIP-8 page-ified storage-state design note
      and the
      #<a href="https://github.com/monad-crypto/MIPs/blob/main/MIPS/MIP-8.md">MIP repository draft</a>#:
      a 128-slot storage page becomes a 64-leaf pair tree, the pair tree is
      hashed, and the final root seals the full 128-bit slot bitmap.
      This layer also contains the inclusion/exclusion proof model and the
      byte-size bounds claimed in the two notes.

    - The third layer connects the model to the generated C++ AST for
      [category/execution/monad/db/storage_page.cpp]: storage-page encoding,
      BLAKE3 call specs, storage-page function specs, and the proofs that
      currently discharge those specs.
*)

(** ** Recommended Reading Order

    1. [induced_subtree]

       Start here for the standalone theorem from
       Merkle Commitments via Induced Subtrees.
       This file knows nothing about BLAKE3, storage pages, or C++.  It proves
       that a nonempty bitmap of complete-tree leaves determines a unique
       minimal rooted connected subtree.

    2. [blake3model]

       Read this before the executable commitment model.  It specializes the
       byte types and cryptographic operations from
       [monad.proofs.libspecs.blake3.model] to MIP-8's leaf, merge, and seal
       modes.  The abstract BLAKE3 operations live in that library model;
       [H64], [seal_empty], and [seal_nonempty] are definitions here.

    3. [commitment]

       This is the mathematical model of the MIP-8 page
       commitment.  The first section gives the simple algorithmic story:
       normalize 128 slots, form optional 64-byte pair leaves, build the
       compact induced value tree, hash it, and seal it with the full slot
       bitmap.  Later sections add located hash traces and prove the binding
       theorem via aligned collision extraction.

    4. [induced_subtree_bridge]

       This file expands a compact [value_tree] back into complete-tree paths
       using [compact_value_tree_nodes].  The original pair-position list
       determines where to restore the collapsed unary paths.
       [build_value_tree_paper_minimal_connected_subtree] and
       [build_value_tree_unique_paper_minimal_connected_subtree] prove
       minimality and uniqueness using [induced_subtree]'s
       [minimal_connected_subtree] predicate, without a second minimality
       definition over compact trees.

    5. [membership_proofs]

       This file models inclusion and exclusion proof witnesses for induced
       subtrees, including the opened pair value.  It proves the
       [min(k - 1, n)] sibling-hash bound for inclusion proofs, the specialized
       MIP-8 [16 + 32 * min(k - 1, 6)] bound, and the 48-byte MIP-8 exclusion
       proof size.  Here [k] counts active pair leaves, not active slots.
       [mip8_false_inclusion_value_extracts_aligned_collision] and
       [mip8_false_exclusion_view_extracts_aligned_collision] connect claimed
       page views to [commitment]'s collision extractor.  Those theorems
       explicitly require the claimed view's root to equal the committed
       root; they do not reconstruct a full page view from arbitrary sibling
       hashes.  The generic bitmap-level soundness results are separate.

    6. [storage_page_indexed_encoding]

       This file is separate from the commitment argument.  It models
       [encode_storage_page] and [decode_storage_page] as ordered index/value
       pairs. It proves encode/decode identity for canonical 128-slot pages
       and uniqueness of accepted encodings. [storage_page_encoding] supplies
       its compact-RLP lemmas and retains the historical RLE page proofs.

    7. [blake3specs]

       This file supplies the MIP-8 adapters between [blake3model] and the
       generic library specs in
       [monad.proofs.libspecs.blake3.blake3_impl_h_specs].  Its definitions
       and bridge lemmas describe the hash parameters, leaf-key cache, and
       seal-block bytes.  The Monad helper call specs themselves are in
       [storage_page_specs].

    8. [storage_page_specs]

       This is the C++ specification layer for [storage_page.cpp].  It gathers
       the page-key, slot-offset, commitment, encoder, and decoder models into
       separation-logic specs for the generated AST.  It also contains the
       small [list N] to optional [slot_word] bridge that specializes
       [commitment] to the storage-page representation used by [bytes32R].

    9. [storage_page_proofs]

       This is a compatibility import, not the file containing the body proofs.
       Each C++ function's proof lives under [storage_page_cpp_proofs/].
       [monad.proofs.execproofs.mip8.storage_page_cpp_proofs.all] combines
       them: [page_commit_cpp_proof_ok], [encode_storage_page_cpp_proof_ok],
       and [decode_storage_page_cpp_proof_ok] discharge the proved helper
       contracts and expose the remaining external interfaces.  These
       interface premises and the axioms reported by [Print Assumptions]
       must both be considered when reading the correctness claims.

    10. [all]

       This is the build-order import file.  Use it when you want the MIP-8
       proof area loaded as one Coq context for search and exploration.
*)

(** ** Visible Import Index

    The imports below are deliberately in the same order as the guide above.
    In generated Coqdoc HTML, each imported module name links to that file's
    generated documentation page.
*)

Require Import monad.proofs.execproofs.mip8.induced_subtree.
Require Import monad.proofs.execproofs.mip8.blake3model.
Require Import monad.proofs.execproofs.mip8.commitment.
Require Import monad.proofs.execproofs.mip8.induced_subtree_bridge.
Require Import monad.proofs.execproofs.mip8.membership_proofs.
Require Import monad.proofs.execproofs.mip8.storage_page_encoding.
Require Import monad.proofs.execproofs.mip8.storage_page_indexed_encoding.
Require Import monad.proofs.execproofs.mip8.blake3specs.
Require Import monad.proofs.execproofs.mip8.storage_page_specs.
Require Import monad.proofs.execproofs.mip8.storage_page_proofs.
Require Import monad.proofs.execproofs.mip8.all.
