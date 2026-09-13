Set Default Goal Selector "!".

(*
  Purpose of this file
  --------------------

  This is the build-order entry point for the MIP 8 proof area.  It imports the
  paper-level induced-subtree proof, the C++-shaped commitment model, the
  bridge from compact MIP 8 value trees back to induced subtrees, the
  inclusion/exclusion proof model, the pure storage-page encoding model, and
  finally the generated-C++ specs/proofs.

  Read the files in this order if you want the conceptual stack:
  induced_subtree -> blake3model -> commitment ->
  induced_subtree_bridge -> membership_proofs -> storage_page_indexed_encoding ->
  blake3specs -> storage_page_specs -> storage_page_cpp_proofs/all ->
  storage_page_proofs.
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
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.all.
Require Import monad.proofs.execproofs.mip8.storage_page_proofs.
