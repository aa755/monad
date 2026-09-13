Set Default Goal Selector "!".

(*
  Compatibility import for the split [storage_page.cpp] C++ proofs.

  The proofs now live one C++ function per file under
  [storage_page_cpp_proofs/].  Keep this file as the historical import path for
  code that still requires [mip8.storage_page_proofs].
*)

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.all.
