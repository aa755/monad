Set Default Goal Selector "!".

(*
  Central import point for C++ specifications.

  C++ proof files often need a broad spec environment even when they directly
  prove only one function.  In particular, the [evmc::bytes32] representation
  and its constructors/destructors live in [exec_specs.v], while smaller
  library adapters live under [libspecs/].  Importing this file makes those
  specs discoverable from one place for [Search], [Check], and proof-combiner
  work.
*)

Require Export monad.proofs.exec_specs.
Require Export monad.proofs.libspecs.ankerl_specs.
Require Export monad.proofs.libspecs.brick_upstream.
Require Export monad.proofs.libspecs.byte_string_specs.
Require Export monad.proofs.libspecs.const_specs.
Require Export monad.proofs.libspecs.deque_specs.
Require Export monad.proofs.libspecs.evmc_specs.
Require Export monad.proofs.libspecs.fiber_specs.
Require Export monad.proofs.libspecs.immer_specs.
Require Export monad.proofs.libspecs.optional_specs.
Require Export monad.proofs.libspecs.result_model.
Require Export monad.proofs.libspecs.outcome_specs.
Require Export monad.proofs.libspecs.system_error2.all.
Require Export monad.proofs.libspecs.outcome_status_code_specs.
Require Export monad.proofs.libspecs.pair_specs.
Require Export monad.proofs.libspecs.ranges_specs.
Require Export monad.proofs.libspecs.rlp_specs.
Require Export monad.proofs.libspecs.span_specs.
Require Export monad.proofs.libspecs.stdlib_specs.
Require Export monad.proofs.libspecs.u256_specs.
Require Export monad.proofs.libspecs.vector_upstream.
Require Export monad.proofs.libspecs.blake3.byte_bridges.
Require Export monad.proofs.libspecs.blake3.blake3_impl_h_specs.
Require Export monad.proofs.libspecs.boost.small_vector_specs.
