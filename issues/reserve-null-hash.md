# Reserve-Balance NULL_HASH Model

Status: still open after the production update to public main
`1d22498c5f6af83d375b504aa12bd5c815cf3545` on 2026-09-07.

The historical `dipped_into_reserve_spec` in `exec_specs.v` requires
`_global "monad::NULL_HASH" |-> bytes32R qnull 0`.
That spec imports `reservebalold.v`, whose `isAcSC` compares the cryptographic
code hash against zero. The newer `reservebal.v` has the same comparison, so
switching model imports alone would not repair it. The C++ constant in
`category/core/bytes.hpp` is instead
`c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`,
the Keccak-256 hash of the empty byte string.

The main-update checkpoint comments out this obsolete spec registration and
its authorized body proof. It is not an assumption available to retained
proofs. Main still compares code hashes with the nonzero `NULL_HASH`; the
model mismatch must be repaired before restoring that correctness claim.

This is not a quotient convention: `bytes32R` owns the concrete bytes and
`code_hash_of_program` denotes the cryptographic code hash. A theorem with
the zero-global precondition does not establish the desired result for
the production global.

Fix the reserve-balance model's comparison and the C++ spec's global
precondition together, then port the dependent model and body proofs.
Do not merely assume that the production constant is zero. The separate
`is_empty_spec` and `is_dead_spec` repairs now use the correct constant;
they do not resolve this reserve-balance connection.

The temporary proof suspension authorized for the main-branch update is
tracked in [reserve-balance-main-port.md](reserve-balance-main-port.md).
This mismatch must be repaired before reinstating a production
`dipped_into_reserve` correctness claim; suspending that proof does not close
this issue.
