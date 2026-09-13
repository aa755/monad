# Proof Files Outside the Checked Import Target

Full-file checks during the EVMOpSem extraction on 2026-09-12 found five
failures outside `monadproofs/proofs/all.v`. The three historical-model
failures have since been repaired and those models added to the checked
target. The two C++ caller proofs below remain outside it. No previously
checked proof was disabled by the extraction or these repairs.

Paths in the table are relative to `monadproofs/proofs/`.

| File | Failing command or dependency | Follow-up |
| --- | --- | --- |
| `execproofs/reservebal/subtract_from_balance_proof.v:83` | `state_check_min_balance_slice_spec_spec_instance` no longer exists. | Port the old helper dependency to the current debit-constraint proof/spec; do not reintroduce a spec for the deleted helper. |
| `execproofs/reservebal/add_to_balance_proof.v:270` | Verification needs a spec for `monad::ReserveBalance::on_credit(const monad::Address&)`. | Specify and prove the Monad-owned callee before restoring the caller to the checked target. |

These are the first errors reported, not evidence that later parts of each
caller already check. A successful `all.vo` build must not be presented as
checking these two files.

## Restored Model Checks

`all.v` now also loads `reservebal.v`, `reservebal2.v`, `reservebal2037.v`,
`reservebaldelayed.v`, `reservebalhybrid.v`, `reservebalnewproposal.v`, and
`reservebaluserfield.v`. `reservebalold.v` was already loaded by the C++ specs.

The fixes qualify `miscPure.Forward`, use stdpp's `list_elem_of_singleton`,
and explicitly type the tail-membership premise of the induction argument in
`reservebalnewproposal.v`, as the working variants already do. `reservebal2.v`
also adopts the required default goal selector. Models, theorem statements,
and assumptions are unchanged. Checking these historical models does not
establish their correspondence to the current production C++.
