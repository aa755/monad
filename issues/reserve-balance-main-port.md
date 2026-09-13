# Reserve-Balance Proof Suspension for the Main-Branch Update

## Status and Reference

The code update and retained-proof port completed on 2026-09-08. Only
`reserve_balance.v` remains suspended among the six files below. The user authorized
temporarily suspending exactly these six files when replacing the local
C++ with unmodified public main. This is not authorization to add assumptions,
weaken other proofs, or keep their old specs as trusted substitutes for the
suspended bodies.

- Passing pre-update Monad baseline: `83749b825`.
- Borg repository: `/home/abhishek/borg-archive-repo`.
- Verified reference archive: `backup-2026-09-07T21:35:41`.
  Fingerprint: `819c8fed70604acd35a579fc61bebf94d8c74c27279ef8bb00920658ea80204d`.
- Main fetched and pinned for the update:
  [`1d22498c5f6af83d375b504aa12bd5c815cf3545`](https://github.com/category-labs/monad/commit/1d22498c5f6af83d375b504aa12bd5c815cf3545).

The archive includes both workspaces, generated ASTs, build artifacts, and
`.opam`. Both Dune's `all.vo` build and interactive checking of `all.v` passed
before this archive was created, with only the separately authorized
Incarnation caller theorem/spec suspended. Use this snapshot for live
old/new proof-state comparisons; do not rediscover the existing proofs.

## Authorized Scope

Paths below are relative to `monadproofs/proofs/execproofs/reservebal/`.
The remaining `reserve_balance.v` import in `monadproofs/proofs/all.v` is
commented out with a reference to this issue. Its source remains available.
`set_storage_proof.v` and the restored debit-constraint proof import the checked
layout lemmas from `check_min_original_balance_proof.v`. The two obsolete C++
body theorems have been removed; their scripts remain in Git and the reference.

| File | Main's change | Required restoration |
| --- | --- | --- |
| `sender_seen_in_current_prefix_proof.v` | The separate C++ helper does not exist. | Restored through the caller: the invariant lemmas remain here, and the loop body proof has moved into `cansenderdip.v`. The obsolete helper spec is deleted. |
| `cansenderdip.v` | The caller contains the prefix-search loop directly. | Restored with the unchanged decision contract, now in `reservebal_specs.v`. The central `all.v` imports the caller proof and, indirectly, its invariant lemmas. |
| `check_min_balance_proof.v` | `State::check_min_balance` does not exist. | Restored for `State::record_balance_constraint_for_debit`, with the former slice contract. Checks the directly included constraint-recording body, not an assumed helper call. |
| `check_min_original_balance_proof.v` | Neither `check_account_min_balance` nor `check_min_original_balance` exists. | The applicable body reasoning and layout lemmas are reused by the debit-constraint proof. The obsolete wrapper/body theorems are retired; the checked shared lemmas remain. |
| `dippedlam.v` | The threshold lambda reads the original balance exactly, then uses `std::min`. | Restored: its contract in `reservebal_specs.v` preserves the threshold result and records the exact-balance update. The proof checks `std::min` inline and reuses the sender/gas-fee threshold lemmas. |
| `reserve_balance.v` | Main adds exemption branches and tracing, and uses exact balance reads. | Reconnect the production body to a model covering those branches, using sound specs for the actual calls. |

The remaining suspended targets' AST-bound `cpp.spec` declarations and registrations in
`exec_specs.v` and `reservebal_specs.v` are also commented out, including the
removed `State::is_delegated` helper and the old lambda contracts. Only the
updated lambda contract is registered for that call. Restored contracts for
main's sender decision and debit-constraint method are in `reservebal_specs.v`.
Reusable pure definitions and lemmas remain active. Removed symbols must not
be silently assumed by retained proofs. The suspension checkpoint is `a057aed98`.
The retained import closure, including the indirect layout-lemma import,
passes the completion checks below.

The prefix-loop restoration reused the old caller and helper proof scripts,
with both reference files checked live in separate Emacs sessions. Changes
were confined to the inlined control flow, return-condition bridges to the
existing history lemmas, local hint registrations, and generated hypothesis
names. No production C++ or decision contract changed, and no helper spec is
assumed in place of the removed function. The new theorem adds no axiom or
admitted item. The other four suspended files were not part of that first restoration.

Restoration validation on 2026-09-08: the complete
`dune build monad/monadproofs/proofs/all.vo` succeeded at 20:23 EDT,
including the restored caller, and the central `all.v` checked through EOF
in Emacs/Proof General. With `Set Printing Fully Qualified` enabled,
`About cansenderdip.prf` lists seven existing callee-spec assumptions;
the deleted prefix-helper spec is not among them. `Print Assumptions` lists
12 pre-existing `monad.*` axioms for the model and representation boundaries,
and does not include `monad.proofs.misc.wp_const_const_delete`.
The restored decision contract is text-identical to the previously suspended
contract. Production C++ still matches the pinned public-main commit.

The lambda restoration also passed `all.vo` on 2026-09-08. Its live proof was
compared with the pre-update lambda in the Borg reference. The same threshold
lemmas handle the sender/gas-fee branches; the only changed state postcondition
is `update_assum_exactness_at addr exact_balance_update orig`, matching
`get_original_balance`. `std::min` is checked inline, not assumed. The proof's
printed assumptions contain no `wp_const_const_delete`, and no new axiom or
admitted item was added.

The debit-constraint restoration checks the production method with the old
slice contract: success records the necessary lower bound on the original
balance, while failure records exactness. Both a current-account entry and a
fallback to the original account are covered, including absent accounts.
The current balance is copied before the original-account lookup, as in main.
The old helper proof only covered the case where those balances coincide;
the restored body also handles a different current balance directly. Existing
layout and map-restoration lemmas were reused, with the old caller and helper
checked live in separate reference Emacs sessions.

`prf_state_record_balance_constraint_for_debit` has twelve existing callee-spec
assumptions, and does not assume either deleted helper. Fully qualified
`Print Assumptions` lists thirteen pre-existing `monad.*` representation/model
axioms, including the existing map decomposition rule `borrowIndex_at`.
It does not contain `wp_const_const_delete`. No new axiom, admitted item,
production-code edit, or weaker debit-constraint contract was introduced.
Validation on 2026-09-08: the restored body checked through `Qed` in Emacs;
the complete `monadproofs/proofs/all.vo` build succeeded (4m08s, 22.9 GiB peak),
and the central `all.v` then checked through EOF in Emacs/Proof General.

The unused `exbb_spec` and `exbt_spec` registrations also name obsolete
recorder-free signatures: public main adds an `ExecutionEventRecorder*`
argument. Their only body-proof clients are in `execute_block.v`, which was
already excluded from `all.v` before this update. Those registrations are
isolated rather than assigning the new recorder an unjustified contract;
no additional checked body proof is suspended.

## Semantic Work Before Restoring the Main Proof

The current C++ spec imports `reservebalold.v`. Its boolean-equivalence
postcondition does not include main's explicit staking-address exemption or
its current-incarnation/init-selfdestruct exemption. The newer model has
exemption machinery, but a connection to the C++ State flags is still needed;
changing the import alone is not a proof.

The top-level `updates_stricter` postcondition already permits exact balance
reads. The restored lambda's postcondition now records that exact update.
Audit the remaining balance-read and tracing specs, including tracer resources,
rather than reuse a stale contract.

Resolve the separate [NULL_HASH mismatch](reserve-null-hash.md) before making
a production correctness claim. Keep the remaining
[optional-layout migration](optional-layout.md) visible; suspending clients
does not prove their representations correct.

## Not Covered by This Exception

- Separately, on 2026-09-07 the user authorized suspending the unfinished
  `try_fix_account_mismatch_proof.v` body and its local spec registration
  before taking the pre-update backup. Its checked helpers remain imported.
  See the [diagnosis](../monadproofs/brickmisc/issues/incarnation-callability.md).
  Main also lacks the local overflow-rejection branch; restoration must check
  the production body, not reinstate that local C++ change.
- MIP-8 body proofs and their combined theorems must remain in the checked
  import closure. Do not replace their proved helper specs with assumptions.
- The cached `ReserveBalance` methods do not acquire body proofs merely by
  updating their C++ source.

## Completion Checks

Production-code checkpoint: `810c815d2`. The source directories, upstream root
files, and submodule pins match the public SHA above exactly. The full C++
build and all six `cpp2v` invocations succeeded. The proof-only `inc_bytes.cpp`
Dune rule needed the newly included `category/crypto` header tree as a
dependency; no production-code workaround was made.

Main also replaces storage-page RLE with ascending `(index, compact value)`
pairs. Its encoder walks the bitmap and the new `values()` span. Encoder and
decoder proofs must be ported to that exact format, preserving round-trip,
canonicality, exact errors, and success-view exhaustion. They are not covered
by the suspension. The `page_commit` body is unchanged.

The new format's round-trip and canonicality proofs and both codec C++ bodies
now check. The encoder's bit-clearing correspondence is proved without
assumptions. On 2026-09-08 the user authorized reusing the existing
`std_countr_zero_ulong_spec` and adding the generic span indexing contract to
the encoder's library interface. The latter owns the concrete span fields,
requires an in-bounds index and a typed backing range, and returns only the
element address. Clients retain their separate element ownership.

The encoder combiner in `7271362b8` discharges `lowest_offset` and
`storage_page_t::size`; the encoder body checks `values()` and `bitmap()`
inline. It also drops the bytes32/assertion assumptions used only by the old
encoder. Compact RLP remains the existing boundary outside the storage-page
files. No new semantic axiom was introduced. The unsupported runtime forms
matter for proving the standard-library bodies, not for using the explicit
library contracts; see the
[runtime-form diagnosis](../monadproofs/brickmisc/issues/stdlib-runtime-forms.md).

On 2026-09-08 the complete `updateMonadCoqAsts.py linux` command returned
success, including C++ compilation and Dune's AST build. An earlier
`dune build monad/monadproofs/proofs/all.vo` failed only at the encoder's
still-open span obligation. The decoder body, lowest-offset helper, and
bitmap-step lemmas have compiled. The unchanged merge proof also rebuilt
successfully; its import has not been removed.

Final validation on 2026-09-08: `dune build monad/monadproofs/proofs/all.vo`
returned exit status 0, including fresh builds of `merge_scratch_level`,
`init_leaf_scratch`, both codec bodies, and the storage-page combiner.
The central `all.v` also checked to EOF through Emacs/Proof General.
No additional body proofs were suspended. Production sources still match the
pinned main commit; generated ASTs remain untracked.

- Preserve `issues/` in the code-sync script; upstream does not contain it.
- Record the target SHA and verify the code-side diff against it, including
  `reserve_balance.cpp` and `storage_page.cpp/.hpp`. No proof-motivated C++ edits.
- Build C++ and regenerate ASTs with `updateMonadCoqAsts.py linux`; generated
  ASTs remain outside Git.
- Check `monadproofs/proofs/all.vo` for the retained proof set. An authorized
  suspension is not a successful proof of the suspended functions.
- For restored proofs, compare old/new live Emacs states at each substantial
  breakage instead of rediscovering the proof. Recheck combined-theorem
  assumptions and restore imports before marking this issue resolved.
