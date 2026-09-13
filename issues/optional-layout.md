# Optional Layout Limitations

## Status: Nontrivial Layouts Deferred

Source migration on 2026-09-07 removed `legacy_optionR` and all references to
it from the proof `.v` files. The two admitted offsets and the admitted legacy
type-pointer observer were removed too. Removing the legacy interface does
not resolve the nontrivial-layout mismatch documented below.

`proofs/libspecs/optional_specs.v` now separates an optional's structural
ownership (`spineR`) from ownership of its contained value (`optionR`). The
concrete spine currently models libstdc++'s trivial-special-members layout.
`optionR_layout` proves that the separation preserves the previous complete
representation. The `monad::uint256_t` optional specs use this representation.

## Client Representations

The deleted predicate owned only the outer struct witness, the engagement
flag, and an optional element at an admitted offset. Migration changes those
contracts to retain the spine; it does not assume an equivalence that could
manufacture the missing nested base and union resources.

- `monad::Account` clients in the imported reserve-balance proofs now retain
  the concrete optional spine while accessing the account. `AccountR` tracks
  `cQp.t`, and its const rule is proved from its fields' const rules. The
  already-abstract `IncarnationR` has an assumed const rule; the account and
  optional structural ownership is not axiomatized.
- `monad::Address` clients now use `optionR`, including the generic optional
  `BundledRep` instance and the sender proof's vector-element representation.
  The current `state_cpp.v` AST declares `_Optional_base<T, true, true>` and
  `_Optional_payload<T, true, true, true>` for Account and Address. The abstract
  `addressR` still takes `Qp`; the adapter matches the existing `monadaddr`
  bundled Rep by using `cQp.frac`. This does not supply a const-conversion law
  for the address object, and no such law was added by this migration.
- `BlockHeader::base_fee_per_gas` now uses the concrete `optionR` spine.
  The scalar `optionalPrimR` boundary now uses it too.
- `dbspecs.v` now uses `optionR` for `optional<vector<monad::Withdrawal>>`,
  temporarily reusing the existing trivial spine at the user's explicit
  request. This removes that legacy use but does not fix its layout:
  `state_cpp.v` declares
  `_Optional_base<vector<monad::Withdrawal>, false, false>` for it. The
  nontrivial-layout implementation is deferred, with the repair plan in the
  comment on `optional_specs.spineR`. Successful typechecking is not evidence
  that this representation matches the C++ object.
- Execution-result optionals in the old, non-imported execution proofs now
  refer to `optionR`. Their specialization still needs checking; replacing the
  name does not establish layout compatibility or restore those old proofs.
- Non-imported balance-mutator proof files now retain `spineR` instead of only
  the engagement flag and outer struct witness when accessing an Account.
  Their unrelated proof failures are outside this representation migration.

The main-branch update and retained-proof port completed on 2026-09-08.
Of the six reserve-balance files temporarily suspended during that update,
only the full `dipped_into_reserve` body proof remains suspended; the other
applicable proofs were restored or incorporated into their surviving callers.
This does not resolve the vector or execution-result layout limitations. See
[reserve-balance-main-port.md](reserve-balance-main-port.md).

Closure requires matching the actual nontrivial layouts and checking their
clients. The central `monadproofs/proofs/all.vo` builds, but it does not check
`dbspecs.v` or the old execution-result clients. The separate `Incarnation`
callability problem is no longer a blocker for that target: the affected
unfinished theorem and its spec registration remain explicitly suspended.
See [the diagnosis](../monadproofs/brickmisc/issues/incarnation-callability.md).

## Migration Validation (2026-09-07)

- The tracked `.v` files contain no remaining references to the legacy
  predicate or its two admitted offsets. No C++ files or proof imports were
  changed, and no axioms or admissions were added.
- Interactive checks passed `optional_specs.v`, `exec_specs.v`, the complete
  sender-prefix proof, and the changed Account helpers in the two historical
  balance-mutator proof files. This does not restore those mutators' old C++
  body proofs.
- `dune build monad/monadproofs/proofs/all.vo` finished with one failure:
  `try_fix_account_mismatch_proof.v:2883`, at the already-documented by-value
  `Incarnation` call. All 33 other direct imports of `all.v` build, including
  the complete MIP-8 entry point and storage-page combiners. The failed import
  was still enabled at that point, so this initial migration check did not
  complete. The subsequent suspension and successful build are recorded below.
- `dbspecs.v` is outside that import closure and cannot currently load its
  missing `monad.asts.trie_rodb` / `monad.asts.trie_db` dependencies. Its new
  withdrawals Rep expression was typechecked interactively in `exec_specs.v`;
  the whole file was not checked.

After that validation, the user authorized suspending the unfinished
`try_fix_account_mismatch` theorem and its unused local spec registration.
The pre-code-update `all.vo` build then passed. This removes that theorem from
the verified scope; it does not resolve the Incarnation callability issue.

## Method States

The current concrete empty state owns the union's active `_M_empty` member.
`reset()` destroys an engaged `_M_value` without necessarily reconstructing
`_M_empty`. Extend the *internal* empty-state representation before adding
reset specs; clients should continue to see only `None`.

The unused generic `opt_move_assign_spec` has been removed. The remaining
Address-specific move assignment requires full ownership of both objects and
preserves the source's engagement and value: Address's defaulted move copies
its scalar bytes. This specification does not generalize to arbitrary
move-only element types.

## Account Spec Repairs

`optional_account_arrow_spec` and `optional_account_arrow_const_spec` now
return only the contained Account pointer, preserving optional ownership.
The stale `reference_to "intx::uint<256u>"` assertion was removed.

`is_empty_spec` now owns an Account, rather than an optional at the same
address. It compares the code hash with the actual `NULL_HASH` bytes and
preserves readable ownership of that global. `is_dead_spec` passes the
same global resource to `is_empty`. Their body proofs are in
`execproofs/account_is_empty.v` and `execproofs/account_is_dead.v`.
