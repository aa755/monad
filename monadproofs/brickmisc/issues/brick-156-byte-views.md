# BRiCk #156 Closure Audit

Issue: https://github.com/SkyLabsAI/BRiCk/issues/156

## Current Status (2026-09-07)

Still open. The workspace has since upgraded to BRiCk
`d6cb1e3c3dc4511c51d1f6efefb94aee665e373a` and auto
`eb03a7100cd00c1a51c6f3769f849124f3f5a0ea`. A source audit at Monad
`9523169d5` confirms that the scalar conversions below remain lemmas, while
`evmc_bytes32_array_byte_view_bridge` remains an axiom used by the application.
No `eval_o_base` rule was found in the active dependency sources.

The upgraded workspace initially stopped in
`try_fix_account_mismatch_proof.v` at the Incarnation operator-call
completeness obligation. The user subsequently authorized suspending that
unfinished theorem and its local spec registration, while retaining its
checked helper lemmas; the pre-code-update `all.vo` build now passes. See the
[live old/new proof-state diagnosis](incarnation-callability.md).
The assumption counts below remain historical, not a fresh assumption audit
of the current import closure. Repeat that audit after the code update.
The standalone inherited-byte-write
example itself was checked after the upgrade and
[posted on #156](https://github.com/SkyLabsAI/BRiCk/issues/156#issuecomment-5576065211).

## Completed Before the Dependency Upgrade

These checks used BRiCk `501d1ed2d7b38034f8ee3f4f132f2e82079954d9`
and auto `a1f5a709318e0de9946a3e106de7856d477b37e4`.

- `monadproofs/brickmisc/minimalexamples/byte_views/scalar_byte_write.v` proves a C++ byte write
  followed by an integer read using upstream object-representation rules.
- `monadproofs/brickmisc/minimalexamples/byte_views/struct_byte_write.v` proves a write into the
  second of two structs through a flat byte pointer, followed by a typed field
  read. The proof preserves the original struct witnesses across the write.
- Their fully qualified `Print Assumptions` outputs contain no `monad.*`
  axioms. They still depend on the existing upstream semantics and automation
  assumptions; this is not an audit certifying that upstream TCB.
- `little_endian_byte_arrayLR_to_unsigned_scalar_int_arrayR` now derives the
  application's scalar reconstruction rule from upstream rules. Its statement
  is unchanged; its fully qualified assumptions contain no `monad.*` axioms.
- The uninitialized-array conversion is now a lemma too:
  `unsigned_scalar_int_uninit_arrayLR_to_uchar_any_arrayLR`. It uses the
  enclosing array's `type_ptr`, `decode_uint_anyR`, and byte-pointer transport.
  The old signed-or-unsigned axiom was removed, not moved or renamed as an
  axiom. Every application uses unsigned 32-bit elements.
- The initialized scalar forward conversion is now proved as well:
  `unsigned_scalar_int_arrayR_to_little_endian_byte_arrayLR`. Both scalar
  directions use upstream byte decoding and pointer-congruence transport.
  The old `unsigned_scalar_int_arrayR_little_endian_byte_arrayLR` axiom is
  deleted. The forward lemma requires the enclosing array's `type_ptr`;
  reconstruction requires the saved native-cell `typed_sliceR`.
- `dune build monad/monadproofs/proofs/all.vo` succeeded from the workspace
  root before the dependency upgrade. The accompanying `dune rocq top`
  audit with `Set Printing Fully Qualified.` reported 11 `monad.*`
  assumptions for `page_commit_cpp_proof_ok`, down from
  12 before the initialized scalar replacement. The inherited-struct bridge
  listed below is the only remaining application byte-conversion axiom.
- Fully qualified `Print Assumptions` reports no `monad.*` axioms for
  `unsigned_scalar_int_arrayR_to_little_endian_byte_arrayLR` or
  `inherited_bytes_with_location`. The latter still has its explicit
  pointer-correspondence premise; this audit does not discharge that premise.
- `storage_get_leaf_iv.v`, `storage_blake3_seal.v`, and
  `init_leaf_scratch.v` checked to the end interactively. Their C++ body proof
  scripts are unchanged; only the initialization-resource handoff lemma in
  `init_leaf_scratch.v` needed adapting. No C++ code or dependency checkout
  changed, and no axiom was added. The explicit global-array typing
  preconditions added to the MIP-8 specs are described below.
- The earlier audit after the uninitialized-array replacement reported 12
  `monad.*` assumptions for `page_commit_cpp_proof_ok`, down from 13.
  `Print Assumptions unsigned_scalar_int_uninit_arrayLR_to_uchar_any_arrayLR`
  reported no `monad.*` assumptions. Both affected caller files checked to the end
  interactively with their existing proof scripts. No C++ code, C++ spec,
  combiner statement, or dependency checkout was changed in that earlier step.

## Remaining Application Obstacles

### Inherited Byte Field

`monadproofs/brickmisc/minimalexamples/byte_views/inherited_struct_byte_write.v` is a standalone
`cpp.prog` reproduction for posting upstream. It uses one derived object and
no Monad imports. It proves a reversible byte view and a byte-write/typed-read
function conditional only on the missing base-offset evaluation fact, while
preserving both struct witnesses. The unconditional C++ proof gets through
the cast but stops at the byte write: it owns the inherited field's byte,
not yet the corresponding flat-pointer byte. That proof state is documented
before `Abort`. The conditional proof reaches the same point and then
finishes using the offset fact as an explicit argument, not a new axiom.

Production `monad::bytes32_t` inherits its byte member from `evmc_bytes32`.
The new direct-member example does not cover that extra base-class offset.
`monadproofs/brickmisc/minimalexamples/byte_views/inherited_byte_offset.v` isolates the difference:

```cpp
struct Base { unsigned char bytes[2]; };
struct Word : Base {};
unsigned char inherited_byte_write(Word (&words)[2]) {
    auto p = reinterpret_cast<unsigned char *>(&words);
    p[2] = 7;
    return words[1].bytes[0];
}
```

The file proves `parent_offset CU "Word" "Base" = Some 0`. The corresponding
`eval_offset CU (o_base CU "Word" "Base") = Some 0` remains an explicitly
aborted diagnostic goal, not an axiom or a claimed C++ correctness theorem.

Interactive `Search` and source searches found:

- `eval_o_field`, `eval_o_sub`, and composition rules, but no `eval_offset`
  rule for `o_base`. The inverse base/derived-pointer rules do not supply the
  numeric layout fact needed by `ptr_cong`.
- `struct_to_raw` includes bases, but its abstract `raw_bytes_of_struct`
  relation has no introduction rules. Its `wf_base` rule gives only a byte-list
  length; its `offset` rule relates contents only for fields. Thus it does not
  currently provide an alternative derivation of the inherited byte contents
  and their reconstruction after a write.
- Pinning and numeric-address transport also require an evaluated offset;
  they do not fill this missing base-offset connection.

An appropriate base-offset rule, or additional introduction/base-content
theory for `raw_bytes_of_struct`, would let the application use the same
byte-transport approach. No such rule was added locally or to BRiCk.

The deeper ownership check is the proved conditional lemma
`inherited_bytes_with_location` in that diagnostic file. It retains both
`structR` witnesses and the inherited byte array's `type_ptr`, and proves
reversible conversion to bytes at the derived-object pointer. The only
location premise is:

```coq
ptr_cong CU
  (p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes") p
```

This is a premise of the lemma, not a newly declared axiom. The proof derives
all byte-typing obligations from the retained witnesses. Thus additional
ownership bookkeeping does solve the typing part, but does not establish
that these two offset expressions identify the same bytes. An `eval_o_base`
rule tied to the layout table would address that particular missing step;
an unrestricted numeric-address equality rule is neither needed nor proposed.
This identifies a gap in the public rules checked here, not a formal
independence proof that no alternative derivation can exist.

Redefining `bytes32R` to own flat bytes would not bypass that step: the
already-verified constructors and field accesses use the inherited field
pointer. They would then need the same correspondence in the opposite
direction. Likewise, preserving `type_ptr` for `flat_out[64]` supplies byte
typing for its whole output region, but does not identify those byte locations
with the inherited members. Neither change justifies assuming that identity.

### Flat-Array Typing

The proven forward flattening rule requires typing for the flat byte
destination. An enclosing array's `type_ptr` supplies this through
`type_ptr_raw_type_ptrs`. `arrayR` only records cell typing and endpoint
validity; `anyR_type_ptr_observe` explicitly excludes arrays too.

The interactive proof state before `memcpy(iv, IV, sizeof(iv))` in
`storage_get_leaf_iv.v` already contains:

```coq
type_ptr (Tarray Tuint 8) (_global storage_get_leaf_iv_static_iv_name)
```

It comes from initialization of the function-local static `iv[8]`. The
analogous witness for the stack `cv[8]` is present in `storage_blake3_seal.v`.
Consequently, their uninitialized destination conversions use the proved rule
without changing either C++ spec. No application proof script needs a new
assumption or a hand-written initialization step.

The source `IV` was different. The old
`Blake3ConstKeyWordsR` global-IV precondition only owns an `arrayR` of eight
integers. `denoteModule` supplies `init_validR` for a global variable, not
its whole-array `type_ptr`. The actual call-site state has only `valid_ptr`
for `_global "IV"`, in addition to that key representation.

The MIP-8 specs now explicitly carry
`type_ptr (Tarray Tuint 8) (_global "IV")`. It is passed through
`page_commit`, `compute_nonempty_subtree_root`, `init_leaves`, and
`blake3_seal`, and through `StorageLeafIvInitInputsR` on the first cache call.
This **strengthens those initialization preconditions**; it is not a proof of
the old, more general spec. Program initialization must supply the witness
for the actual declared `IV[8]`, together with the existing initialized-cell
ownership. The function proofs do not prove global initialization.

The generic BLAKE3 key representations and C++ specs are unchanged: a key
argument may still be an eight-word span within a larger allocation. Only
the known MIP-8 global and the byte-view lemmas need the enclosing-array
witness. No new axiom is used to produce it.

## Closure Gate

Do not close #156 just because the two direct examples check. The application
still uses this local conversion assumption:

- `monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_byte_bridges.evmc_bytes32_array_byte_view_bridge`

After replacing its uses, rebuild `monadproofs/proofs/all.vo` and repeat
fully qualified `Print Assumptions` on `page_commit_cpp_proof_ok`. Only then
publish the completed replacement proofs and close the issue.
