# MIP-8 Proof Sources (Pruning Experiment)

This branch retains the storage-page commitment, inclusion/exclusion, and
compact-RLP encoding/decoding models, their proofs, and the C++ storage-page
proofs and supporting specifications. It removes State/BlockState,
reserve-balance, optimistic-execution, and unrelated experimental material.
The full proof tree remains on `main`.

Start with [the commitment model](proofs/execproofs/mip8/commitment.v),
[the codec model](proofs/execproofs/mip8/storage_page_indexed_encoding.v), and
[the C++ linking theorems](proofs/execproofs/mip8/storage_page_cpp_proofs/all.v).
Those theorems retain their external-library premises and existing axioms;
this pruning does not discharge them or increase the scope of verification.

These sources build in the composed FV workspace. From its root, run:

```sh
dune build monad/monadproofs/proofs/all.vo
```

See [CI](ci/README.md) for PR checks. The live CI's pinned proof manifest must
be explicitly reviewed before it can accept this intentional coverage reduction.
