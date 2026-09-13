# BRiCk Proof Support and Reproductions

This directory collects upstream-facing work arising from Monad C++ proofs.
It is not a copy of BRiCk, and placement here does not imply upstream acceptance.

- [issues/](issues/): diagnoses and unresolved requirements involving BRiCk
  or auto. Monad-specific model and proof-port issues remain in
  [monadproofs/issues/](../issues/).
- [minimalexamples/](minimalexamples/): small C++ programs and their proof
  attempts or regression tests. `deconst/` covers const-pointer array
  initialization; `hetero/` covers mixed-type compound arithmetic;
  `byte_views/` covers scalar, direct-member struct, and inherited-member
  byte writes. Unfinished attempts use `Abort`; conditional theorems state
  the missing premises explicitly.
- [upstream/](upstream/): reusable proved lemmas proposed for upstreaming.
  [scalar_bytes.v](upstream/scalar_bytes.v) supplies scalar and array byte-view
  lemmas used by the application through `proofs/libspecs/brick_upstream.v`.
  It adds no local conversion axiom; it depends on BRiCk's existing theory.

All Rocq files here are reachable from [proofs/all.v](../proofs/all.v).
From the composed FV workspace root, check them together with their clients:

```sh
dune build monad/monadproofs/proofs/all.vo
```
