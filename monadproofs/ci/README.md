# Rocq proof CI

`rocq/proofs` checks the C++ and `monadproofs/` sources from the same commit.
The private controller builds C++, regenerates the six main cpp2v ASTs, then
builds `monad/monadproofs/proofs/all.vo` in its pinned FV workspace. It replaces
the complete proof directory; deleted or missing proofs cannot fall back to
a copy in the checker image. Generated ASTs are build outputs, not PR inputs.

GitHub receives only `success` or `failure`, without logs, diagnostics, source
excerpts, artifacts, or a build URL. GitHub's commit, publisher, and timing
metadata remain visible. There is no public GitHub Actions runner attached
to the private machine.

## Updating code and proofs

Put C++ changes and the necessary `.v` proof changes in the same PR. The
controller reads committed Git blobs, not a developer's working tree. A
proof-only change also triggers verification. It does not require rebuilding
the checker image unless the private toolchain or reviewed build policy changes.

The pilot accepts ordinary C/C++ changes under `category/`, plus proof sources
and documentation under `monadproofs/`.
Build configuration, proof-suite import lists (`all.v`), and compiler-input
fixtures are pinned in a private, reviewed manifest. Changing those files or
removing a required proof file needs an operator policy update. Executable
scripts, plugins, symlinks, and precompiled proof artifacts are not accepted as
candidate proof inputs. Production build/dependency changes also need review.

Only authors selected by the pinned [policy](policy.json) run
jobs. Editing that policy in a PR does not change the controller's authority.
Proof checking executes tactics, so accepting arbitrary untrusted authors
would require a separate security review. The private harness, licensed
automation, credentials, logs, images, and cache are not distributed here.

Jobs run serially and share a private, persistent, multi-version Dune cache.
Reuse depends on all tracked build inputs, including imported theories and
generated C++ ASTs, not just the edited `.v` file. A fresh build can take more
than 30 minutes.

## Merge protection

The check applies to the exact PR head SHA, not a synthetic merge. `main`
requires `rocq/proofs` and an up-to-date PR branch, including for administrators.
If `main` advances after a successful run, the old status remains green but
the outdated PR cannot merge. Merge or rebase the new `main` into the PR and
wait for a successful check on the new head. The controller does not currently
implement GitHub's merge queue.

The reporter uses a personal token, so the required context is not bound to a
GitHub App identity. Do not give other users the reporting credential. A wider
rollout should consider an App with expected-source enforcement.

## What success establishes

The selected proof suite compiled against that commit's regenerated ASTs and
its own specifications, models, and existing assumptions. This is not proof
that every Monad function is verified, all assumptions are sound, or every
execution terminates. Review changes to specifications, models, axioms, and
proof coverage; compilation alone does not establish that a specification was
not weakened. This experimental branch deliberately narrows
[proofs/all.v](../proofs/all.v) to MIP-8, including encoding and decoding.
Its deletions and build-configuration changes require an explicit review of
the controller's private manifest; this branch does not update that manifest.

The original proof sources are distributed under the repository's license;
existing per-file notices remain applicable. Building additionally requires
the external BRiCk, automation, and library-spec theories in
the composed FV workspace. Publishing these clients does not redistribute or
grant rights to those dependencies.

References: [GitHub commit statuses](https://docs.github.com/en/rest/commits/statuses)
and [required checks](https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks).
