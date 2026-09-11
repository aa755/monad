# Rocq proof CI

`rocq/proofs` is an external commit-status check. A private controller selects an
exact commit, builds C++, regenerates the C++ ASTs, and checks the pinned Rocq
proof suite. GitHub receives only `success` or `failure`, with no diagnostic,
source excerpt, artifact, or build-log URL. GitHub's usual commit, status-author,
and timing metadata remain visible.

There is no self-hosted Actions runner attached to this public repository. PR
workflows cannot submit commands to the private controller. Its scripts, proof
sources, licensed dependencies, containers, and shared Dune cache stay private.

## Triggers and scope

[The policy](../.github/rocq-proof-ci.json) selects branch heads and PR base
branches. The controller pins a reviewed revision of this policy; editing it in
a PR does not change the controller's behavior. During the initial rollout,
only PRs by the listed authors execute builds. Other PRs receive `failure` until
the operator approves a policy change.

The check certifies the tested commit, not a synthetic merge with its base.
Rebase or update the PR when checking its combined effect with newer main.
All imported proofs must check; this does not verify every C++ function, remove
existing library assumptions, or establish termination of every program.

The current candidate policy accepts regular, non-executable C/C++ files under
`category/`. This policy file and this document are inert metadata, never build
commands. Other changes, including build rules or dependency revisions, require
a reviewed baseline/image update; until then they fail closed. A failure may
therefore mean a broken proof, unsupported change, or infrastructure failure.
Detailed diagnostics are available only to the private controller's operator.

## Activation

Pushing this branch alone does not start a private machine or configure GitHub
authentication. The operator must separately activate the prepared local service
with repository-scoped commit-status write permission. No controller credentials
belong in this repository or in Actions secrets.

After activation, the controller polls for new heads and publishes their result.
To make this mandatory for merging, require the `rocq/proofs` commit-status
context in the repository's branch rules. Missing results are not successful
checks. Use the designated status publisher when configuring the rule's expected
source; do not grant other users that credential.

GitHub supports this integration through its
[commit-status API](https://docs.github.com/en/rest/commits/statuses).
