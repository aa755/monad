# By-Value Calls With an Unsupported Bitfield Type

## Status

The body proof of `monad::State::try_fix_account_mismatch` is suspended because
the call rule requires a complete declaration of `monad::Incarnation`, which
cpp2v marks unsupported due to its bitfields. See
[BRiCk #307](https://github.com/SkyLabsAI/BRiCk/issues/307).

[The proof file](../../proofs/execproofs/try_fix_account_mismatch_proof.v) remains
imported by [all.v](../../proofs/all.v) for its checked helper lemmas. The
unfinished body theorem and its local spec registration are commented out;
building `all.vo` does not establish correctness of this method.

## Failing Check

Auto commit `7270cc47560715057725186b93542537556c9496` replaces the admitted
`invoke.wp_operand_opcall_invoke` with a proof and adds this premise:

```coq
SolveCallableType (types tu) fty
```

For the failing call, `fty` is:

```coq
"bool(monad::Incarnation, monad::Incarnation)"%cpp_type
```

The generated `state_cpp.v` represents `monad::Incarnation` with a
`Dunsupported` declaration and the message `"bitfields are not supported"`.
At the failure point, the following query returned `false`:

```coq
Eval vm_compute in
  (callable_type.callable_type_bool (types state_cpp.source)
    "bool(monad::Incarnation, monad::Incarnation)"%cpp_type).
(* = false : bool *)
```

The check requires complete return and by-value argument types in the
translation unit. An opaque `IncarnationR` with a `type_ptr` observation does
not fill in that translation unit's missing class definition. Its observation
describes an object in the runtime `genv`, not a complete declaration in
`state_cpp.source`.

## Before and After the Upgrade

The old and upgraded proofs were checked interactively at the same `go`
immediately before `iExists original_ac`.

- Old auto (`a1f5a709`): `go` advances through the operator call to an
  existential `acct : AccountM`; `iExists original_ac` then succeeds.
- Upgraded auto (`eb03a710`): `go` leaves the `wp_operand` of
  `monad::operator==(monad::Incarnation, monad::Incarnation)`. The following
  existential tactic therefore has the wrong goal shape.

Comparing `Check invoke.wp_operand_opcall_invoke` and the rule's source
confirmed that the old admitted rule lacked the completeness premise. The
new obligation explains the failure without a change to the account invariant.

## Required Resolution

Restoring the theorem requires resolving the callability issue and porting to
the current production body. Assuming the failed completeness check or
reinstating the old admitted rule would not resolve the missing justification.

Two possible resolutions need investigation:

1. Support the necessary bitfield class/ABI information in cpp2v/BRiCk.
2. Prove a generic alternative call rule using the runtime type environment
   and the callee specification, without requiring completeness in this
   partial translation unit. The lower-level `wp_operand_operator_call` and
   `wp_fptr_cptrR_C` rules are relevant, but they do not by themselves restore
   the existing unmaterialized-call proof state. Such an adapter would need a
   separate proof; it is not an available workaround established by this note.

`wp_operand_mono` alone is not such an adapter: it transports a proof from a
smaller translation unit to a larger one, not a runtime-environment proof back
to the partial source unit.
