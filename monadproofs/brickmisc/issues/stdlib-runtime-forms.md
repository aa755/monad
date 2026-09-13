# Runtime Standard-Library Forms Missing from the Current Rules

Observed with BRiCk `d6cb1e3c3dc4511c51d1f6efefb94aee665e373a` and auto
`eb03a7100cd00c1a51c6f3769f849124f3f5a0ea`, while porting proofs to Monad
main `1d22498c5f6af83d375b504aa12bd5c815cf3545`.

No new semantic axiom was added. On 2026-09-08 the user authorized using
the existing `std_countr_zero_ulong_spec` and a generic `std::span::operator[]`
contract in the encoder's library interface. The span contract is in
[span_specs.v](../../proofs/libspecs/span_specs.v); it preserves the span's pointer and extent
ownership and returns an in-bounds element address. It does not supply element
ownership. Monad's `lowest_offset` body is proved using the bit-scan contract.
The missing runtime rules below matter for verifying the library bodies,
not for clients that explicitly assume these library contracts.

## `if consteval`

The smallest relevant C++ body is:

```cpp
constexpr bool is_constant_evaluated() noexcept {
    if consteval { return true; }
    else { return false; }
}
```

For a runtime call, the desired result is `false`. The generated statement is:

```coq
Sif_consteval
  (Sseq [Sreturn (Some (Ebool true))])
  (Sseq [Sreturn (Some (Ebool false))])
```

This is the exact body reached interactively when inlining the installed
libstdc++ `std::__is_constant_evaluated()` into `std::span::operator[]`.
The client owns the span's pointer and extent fields, its struct witnesses,
and the backing element array. It also has the proved in-bounds index. The
remaining goal is the statement WP for the expression above, not an element
ownership or bounds obligation.

In this libstdc++ configuration, the assertion is expanded as:

```cpp
if (std::__is_constant_evaluated() && !bool(index < size()))
    std::__glibcxx_assert_fail();
```

Consequently, proving `index < size()` does not avoid the call: the left side
of `&&` is evaluated first.

Interactive `Search Sif_consteval.` returns the syntax induction principles,
not an execution rule. Text searches of BRiCk's logic and auto's hints also
find no execution rule. `lang/cpp/syntax/supported.v` explicitly classifies
the statement as unsupported. The existing ordinary-if rules do not apply to
this distinct AST constructor.

A generic runtime rule selecting the else statement would address this
case. Alternatively, clients can use a standard-library accessor contract;
that changes the library assumptions, not the C++ body. Either choice must
be explicit. The production source must not be changed to dodge this case.

## `__builtin_ctzg`

The current libstdc++ instantiation of `std::countr_zero<unsigned long>`
delegates to `std::__countr_zero<unsigned long>`, whose relevant operation is:

```cpp
return __builtin_ctzg(x, digits);
```

The zero fallback `digits` is the integer type's width. This differs from
the older one-argument builtins, whose zero input is undefined. The AST also
reads `__gnu_cxx::__int_traits<unsigned long>::__digits` as a global.

BRiCk provides `wp_ctz`, `wp_ctzl`, and `wp_ctzll`, and auto registers the
corresponding hints. Their conclusions mention different builtin names and
one argument; they do not establish the WP for this two-argument builtin.
No `__builtin_ctzg` rule occurs in the currently vendored BRiCk/auto theories.

Monad's existing `std_countr_zero_ulong_spec` is already a library assumption
of the page-commit proof. Reusing it for the updated encoder adds a callee
spec to the encoder's previous external interface, not a new axiom.
Proving the library function instead would require addressing
the new builtin and the width-global resource.
