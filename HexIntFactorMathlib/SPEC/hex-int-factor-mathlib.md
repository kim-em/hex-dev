# hex-int-factor-mathlib (depends on hex-int-factor + hex-primality-mathlib + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owner: `HexIntFactor`

Computational performance owner: `HexIntFactor`

The public surface consists only of theorems transporting checked
factorizations, divisor functions, squarefree decomposition, and multiplicative
order to Mathlib's representations. It owns no executable search, checker,
reifier, tactic, elaborator, conformance target, compiled benchmark, or proof
probe. The normal-form expressions in theorem statements are not separately
advertised executable operations.

## Scope

`Factorization.lean` identifies the canonical checked prime-power list with
`Nat.factorization`, `Nat.primeFactorsList`, `Nat.divisors`, `Nat.totient`, and
the corresponding squarefree data. `Order.lean` identifies the Mathlib-free
`Hex.Nat.orderOf` with the order of a natural cast and of the associated unit
in `ZMod`.

The computational owner measures certificate replay, factor search, divisor
functions, and order search. The prerequisite `HexPrimalityMathlib` separately
owns its executable primality elaboration surface and is therefore not covered
by this classification.

## External comparators

No external comparator is required for this layer.

**Justification:** `correspondence-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. The transported algorithms are
implemented and compared by `HexIntFactor`; this layer adds proofs of agreement,
not a competing runtime surface.
