# hex-poly-mathlib (depends on hex-poly + Mathlib)

Proves the ring equivalence between `DensePoly R` and Mathlib's
`Polynomial R`:

```lean
def equiv [CommRing R] [DecidableEq R] : DensePoly R ≃+* Polynomial R
```

Also proves GCD/ExtGCD correspondence with Mathlib's `Polynomial.gcd`.

## External comparators

No external comparator is required.

**Justification:** HexPolyMathlib is the correspondence library from
`Hex.DensePoly` to `Mathlib.Polynomial`; the relevant
comparison surface is the within-Lean `compare` group registering
Hex conversion targets against Mathlib's native polynomial-arithmetic
targets, per
`SPEC/benchmarking.md §"Within-Lean comparisons"`. Those
within-Lean compare groups exercise the same operations on
matched inputs and verify hash agreement; that is the relevant
shape of comparison for a correspondence library. External tools (FLINT
etc.) would compare against the underlying polynomial arithmetic,
which is HexPoly's surface and is covered there.


## Polynomial literal adapter request

[The `min_poly` frontend](../../HexMinPolyMathlib/SPEC/hex-min-poly-mathlib.md#the-min_poly-tactic)
requires a closed Mathlib polynomial literal adapter: recognize a polynomial
in the supported field codec, expose ascending coefficients, and prove the
identification with their decoded polynomial. Reuse this layer's polynomial
equivalence and the field codecs requested against
[hex-matrix-mathlib](../../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#requests-from-structural-tactic-frontends).
The initial carrier is `ℚ`; prime residues are a later codec extension.
This is a requested shared adapter, not an existing API or an alternative
minimal-polynomial checker. Its elaboration cost belongs in the consuming
tactic's complete fresh-module probes.
