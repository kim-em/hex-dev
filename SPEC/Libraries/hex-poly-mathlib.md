# hex-poly-mathlib (depends on hex-poly + Mathlib)

Proves the ring equivalence between `DensePoly R` and Mathlib's
`Polynomial R`:

```lean
def equiv [CommRing R] [DecidableEq R] : DensePoly R ≃+* Polynomial R
```

Also proves GCD/ExtGCD correspondence with Mathlib's `Polynomial.gcd`.

## External comparators

No external comparator is required.

**Justification:** `mathlib-bridge` per
`SPEC/benchmarking.md §"Comparator naming"`. HexPolyMathlib is the
bridge from `Hex.DensePoly` to `Mathlib.Polynomial`; the relevant
comparison surface is the within-Lean `compare` group registering
Hex bridge targets against Mathlib's native polynomial-arithmetic
targets, per
`SPEC/benchmarking.md §"Within-Lean comparisons"`. Those
within-Lean compare groups exercise the same operations on
matched inputs and verify hash agreement; that is the relevant
shape of comparison for a Mathlib bridge. External tools (FLINT
etc.) would compare against the underlying polynomial arithmetic,
which is HexPoly's surface and is covered there.
