# hex-min-poly-mathlib

`hex-min-poly-mathlib` is the proof-only correspondence layer between the
Mathlib-free executable API in `hex-min-poly` and Mathlib's matrix and
polynomial theory. It adds no competing computational implementation.

## Correspondence

For a field `F` with decidable equality, `equiv_minPoly` proves

```lean
equiv (Hex.Matrix.minPoly A) = minpoly F (matrixEquiv A).
```

`vectorEquiv_evalVec` identifies executable Horner evaluation on a vector
with Mathlib `aeval` followed by `mulVec`. Consequently,
`vecMinPoly_dvd_iff` says that the converted vector order divides a Mathlib
polynomial exactly when that polynomial annihilates the converted vector.
`equiv_lcm` identifies `Hex.DensePoly.lcm` with Mathlib's normalized LCM.

## Consequences

The bridge proves that the executable minimal polynomial:

- divides the executable characteristic polynomial;
- has degree at most the matrix dimension;
- is invariant under transposition;
- is invariant under conjugation by a unit, hence under similarity.

The characteristic-polynomial consequences depend on
`hex-char-poly-mathlib`. All executable work, certificates, conformance, and
performance evidence belong to `hex-min-poly`.

## Performance classification

This is a correspondence-only Mathlib layer. It owns no compiled operation,
elaborator, tactic, or proof-search procedure, so it has no benchmark track
and no external comparator. The computational performance owner is
`hex-min-poly`.
