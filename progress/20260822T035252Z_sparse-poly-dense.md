# hex-sparse-poly: dense conversions (milestone 3)

## Accomplished

- `HexSparsePoly/Dense.lean`: `coeffsOfTerms` (indexed writes, last write
  wins, matching the SPEC's negative-case semantics), `termsOfCoeffsList`
  / `termsOfCoeffs`, `toDense` via `DensePoly.ofCoeffs`, `ofDense` as the
  list-walk specification with the `termsOfCoeffsArray` pass behind a
  proved `@[csimp]` equality.
- `coeff_toDense` / `coeff_ofDense`, both array-level round trips
  (`terms_coeffs` under `SparsePolyCanonical`, `coeffs_terms` under
  `DensePolyNormalized`), both bundled round trips, `toDense_inj`.
- Homomorphism laws both directions (`zero`, `one`, `monomial`, `add`,
  `neg`, `mul`), with `toDense_mul` proved by decomposing the pairwise
  product into a fold of `mulMonomial`s (`mul_eq_foldl`) and matching it
  against a fold of dense monomial multiples.
- `coeff_mul` by transport, and the eight multiplicative ring laws
  (moved here from `Arith.lean`, since their SPEC-prescribed transport
  proofs need this layer; they hold at `Lean.Grind.CommRing`, which is
  where the dense side proves them).
- Degree-boundary transport: `degree?_toDense`, `leadingCoeff_toDense`,
  sparse `Monic`, `monic_toDense`.

Zero `sorry` across the whole library.

## Current frontier

Milestones 1–3 of the SPEC are done and fully proved.

## Next step

Milestone 4 (`HexSparsePoly/Eval.lean`): gap-Horner `eval`, `derivative`
with the positive-characteristic zero filter, `substPow`, `substScale`,
`compose`, and the dense agreement theorems.

## Blockers

None.
