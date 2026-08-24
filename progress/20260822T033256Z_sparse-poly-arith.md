# hex-sparse-poly: arithmetic (milestone 2)

## Accomplished

- `HexSparsePoly/Arith.lean`: the generic sorted-merge combinator
  `mergeWith` with its canonicality and coefficient lemmas, the generic
  filtered coefficient map `mapTerms` likewise, and on top of them
  `add`/`sub` (linear merges), `neg`, `scale`, `mulMonomial`, `mul` as
  the SPEC's pairwise-product specification through `ofTerms`, binary
  `pow`, and the `Add`/`Sub`/`Neg`/`Mul`/`Pow`/`Dvd` instances.
- Coefficient laws in the house two-tier shape: raw forms under explicit
  pointwise hypotheses (`coeff_add'`, `coeff_sub'`, `coeff_neg'`,
  `coeff_scale'`, `coeff_mulMonomial'`) plus `Lean.Grind.Semiring`/
  `Ring` wrappers, all proved.
- Additive ring laws (`add_comm`, `add_assoc`, `add_zero`, `zero_add`)
  proved via `ext_coeff` + `grind`.

## Current frontier

The multiplicative laws (`mul_assoc`, `mul_one`, `one_mul`, `mul_zero`,
`zero_mul`, both distributivities, `mul_comm`) are stated with `sorry`,
deliberately: the SPEC proves `coeff_mul` by transport through
`toDense_mul` in milestone 3, and these follow from it. Eight sorries,
all in `Arith.lean` §Laws.

## Next step

Milestone 3 (`HexSparsePoly/Dense.lean`): the conversions, homomorphism
laws, round trips, then discharge the eight multiplicative-law sorries
by transport.

## Blockers

None.
