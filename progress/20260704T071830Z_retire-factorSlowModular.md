# Retire the exhaustive factorSlowModular tier (#8581)

## Accomplished
Part 4 of the BZ factor-path cleanup. Deleted the executable exhaustive
modular recombination tier and its core from
`HexBerlekampZassenhaus/Basic.lean`:

- `exhaustiveCoreFactorsWithBound` and the `exhaustiveMonicCoreGuardPrimeData?`
  guard + its `#guard`.
- `exhaustiveSlowRawFactorsWithBound?` + `exhaustiveSlowRawFactorsWithBound?_eq_some`
  + `exhaustiveSlowRawFactorsWithBound_mem_normalization_or_core`.
- `factorSlowModularFactorsWithBound` (+ `#guard`, `_branch` theorem),
  `factorSlowModularWithBound`, `factorSlowModular`, and the
  `factorSlowModular_eq_factorSlowModularWithBound_default` simp lemma.
- The dead modular-first wrapper `factorSlowFactorsWithBound` (no consumers).
- The `exhaustiveCoreFactorsWithBound_*` Basic proof family:
  `_normalizeFactorSign`, `_shouldRecord`, `_primitive`, `_product`, `_monic`,
  `_degree_pos`, `_degree_pos_of_primitive_pos_lc_core`.
- The f-level product lemmas: `factorSlowModularFactorsWithBound_polyProduct_of_some`,
  `factorSlowModular_product_of_all_recorded_normalized`,
  `factorSlowModular_product_of_{constant,quadratic,exhaustive}_branch`,
  `factorSlowModularWithBound_product_of_some`.
- Removed / reworded every surviving docstring/comment reference so the grep is
  clean; converted the two `factorSlowModular`-referencing `#guard`s that fed
  KEPT fixtures (`nonMonicCubicRegression`, `exhaustiveNonMonicQuadraticGuard`)
  to `factor` / `factorSlowTrial` coverage.

Kept the two generic `polyProduct` helpers
(`leadingCoeff_polyProduct_toArray_pos`,
`polyProduct_toArray_monic_factors_monic_of_pos_lc`) since they are reusable and
not tier-named.

Conformance: substituted the three `factorSlowModular` product/coeff-set guards
(quadSqrt2Sqrt3, swinnertonDyerSD3, phi15) with `factorClassicalNoDecline` on the
same fixtures, preserving the same assertion shape and updating comments to
describe size-ordered full classical recombination. Updated the coverage
docstring.

## Current frontier
Whole-graph `lake build` (incl. `HexConformance` and bench exes) green; grep for
`factorSlowModular` / `exhaustiveCoreFactorsWithBound` clean across the tree
(progress/reports/status exempt); the trial tier
`exhaustiveIntegerTrialCoreFactorsWithBound*`, classical tier, and headline
`factor`/`factorHybrid*` intact.

## Next step
Publish sync will mirror the pruned Basic/Conformance to the released
`hex-berlekamp-zassenhaus` repo on the next release run.

## Blockers
None.
