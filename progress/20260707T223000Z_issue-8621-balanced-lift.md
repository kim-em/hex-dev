# issue-8621: balanced product-tree multifactor Hensel lift

## Accomplished
- Reshaped `Hex.ZPoly.multifactorLiftQuadraticList` (HexHensel/QuadraticMultifactor.lean)
  from a sequential O(n·r) peel into a balanced product tree (split factor list
  at length/2, lift prod(L) vs prod(R) via `henselLiftQuadratic`, recurse,
  concatenate L-then-R). Well-founded on list length.
- Redefined `QuadraticMultifactorLiftInvariant` and
  `QuadraticMultifactorCoprimeSplits` on the same balanced recursion.
- Reproved all 4 public consumers (`multifactorLiftQuadratic_spec`,
  `_size_eq_input`, `_each_congr_mod_base`, `_each_monic`) via the generated
  `.induct` principle, plus the producer
  `quadraticMultifactorLiftInvariant_of_factorsModP`. NO Hensel-uniqueness
  needed there. Added helpers: `monic_mul`, `monic_polyProduct_toArray`,
  `polyProduct_map_liftToZ_append`, `congr_getD_append`, `length_take_add_drop`.
- All public theorem STATEMENTS byte-identical. `HexHensel` and
  `HexBerlekampZassenhaus` build green.

## Current frontier
- `lake build HexBerlekampZassenhausMathlib` fails only in
  `HexHenselMathlib/Correctness.lean` at two UNUSED-but-gating cross-check
  theorems lock-step-coupled to the old sequential shape:
  `multifactorLift_eq_multifactorLiftQuadratic` (+ worker
  `multifactorLiftList_map_eq_quadratic`) and the dead invariant bridge
  `quadraticMultifactorLiftInvariant_of_multifactorLiftInvariant(_congr)`.
- Also pending: HenselFactorProps discharger
  `quadraticMultifactorCoprimeSplits_of_factorProduct_no_squared` (balanced
  coprime-splits, reuse gcd²∣X squarefree argument, split-agnostic).

## Next step
- Reprove the invariant bridge: linear invariant → balanced quadratic invariant,
  deriving prod(L)-vs-prod(R) coprimality via FpPoly CommonDvdOne
  (`gcd_eq_one_of_monic_of_common_dvd_one`, `coprime_mul_of_coprime_both`) +
  normalizedXGCD scale-to-1.
- Reprove the agreement via a generation-agnostic `output_map_eq_linear`
  (lock-step on linear, balanced output abstract; feed balanced specs).
- Reprove the discharger for balanced coprime-splits.

## Blockers
- None hard; main risk is Mathlib/FpPoly coprimality friction in the bridge.
