# Two-circle campaign, tc1: Möbius correspondence layer

## Accomplished

New `HexRealRootsMathlib/MobiusCorrespond.lean` (sorry-free), connecting the
executable `Hex.mobiusTransform`/`Hex.descartesVar` to abstract `Polynomial`
machinery:

- **Abstract transform** `mobiusPoly n a b P :=
  (reflect n ((P.comp (X + C b)).comp (C (a-b) * X))).comp (X + C 1)` over a
  `CommRing`, with `mobiusInner` (the pre-reflection stage) split out.
- Multiplicativity (`mobiusPoly_mul` via `reflect_mul`), power form
  (`mobiusPoly_pow`), constants (`mobiusPoly_C`/`_one`).
- Field eval identity `mobiusPoly_eval`:
  `eval z = (1+z)^n * P.eval ((a+b*z)/(1+z))` for `1+z ≠ 0`.
- Value at `-1` (`mobiusPoly_eval_neg_one`, `_leading`) giving nonvanishing
  `mobiusPoly_ne_zero` (exact degree) and `mobiusPoly_ne_zero_of_ne`
  (degree-free, injectivity chain).
- Linear values `mobiusPoly_X_sub_C` (interior root `w ↦ (w-a)/(b-w)`) and
  `mobiusPoly_X_sub_C_upper` (`X - C b ↦ C (a-b)`).
- `rootMultiplicity_mobiusPoly` (field, `a ≠ b`, `w ≠ b`),
  `pos_root_mobiusPoly_iff` (ℝ, open-interval bijection),
  `countP_roots_mobiusPoly` (ℝ multiset count via `Finset.sum_nbij'`),
  `roots_mobiusPoly` (ℂ: roots = image of `roots.filter (· ≠ b)`, by
  root-peeling induction with FTA).
- **Descartes bridge** `descartesVar_eq_signVariations`: `Hex.descartesVar q =
  Polynomial.signVariations (toPolyℝ q)` (total, `q = 0` included). Route:
  Hex.signVar → Sturm.signVariations (`ChainCorrespond.signVar_eq`), reversal
  invariance (`signVariations_reverse`), then an adjacent-count ↔
  `destutter'`-length induction (`countSignChanges_destutter'`) to Mathlib's
  destutter-based `Polynomial.signVariations` on the descending `coeffList`.
- **Executable bridge** `toPolyℝ_mobiusTransform`:
  `toPolyℝ (mobiusTransform p I) = C (2^(s·n)) * mobiusPoly n a b (toPolyℝ p)`
  with `(α, β, s)` from public mirrors `numExp`/`endpoints`/`mobiusSteps` of
  the private executable helpers, identified by `rfl` after endpoint
  constructor case-split. Per-stage lemmas: `toPolyℝ_compose` (new generic
  `HexPolyMathlib.toPolynomial_compose` in `HexPolyMathlib/Basic.lean`),
  `toPolyℝ_dilate`, clearing (`toPolyℝ_cleared`), reversal-at-n
  (`toPolyℝ_reversed` = `reflect n`), stage algebra (`inner_stages`).
  Existential positive-factor form `toPolyℝ_mobiusTransform'`.
- **Composed corollary** `descartesVar_mobiusTransform`:
  `descartesVar (mobiusTransform p I) = signVariations (mobiusPoly n a b
  (toPolyℝ p))` via `signVariations_C_mul`.
- Sanity examples match the `(x-1, (0,2])` fixture from `HexRealRoots.Mobius`.

## Current frontier

`lake build` full-tree verification in flight at commit time; module and
`HexRealRootsMathlib` targets build clean (no warnings in the new files).

## Next step

tc2-parity/tc3-sector/tc4-region consume `mobiusPoly_eval`,
`countP_roots_mobiusPoly`, `roots_mobiusPoly`, and
`descartesVar_mobiusTransform`; umbrella-import conflicts with their PRs are
resolved by the orchestrator.

## Blockers

None.
