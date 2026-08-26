# Separation bounds: rootBound done, sepPrec deferred

## Accomplished

- New `HexRealRootsMathlib/Separation.lean` (sorry-free), added to the
  umbrella. Proves `rootBound_bounds_roots`: for `toPolyℝ p ≠ 0`, every
  real root `r` satisfies `|r| < Dyadic.toReal (Hex.rootBound p)`. Route:
  Cauchy's bound `Polynomial.IsRoot.norm_lt_cauchyBound`, then
  `cauchyBound_le_rootBound` shows the power-of-two rounding dominates the
  Mathlib `cauchyBound` (an `NNReal` `sup/lc + 1`) by bridging the
  coefficient sup to the executable `foldl max` and using the ceiling-log
  characterisation `le_two_pow_ceilLog2Nat : m ≤ 2 ^ ceilLog2Nat m`.
- Supporting sorry-free lemmas: `toRat_shiftLeft`, `toReal_ofInt`,
  `toReal_twoPow` (dyadic `2^k` cast), `range_foldl_max_eq_finset_sup`,
  `natDegree_toPolyℝ`, `coeff_toPolyℝ`; the `toPolyℂ` cast abbrev for the
  follow-up.
- `HexRealRoots/Prec.lean`: added `@[expose]` to `twoPow`, `ceilLog2Nat`,
  `rootBound`, `sepPrec` (needed so the Mathlib layer can unfold them), plus
  three defining-equation lemmas `rootBound_of_degree?_{none,zero,pos}`
  (the executable-layer pattern, since the `some 0`/`some d` overlap does
  not reduce by `rfl` cross-module). Executable library still builds; dag
  check green.
- Added an explicit `toPolyℝ p ≠ 0` hypothesis to `rootBound_bounds_roots`:
  the SPEC statement is false for `p = 0` (`toPolyℝ 0 = 0` has every real as
  a root while `rootBound = 1`). This is the honest correction.

## Current frontier

`sepPrec_separates` (the Mahler root-separation bound) is NOT done. It is
the project's hardest remaining assembly and does not close in one session.

## Next step

Build the classical Mahler bound over `Polynomial ℂ` (upstreamable, Hex-free):
1. Discriminant absolute-value corollary: from `Polynomial.discr_eq_prod_roots`
   (Discr.lean) derive `‖discr f‖ = ‖lc‖^(2n-2) · ∏_{i<j} ‖αᵢ-αⱼ‖²` for a
   nodup enumeration of the roots (Multiset→Fin glue; flagged as the needed
   glue).
2. `Matrix.det_vandermonde` gives `|det V| = ∏_{i<j}‖αᵢ-αⱼ‖`, so
   `|det V|² = ‖discr f‖ / ‖lc‖^(2n-2)`.
3. Mahler's isolating-column trick + `Matrix.norm_det_le_prod_norm_column`
   (Hadamard.lean) to expose one factor `‖z₁-z₂‖`, with column sums bounded
   via `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`.
4. Landau (`HexPolyZMathlib.mahlerMeasure_le_l2norm`) +
   `l2norm_toPolynomial_sq_le_coeffNormSq` +
   `HexPolyZ.coeffL2NormBound_sq_le_two_mul_coeffNormSq` to reach the
   `sepPrec` closed form; the ceiling-log lemma `le_two_pow_ceilLog2Nat` is
   already available for the numeric rounding chain.
Bridge `SquareFreeRat p` to the `Separable` hypothesis `one_le_abs_discr`
wants: no bridge exists yet, so add an explicit
`((toPolynomial p).map (Int.castRingHom ℚ)).Separable` hypothesis and note
`squareFreeRat_iff` (upcoming ChainCorrespond work) discharges it.

## Blockers

None mechanical; sepPrec is pure scope (large hard analysis).
