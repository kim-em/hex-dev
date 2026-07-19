# hex-poly-z-mathlib (depends on hex-poly-z + hex-poly-mathlib + Mathlib)

Proves `DensePoly Int ≃+* Polynomial ℤ`, the Mignotte bound, and the
Mathlib-side analytic polynomial inequalities over `Polynomial ℂ` that
downstream integer-polynomial factorization needs.

**Mignotte bound — proof strategy.**

Statement (needs `hf : f ≠ 0`; false otherwise since every polynomial
divides 0):

```lean
theorem mignotte_bound (f g : Polynomial ℤ) (hf : f ≠ 0) (hg : g ∣ f) (j : ℕ) :
    (Int.natAbs (g.coeff j) : ℝ) ≤ Nat.choose g.natDegree j * l2norm f
```

where `l2norm f := Real.sqrt (∑ i in f.support, (f.coeff i : ℝ) ^ 2)`.
The core theorem is over `ℝ` (matching Mathlib's Mahler measure API).
An integer-facing corollary can extract `|g.coeff j| ≤ ⌊...⌋₊` if
needed by downstream code.

**Mathlib API.** All heavy analysis is in
`Mathlib.Analysis.Polynomial.MahlerMeasure`.
https://github.com/leanprover-community/mathlib4/pull/37349 added:

- `mahlerMeasure_le_sqrt_sum_sq_norm_coeff` (Landau's inequality)
- `le_mahlerMeasure_mul_right` (monotonicity)
- `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`
  (Mignotte bound)

The earlier Mahler measure library (by Fabrizio Barroero) provides:

- `mahlerMeasure_mul`: `M(p * q) = M(p) * M(q)`
- `norm_coeff_le_choose_mul_mahlerMeasure`: `‖p.coeff n‖ ≤ C(deg, n) * M(p)`
- `one_le_prod_max_one_norm_roots`: `∏ max(1, ‖αᵢ‖) ≥ 1`

**Proof outline and glue steps.**

1. **Cast to `ℂ[X]`.** Define `F G H : Polynomial ℂ` via
   `Polynomial.map (Int.castRingHom ℂ)`. From `hg`, obtain
   `h : Polynomial ℤ` with `f = g * h`; map to `F = G * H`
   via `Polynomial.map_mul`.

2. **Nonzero factors.** From `hf` and `f = g * h`, since
   `Polynomial ℤ` is a domain, get `g ≠ 0` and `h ≠ 0`. Then
   `H ≠ 0` (and `G ≠ 0`) by injectivity of `Int.castRingHom ℂ`
   (via `Polynomial.map_ne_zero_of_injective` or `map_injective`).

3. **Mahler measure ≥ 1 for integer polynomials.** `H ≠ 0` alone
   is not enough (`(1/2 : ℂ[X])` has Mahler measure `1/2`). The
   key is that `h` has integer coefficients: `leadingCoeff h` is
   a nonzero integer, so `‖leadingCoeff H‖ ≥ 1`. Combined with
   `one_le_prod_max_one_norm_roots` and
   `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`, this gives
   `1 ≤ H.mahlerMeasure`.

4. **Monotonicity.** Apply `le_mahlerMeasure_mul_right` (or use
   `mahlerMeasure_mul` + `1 ≤ H.mahlerMeasure`) to get
   `G.mahlerMeasure ≤ F.mahlerMeasure`.

5. **Coefficient bound.** Apply
   `norm_coeff_le_choose_mul_mahlerMeasure` to `G`:
   `‖G.coeff j‖ ≤ C(G.natDegree, j) * G.mahlerMeasure`.
   Chain with step 4 to get `≤ C(G.natDegree, j) * F.mahlerMeasure`.

6. **Landau bound.** Apply `mahlerMeasure_le_sqrt_sum_sq_norm_coeff`
   to bound `F.mahlerMeasure ≤ √(∑ ‖F.coeff i‖²)`.

7. **Transport back to `ℤ`.** Four lemmas:
   - **Coefficients:** `G.coeff j = ↑(g.coeff j)` — by
     `Polynomial.coeff_map`.
   - **Degree:** `G.natDegree = g.natDegree` — by
     `Polynomial.natDegree_map_of_injective` (injective cast).
   - **Support:** `F.support = f.support` — by
     `Polynomial.support_map_of_injective` (injective cast).
     Needed to rewrite the L2 sum from `F`'s support to `f`'s.
   - **Norms:** `‖((g.coeff j : ℤ) : ℂ)‖ = |(g.coeff j : ℝ)|` —
     via `Complex.norm_intCast` or `Complex.norm_ofReal` +
     `Int.cast_abs`. The L2 sum rewrites similarly since
     `‖((f.coeff i : ℤ) : ℂ)‖² = (f.coeff i : ℝ)²`. The final
     LHS rewrites from `‖...‖` to `(Int.natAbs (g.coeff j) : ℝ)`
     to match the theorem statement.

**Open Mathlib PR:** https://github.com/leanprover-community/mathlib4/pull/33463
("Mahler Measure for other rings") extends the Mahler measure definition
beyond `ℂ[X]`. If this lands, the `ℤ → ℂ` coercion step becomes cleaner.

**Robinson-form derivative surface (CLD Φ Mahler bound).**

The analytic input for the BHKS van Hoeij CLD `Φ` coefficient bound belongs in
`hex-poly-z-mathlib`, not in the Mathlib-free `hex-poly-z` library. It is a
collection of theorems about roots of complex polynomials that uses Mathlib's
complex polynomial root and Mahler-measure APIs.

This library owns the Robinson-reflection root-deletion surface in
`HexPolyZMathlib/RobinsonForm.lean`. The Robinson form keeps roots in the
closed unit disk as `X - C α` and reflects exterior roots to
`1 - C (conj α) * X`; the derivative is expanded as a sum of root-deletion
summands whose Mahler measures are individually controlled:

- The root-deletion derivative summand `Polynomial.rootDeletionDerivativeSummand g α`
  and the derivative expansion
  `Polynomial.derivative_eq_sum_rootDeletionDerivativeSummand`.
- The per-summand Mahler-measure bound
  `Polynomial.mahlerMeasure_rootDeletionDerivativeSummand_le`.

`HexBerlekampZassenhausMathlib/CLDColumnBound.lean` consumes this surface to
discharge the `hphi_mahler` hypothesis of `abs_phi_coeff_le` — the replacement
analytic obligation for the BHKS CLD `Φ` Mahler-measure bound.

Downstream libraries may depend on these theorems as Mathlib-side analytic
inputs. Mathlib-free libraries must not import this surface directly; they
should consume executable bounds or conditional hypotheses whose proofs are
discharged here.

**Shared root-separation foundations.** The generic parts of the Mahler
root-separation development live here once for both roots companions:

- `HexPolyZMathlib/Discriminant.lean` proves the root-product form of
  `Polynomial.discr`, its nonvanishing for separable polynomials, base-change
  compatibility, and the integer lower bound `1 ≤ |discr f|`.
- `HexPolyZMathlib/Hadamard.lean` proves the sharp column-norm determinant
  inequality `Matrix.norm_det_le_prod_norm_column` over an `RCLike` field.

Both modules are stated at ordinary Mathlib generality and import no executable
root-isolation library. Companion-specific precision arithmetic remains in the
corresponding roots companion.
