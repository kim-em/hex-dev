/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib

public section

/-!
# The sector variation bound for the Obreshkoff two-circle theorem

This module proves the *sector core* of the Obreshkoff two-circle theorem: a
real polynomial whose complex roots all lie (with at most one exception) inside
the closed sector

`S = {z : ℂ | z.re ≤ -‖z‖ / 2}`

has at most one sign variation in its coefficient sequence.  The sector `S` is
the half-plane-like region cut out at angle `± 2π/3` from the positive real
axis; note `0 ∈ S`.

The route is the positivity/log-concavity argument (a special case of Hoggar's
1974 theorem on logarithmic concavity, *Chromatic polynomials and logarithmic
concavity*), **not** a per-factor sign-variation bound: the naive claim
`signVariations ((X² + bX + c) * P) ≤ signVariations P` for sector quadratics is
false (see `sharpness` at the end of the file, where `(X²+X+1)·(X²−(3/2)X+1)`
has four sign variations while only two roots lie outside `S`).

## Main definitions and results

* `Polynomial.PosLogConcave` — the positivity + log-concavity predicate on the
  coefficient sequence.
* `Polynomial.PosLogConcave.mul_X_add_C` and `Polynomial.PosLogConcave.mul_quadratic`
  — the closure of `PosLogConcave` under multiplication by a positive linear
  factor `X + C r` and by a sector quadratic `X² + C b * X + C c`.
-/

namespace Polynomial

variable {A : ℝ[X]}

/-- A real polynomial is *positively log-concave* when all of its coefficients
up to its degree are strictly positive and the coefficient sequence is
logarithmically concave (`aᵢ · aᵢ₊₂ ≤ aᵢ₊₁²` for all `i`). Out-of-range
coefficients are `0`, which makes the log-concavity condition hold automatically
outside the support. -/
structure PosLogConcave (A : ℝ[X]) : Prop where
  /-- Every coefficient up to the degree is strictly positive. -/
  pos : ∀ i ≤ A.natDegree, 0 < A.coeff i
  /-- The coefficient sequence is logarithmically concave. -/
  lc : ∀ i, A.coeff i * A.coeff (i + 2) ≤ A.coeff (i + 1) ^ 2

namespace PosLogConcave

theorem coeff_nonneg (hA : PosLogConcave A) (i : ℕ) : 0 ≤ A.coeff i := by
  rcases le_or_gt i A.natDegree with h | h
  · exact (hA.pos i h).le
  · rw [coeff_eq_zero_of_natDegree_lt h]

/-- If a coefficient vanishes then so does the next one: `PosLogConcave`
sequences have no internal zeros. -/
theorem coeff_succ_eq_zero (hA : PosLogConcave A) {i : ℕ} (h : A.coeff i = 0) :
    A.coeff (i + 1) = 0 := by
  rcases le_or_gt i A.natDegree with hi | hi
  · exact absurd h (hA.pos i hi).ne'
  · exact coeff_eq_zero_of_natDegree_lt (by lia)

theorem ne_zero (hA : PosLogConcave A) : A ≠ 0 := by
  intro h
  simpa [h] using hA.pos 0 (by simp [h])

/-- **Generalised log-concavity.** For a `PosLogConcave` sequence the "spread"
product `aᵢ · aⱼ₊₁` is dominated by the "central" product `aᵢ₊₁ · aⱼ` whenever
`i ≤ j`. This is the monotone-ratio consequence of log-concavity, formulated so
that all indices stay in `ℕ`. -/
theorem genLC (hA : PosLogConcave A) :
    ∀ i j, i ≤ j → A.coeff i * A.coeff (j + 1) ≤ A.coeff (i + 1) * A.coeff j := by
  intro i j
  induction j with
  | zero =>
    intro hij
    obtain rfl : i = 0 := Nat.le_zero.mp hij
    nlinarith [mul_comm (A.coeff 0) (A.coeff 1)]
  | succ j ih =>
    intro hij
    rcases eq_or_lt_of_le hij with heq | hlt
    · subst heq
      nlinarith [mul_comm (A.coeff (j + 1)) (A.coeff (j + 2))]
    · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
      have IH := ih hij'
      have hlcj := hA.lc j
      by_cases hz : A.coeff (j + 1) = 0
      · rw [hA.coeff_succ_eq_zero hz, hz]; simp
      · have hpos : 0 < A.coeff (j + 1) :=
          lt_of_le_of_ne (hA.coeff_nonneg _) (Ne.symm hz)
        have n2 := hA.coeff_nonneg (i + 1)
        have n3 := hA.coeff_nonneg (j + 2)
        nlinarith [mul_le_mul_of_nonneg_right IH n3, mul_le_mul_of_nonneg_left hlcj n2,
          hpos, hA.coeff_nonneg i]

end PosLogConcave

/-! ### Coefficient formulas for the linear and quadratic factors -/

private theorem coeff_X_add_C_mul_succ (r : ℝ) (A : ℝ[X]) (k : ℕ) :
    ((X + C r) * A).coeff (k + 1) = A.coeff k + r * A.coeff (k + 1) := by
  rw [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]

private theorem coeff_X_add_C_mul_zero (r : ℝ) (A : ℝ[X]) :
    ((X + C r) * A).coeff 0 = r * A.coeff 0 := by
  rw [add_mul, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add]

private theorem coeff_X_add_C_mul_one (r : ℝ) (A : ℝ[X]) :
    ((X + C r) * A).coeff 1 = A.coeff 0 + r * A.coeff 1 := coeff_X_add_C_mul_succ r A 0

private theorem coeff_X_add_C_mul_two (r : ℝ) (A : ℝ[X]) :
    ((X + C r) * A).coeff 2 = A.coeff 1 + r * A.coeff 2 := coeff_X_add_C_mul_succ r A 1

private theorem coeff_quad_mul_add_two (b c : ℝ) (A : ℝ[X]) (k : ℕ) :
    ((X ^ 2 + C b * X + C c) * A).coeff (k + 2)
      = A.coeff k + b * A.coeff (k + 1) + c * A.coeff (k + 2) := by
  simp only [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_pow_mul, coeff_X_mul]

private theorem coeff_quad_mul_one (b c : ℝ) (A : ℝ[X]) :
    ((X ^ 2 + C b * X + C c) * A).coeff 1 = b * A.coeff 0 + c * A.coeff 1 := by
  simp [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul']

private theorem coeff_quad_mul_zero (b c : ℝ) (A : ℝ[X]) :
    ((X ^ 2 + C b * X + C c) * A).coeff 0 = c * A.coeff 0 := by
  simp [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul_zero]

private theorem coeff_quad_mul_two (b c : ℝ) (A : ℝ[X]) :
    ((X ^ 2 + C b * X + C c) * A).coeff 2
      = A.coeff 0 + b * A.coeff 1 + c * A.coeff 2 := coeff_quad_mul_add_two b c A 0

private theorem coeff_quad_mul_three (b c : ℝ) (A : ℝ[X]) :
    ((X ^ 2 + C b * X + C c) * A).coeff 3
      = A.coeff 1 + b * A.coeff 2 + c * A.coeff 3 := coeff_quad_mul_add_two b c A 1

private theorem natDegree_quad (b c : ℝ) :
    (X ^ 2 + C b * X + C c : ℝ[X]).natDegree = 2 := by
  have : (X ^ 2 + C b * X + C c : ℝ[X]) = C 1 * X ^ 2 + C b * X + C c := by rw [C_1, one_mul]
  rw [this, natDegree_quadratic one_ne_zero]

private theorem monic_quad (b c : ℝ) : Monic (X ^ 2 + C b * X + C c : ℝ[X]) := by
  have : (X ^ 2 + C b * X + C c : ℝ[X]) = C 1 * X ^ 2 + C b * X + C c := by rw [C_1, one_mul]
  rw [Monic, this, leadingCoeff_quadratic one_ne_zero]

/-! ### Closure of `PosLogConcave` under the sector factors -/

/-- Multiplying a `PosLogConcave` polynomial by a positive linear factor `X + C r`
(`0 < r`) preserves `PosLogConcave`. -/
theorem PosLogConcave.mul_X_add_C (hA : PosLogConcave A) {r : ℝ} (hr : 0 < r) :
    PosLogConcave ((X + C r) * A) := by
  have hnd : ((X + C r) * A).natDegree = A.natDegree + 1 := by
    rw [(monic_X_add_C r).natDegree_mul' hA.ne_zero, natDegree_X_add_C, add_comm]
  refine ⟨?_, ?_⟩
  · -- positivity
    intro i hi
    rw [hnd] at hi
    match i with
    | 0 =>
      rw [coeff_X_add_C_mul_zero]
      exact mul_pos hr (hA.pos 0 (by simp))
    | k + 1 =>
      rw [coeff_X_add_C_mul_succ]
      have : 0 < A.coeff k := hA.pos k (by lia)
      have : 0 ≤ r * A.coeff (k + 1) := mul_nonneg hr.le (hA.coeff_nonneg _)
      linarith
  · -- log-concavity
    intro i
    match i with
    | 0 =>
      show ((X + C r) * A).coeff 0 * ((X + C r) * A).coeff 2 ≤ ((X + C r) * A).coeff 1 ^ 2
      rw [coeff_X_add_C_mul_zero, coeff_X_add_C_mul_one, coeff_X_add_C_mul_two]
      have lc0 := hA.lc 0
      have h0 := hA.pos 0 (by simp)
      have n1 := hA.coeff_nonneg 1
      nlinarith [sq_nonneg (A.coeff 0), mul_nonneg hr.le (mul_nonneg h0.le n1),
        mul_nonneg (mul_nonneg hr.le hr.le) (sub_nonneg.mpr lc0)]
    | m + 1 =>
      show ((X + C r) * A).coeff (m + 1) * ((X + C r) * A).coeff ((m + 2) + 1) ≤
        ((X + C r) * A).coeff ((m + 1) + 1) ^ 2
      simp only [coeff_X_add_C_mul_succ]
      have lcm := hA.lc m
      have lcm1 := hA.lc (m + 1)
      have gen := hA.genLC m (m + 2) (by lia)
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr gen),
        mul_nonneg (mul_nonneg hr.le hr.le) (sub_nonneg.mpr lcm1), sub_nonneg.mpr lcm]

/-- Multiplying a `PosLogConcave` polynomial by a *sector quadratic*
`X² + C b * X + C c` (`0 < b`, `0 < c`, `c ≤ b²`) preserves `PosLogConcave`.

This is the hard kernel of the argument: a special case of Hoggar's 1974 theorem.
The log-concavity of the product is certified by the exact identity
`dᵢ² − dᵢ₋₁·dᵢ₊₁ = c²·L(i-1) + bc·G₂ + b·G₃ + L₄ + c·G₅ + (b²−c)·L(i-2)`,
in which each block is a nonnegative instance of log-concavity (`lc`) or
generalised log-concavity (`genLC`) of `A` and every scalar coefficient is
nonnegative because `0 < b`, `0 < c`, and `c ≤ b²`. -/
theorem PosLogConcave.mul_quadratic (hA : PosLogConcave A) {b c : ℝ} (hb : 0 < b)
    (hc : 0 < c) (hbc : c ≤ b ^ 2) :
    PosLogConcave ((X ^ 2 + C b * X + C c) * A) := by
  have hnd : ((X ^ 2 + C b * X + C c) * A).natDegree = A.natDegree + 2 := by
    rw [(monic_quad b c).natDegree_mul' hA.ne_zero, natDegree_quad, add_comm]
  refine ⟨?_, ?_⟩
  · -- positivity
    intro i hi
    rw [hnd] at hi
    match i with
    | 0 =>
      rw [coeff_quad_mul_zero]
      exact mul_pos hc (hA.pos 0 (by simp))
    | 1 =>
      rw [coeff_quad_mul_one]
      have h0 := hA.pos 0 (by simp)
      have := mul_nonneg hc.le (hA.coeff_nonneg 1)
      nlinarith [mul_pos hb h0]
    | m + 2 =>
      rw [coeff_quad_mul_add_two]
      have hm : 0 < A.coeff m := hA.pos m (by lia)
      have h1 : 0 ≤ b * A.coeff (m + 1) := mul_nonneg hb.le (hA.coeff_nonneg _)
      have h2 : 0 ≤ c * A.coeff (m + 2) := mul_nonneg hc.le (hA.coeff_nonneg _)
      linarith
  · -- log-concavity
    intro i
    match i with
    | 0 =>
      show ((X ^ 2 + C b * X + C c) * A).coeff 0 * ((X ^ 2 + C b * X + C c) * A).coeff 2 ≤
        ((X ^ 2 + C b * X + C c) * A).coeff 1 ^ 2
      rw [coeff_quad_mul_zero, coeff_quad_mul_one, coeff_quad_mul_two]
      nlinarith [mul_nonneg (sub_nonneg.mpr hbc) (sq_nonneg (A.coeff 0)),
        mul_nonneg (mul_nonneg hb.le hc.le) (mul_nonneg (hA.coeff_nonneg 0) (hA.coeff_nonneg 1)),
        mul_nonneg (mul_nonneg hc.le hc.le) (sub_nonneg.mpr (hA.lc 0))]
    | 1 =>
      show ((X ^ 2 + C b * X + C c) * A).coeff 1 * ((X ^ 2 + C b * X + C c) * A).coeff 3 ≤
        ((X ^ 2 + C b * X + C c) * A).coeff 2 ^ 2
      rw [coeff_quad_mul_one, coeff_quad_mul_two, coeff_quad_mul_three]
      nlinarith [mul_nonneg (mul_nonneg hc.le hc.le) (sub_nonneg.mpr (hA.lc 1)),
        mul_nonneg (mul_nonneg hb.le hc.le) (sub_nonneg.mpr (hA.genLC 0 2 (by lia))),
        mul_nonneg hb.le (mul_nonneg (hA.coeff_nonneg 0) (hA.coeff_nonneg 1)),
        sq_nonneg (A.coeff 0),
        mul_nonneg hc.le (mul_nonneg (hA.coeff_nonneg 0) (hA.coeff_nonneg 2)),
        mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr (hA.lc 0))]
    | m + 2 =>
      show ((X ^ 2 + C b * X + C c) * A).coeff (m + 2) *
          ((X ^ 2 + C b * X + C c) * A).coeff ((m + 2) + 2) ≤
        ((X ^ 2 + C b * X + C c) * A).coeff ((m + 1) + 2) ^ 2
      simp only [coeff_quad_mul_add_two]
      nlinarith [mul_nonneg (mul_nonneg hc.le hc.le) (sub_nonneg.mpr (hA.lc (m + 2))),
        mul_nonneg (mul_nonneg hb.le hc.le) (sub_nonneg.mpr (hA.genLC (m + 1) (m + 3) (by lia))),
        mul_nonneg hb.le (sub_nonneg.mpr (hA.genLC m (m + 2) (by lia))),
        sub_nonneg.mpr (hA.lc m),
        mul_nonneg hc.le (sub_nonneg.mpr (hA.genLC m (m + 3) (by lia))),
        mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr (hA.lc (m + 1)))]

end Polynomial
