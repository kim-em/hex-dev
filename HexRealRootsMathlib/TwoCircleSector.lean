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

/-! ### The Obreshkoff sector -/

open Complex in
/-- The closed Obreshkoff sector `{z | z.re ≤ -‖z‖ / 2}`: the closed sector of
half-angle `π/3` opening along the negative real axis. Note `0 ∈ Sector`. -/
def Sector : Set ℂ := {z | z.re ≤ -‖z‖ / 2}

theorem mem_sector {z : ℂ} : z ∈ Sector ↔ z.re ≤ -‖z‖ / 2 := Iff.rfl

/-- A real number lies in the sector (as a complex number) iff it is `≤ 0`. -/
theorem ofReal_mem_sector {t : ℝ} : ((t : ℝ) : ℂ) ∈ Sector ↔ t ≤ 0 := by
  rw [mem_sector, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt t 0 with h | h
  · simp only [h, iff_true, abs_of_nonpos h]; linarith
  · simp only [abs_of_pos h]
    constructor <;> intro h' <;> linarith

/-- The sector is closed under complex conjugation. -/
theorem conj_mem_sector {z : ℂ} (hz : z ∈ Sector) : (starRingEnd ℂ) z ∈ Sector := by
  rw [mem_sector, Complex.conj_re, Complex.norm_conj]; exact hz

/-! ### From roots in the sector to `PosLogConcave` -/

/-- A monic real linear factor whose complex root lies in `Sector ∖ {0}` has the
form `X + C r` with `0 < r`, hence multiplying preserves `PosLogConcave`. -/
private theorem posLogConcave_mul_of_monicDegOne {f A : ℝ[X]} (hA : PosLogConcave A)
    (hf : IsMonicOfDegree f 1) (h0 : f.coeff 0 ≠ 0)
    (hroots : ∀ z : ℂ, aeval z f = 0 → z ∈ Sector) :
    PosLogConcave (f * A) := by
  set c₀ := f.coeff 0 with hc₀
  have hfeq : f = X + C c₀ := by
    have hdeg : f.degree = 1 := by
      rw [degree_eq_natDegree hf.monic.ne_zero, hf.natDegree_eq]; rfl
    rw [eq_X_add_C_of_degree_eq_one hdeg, hf.leadingCoeff_eq, map_one, one_mul]
  have hrootmem : ((-c₀ : ℝ) : ℂ) ∈ Sector := by
    apply hroots
    rw [hfeq]; simp
  rw [ofReal_mem_sector] at hrootmem
  have hc₀pos : 0 < c₀ := by
    rcases lt_or_eq_of_le (by linarith : c₀ ≥ 0) with h | h
    · exact h
    · exact absurd h.symm h0
  rw [hfeq]
  exact hA.mul_X_add_C hc₀pos

/-- A monic real quadratic factor whose complex roots lie in `Sector ∖ {0}` has
the form `X² + C b * X + C c` with `0 < b`, `0 < c`, and `c ≤ b²`, hence
multiplying preserves `PosLogConcave`. -/
private theorem posLogConcave_mul_of_monicDegTwo {f A : ℝ[X]} (hA : PosLogConcave A)
    (hf : IsMonicOfDegree f 2) (h0 : f.coeff 0 ≠ 0)
    (hroots : ∀ z : ℂ, aeval z f = 0 → z ∈ Sector) :
    PosLogConcave (f * A) := by
  -- It suffices to write `f = X² + C b * X + C c` with the required sign conditions.
  suffices h : ∃ b c : ℝ, f = X ^ 2 + C b * X + C c ∧ 0 < b ∧ 0 < c ∧ c ≤ b ^ 2 by
    obtain ⟨b, c, hfeq, hb, hc, hbc⟩ := h
    rw [hfeq]
    exact hA.mul_quadratic hb hc hbc
  by_cases hreal : ∃ ρ : ℝ, aeval (ρ : ℝ) f = 0
  · -- real root case: `f = (X - C ρ)(X + C d)` with `ρ < 0 < d`
    obtain ⟨ρ, hρ⟩ := hreal
    have hdvd : (X - C ρ) ∣ f := dvd_iff_isRoot.mpr (by simpa [IsRoot, ← aeval_def] using hρ)
    obtain ⟨q, hq⟩ := hdvd
    have hXsub : IsMonicOfDegree (X - C ρ : ℝ[X]) 1 :=
      ⟨natDegree_X_sub_C ρ, monic_X_sub_C ρ⟩
    have hqmd : IsMonicOfDegree q 1 := by
      apply hXsub.of_mul_left
      rw [← hq]; exact (show (1 : ℕ) + 1 = 2 by rfl) ▸ hf
    set d := q.coeff 0 with hd
    have hqeq : q = X + C d := by
      have hdeg : q.degree = 1 := by
        rw [degree_eq_natDegree hqmd.monic.ne_zero, hqmd.natDegree_eq]; rfl
      rw [eq_X_add_C_of_degree_eq_one hdeg, hqmd.leadingCoeff_eq, map_one, one_mul]
    -- both real roots lie in the sector
    have hρmem : ((ρ : ℝ) : ℂ) ∈ Sector := hroots _ (by
      have : aeval ((ρ : ℝ) : ℂ) f = algebraMap ℝ ℂ (aeval ρ f) :=
        (aeval_algebraMap_apply_eq_algebraMap_eval ρ f)
      rw [this, hρ, map_zero])
    have hdmem : ((-d : ℝ) : ℂ) ∈ Sector := hroots _ (by
      have hroot : aeval (-d) f = 0 := by
        rw [hq, hqeq, map_mul]; simp [aeval_def]
      have : aeval (((-d : ℝ)) : ℂ) f = algebraMap ℝ ℂ (aeval (-d) f) :=
        (aeval_algebraMap_apply_eq_algebraMap_eval (-d) f)
      rw [this, hroot, map_zero])
    rw [ofReal_mem_sector] at hρmem
    rw [ofReal_mem_sector] at hdmem
    have hdnn : 0 ≤ d := by linarith
    -- `c = f.coeff 0 = -(ρ * d)`, nonzero, so both `ρ, d` nonzero
    have hfeq : f = X ^ 2 + C (d - ρ) * X + C (-(ρ * d)) := by
      rw [hq, hqeq, C_sub, C_neg, C_mul]; ring
    have hc0 : f.coeff 0 = -(ρ * d) := by rw [hfeq]; simp
    have hne : ρ * d ≠ 0 := by rw [hc0] at h0; simpa using h0
    have hρneg : ρ < 0 := lt_of_le_of_ne hρmem (fun h => hne (by simp [h]))
    have hdpos : 0 < d := lt_of_le_of_ne hdnn (fun h => hne (by rw [← h]; ring))
    refine ⟨d - ρ, -(ρ * d), hfeq, by linarith, by nlinarith, by nlinarith⟩
  · -- no real root: `f` is irreducible over `ℝ`, take a non-real root
    push_neg at hreal
    obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z f = 0 :=
      IsAlgClosed.exists_aeval_eq_zero ℂ f (by
        rw [degree_eq_natDegree hf.monic.ne_zero, hf.natDegree_eq]; decide)
    have hzim : z.im ≠ 0 := by
      intro him
      apply hreal z.re
      have : ((z.re : ℝ) : ℂ) = z := by
        apply Complex.ext <;> simp [him]
      have h2 : aeval (((z.re : ℝ)) : ℂ) f = algebraMap ℝ ℂ (aeval z.re f) :=
        aeval_algebraMap_apply_eq_algebraMap_eval z.re f
      rw [this] at h2
      have : algebraMap ℝ ℂ (aeval z.re f) = 0 := by rw [← h2, hz]
      simpa using this
    -- `f = X² - C (2 z.re) X + C ‖z‖²`
    have hdvd : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) ∣ f :=
      quadratic_dvd_of_aeval_eq_zero_im_ne_zero f hz hzim
    have hpmd : IsMonicOfDegree (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]) 2 := by
      have heq : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X])
          = X ^ 2 + C (-(2 * z.re)) * X + C (‖z‖ ^ 2) := by rw [C_neg]; ring
      rw [heq]
      exact ⟨natDegree_quad _ _, monic_quad _ _⟩
    obtain ⟨s, hs⟩ := hdvd
    have hs1 : IsMonicOfDegree s 0 := by
      apply hpmd.of_mul_left
      rw [← hs]; exact (show (2 : ℕ) + 0 = 2 by rfl) ▸ hf
    rw [isMonicOfDegree_zero_iff] at hs1
    have hfeq : f = X ^ 2 + C (-(2 * z.re)) * X + C (‖z‖ ^ 2) := by
      rw [hs, hs1, mul_one, C_neg]; ring
    have hznorm : 0 < ‖z‖ := by
      rw [norm_pos_iff]; intro h; rw [h] at hzim; simp at hzim
    have hzsec : z.re ≤ -‖z‖ / 2 := hroots z hz
    refine ⟨-(2 * z.re), ‖z‖ ^ 2, hfeq, by linarith, by positivity, ?_⟩
    have : ‖z‖ ≤ -(2 * z.re) := by linarith
    nlinarith [this, hznorm]

/-- **Sector core.** If `Q` is monic with `Q.coeff 0 ≠ 0` and every complex root
of `Q` lies in the sector, then `Q` is positively log-concave. -/
theorem posLogConcave_of_aeval_mem_sector {Q : ℝ[X]} (hQ : Q.Monic) (h0 : Q.coeff 0 ≠ 0)
    (hroots : ∀ z : ℂ, aeval z Q = 0 → z ∈ Sector) : PosLogConcave Q := by
  generalize hn : Q.natDegree = N
  induction N using Nat.strong_induction_on generalizing Q with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- base case: `Q` is a monic constant, hence `1`
      subst hN0
      have hQ1 : Q = 1 := by rw [← isMonicOfDegree_zero_iff]; exact ⟨hn, hQ⟩
      rw [hQ1]
      refine ⟨fun i hi => ?_, fun i => by simp [coeff_one]⟩
      simp only [natDegree_one, Nat.le_zero] at hi
      subst hi; simp [coeff_one]
    · -- inductive step
      obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      have hmd : IsMonicOfDegree Q (m + 1) := ⟨hn, hQ⟩
      obtain ⟨f₁, f₂, hf₁, hQeq⟩ := hmd.eq_isMonicOfDegree_one_or_two_mul
      have hf2ne : f₂ ≠ 0 := right_ne_zero_of_mul (hQeq ▸ hmd.monic.ne_zero)
      have hf20 : f₂.coeff 0 ≠ 0 := fun h => h0 (by rw [hQeq, mul_coeff_zero, h, mul_zero])
      have hf10 : f₁.coeff 0 ≠ 0 := fun h => h0 (by rw [hQeq, mul_coeff_zero, h, zero_mul])
      have hroots₂ : ∀ z : ℂ, aeval z f₂ = 0 → z ∈ Sector :=
        fun z hz => hroots z (by rw [hQeq, map_mul, hz, mul_zero])
      have hroots₁ : ∀ z : ℂ, aeval z f₁ = 0 → z ∈ Sector :=
        fun z hz => hroots z (by rw [hQeq, map_mul, hz, zero_mul])
      rcases hf₁ with hf₁ | hf₁
      · -- degree 1 factor
        have hf2md : IsMonicOfDegree f₂ m :=
          hf₁.of_mul_left (by rw [add_comm, ← hQeq]; exact hmd)
        have hf2plc : PosLogConcave f₂ :=
          ih m (by omega) hf2md.monic hf20 hroots₂ hf2md.natDegree_eq
        rw [hQeq]
        exact posLogConcave_mul_of_monicDegOne hf2plc hf₁ hf10 hroots₁
      · -- degree 2 factor
        have hmpos : 1 ≤ m := by
          have : Q.natDegree = 2 + f₂.natDegree := by
            rw [hQeq, natDegree_mul hf₁.monic.ne_zero hf2ne, hf₁.natDegree_eq]
          omega
        have hf2md : IsMonicOfDegree f₂ (m - 1) :=
          hf₁.of_mul_left (by rw [show 2 + (m - 1) = m + 1 by omega, ← hQeq]; exact hmd)
        have hf2plc : PosLogConcave f₂ :=
          ih (m - 1) (by omega) hf2md.monic hf20 hroots₂ hf2md.natDegree_eq
        rw [hQeq]
        exact posLogConcave_mul_of_monicDegTwo hf2plc hf₁ hf10 hroots₁

end Polynomial
