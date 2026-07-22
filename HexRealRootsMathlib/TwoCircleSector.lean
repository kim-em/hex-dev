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
false (see the sharpness section at the end of the file, where
`(X²+X+1)·(X²−(3/2)X+1)` has four sign variations while only two roots lie
outside `S`).

## Main definitions and results

* `Polynomial.PosLogConcave` — the positivity + log-concavity predicate on the
  coefficient sequence.
* `Polynomial.PosLogConcave.mul_X_add_C` and `Polynomial.PosLogConcave.mul_quadratic`
  — the closure of `PosLogConcave` under multiplication by a positive linear
  factor `X + C r` and by a sector quadratic `X² + C b * X + C c` (`0 < b`,
  `0 < c`, `c ≤ b²`).
* `Polynomial.sector` — the closed sector, with `posLogConcave_of_aeval_mem_sector`
  turning "monic, nonzero constant term, all complex roots in the sector" into
  `PosLogConcave`.
* `Polynomial.signVariations_le_one_of_sector` — **the sector variation bound**:
  `P ≠ 0` with at most one complex root (with multiplicity) outside the sector
  has `signVariations P ≤ 1`.
* `Polynomial.signVariations_eq_zero_of_sector` — the `λ = 0` case: no roots
  outside the sector forces `signVariations P = 0`.

This development is Hex-free: it is a slice over `Polynomial ℝ`/`ℂ` intended to
be upstreamable to Mathlib. No formalisation of the two-circle theorem (or of
this sector core) is known in any proof assistant.
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
  simp [add_mul, coeff_add, mul_assoc]

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
half-angle `π/3` opening along the negative real axis. Note `0 ∈ sector`. -/
def sector : Set ℂ := {z | z.re ≤ -‖z‖ / 2}

theorem mem_sector {z : ℂ} : z ∈ sector ↔ z.re ≤ -‖z‖ / 2 := Iff.rfl

/-- A real number lies in the sector (as a complex number) iff it is `≤ 0`. -/
theorem ofReal_mem_sector {t : ℝ} : ((t : ℝ) : ℂ) ∈ sector ↔ t ≤ 0 := by
  rw [mem_sector, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt t 0 with h | h
  · simp only [h, iff_true, abs_of_nonpos h]; linarith
  · simp only [abs_of_pos h]
    constructor <;> intro h' <;> linarith

/-- The sector is closed under complex conjugation. -/
theorem conj_mem_sector {z : ℂ} (hz : z ∈ sector) : (starRingEnd ℂ) z ∈ sector := by
  rw [mem_sector, Complex.conj_re, Complex.norm_conj]; exact hz

/-! ### From roots in the sector to `PosLogConcave` -/

/-- A monic real linear factor whose complex root lies in `sector ∖ {0}` has the
form `X + C r` with `0 < r`, hence multiplying preserves `PosLogConcave`. -/
private theorem posLogConcave_mul_of_monicDegOne {f A : ℝ[X]} (hA : PosLogConcave A)
    (hf : IsMonicOfDegree f 1) (h0 : f.coeff 0 ≠ 0)
    (hroots : ∀ z : ℂ, aeval z f = 0 → z ∈ sector) :
    PosLogConcave (f * A) := by
  set c₀ := f.coeff 0 with hc₀
  have hfeq : f = X + C c₀ := by
    have hdeg : f.degree = 1 := by
      rw [degree_eq_natDegree hf.monic.ne_zero, hf.natDegree_eq]; rfl
    rw [eq_X_add_C_of_degree_eq_one hdeg, hf.leadingCoeff_eq, map_one, one_mul]
  have hrootmem : ((-c₀ : ℝ) : ℂ) ∈ sector := by
    apply hroots
    rw [hfeq]; simp
  rw [ofReal_mem_sector] at hrootmem
  have hc₀pos : 0 < c₀ := by
    rcases lt_or_eq_of_le (by linarith : c₀ ≥ 0) with h | h
    · exact h
    · exact absurd h.symm h0
  rw [hfeq]
  exact hA.mul_X_add_C hc₀pos

/-- A monic real quadratic factor whose complex roots lie in `sector ∖ {0}` has
the form `X² + C b * X + C c` with `0 < b`, `0 < c`, and `c ≤ b²`, hence
multiplying preserves `PosLogConcave`. -/
private theorem posLogConcave_mul_of_monicDegTwo {f A : ℝ[X]} (hA : PosLogConcave A)
    (hf : IsMonicOfDegree f 2) (h0 : f.coeff 0 ≠ 0)
    (hroots : ∀ z : ℂ, aeval z f = 0 → z ∈ sector) :
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
    have hρmem : ((ρ : ℝ) : ℂ) ∈ sector := hroots _ (by
      have : aeval ((ρ : ℝ) : ℂ) f = algebraMap ℝ ℂ (aeval ρ f) :=
        (aeval_algebraMap_apply_eq_algebraMap_eval ρ f)
      rw [this, hρ, map_zero])
    have hdmem : ((-d : ℝ) : ℂ) ∈ sector := hroots _ (by
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
    push Not at hreal
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

/-- **sector core.** If `Q` is monic with `Q.coeff 0 ≠ 0` and every complex root
of `Q` lies in the sector, then `Q` is positively log-concave. -/
theorem posLogConcave_of_aeval_mem_sector {Q : ℝ[X]} (hQ : Q.Monic) (h0 : Q.coeff 0 ≠ 0)
    (hroots : ∀ z : ℂ, aeval z Q = 0 → z ∈ sector) : PosLogConcave Q := by
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
      have hroots₂ : ∀ z : ℂ, aeval z f₂ = 0 → z ∈ sector :=
        fun z hz => hroots z (by rw [hQeq, map_mul, hz, mul_zero])
      have hroots₁ : ∀ z : ℂ, aeval z f₁ = 0 → z ∈ sector :=
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

/-! ### Sign-variation bounds from coefficient signs

Both bounds are proved by `eraseLead` induction on the coefficient predicates,
so no `coeffList` surgery is needed. -/

/-- A nonnegative-coefficient polynomial has no sign variations. -/
theorem signVariations_eq_zero_of_coeff_nonneg {P : ℝ[X]} (h : ∀ i, 0 ≤ P.coeff i) :
    P.signVariations = 0 := by
  generalize hn : P.natDegree = N
  induction N using Nat.strong_induction_on generalizing P with
  | _ N ih =>
    by_cases hP : P = 0
    · simp [hP]
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      rw [eq_C_of_natDegree_eq_zero hn, ← monomial_zero_left]
      exact signVariations_monomial 0 _
    · have hlead : 0 < P.leadingCoeff :=
        lt_of_le_of_ne (h _) (Ne.symm (leadingCoeff_ne_zero.mpr hP))
      have heLcoeff : ∀ i, 0 ≤ P.eraseLead.coeff i := by
        intro i
        rw [eraseLead_coeff]
        split
        · exact le_refl 0
        · exact h i
      have hite : ¬(SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff) := by
        rw [sign_pos hlead]
        intro hcon
        have : SignType.sign P.eraseLead.leadingCoeff = -1 := by
          rw [← neg_neg (SignType.sign P.eraseLead.leadingCoeff), ← hcon]
        exact absurd (sign_eq_neg_one_iff.mp this) (not_lt.mpr (heLcoeff _))
      rw [signVariations_eq_eraseLead_add_ite hP, if_neg hite, add_zero]
      exact ih _ (lt_of_le_of_lt (eraseLead_natDegree_le P) (by omega)) heLcoeff rfl

/-- **The threshold bound.** If the coefficients of `P` are nonpositive below an
index `θ` and nonnegative from `θ` on, then `P` has at most one sign variation. -/
theorem signVariations_le_one_of_coeff_threshold {P : ℝ[X]} {θ : ℕ}
    (h1 : ∀ i < θ, P.coeff i ≤ 0) (h2 : ∀ i, θ ≤ i → 0 ≤ P.coeff i) :
    P.signVariations ≤ 1 := by
  generalize hn : P.natDegree = N
  induction N using Nat.strong_induction_on generalizing P θ with
  | _ N ih =>
    by_cases hP : P = 0
    · simp [hP]
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      rw [eq_C_of_natDegree_eq_zero hn, ← monomial_zero_left, signVariations_monomial]
      exact zero_le_one
    rcases lt_or_ge P.leadingCoeff 0 with hneg | hpos'
    · -- the leading coefficient is negative, so all coefficients are `≤ 0`
      have hndθ : P.natDegree < θ := by
        by_contra hcon
        push Not at hcon
        exact absurd (h2 _ hcon) (not_le.mpr hneg)
      have hnn : ∀ i, 0 ≤ (-P).coeff i := by
        intro i
        rw [coeff_neg, neg_nonneg]
        rcases le_or_gt i P.natDegree with hi | hi
        · exact h1 i (lt_of_le_of_lt hi hndθ)
        · rw [coeff_eq_zero_of_natDegree_lt hi]
      calc P.signVariations = (-P).signVariations := (signVariations_neg P).symm
        _ = 0 := signVariations_eq_zero_of_coeff_nonneg hnn
        _ ≤ 1 := zero_le_one
    have hlead : 0 < P.leadingCoeff :=
      lt_of_le_of_ne hpos' (Ne.symm (leadingCoeff_ne_zero.mpr hP))
    have heLnd : P.eraseLead.natDegree < N :=
      lt_of_le_of_lt (eraseLead_natDegree_le P) (by omega)
    rcases lt_or_ge P.eraseLead.leadingCoeff 0 with heL | heL
    · -- one variation may occur at the top; below it everything is nonpositive
      have heLndθ : P.eraseLead.natDegree < θ := by
        by_contra hcon
        push Not at hcon
        have hne : P.eraseLead.natDegree ≠ P.natDegree := by omega
        have hcoeff : P.eraseLead.leadingCoeff = P.coeff P.eraseLead.natDegree := by
          rw [leadingCoeff, eraseLead_coeff, if_neg hne]
        rw [hcoeff] at heL
        exact absurd (h2 _ hcon) (not_le.mpr heL)
      have hnn : ∀ i, 0 ≤ (-P.eraseLead).coeff i := by
        intro i
        rw [coeff_neg, neg_nonneg]
        rcases le_or_gt i P.eraseLead.natDegree with hi | hi
        · rw [eraseLead_coeff]
          split
          · exact le_refl 0
          · exact h1 i (lt_of_le_of_lt hi heLndθ)
        · rw [coeff_eq_zero_of_natDegree_lt hi]
      have h0 : P.eraseLead.signVariations = 0 := by
        rw [← signVariations_neg]
        exact signVariations_eq_zero_of_coeff_nonneg hnn
      rw [signVariations_eq_eraseLead_add_ite hP, h0, zero_add]
      split <;> norm_num
    · -- no variation at the top; recurse into `eraseLead`
      have hite : ¬(SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff) := by
        rw [sign_pos hlead]
        intro hcon
        have : SignType.sign P.eraseLead.leadingCoeff = -1 := by
          rw [← neg_neg (SignType.sign P.eraseLead.leadingCoeff), ← hcon]
        exact absurd (sign_eq_neg_one_iff.mp this) (not_lt.mpr heL)
      rw [signVariations_eq_eraseLead_add_ite hP, if_neg hite, add_zero]
      have h1' : ∀ i < θ, P.eraseLead.coeff i ≤ 0 := by
        intro i hi
        rw [eraseLead_coeff]
        split
        · exact le_refl 0
        · exact h1 i hi
      have h2' : ∀ i, θ ≤ i → 0 ≤ P.eraseLead.coeff i := by
        intro i hi
        rw [eraseLead_coeff]
        split
        · exact le_refl 0
        · exact h2 i hi
      exact ih _ heLnd h1' h2' rfl

/-! ### The threshold instantiation -/

/-- A `PosLogConcave` polynomial times any power of `X` has no sign variations. -/
theorem PosLogConcave.signVariations_X_pow_mul (hQ : PosLogConcave A) (k : ℕ) :
    ((X : ℝ[X]) ^ k * A).signVariations = 0 := by
  apply signVariations_eq_zero_of_coeff_nonneg
  intro i
  rw [coeff_X_pow_mul']
  split
  · exact hQ.coeff_nonneg _
  · exact le_refl 0

/-- **The peeled threshold bound.** Multiplying a `PosLogConcave` polynomial by
one real linear factor `X - C r` (any `r : ℝ`) and any power of `X` yields at
most one sign variation. For `r ≤ 0` all coefficients stay nonnegative; for
`0 < r` the monotone-ratio consequence of log-concavity produces a single
nonpositive-to-nonnegative threshold in the coefficients. -/
theorem PosLogConcave.signVariations_X_pow_mul_X_sub_C_mul (hA : PosLogConcave A)
    (r : ℝ) (k : ℕ) :
    ((X : ℝ[X]) ^ k * ((X - C r) * A)).signVariations ≤ 1 := by
  have hWeq : (X - C r) * A = (X + C (-r)) * A := by rw [C_neg]; ring
  rcases le_or_gt r 0 with hr | hr
  · -- `r ≤ 0`: all coefficients of the product are nonnegative
    have hnn : ∀ j, 0 ≤ ((X - C r) * A).coeff j := by
      intro j
      rw [hWeq]
      match j with
      | 0 =>
        rw [coeff_X_add_C_mul_zero]
        exact mul_nonneg (by linarith) (hA.coeff_nonneg 0)
      | m + 1 =>
        rw [coeff_X_add_C_mul_succ]
        have h1 := hA.coeff_nonneg m
        have h2 := mul_nonneg (by linarith : (0:ℝ) ≤ -r) (hA.coeff_nonneg (m + 1))
        linarith
    have hzero : ((X : ℝ[X]) ^ k * ((X - C r) * A)).signVariations = 0 := by
      apply signVariations_eq_zero_of_coeff_nonneg
      intro i
      rw [coeff_X_pow_mul']
      split
      · exact hnn _
      · exact le_refl 0
    rw [hzero]
    exact zero_le_one
  · -- `0 < r`: single sign threshold via monotone ratios
    have hex : ∃ i, 1 ≤ i ∧ 0 ≤ ((X - C r) * A).coeff i := by
      refine ⟨A.natDegree + 1, by omega, ?_⟩
      rw [hWeq, coeff_X_add_C_mul_succ, coeff_eq_zero_of_natDegree_lt (lt_add_one _), mul_zero,
        add_zero]
      exact (hA.pos A.natDegree le_rfl).le
    let θ := Nat.find hex
    have hθ1 : 1 ≤ θ := (Nat.find_spec hex).1
    have hθnn : 0 ≤ ((X - C r) * A).coeff θ := (Nat.find_spec hex).2
    -- propagation: nonnegativity persists above the threshold
    have hprop : ∀ i, 1 ≤ i → 0 ≤ ((X - C r) * A).coeff i →
        0 ≤ ((X - C r) * A).coeff (i + 1) := by
      intro i hi hnn
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [hWeq, coeff_X_add_C_mul_succ] at hnn
      rw [hWeq, show m + 1 + 1 = (m + 1) + 1 from rfl, coeff_X_add_C_mul_succ]
      by_cases hz : A.coeff (m + 1) = 0
      · rw [hz, hA.coeff_succ_eq_zero hz, mul_zero, add_zero]
      · have hpos : 0 < A.coeff (m + 1) := lt_of_le_of_ne (hA.coeff_nonneg _) (Ne.symm hz)
        have hlcm := hA.lc m
        have h2 := hA.coeff_nonneg (m + 2)
        nlinarith [mul_le_mul_of_nonneg_right (by linarith : r * A.coeff (m + 1) ≤ A.coeff m) h2]
    have h2 : ∀ i, θ ≤ i → 0 ≤ ((X - C r) * A).coeff i := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => exact hθnn
      | succ i hi ih => exact hprop i (le_trans hθ1 hi) ih
    have h1 : ∀ i < θ, ((X - C r) * A).coeff i ≤ 0 := by
      intro i hi
      have hni := Nat.find_min hex hi
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · rw [hWeq, coeff_X_add_C_mul_zero]
        have := hA.coeff_nonneg 0
        nlinarith
      · push Not at hni
        exact (hni hipos).le
    apply signVariations_le_one_of_coeff_threshold (θ := θ + k)
    · intro i hi
      rw [coeff_X_pow_mul']
      split
      · exact h1 _ (by omega)
      · exact le_refl 0
    · intro i hi
      rw [coeff_X_pow_mul', if_pos (by omega)]
      exact h2 _ (by omega)

/-! ### Assembly -/

/-- Every nonzero real polynomial is a nonzero scalar times `X ^ k` times a
monic polynomial with nonzero constant coefficient. -/
private theorem exists_C_mul_X_pow_mul {P : ℝ[X]} (hP : P ≠ 0) :
    ∃ (c : ℝ) (k : ℕ) (Q : ℝ[X]), c ≠ 0 ∧ Q.Monic ∧ Q.coeff 0 ≠ 0 ∧
      P = C c * (X ^ k * Q) := by
  have hc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hM₀m : (P * C P.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hP
  obtain ⟨Q, hQe, hQnd⟩ :=
    (P * C P.leadingCoeff⁻¹).exists_eq_pow_rootMultiplicity_mul_and_not_dvd hM₀m.ne_zero 0
  rw [C_0, sub_zero] at hQe hQnd
  refine ⟨P.leadingCoeff, rootMultiplicity 0 (P * C P.leadingCoeff⁻¹), Q, hc, ?_, ?_, ?_⟩
  · rw [Monic, ← leadingCoeff_monic_mul (monic_X_pow _), ← hQe]
    exact hM₀m
  · exact fun h => hQnd (X_dvd_iff.mpr h)
  · rw [← hQe, mul_comm (C P.leadingCoeff), mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, mul_one]

noncomputable instance : DecidablePred (· ∈ sector) :=
  fun _ => decidable_of_iff _ mem_sector.symm

/-- **The sector variation bound** (the core of the Obreshkoff two-circle
theorem). If at most one complex root of the nonzero real polynomial `P`,
counted with multiplicity, lies outside the sector `{z | z.re ≤ -‖z‖ / 2}`,
then the coefficients of `P` have at most one sign variation. -/
theorem signVariations_le_one_of_sector {P : ℝ[X]} (hP : P ≠ 0)
    (h : (P.map (algebraMap ℝ ℂ)).roots.countP (· ∉ sector) ≤ 1) :
    P.signVariations ≤ 1 := by
  obtain ⟨c, k, Q, hc, hQm, hQ0, hPeq⟩ := exists_C_mul_X_pow_mul hP
  have hsv : P.signVariations = ((X : ℝ[X]) ^ k * Q).signVariations := by
    rw [hPeq, signVariations_C_mul _ hc]
  have hQne : Q ≠ 0 := hQm.ne_zero
  -- transfer the root count from `P` to `Q`
  have hdvd : Q.map (algebraMap ℝ ℂ) ∣ P.map (algebraMap ℝ ℂ) :=
    ⟨(C c * X ^ k).map (algebraMap ℝ ℂ), by
      rw [← Polynomial.map_mul, hPeq]; ring_nf⟩
  have hcount : (Q.map (algebraMap ℝ ℂ)).roots.countP (· ∉ sector) ≤ 1 :=
    le_trans (Multiset.countP_le_of_le _ (roots.le_of_dvd (map_ne_zero hP) hdvd)) h
  by_cases hex : ∃ w ∈ (Q.map (algebraMap ℝ ℂ)).roots, w ∉ sector
  · -- one root `w` outside the sector; it must be real and positive
    obtain ⟨w, hwmem, hwout⟩ := hex
    have hwim : w.im = 0 := by
      by_contra him
      have hwroot : aeval w Q = 0 := by
        rw [mem_roots_map hQne] at hwmem
        rw [aeval_def]
        exact hwmem
      have hconjmem : (starRingEnd ℂ) w ∈ (Q.map (algebraMap ℝ ℂ)).roots := by
        rw [mem_roots_map hQne, ← aeval_def, aeval_conj, hwroot, map_zero]
      have hconjout : (starRingEnd ℂ) w ∉ sector := fun hmem => hwout (by
        have h2 := conj_mem_sector hmem
        rwa [Complex.conj_conj] at h2)
      have hne : w ≠ (starRingEnd ℂ) w :=
        fun heq => him (Complex.conj_eq_iff_im.mp heq.symm)
      -- two distinct roots outside the sector contradict the count bound
      have hwf : w ∈ (Q.map (algebraMap ℝ ℂ)).roots.filter (· ∉ sector) :=
        Multiset.mem_filter.mpr ⟨hwmem, hwout⟩
      have hcf : (starRingEnd ℂ) w ∈
          ((Q.map (algebraMap ℝ ℂ)).roots.filter (· ∉ sector)).erase w := by
        rw [Multiset.mem_erase_of_ne (Ne.symm hne)]
        exact Multiset.mem_filter.mpr ⟨hconjmem, hconjout⟩
      have h2 : 2 ≤ (Q.map (algebraMap ℝ ℂ)).roots.countP (· ∉ sector) := by
        rw [Multiset.countP_eq_card_filter, ← Multiset.cons_erase hwf, Multiset.card_cons]
        have := Multiset.card_pos_iff_exists_mem.mpr ⟨_, hcf⟩
        omega
      omega
    -- `w` is the positive real `r`; peel the factor `X - C r` from `Q`
    have hwr : w = ((w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hwim]
    have haevalr : aeval w.re Q = 0 := by
      have h1 : aeval w Q = 0 := by
        rw [mem_roots_map hQne] at hwmem
        rw [aeval_def]
        exact hwmem
      rw [hwr, ← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval,
        Complex.coe_algebraMap, Complex.ofReal_eq_zero] at h1
      exact h1
    obtain ⟨M, hM⟩ : (X - C w.re) ∣ Q :=
      dvd_iff_isRoot.mpr (by rwa [IsRoot, ← coe_aeval_eq_eval])
    have hMm : M.Monic := by
      rw [Monic, ← leadingCoeff_monic_mul (monic_X_sub_C w.re), ← hM]
      exact hQm
    have hM0 : M.coeff 0 ≠ 0 := fun h0 => hQ0 (by rw [hM, mul_coeff_zero, h0, mul_zero])
    -- the remaining roots all lie in the sector
    have hmapQeq : Q.map (algebraMap ℝ ℂ) = (X - C (w.re : ℂ)) * M.map (algebraMap ℝ ℂ) := by
      rw [hM, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, Complex.coe_algebraMap]
    have hrootsQ : (Q.map (algebraMap ℝ ℂ)).roots =
        ((w.re : ℝ) : ℂ) ::ₘ (M.map (algebraMap ℝ ℂ)).roots := by
      rw [hmapQeq, roots_mul (hmapQeq ▸ map_ne_zero hQne), roots_X_sub_C,
        Multiset.singleton_add]
    have hMcount : (M.map (algebraMap ℝ ℂ)).roots.countP (· ∉ sector) = 0 := by
      rw [hrootsQ, Multiset.countP_cons, if_pos (hwr ▸ hwout)] at hcount
      omega
    have hMplc : PosLogConcave M := by
      apply posLogConcave_of_aeval_mem_sector hMm hM0
      intro z hz
      by_contra hzout
      exact Multiset.countP_eq_zero.mp hMcount z
        ((mem_roots_map hMm.ne_zero).mpr (by rwa [← aeval_def])) hzout
    rw [hsv, hM]
    exact hMplc.signVariations_X_pow_mul_X_sub_C_mul w.re k
  · -- all roots inside the sector: `Q` is `PosLogConcave`, so no variations
    push Not at hex
    have hQplc : PosLogConcave Q := by
      apply posLogConcave_of_aeval_mem_sector hQm hQ0
      intro z hz
      exact hex z ((mem_roots_map hQne).mpr (by rwa [← aeval_def]))
    rw [hsv, hQplc.signVariations_X_pow_mul]
    exact zero_le_one

/-- **The λ = 0 case of the sector variation bound.** If every complex root of
the nonzero real polynomial `P` lies in the sector, its coefficients have no
sign variation at all. -/
theorem signVariations_eq_zero_of_sector {P : ℝ[X]} (hP : P ≠ 0)
    (h : (P.map (algebraMap ℝ ℂ)).roots.countP (· ∉ sector) = 0) :
    P.signVariations = 0 := by
  obtain ⟨c, k, Q, hc, hQm, hQ0, hPeq⟩ := exists_C_mul_X_pow_mul hP
  have hQne : Q ≠ 0 := hQm.ne_zero
  have hdvd : Q.map (algebraMap ℝ ℂ) ∣ P.map (algebraMap ℝ ℂ) :=
    ⟨(C c * X ^ k).map (algebraMap ℝ ℂ), by
      rw [← Polynomial.map_mul, hPeq]; ring_nf⟩
  have hcount : (Q.map (algebraMap ℝ ℂ)).roots.countP (· ∉ sector) = 0 :=
    Nat.le_zero.mp (h ▸ Multiset.countP_le_of_le _ (roots.le_of_dvd (map_ne_zero hP) hdvd))
  have hQplc : PosLogConcave Q := by
    apply posLogConcave_of_aeval_mem_sector hQm hQ0
    intro z hz
    by_contra hzout
    exact Multiset.countP_eq_zero.mp hcount z
      ((mem_roots_map hQne).mpr (by rwa [← aeval_def])) hzout
  rw [hPeq, signVariations_C_mul _ hc, hQplc.signVariations_X_pow_mul]

/-! ### Sharpness

The naive per-factor bound `signVariations ((X² + bX + c) * P) ≤ signVariations P`
for sector quadratics is false, and so is the general count bound
"`signVariations ≤` number of roots outside the sector":

`(X² + X + 1) * (X² - (3/2)X + 1) = X⁴ - (1/2)X³ + (1/2)X² - (1/2)X + 1`

has four sign variations `(+,-,+,-,+)`, while only the two roots of
`X² - (3/2)X + 1` (which lie at `re = 3/4 > 0`) are outside the sector; the
roots of `X² + X + 1` are `exp (± 2πi/3)`, on the sector boundary. Hence the
correct statement is the threshold form proved above (`λ ≤ 1` roots outside
give at most one variation), not a variation count bounded by the number of
outside roots. -/

/-- The product underlying the sharpness example, cleared of denominators
(twice the monic quartic): the coefficient signs `(+,-,+,-,+)` give four sign
variations. -/
example : ((X ^ 2 + X + 1) * (2 * X ^ 2 - 3 * X + 2) : ℝ[X])
    = 2 * X ^ 4 - X ^ 3 + X ^ 2 - X + 2 := by
  ring

end Polynomial
