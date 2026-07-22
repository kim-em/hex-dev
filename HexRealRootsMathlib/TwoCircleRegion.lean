/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib

public section

/-!
# The two-circle region geometry

For a real interval `(a, b)` with `a < b`, the classical *two-circle region* is
the union of the two open discs whose boundaries pass through `a` and `b` with
centres `(a+b)/2 ± i·(b−a)/(2√3)` and radius `(b−a)/√3` (the inscribed-angle
`2π/3` construction over the segment). Rather than working with the discs
directly we use the algebraic *Möbius seed*

`s = (w − a) · conj (b − w)`

and characterise membership by the sign of `s.re` and the size of `s.im`. Write
`x = w.re`, `y = w.im`, `h = b − a`, `X = x − (a+b)/2`; then

`s.re = h²/4 − X² − y²`,  `s.im = h · y`.

The region is `InTwoCircle a b w`, the **open** condition
`0 < s.re ∨ 3·s.re² < s.im²`, whose complement is the **closed** sector
condition `s.re ≤ 0 ∧ s.im² ≤ 3·s.re²`.

Main results:

* `not_inTwoCircle_iff_mem_sector` — for `w ≠ b`, `w` is *outside* the region
  iff the Möbius image `(w − a)/(b − w)` lies in the closed sector
  `S = {z | z.re ≤ −‖z‖/2}` (the consumer contract for the variation count).
  This is the `Complex.abs`-free form of the sector `{z | z.re ≤ −Complex.abs z / 2}`;
  in this Mathlib the complex modulus is the norm `‖·‖`.
* `dist_le` — the region is enclosed in the ball of radius `√3·(b−a)/2` about
  the midpoint (the ball bound used for the coefficient estimate).
* `inTwoCircle_conj` — the region is symmetric under complex conjugation.
* `inTwoCircle_ofReal` — every real point of the open interval `(a, b)` lies in
  the region (placing real roots).
* `inTwoCircle_iff_disc` — the algebraic predicate is exactly the classical
  union of the two open discs (documentation that the seed characterisation is
  the two-circle region).
-/

namespace HexRealRootsMathlib
namespace TwoCircle

open Complex

/-- The **two-circle region** of the interval `(a, b)`, as an algebraic
condition on the Möbius seed `s = (w − a)·conj(b − w)`: `w` is *inside* when
`0 < s.re` or `3·s.re² < s.im²`. This is the open region; its complement is the
closed sector condition `s.re ≤ 0 ∧ s.im² ≤ 3·s.re²`. -/
def InTwoCircle (a b : ℝ) (w : ℂ) : Prop :=
  0 < ((w - a) * (starRingEnd ℂ) (b - w)).re ∨
    3 * ((w - a) * (starRingEnd ℂ) (b - w)).re ^ 2
      < ((w - a) * (starRingEnd ℂ) (b - w)).im ^ 2

/-- The closed sector `S = {z | z.re ≤ −‖z‖/2}` (half-angle `2π/3`), the target
of the Möbius image. Classically written with `Complex.abs`; here the modulus is
the norm `‖·‖`. -/
def sector : Set ℂ := {z : ℂ | z.re ≤ -‖z‖ / 2}

/-- Membership in the closed sector unfolds to the scalar inequality. Exported so
consumers can bridge this sector to `Polynomial.sector` (the identical set in the
sign-variation development) without unfolding the opaque `def` across modules. -/
theorem mem_sector {z : ℂ} : z ∈ sector ↔ z.re ≤ -‖z‖ / 2 := Iff.rfl

/-- Real part of the Möbius seed `s = (w − a)·conj(b − w)`. -/
theorem seed_re (a b : ℝ) (w : ℂ) :
    ((w - a) * (starRingEnd ℂ) (b - w)).re = (w.re - a) * (b - w.re) - w.im ^ 2 := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Imaginary part of the Möbius seed `s = (w − a)·conj(b − w)`. -/
theorem seed_im (a b : ℝ) (w : ℂ) :
    ((w - a) * (starRingEnd ℂ) (b - w)).im = w.im * (b - a) := by
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Sector membership as a scalar inequality: for real `p, q`,
`p ≤ −√(p²+q²)/2 ↔ p ≤ 0 ∧ q² ≤ 3p²`. This is the exact boundary matching that
makes the region open and the sector closed. -/
theorem sector_re_iff (p q : ℝ) :
    p ≤ -Real.sqrt (p ^ 2 + q ^ 2) / 2 ↔ p ≤ 0 ∧ q ^ 2 ≤ 3 * p ^ 2 := by
  have hs : Real.sqrt (p ^ 2 + q ^ 2) ^ 2 = p ^ 2 + q ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hn : 0 ≤ Real.sqrt (p ^ 2 + q ^ 2) := Real.sqrt_nonneg _
  constructor
  · intro h
    have hle : Real.sqrt (p ^ 2 + q ^ 2) ≤ -2 * p := by linarith
    refine ⟨by linarith, ?_⟩
    nlinarith [hs, hle, hn]
  · rintro ⟨hp, hq⟩
    have h4 : p ^ 2 + q ^ 2 ≤ (-2 * p) ^ 2 := by nlinarith
    have hle : Real.sqrt (p ^ 2 + q ^ 2) ≤ -2 * p :=
      calc Real.sqrt (p ^ 2 + q ^ 2) ≤ Real.sqrt ((-2 * p) ^ 2) := Real.sqrt_le_sqrt h4
        _ = |(-2 * p)| := Real.sqrt_sq_eq_abs _
        _ = -2 * p := abs_of_nonneg (by linarith)
    linarith

/-- **Möbius-image characterisation of the region complement.** For `w ≠ b`, the
point `w` is *outside* the two-circle region iff its Möbius image
`(w − a)/(b − w)` lies in the closed sector `S = {z | z.re ≤ −‖z‖/2}`. -/
theorem not_inTwoCircle_iff_mem_sector (a b : ℝ) (w : ℂ) (hw : w ≠ (b : ℂ)) :
    ¬ InTwoCircle a b w ↔ (w - a) / (b - w) ∈ sector := by
  have hv0 : ((b : ℂ) - w) ≠ 0 := sub_ne_zero.mpr fun h => hw h.symm
  have hN0 : 0 < Complex.normSq ((b : ℂ) - w) := Complex.normSq_pos.mpr hv0
  unfold InTwoCircle
  simp only [sector, Set.mem_setOf_eq]
  set s : ℂ := (w - (a : ℂ)) * (starRingEnd ℂ) ((b : ℂ) - w) with hsdef
  set N : ℝ := Complex.normSq ((b : ℂ) - w) with hNdef
  have hzeq : (w - (a : ℂ)) / ((b : ℂ) - w) = s / (N : ℂ) := by
    rw [hsdef, hNdef, div_eq_mul_inv (w - (a : ℂ)), Complex.inv_def, Complex.ofReal_inv,
      div_eq_mul_inv s]
    ring
  have hre : ((w - (a : ℂ)) / ((b : ℂ) - w)).re = s.re / N := by
    rw [hzeq, Complex.div_ofReal_re]
  have hnorm : ‖(w - (a : ℂ)) / ((b : ℂ) - w)‖ = ‖s‖ / N := by
    rw [hzeq, Complex.norm_div, Complex.norm_of_nonneg hN0.le]
  rw [hre, hnorm]
  simp only [not_or, not_lt]
  rw [show -(‖s‖ / N) / 2 = (-‖s‖ / 2) / N from by ring,
    div_le_div_iff_of_pos_right hN0, Complex.norm_eq_sqrt_sq_add_sq]
  exact (sector_re_iff s.re s.im).symm

/-- The right endpoint `b` is not in the region (the seed vanishes there); the
Möbius image is undefined, so `b`-roots are treated separately. -/
theorem not_inTwoCircle_self (a b : ℝ) : ¬ InTwoCircle a b (b : ℂ) := by
  simp only [InTwoCircle, seed_re, seed_im, Complex.ofReal_re, Complex.ofReal_im,
    not_or, not_lt]
  constructor <;> nlinarith

/-- Scalar form of the ball bound: from the region disjunction on `s.re = h²/4 − T`
and `s.im² = h²·y²`, the squared distance `T` is at most `3h²/4`. -/
theorem ball_bound_real {h y2 T : ℝ} (hy2 : 0 ≤ y2) (hyT : y2 ≤ T)
    (hdisj : 0 < h ^ 2 / 4 - T ∨ 3 * (h ^ 2 / 4 - T) ^ 2 < h ^ 2 * y2) :
    T ≤ 3 * h ^ 2 / 4 := by
  rcases hdisj with h1 | h2
  · nlinarith [sq_nonneg h]
  · have hle : h ^ 2 * y2 ≤ h ^ 2 * T := by nlinarith [sq_nonneg h, hyT]
    have hkey : 3 * (h ^ 2 / 4 - T) ^ 2 < h ^ 2 * T := lt_of_lt_of_le h2 hle
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [hkey, hcon, sq_nonneg h]

/-- **Ball bound.** The two-circle region of `(a, b)` (`a ≤ b`) is contained in
the closed ball of radius `√3·(b−a)/2` about the midpoint `(a+b)/2`. -/
theorem dist_le (a b : ℝ) (w : ℂ) (hab : a ≤ b) (hw : InTwoCircle a b w) :
    dist w (((a + b) / 2 : ℝ) : ℂ) ≤ Real.sqrt 3 * (b - a) / 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set T : ℝ := (w.re - (a + b) / 2) ^ 2 + w.im ^ 2 with hT
  have hsre : ((w - (a : ℂ)) * (starRingEnd ℂ) ((b : ℂ) - w)).re = (b - a) ^ 2 / 4 - T := by
    rw [seed_re, hT]; ring
  have hsim2 : ((w - (a : ℂ)) * (starRingEnd ℂ) ((b : ℂ) - w)).im ^ 2 = (b - a) ^ 2 * w.im ^ 2 := by
    rw [seed_im]; ring
  have hTbound : T ≤ 3 * (b - a) ^ 2 / 4 := by
    have hdisj : 0 < (b - a) ^ 2 / 4 - T ∨ 3 * ((b - a) ^ 2 / 4 - T) ^ 2 < (b - a) ^ 2 * w.im ^ 2 := by
      unfold InTwoCircle at hw
      rw [hsre, hsim2] at hw
      exact hw
    exact ball_bound_real (h := b - a) (sq_nonneg w.im) (by rw [hT]; nlinarith [sq_nonneg (w.re - (a + b) / 2)]) hdisj
  rw [Complex.dist_eq_re_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  rw [show (w.re - (a + b) / 2) ^ 2 + w.im ^ 2 = T from hT.symm, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [hTbound, h3, hab]

/-- **Conjugation symmetry.** The two-circle region is invariant under complex
conjugation (the seed conjugates, so `s.re` is preserved and `s.im²` is
unchanged). -/
theorem inTwoCircle_conj (a b : ℝ) (w : ℂ) :
    InTwoCircle a b (starRingEnd ℂ w) ↔ InTwoCircle a b w := by
  simp only [InTwoCircle, seed_re, seed_im, Complex.conj_re, Complex.conj_im, neg_sq,
    neg_mul]

/-- **Real membership.** Every real point of the open interval `(a, b)` lies in
the two-circle region. -/
theorem inTwoCircle_ofReal (a b w : ℝ) (h1 : a < w) (h2 : w < b) :
    InTwoCircle a b (w : ℂ) := by
  left
  rw [seed_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)]

/-! ### Sanity checks on concrete points (`a = 0`, `b = 2`). -/

-- Midpoint `w = 1`: `s = 1` is real positive, so in-region.
example : InTwoCircle 0 2 1 := by
  left; rw [seed_re]; norm_num

-- `w = 1 + I/2`: `s.re = 1 - 1/4 = 3/4 > 0`, so in-region.
example : InTwoCircle 0 2 (⟨1, 1 / 2⟩ : ℂ) := by
  left; rw [seed_re]; norm_num

-- `w = 3` (real, right of the interval): `s = -3` is real negative, so out.
example : ¬ InTwoCircle 0 2 3 := by
  simp only [InTwoCircle, seed_re, seed_im, not_or, not_lt]
  norm_num

-- Endpoint `w = 0 = a`: `s = 0`, so out (boundary).
example : ¬ InTwoCircle 0 2 0 := by
  simp only [InTwoCircle, seed_re, seed_im, not_or, not_lt]
  norm_num

/-- The two disc centres `(a+b)/2 ± i·(b−a)/(2√3)`. -/
noncomputable def centrePos (a b : ℝ) : ℂ :=
  ((a + b) / 2 : ℝ) + Complex.I * ((b - a) / (2 * Real.sqrt 3) : ℝ)
noncomputable def centreNeg (a b : ℝ) : ℂ :=
  ((a + b) / 2 : ℝ) - Complex.I * ((b - a) / (2 * Real.sqrt 3) : ℝ)

/-- The common disc radius `(b−a)/√3`. -/
noncomputable def discRadius (a b : ℝ) : ℝ := (b - a) / Real.sqrt 3

@[simp] theorem centrePos_re (a b : ℝ) : (centrePos a b).re = (a + b) / 2 := by
  simp only [centrePos, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero]

@[simp] theorem centrePos_im (a b : ℝ) : (centrePos a b).im = (b - a) / (2 * Real.sqrt 3) := by
  simp only [centrePos, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add]

@[simp] theorem centreNeg_re (a b : ℝ) : (centreNeg a b).re = (a + b) / 2 := by
  simp only [centreNeg, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, sub_self]

@[simp] theorem centreNeg_im (a b : ℝ) : (centreNeg a b).im = -((b - a) / (2 * Real.sqrt 3)) := by
  simp only [centreNeg, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add, zero_sub]

/-- `dist w c < discRadius a b` as a squared coordinate inequality. -/
theorem dist_lt_discRadius_iff (a b : ℝ) (w c : ℂ) (hρ : 0 < discRadius a b) :
    dist w c < discRadius a b ↔ (w.re - c.re) ^ 2 + (w.im - c.im) ^ 2 < (b - a) ^ 2 / 3 := by
  have hρ2 : discRadius a b ^ 2 = (b - a) ^ 2 / 3 := by
    rw [discRadius, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [Complex.dist_eq_re_im, Real.sqrt_lt' hρ, hρ2]

/-- The pure-scalar core of the disc characterisation: for reals `R, c`, the
open-region disjunction on `R` (a stand-in for `s.re`) matches the union of the
two half-plane conditions coming from the two discs. -/
theorem region_iff_disc_real (R c : ℝ) :
    (0 < R ∨ R ^ 2 < c ^ 2) ↔ (-R < c ∨ -R < -c) := by
  constructor
  · rintro (h | h)
    · rcases le_or_gt 0 c with hc | hc
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rcases le_or_gt 0 c with hc | hc
      · exact Or.inl (by nlinarith [h, hc])
      · exact Or.inr (by nlinarith [h, hc])
  · rintro (h | h)
    · rcases lt_or_ge 0 R with hR | hR
      · exact Or.inl hR
      · exact Or.inr (by nlinarith [h, hR])
    · rcases lt_or_ge 0 R with hR | hR
      · exact Or.inl hR
      · exact Or.inr (by nlinarith [h, hR])

/-- **Disc characterisation.** The algebraic region is exactly the classical
union of the two open discs through `a` and `b` with centres
`(a+b)/2 ± i·(b−a)/(2√3)` and radius `(b−a)/√3`. -/
theorem inTwoCircle_iff_disc (a b : ℝ) (w : ℂ) (hab : a ≤ b) :
    InTwoCircle a b w ↔
      dist w (centrePos a b) < discRadius a b ∨ dist w (centreNeg a b) < discRadius a b := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3pos
  rcases eq_or_lt_of_le hab with rfl | hlt
  · -- Degenerate `a = b`: both the region and the (radius-0) disc union are empty.
    have hL : ¬ InTwoCircle a a w := by
      unfold InTwoCircle
      rw [seed_re, seed_im]
      rintro (h | h)
      · nlinarith [sq_nonneg (w.re - a), sq_nonneg w.im]
      · nlinarith [sq_nonneg ((w.re - a) * (a - w.re) - w.im ^ 2)]
    have hRHS : ¬ (dist w (centrePos a a) < discRadius a a ∨
        dist w (centreNeg a a) < discRadius a a) := by
      have h0 : discRadius a a = 0 := by rw [discRadius]; simp
      rw [h0]
      rintro (h | h) <;> exact absurd h (not_lt.mpr dist_nonneg)
    exact iff_of_false hL hRHS
  · -- Main case `a < b`.
    have hρ : 0 < discRadius a b := by
      rw [discRadius]; exact div_pos (by linarith) hs3pos
    rw [dist_lt_discRadius_iff a b w (centrePos a b) hρ,
      dist_lt_discRadius_iff a b w (centreNeg a b) hρ,
      centrePos_re, centrePos_im, centreNeg_re, centreNeg_im]
    have hk2 : ((b - a) / (2 * Real.sqrt 3)) ^ 2 = (b - a) ^ 2 / 12 := by
      rw [div_pow, mul_pow, hs3]; ring
    have hcross : 2 * w.im * ((b - a) / (2 * Real.sqrt 3)) = w.im * (b - a) / Real.sqrt 3 := by
      field_simp
    have esqP : (w.im - (b - a) / (2 * Real.sqrt 3)) ^ 2
        = w.im ^ 2 - w.im * (b - a) / Real.sqrt 3 + (b - a) ^ 2 / 12 := by
      rw [sub_sq, hk2, hcross]
    have esqN : (w.im - -((b - a) / (2 * Real.sqrt 3))) ^ 2
        = w.im ^ 2 + w.im * (b - a) / Real.sqrt 3 + (b - a) ^ 2 / 12 := by
      rw [sub_neg_eq_add, add_sq, hk2, hcross]
    set c : ℝ := w.im * (b - a) / Real.sqrt 3 with hc
    set R : ℝ := (b - a) ^ 2 / 4 - ((w.re - (a + b) / 2) ^ 2 + w.im ^ 2) with hRdef
    have keyPos : (w.re - (a + b) / 2) ^ 2 + (w.im - (b - a) / (2 * Real.sqrt 3)) ^ 2
        - (b - a) ^ 2 / 3 = -R - c := by
      rw [esqP, hRdef, hc]; ring
    have keyNeg : (w.re - (a + b) / 2) ^ 2 + (w.im - -((b - a) / (2 * Real.sqrt 3))) ^ 2
        - (b - a) ^ 2 / 3 = -R + c := by
      rw [esqN, hRdef, hc]; ring
    have hdiscPos : ((w.re - (a + b) / 2) ^ 2 + (w.im - (b - a) / (2 * Real.sqrt 3)) ^ 2
        < (b - a) ^ 2 / 3) ↔ -R < c := by
      constructor <;> intro h <;> linarith [keyPos]
    have hdiscNeg : ((w.re - (a + b) / 2) ^ 2 + (w.im - -((b - a) / (2 * Real.sqrt 3))) ^ 2
        < (b - a) ^ 2 / 3) ↔ -R < -c := by
      constructor <;> intro h <;> linarith [keyNeg]
    rw [hdiscPos, hdiscNeg, ← region_iff_disc_real R c]
    have hRs : ((w - (a : ℂ)) * (starRingEnd ℂ) ((b : ℂ) - w)).re = R := by
      rw [seed_re, hRdef]; ring
    have hcs : ((w - (a : ℂ)) * (starRingEnd ℂ) ((b : ℂ) - w)).im ^ 2 = 3 * c ^ 2 := by
      rw [seed_im, hc, div_pow, hs3]; ring
    unfold InTwoCircle
    rw [hRs, hcs]
    exact or_congr_right (by constructor <;> intro h <;> linarith)

end TwoCircle
end HexRealRootsMathlib
