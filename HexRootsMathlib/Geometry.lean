/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Basic
public import Mathlib.Analysis.Complex.Norm

public section

/-!
# Geometry for complex root isolation

This module relates the executable modulus bounds and dyadic squares from
`HexRoots` to the Euclidean and sup-norm geometry of `ℂ`.
-/

namespace HexRootsMathlib

noncomputable section

namespace GaussDyadic

/-- The real value of the executable lower modulus bound. -/
@[simp] theorem toReal_lo (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.lo z) =
      max |(toComplex z).re| |(toComplex z).im| := by
  simp [Hex.GaussDyadic.lo]

/-- The real value of the executable upper modulus bound. -/
@[simp] theorem toReal_hi (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.hi z) =
      |(toComplex z).re| + |(toComplex z).im| := by
  simp [Hex.GaussDyadic.hi]

/-- The executable `lo` bound is below the complex modulus. -/
theorem lo_le_norm (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.lo z) ≤ ‖toComplex z‖ := by
  rw [toReal_lo]
  exact max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

/-- The complex modulus is at most `√2` times the executable `lo` bound. -/
theorem norm_le_sqrt_two_mul_lo (z : Hex.GaussDyadic) :
    ‖toComplex z‖ ≤ √2 * Dyadic.toReal (Hex.GaussDyadic.lo z) := by
  simpa only [toReal_lo] using Complex.norm_le_sqrt_two_mul_max (toComplex z)

/-- The complex modulus is below the executable `hi` bound. -/
theorem norm_le_hi (z : Hex.GaussDyadic) :
    ‖toComplex z‖ ≤ Dyadic.toReal (Hex.GaussDyadic.hi z) := by
  rw [toReal_hi]
  exact Complex.norm_le_abs_re_add_abs_im _

/-- The executable `hi` bound is at most `√2` times the complex modulus. -/
theorem hi_le_sqrt_two_mul_norm (z : Hex.GaussDyadic) :
    Dyadic.toReal (Hex.GaussDyadic.hi z) ≤ √2 * ‖toComplex z‖ := by
  rw [toReal_hi]
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  have hre : |(toComplex z).re| ^ 2 = (toComplex z).re ^ 2 := sq_abs _
  have him : |(toComplex z).im| ^ 2 = (toComplex z).im ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|(toComplex z).re| - |(toComplex z).im|)]

end GaussDyadic

/-! ### Rational bounds for `√2` -/

/-- The executable lower approximation `181/128` is strictly below `√2`. -/
theorem sqrt2Lo_lt_sqrt_two : Dyadic.toReal Hex.sqrt2Lo < √2 := by
  rw [← sq_lt_sq₀ (by
    simp [Hex.sqrt2Lo, Dyadic.toReal_ofIntWithPrec]
    positivity) (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
  have h := Dyadic.toReal_lt_toReal_iff.mpr Hex.sqrt2Lo_sq_lt_two
  have htwo : Dyadic.toReal (2 : _root_.Dyadic) = (2 : ℝ) := by
    change Dyadic.toReal (.ofInt 2) = (2 : ℝ)
    simp
  rw [htwo] at h
  simpa only [Dyadic.toReal_mul, pow_two] using h

/-- The executable upper approximation `1449/1024` is strictly above `√2`. -/
theorem sqrt_two_lt_sqrt2Hi : √2 < Dyadic.toReal Hex.sqrt2Hi := by
  rw [← sq_lt_sq₀ (Real.sqrt_nonneg _) (by
    simp [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    positivity), Real.sq_sqrt (by norm_num)]
  have h := Dyadic.toReal_lt_toReal_iff.mpr Hex.two_lt_sqrt2Hi_sq
  have htwo : Dyadic.toReal (2 : _root_.Dyadic) = (2 : ℝ) := by
    change Dyadic.toReal (.ofInt 2) = (2 : ℝ)
    simp
  rw [htwo] at h
  simpa only [Dyadic.toReal_mul, pow_two] using h

/-! ### Sup-norm squares and circumscribed discs -/

/-- The sup norm on `ℂ`, used to view an axis-aligned square as a ball. -/
@[expose] def supNorm (z : ℂ) : ℝ := max |z.re| |z.im|

/-- The distance associated to `supNorm`. -/
@[expose] def supDist (z w : ℂ) : ℝ := supNorm (z - w)

/-- A closed sup-norm ball in `ℂ`. -/
@[expose] def supClosedBall (c : ℂ) (r : ℝ) : Set ℂ :=
  {z | supDist z c ≤ r}

namespace DyadicSquare

/-
These names deliberately mirror `Hex.DyadicSquare.center` and `halfWidth`.
Dot notation on `s : Hex.DyadicSquare` selects the executable definitions;
the Mathlib interpretations use the explicit `DyadicSquare.*` prefix.
-/

/-- The complex centre of a dyadic square. -/
@[expose] def center (s : Hex.DyadicSquare) : ℂ :=
  GaussDyadic.toComplex s.center

/-- The real half-width of a dyadic square. -/
@[expose] def halfWidth (s : Hex.DyadicSquare) : ℝ :=
  Dyadic.toReal s.halfWidth

/-- The Euclidean radius of the square's circumscribed disc. -/
@[expose] def radius (s : Hex.DyadicSquare) : ℝ :=
  halfWidth s * √2

/-- The closed axis-aligned square represented by `s`. -/
@[expose] def closedSquare (s : Hex.DyadicSquare) : Set ℂ :=
  supClosedBall (center s) (halfWidth s)

/-- The open circumscribed disc of `s`. -/
@[expose] def disc (s : Hex.DyadicSquare) : Set ℂ :=
  Metric.ball (center s) (radius s)

/-- The closed circumscribed disc of `s`. -/
@[expose] def closedDisc (s : Hex.DyadicSquare) : Set ℂ :=
  Metric.closedBall (center s) (radius s)

@[simp] theorem center_eq (s : Hex.DyadicSquare) :
    center s = GaussDyadic.toComplex s.center := rfl

@[simp] theorem halfWidth_eq (s : Hex.DyadicSquare) :
    halfWidth s = (2 : ℝ) ^ (-s.prec) := by
  simp [halfWidth, Hex.DyadicSquare.halfWidth]

@[simp] theorem radius_eq (s : Hex.DyadicSquare) :
    radius s = (2 : ℝ) ^ (-s.prec) * √2 := by
  simp [radius]

@[simp] theorem disc_eq (s : Hex.DyadicSquare) :
    disc s = Metric.ball (center s) ((2 : ℝ) ^ (-s.prec) * √2) := by
  simp [disc]

theorem closedSquare_eq_supClosedBall (s : Hex.DyadicSquare) :
    closedSquare s = supClosedBall (center s) (halfWidth s) := rfl

/-- The centre belongs to its closed square. -/
theorem center_mem_closedSquare (s : Hex.DyadicSquare) : center s ∈ closedSquare s := by
  rw [closedSquare, supClosedBall, Set.mem_setOf_eq, supDist, sub_self, supNorm]
  simp only [Complex.zero_re, abs_zero, Complex.zero_im, max_self]
  rw [halfWidth_eq]
  exact (zpow_pos (by norm_num) _).le

theorem radiusLo_eq (s : Hex.DyadicSquare) :
    Dyadic.toReal s.radiusLo = halfWidth s * Dyadic.toReal Hex.sqrt2Lo := by
  simp only [Hex.DyadicSquare.radiusLo, Hex.sqrt2Lo, Dyadic.toReal_ofIntWithPrec,
    halfWidth_eq]
  rw [show -(s.prec + 7) = -s.prec + (-7) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem radiusHi_eq (s : Hex.DyadicSquare) :
    Dyadic.toReal s.radiusHi = halfWidth s * Dyadic.toReal Hex.sqrt2Hi := by
  simp only [Hex.DyadicSquare.radiusHi, Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec,
    halfWidth_eq]
  rw [show -(s.prec + 10) = -s.prec + (-10) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem radiusLo_lt_radius (s : Hex.DyadicSquare) :
    Dyadic.toReal s.radiusLo < radius s := by
  rw [radiusLo_eq, radius]
  apply mul_lt_mul_of_pos_left sqrt2Lo_lt_sqrt_two
  rw [halfWidth_eq]
  exact zpow_pos (by norm_num) _

theorem radius_lt_radiusHi (s : Hex.DyadicSquare) :
    radius s < Dyadic.toReal s.radiusHi := by
  rw [radiusHi_eq, radius]
  apply mul_lt_mul_of_pos_left sqrt_two_lt_sqrt2Hi
  rw [halfWidth_eq]
  exact zpow_pos (by norm_num) _

/-- The square is contained in its closed circumscribed Euclidean disc. -/
theorem closedSquare_subset_closedDisc (s : Hex.DyadicSquare) :
    closedSquare s ⊆ closedDisc s := by
  intro z hz
  rw [closedSquare, supClosedBall, Set.mem_setOf_eq] at hz
  rw [closedDisc, Metric.mem_closedBall, Complex.dist_eq]
  calc
    ‖z - center s‖ ≤ √2 * supNorm (z - center s) :=
      Complex.norm_le_sqrt_two_mul_max (z - center s)
    _ ≤ √2 * halfWidth s := mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)
    _ = radius s := by rw [radius, mul_comm]

/-- The closed square lies in the open disc obtained from the executable
strict upper radius bound. -/
theorem closedSquare_subset_ball_radiusHi (s : Hex.DyadicSquare) :
    closedSquare s ⊆ Metric.ball (center s) (Dyadic.toReal s.radiusHi) := by
  intro z hz
  have hclosed := closedSquare_subset_closedDisc s hz
  rw [closedDisc, Metric.mem_closedBall] at hclosed
  rw [Metric.mem_ball]
  exact hclosed.trans_lt (radius_lt_radiusHi s)

end DyadicSquare

end

end HexRootsMathlib
