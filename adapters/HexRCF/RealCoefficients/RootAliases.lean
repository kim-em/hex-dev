/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Coefficients
public import HexNumberFieldMathlib.Radical

public section

namespace Hex.RCF.RealCoefficients.Coefficients

private theorem radical_value (a : RealAlgebraicNumber) (n : Nat) (ha : 0 ≤ a) :
    (a.toAlgebraic.nthRoot n).toComplex = ((a.toReal ^ (1 / (n : ℝ)) : ℝ) : ℂ) := by
  have nonneg : 0 ≤ a.toReal := by
    simpa only [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal] using ha
  rw [AlgebraicNumber.nthRoot_toComplex, ← RealAlgebraicNumber.ofReal_toReal,
    Complex.ofReal_cpow nonneg]
  simp only [one_div, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The existing principal radical, packaged with its proved real embedding.
The nonnegative-base condition selects exactly Mathlib's real-power branch.
Index zero retains the underlying total convention, giving one. -/
@[expose] def root (a : RealAlgebraicNumber) (n : Nat) (ha : 0 ≤ a) : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic (a.toAlgebraic.nthRoot n) (by
    rw [AlgebraicNumber.isReal_iff, radical_value a n ha]
    rfl)

/-- Checked identification of the chosen algebraic radical with `Real.rpow`. -/
theorem root_toReal (a : RealAlgebraicNumber) (n : Nat) (ha : 0 ≤ a) :
    (root a n ha).toReal = a.toReal ^ (1 / (n : ℝ)) := by
  apply Complex.ofReal_injective
  rw [RealAlgebraicNumber.ofReal_toReal]
  exact radical_value a n ha

/-- The selected radical has the nonnegative real embedding. -/
theorem root_nonneg (a : RealAlgebraicNumber) (n : Nat) (ha : 0 ≤ a) :
    0 ≤ root a n ha := by
  rw [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal, root_toReal]
  apply Real.rpow_nonneg
  simpa only [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal] using ha

/-- For positive degree the selected radical satisfies its defining equation
in the existing algebraic-number field. -/
theorem root_pow (a : RealAlgebraicNumber) (n : Nat) (ha : 0 ≤ a) (hn : n ≠ 0) :
    root a n ha ^ n = a := by
  apply RealAlgebraicNumber.toReal_injective
  change RealAlgebraicNumber.toRealHom (root a n ha ^ n) = a.toReal
  rw [map_pow]
  change (root a n ha).toReal ^ n = a.toReal
  rw [root_toReal, one_div]
  apply Real.rpow_inv_natCast_pow _ hn
  simpa only [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal] using ha

/-- Square-root notation is the degree-two instance of the same chosen root. -/
theorem root_two (a : RealAlgebraicNumber) (ha : 0 ≤ a) :
    (root a 2 ha).toReal = Real.sqrt a.toReal := by
  rw [root_toReal, Real.sqrt_eq_rpow]
  norm_num

end Hex.RCF.RealCoefficients.Coefficients
