/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealAlgebraic.Norm
public import HexRealAlgebraicMathlib.Complex
public section

/-! Exact real-valued complex norms and their field laws. -/
namespace Hex.AlgebraicNumber

/-- The packed product is the complex squared norm. -/
@[simp] theorem normSq_toReal (a : AlgebraicNumber) :
    a.normSq.toReal = Complex.normSq a.toComplex := by
  have hr : (a * a.conj).isReal = true := by
    rw [isReal_iff, mul_toComplex, conj_toComplex, Complex.mul_conj]
    rfl
  change (RealAlgebraicNumber.Internal.pack (a * a.conj)).toAlgebraic.toComplex.re = _
  rw [RealAlgebraicNumber.pack_val _ hr, mul_toComplex, conj_toComplex, Complex.mul_conj]
  rfl

/-- Squared norms are nonnegative. -/
theorem normSq_nonneg (a : AlgebraicNumber) : 0 ≤ a.normSq := by
  rw [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal, normSq_toReal]
  exact Complex.normSq_nonneg _

/-- The executable modulus agrees with the complex norm. -/
@[simp] theorem abs_toReal (a : AlgebraicNumber) : a.abs.toReal = ‖a.toComplex‖ := by
  unfold abs
  split
  · rename_i hr
    calc
      _ = |a.toComplex.re| := RealAlgebraicNumber.abs_toReal (RealAlgebraicNumber.ofAlgebraic a hr)
      _ = ‖a.toComplex‖ := by
        conv_rhs => rw [← ofReal_re a hr, Complex.norm_real, Real.norm_eq_abs]
  · rw [RealAlgebraicNumber.sqrt?_eq_some a.normSq (normSq_nonneg a),
      RealAlgebraicNumber.sqrt_toReal, normSq_toReal]
    exact Complex.norm_def _ |>.symm

/-- Moduli are nonnegative. -/
theorem abs_nonneg (a : AlgebraicNumber) : 0 ≤ a.abs := by
  rw [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal, abs_toReal]
  exact norm_nonneg _

@[simp] theorem normSq_eq_zero (a : AlgebraicNumber) : a.normSq = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply toComplex_injective
    rw [zero_toComplex]
    apply Complex.normSq_eq_zero.mp
    simpa using congrArg RealAlgebraicNumber.toReal h
  · rintro rfl
    apply RealAlgebraicNumber.toReal_injective
    simp

@[simp] theorem abs_eq_zero (a : AlgebraicNumber) : a.abs = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply toComplex_injective
    rw [zero_toComplex]
    apply norm_eq_zero.mp
    simpa using congrArg RealAlgebraicNumber.toReal h
  · rintro rfl
    apply RealAlgebraicNumber.toReal_injective
    simp

@[simp] theorem normSq_conj (a : AlgebraicNumber) : a.conj.normSq = a.normSq := by
  apply RealAlgebraicNumber.toReal_injective
  simp [conj_toComplex]

@[simp] theorem abs_conj (a : AlgebraicNumber) : a.conj.abs = a.abs := by
  apply RealAlgebraicNumber.toReal_injective
  simp [conj_toComplex]

@[simp] theorem normSq_mul (a b : AlgebraicNumber) : (a * b).normSq = a.normSq * b.normSq := by
  apply RealAlgebraicNumber.toReal_injective
  simp [mul_toComplex, Complex.normSq_mul]

@[simp] theorem abs_mul (a b : AlgebraicNumber) : (a * b).abs = a.abs * b.abs := by
  apply RealAlgebraicNumber.toReal_injective
  simp [mul_toComplex]

/-- Squaring the modulus recovers the squared norm. -/
@[simp] theorem abs_sq (a : AlgebraicNumber) : a.abs ^ 2 = a.normSq := by
  apply RealAlgebraicNumber.toReal_injective
  change (RealAlgebraicNumber.natPow a.abs 2).toReal = _
  rw [RealAlgebraicNumber.natPow_toReal, abs_toReal, normSq_toReal, Complex.sq_norm]

@[simp] theorem abs_ofReal (a : RealAlgebraicNumber) : (ofReal a).abs = a.abs := by
  apply RealAlgebraicNumber.toReal_injective
  rw [abs_toReal, ofReal_toComplex, Complex.norm_real, Real.norm_eq_abs,
    RealAlgebraicNumber.abs_toReal]

/-- info: 'Hex.AlgebraicNumber.abs_toReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_toReal

end Hex.AlgebraicNumber
