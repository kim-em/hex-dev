/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealAlgebraic.Complex
public import HexRealAlgebraicMathlib.Order
public import HexNumberFieldMathlib.Conjugate
public import HexNumberFieldMathlib.Radical
public import HexRealAlgebraicMathlib.Sqrt
public import HexNumberFieldMathlib.Order
public section

/-! Exact real and imaginary projections and their arithmetic laws. -/
namespace Hex.AlgebraicNumber

private theorem re_formula (a : AlgebraicNumber) :
    ((a + a.conj) / 2).toComplex = (a.toComplex.re : ℂ) := by
  rw [div_toComplex, add_toComplex, conj_toComplex, ofNat_toComplex]
  exact (Complex.re_eq_add_conj a.toComplex).symm

private theorem im_formula (a : AlgebraicNumber) :
    ((a - a.conj) / (2 * I)).toComplex = (a.toComplex.im : ℂ) := by
  rw [div_toComplex, sub_toComplex, conj_toComplex, mul_toComplex,
    ofNat_toComplex, I_toComplex]
  exact (Complex.im_eq_sub_conj a.toComplex).symm

/-- The real projection denotes the complex number's real coordinate. -/
theorem re_toComplex (a : AlgebraicNumber) :
    a.re.toAlgebraic.toComplex = (a.toComplex.re : ℂ) := by
  unfold re
  split
  · rename_i h
    exact (ofReal_re a h).symm
  · have h : ((a + a.conj) / 2).isReal = true := by
      rw [isReal_iff, re_formula]
      rfl
    rw [RealAlgebraicNumber.pack_val _ h, re_formula]

/-- The imaginary projection denotes the complex number's imaginary coordinate. -/
theorem im_toComplex (a : AlgebraicNumber) :
    a.im.toAlgebraic.toComplex = (a.toComplex.im : ℂ) := by
  unfold im
  split
  · rename_i h
    rw [RealAlgebraicNumber.zero_toAlgebraic, zero_toComplex, (isReal_iff a).mp h]
    rfl
  · have h : ((a - a.conj) / (2 * I)).isReal = true := by
      rw [isReal_iff, im_formula]
      rfl
    rw [RealAlgebraicNumber.pack_val _ h, im_formula]

@[simp] theorem re_toReal (a : AlgebraicNumber) : a.re.toReal = a.toComplex.re := by
  change a.re.toAlgebraic.toComplex.re = _
  rw [re_toComplex]
  rfl

@[simp] theorem im_toReal (a : AlgebraicNumber) : a.im.toReal = a.toComplex.im := by
  change a.im.toAlgebraic.toComplex.re = _
  rw [im_toComplex]
  rfl

@[simp] theorem ofReal_toComplex (a : RealAlgebraicNumber) :
    (ofReal a).toComplex = (a.toReal : ℂ) :=
  (RealAlgebraicNumber.ofReal_toReal a).symm

/-- The checked real projection agrees with its field formula. -/
theorem re_toAlgebraic (a : AlgebraicNumber) : a.re.toAlgebraic = (a + a.conj) / 2 :=
  toComplex_injective ((re_toComplex a).trans (re_formula a).symm)

/-- The checked imaginary projection agrees with its field formula. -/
theorem im_toAlgebraic (a : AlgebraicNumber) : a.im.toAlgebraic = (a - a.conj) / (2 * I) :=
  toComplex_injective ((im_toComplex a).trans (im_formula a).symm)

@[simp] theorem re_ofReal (a : RealAlgebraicNumber) : (ofReal a).re = a := by
  apply RealAlgebraicNumber.toReal_injective
  rw [re_toReal, ofReal_toComplex]
  rfl

@[simp] theorem im_ofReal (a : RealAlgebraicNumber) : (ofReal a).im = 0 := by
  apply RealAlgebraicNumber.toReal_injective
  rw [im_toReal, ofReal_toComplex, RealAlgebraicNumber.zero_toReal]
  rfl

/-- Reassemble a number from its exact real and imaginary parts. -/
theorem re_add_im (a : AlgebraicNumber) : ofReal a.re + ofReal a.im * I = a := by
  apply toComplex_injective
  rw [add_toComplex, mul_toComplex, ofReal_toComplex, ofReal_toComplex,
    re_toReal, im_toReal, I_toComplex]
  exact Complex.re_add_im _

/-- Real and imaginary projections determine the algebraic number. -/
@[ext (iff := false)] theorem ext_re_im {a b : AlgebraicNumber} (hr : a.re = b.re) (hi : a.im = b.im) : a = b := by
  have hr' : a.toComplex.re = b.toComplex.re := by
    simpa only [re_toReal] using congrArg RealAlgebraicNumber.toReal hr
  have hi' : a.toComplex.im = b.toComplex.im := by
    simpa only [im_toReal] using congrArg RealAlgebraicNumber.toReal hi
  exact toComplex_injective (Complex.ext hr' hi')

@[simp] theorem re_conj (a : AlgebraicNumber) : a.conj.re = a.re := by
  apply RealAlgebraicNumber.toReal_injective
  simp [conj_toComplex]

@[simp] theorem im_conj (a : AlgebraicNumber) : a.conj.im = -a.im := by
  apply RealAlgebraicNumber.toReal_injective
  simp [conj_toComplex]

@[simp] theorem re_add (a b : AlgebraicNumber) : (a + b).re = a.re + b.re := by
  apply RealAlgebraicNumber.toReal_injective
  simp [add_toComplex]

@[simp] theorem im_add (a b : AlgebraicNumber) : (a + b).im = a.im + b.im := by
  apply RealAlgebraicNumber.toReal_injective
  simp [add_toComplex]

@[simp] theorem re_neg (a : AlgebraicNumber) : (-a).re = -a.re := by
  apply RealAlgebraicNumber.toReal_injective
  simp [neg_toComplex]

@[simp] theorem im_neg (a : AlgebraicNumber) : (-a).im = -a.im := by
  apply RealAlgebraicNumber.toReal_injective
  simp [neg_toComplex]

@[simp] theorem re_sub (a b : AlgebraicNumber) : (a - b).re = a.re - b.re := by
  apply RealAlgebraicNumber.toReal_injective
  simp [sub_toComplex]

@[simp] theorem im_sub (a b : AlgebraicNumber) : (a - b).im = a.im - b.im := by
  apply RealAlgebraicNumber.toReal_injective
  simp [sub_toComplex]

@[simp] theorem re_mul (a b : AlgebraicNumber) : (a * b).re = a.re * b.re - a.im * b.im := by
  apply RealAlgebraicNumber.toReal_injective
  simp [mul_toComplex, Complex.mul_re]

@[simp] theorem im_mul (a b : AlgebraicNumber) : (a * b).im = a.re * b.im + a.im * b.re := by
  apply RealAlgebraicNumber.toReal_injective
  simp [mul_toComplex, Complex.mul_im]

@[simp] theorem re_zero : (0 : AlgebraicNumber).re = 0 := by
  apply RealAlgebraicNumber.toReal_injective
  simp
@[simp] theorem im_zero : (0 : AlgebraicNumber).im = 0 := by
  apply RealAlgebraicNumber.toReal_injective
  simp
@[simp] theorem re_one : (1 : AlgebraicNumber).re = 1 := by
  apply RealAlgebraicNumber.toReal_injective
  simp
@[simp] theorem im_one : (1 : AlgebraicNumber).im = 0 := by
  apply RealAlgebraicNumber.toReal_injective
  simp
@[simp] theorem re_I : I.re = 0 := by
  apply RealAlgebraicNumber.toReal_injective
  simp [I_toComplex]
@[simp] theorem im_I : I.im = 1 := by
  apply RealAlgebraicNumber.toReal_injective
  simp [I_toComplex]

/-- The complex order in terms of exact real-algebraic projections. -/
theorem le_parts (a b : AlgebraicNumber) : a ≤ b ↔ a.re ≤ b.re ∧ a.im = b.im := by
  rw [le_iff, RealAlgebraicNumber.le_iff, re_toReal, re_toReal]
  exact and_congr_right fun _ =>
    ⟨fun h => RealAlgebraicNumber.toReal_injective (by simpa using h),
      fun h => by simpa using congrArg RealAlgebraicNumber.toReal h⟩

/-- Inclusion of the real algebraic numbers as a ring homomorphism. -/
def ofRealHom : RealAlgebraicNumber →+* AlgebraicNumber where
  toFun := ofReal
  map_zero' := RealAlgebraicNumber.zero_toAlgebraic
  map_one' := RealAlgebraicNumber.one_toAlgebraic
  map_add' := RealAlgebraicNumber.add_toAlgebraic
  map_mul' := RealAlgebraicNumber.mul_toAlgebraic

/-- Inclusion preserves and reflects the real order. -/
def ofRealOrder : RealAlgebraicNumber ↪o AlgebraicNumber where
  toFun := ofReal
  inj' := fun _ _ h => RealAlgebraicNumber.ext (show _ from h)
  map_rel_iff' := by
    intro a b
    change ofReal a ≤ ofReal b ↔ a ≤ b
    rw [le_iff, ofReal_toComplex, ofReal_toComplex, RealAlgebraicNumber.le_iff]
    simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]

/-- On nonnegative real values the complex and real square roots agree. -/
theorem sqrt_ofReal (a : RealAlgebraicNumber) (ha : 0 ≤ a) :
    (ofReal a).sqrt = ofReal (a.sqrt ha) := by
  apply toComplex_injective
  rw [sqrt_toComplex, ofReal_toComplex, ofReal_toComplex, RealAlgebraicNumber.sqrt_toReal]
  exact Complex.sqrt_of_nonneg (by
    change 0 ≤ a.toReal ∧ (0 : ℝ) = 0
    exact ⟨by simpa only [RealAlgebraicNumber.le_iff, RealAlgebraicNumber.zero_toReal] using ha, rfl⟩)

end Hex.AlgebraicNumber
