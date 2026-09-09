/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.Embedding
public import HexNumberFieldMathlib.Nearest
public section

/-! Conjugation makes the executable field a star ring. -/
namespace Hex.AlgebraicNumber

@[simp] theorem conj_add (a b : AlgebraicNumber) : (a + b).conj = a.conj + b.conj := by
  apply toComplex_injective
  simp only [conj_toComplex, add_toComplex, map_add]

@[simp] theorem conj_mul (a b : AlgebraicNumber) : (a * b).conj = a.conj * b.conj := by
  apply toComplex_injective
  simp only [conj_toComplex, mul_toComplex, map_mul]

@[simp] theorem conj_eq_self_iff (a : AlgebraicNumber) : a.conj = a ↔ a.isReal = true := by
  rw [isReal_iff]
  constructor
  · intro h
    have hc := congrArg toComplex h
    rw [conj_toComplex] at hc
    exact Complex.conj_eq_iff_im.mp hc
  · intro h
    apply toComplex_injective
    rw [conj_toComplex]
    exact Complex.conj_eq_iff_im.mpr h

instance : StarRing AlgebraicNumber where
  star := conj
  star_involutive := conj_conj
  star_mul a b := by rw [conj_mul, mul_comm]
  star_add := conj_add

/-- Conjugation as an involutive field automorphism. -/
def conjRingEquiv : AlgebraicNumber ≃+* AlgebraicNumber where
  toFun := conj
  invFun := conj
  left_inv := conj_conj
  right_inv := conj_conj
  map_add' := conj_add
  map_mul' := conj_mul

@[simp] theorem conj_neg (a : AlgebraicNumber) : (-a).conj = -a.conj := map_neg conjRingEquiv a
@[simp] theorem conj_sub (a b : AlgebraicNumber) : (a - b).conj = a.conj - b.conj :=
  map_sub conjRingEquiv a b
@[simp] theorem conj_inv (a : AlgebraicNumber) : a⁻¹.conj = a.conj⁻¹ := map_inv₀ conjRingEquiv a
@[simp] theorem conj_div (a b : AlgebraicNumber) : (a / b).conj = a.conj / b.conj :=
  map_div₀ conjRingEquiv a b

end Hex.AlgebraicNumber
