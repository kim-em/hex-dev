/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.Field
public section

/-! The canonical field embedding and its rational algebra structure. -/
namespace Hex.AlgebraicNumber

/-- The interpretation as a field homomorphism. -/
@[expose] noncomputable def toComplexHom : AlgebraicNumber →+* ℂ where
  toFun := toComplex
  map_zero' := zero_toComplex
  map_one' := one_toComplex
  map_add' := add_toComplex
  map_mul' := mul_toComplex

instance : CharZero AlgebraicNumber where
  cast_injective m n h := by
    have hh := congrArg toComplexHom h
    simpa using hh

/-- The complex embedding respects the canonical rational algebra structure. -/
@[expose] noncomputable def toComplexAlgHom : AlgebraicNumber →ₐ[ℚ] ℂ :=
  { toComplexHom with commutes' := fun q => map_ratCast toComplexHom q }

@[simp] theorem natCast_toComplex (n : Nat) : (n : AlgebraicNumber).toComplex = (n : ℂ) :=
  map_natCast toComplexHom n

@[simp] theorem intCast_toComplex (n : Int) : (n : AlgebraicNumber).toComplex = (n : ℂ) :=
  map_intCast toComplexHom n

@[simp] theorem ratCast_toComplex (q : Rat) : (q : AlgebraicNumber).toComplex = (q : ℂ) :=
  map_ratCast toComplexHom q

@[simp] theorem ofNat_toComplex (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : AlgebraicNumber).toComplex = (ofNat(n) : ℂ) :=
  map_ofNat toComplexHom n

end Hex.AlgebraicNumber
