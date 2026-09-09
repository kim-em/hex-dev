/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Basic

public section

/-! A field structure whose data is the executable canonical arithmetic. -/

namespace Hex.RealAlgebraicNumber

/-- The law-bearing field whose data fields are the executable canonical
operations. -/
@[expose, reducible]
noncomputable def field : Field RealAlgebraicNumber := by
  letI : SMul ℚ≥0 RealAlgebraicNumber :=
    ⟨fun q a => smul (q : Rat) a⟩
  letI : NNRatCast RealAlgebraicNumber :=
    ⟨fun q => ofRat (q : Rat)⟩
  letI : RatCast RealAlgebraicNumber := ⟨ofRat⟩
  apply Function.Injective.field toReal toReal_injective
  · exact zero_toReal
  · exact one_toReal
  · exact add_toReal
  · exact mul_toReal
  · exact neg_toReal
  · exact sub_toReal
  · exact inv_toReal
  · exact div_toReal
  · intro n a
    change (smul (n : Rat) a).toReal = n • a.toReal
    rw [smul_toReal, nsmul_eq_mul]
    rfl
  · intro n a
    change (smul (n : Rat) a).toReal = n • a.toReal
    rw [smul_toReal, zsmul_eq_mul]
    rfl
  · intro q a
    change (smul (q : Rat) a).toReal = q • a.toReal
    rw [smul_toReal, NNRat.smul_def]
    rfl
  · intro q a
    change (smul q a).toReal = q • a.toReal
    rw [Rat.smul_def]
    exact smul_toReal q a
  · exact natPow_toReal
  · exact intPow_toReal
  · intro n
    change (ofRat (n : Rat)).toReal = (n : ℝ)
    rw [ofRat_toReal]
    norm_cast
  · intro n
    change (ofRat (n : Rat)).toReal = (n : ℝ)
    rw [ofRat_toReal]
    norm_cast
  · intro q
    change (ofRat (q : Rat)).toReal = (q : ℝ)
    rw [ofRat_toReal]
    norm_cast
  · exact ofRat_toReal

/-- Canonical algebraic numbers form a field without replacing any executable
arithmetic operation. The instance is computable: every data field is the
executable operation, written out, and every law is the corresponding law
of `field`. Code elaborated through the field structure, such as `a ^ n`
resolved by Mathlib's monoid power, therefore compiles and runs. -/
instance instField : Field RealAlgebraicNumber where
  add := (· + ·)
  add_assoc := field.add_assoc
  zero := 0
  zero_add := field.zero_add
  add_zero := field.add_zero
  nsmul := fun n a => n • a
  nsmul_zero := field.nsmul_zero
  nsmul_succ := field.nsmul_succ
  add_comm := field.add_comm
  mul := (· * ·)
  mul_assoc := field.mul_assoc
  one := 1
  one_mul := field.one_mul
  mul_one := field.mul_one
  npow := fun n a => a ^ n
  npow_zero := field.npow_zero
  npow_succ := field.npow_succ
  zero_mul := field.zero_mul
  mul_zero := field.mul_zero
  left_distrib := field.left_distrib
  right_distrib := field.right_distrib
  natCast := Nat.cast
  natCast_zero := field.natCast_zero
  natCast_succ := field.natCast_succ
  neg := (- ·)
  sub := (· - ·)
  zsmul := fun n a => n • a
  sub_eq_add_neg := field.sub_eq_add_neg
  zsmul_zero' := field.zsmul_zero'
  zsmul_succ' := field.zsmul_succ'
  zsmul_neg' := field.zsmul_neg'
  neg_add_cancel := field.neg_add_cancel
  intCast := Int.cast
  intCast_ofNat := field.intCast_ofNat
  intCast_negSucc := field.intCast_negSucc
  mul_comm := field.mul_comm
  inv := (·⁻¹)
  div := (· / ·)
  zpow := fun n a => a ^ n
  div_eq_mul_inv := field.div_eq_mul_inv
  zpow_zero' := field.zpow_zero'
  zpow_succ' := field.zpow_succ'
  zpow_neg' := field.zpow_neg'
  exists_pair_ne := field.exists_pair_ne
  nnratCast := fun q => ofRat (q : Rat)
  ratCast := ofRat
  mul_inv_cancel := field.mul_inv_cancel
  inv_zero := field.inv_zero
  nnratCast_def := field.nnratCast_def
  nnqsmul := fun q a => smul (q : Rat) a
  nnqsmul_def := field.nnqsmul_def
  ratCast_def := field.ratCast_def
  qsmul := fun q a => q • a
  qsmul_def := field.qsmul_def


end Hex.RealAlgebraicNumber
