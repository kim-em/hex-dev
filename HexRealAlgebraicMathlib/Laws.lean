/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraic.Laws
public import HexRealAlgebraicMathlib.Order

public section

/-! The unconditional companion witness for the Mathlib-free law adapters. -/

namespace Hex.RealAlgebraicNumber

instance instLaws : Laws where
  beq_iff := beq_iff
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  pow_zero := pow_zero
  pow_succ := pow_succ
  natCast_zero := Nat.cast_zero
  natCast_one := Nat.cast_one
  natCast_succ := Nat.cast_succ
  nsmul_eq_mul := fun n a => nsmul_eq_mul n a
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg
  neg_zsmul := fun n a => neg_zsmul a n
  intCast_neg := Int.cast_neg
  mul_comm := mul_comm
  div_eq_mul_inv := div_eq_mul_inv
  zero_ne_one := zero_ne_one
  inv_zero := inv_zero
  mul_inv_cancel := mul_inv_cancel₀
  zpow_zero := zpow_zero
  zpow_succ := fun a n => by
    simp only [← Int.natCast_succ, zpow_natCast, pow_succ]
  zpow_neg := zpow_neg
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ => le_antisymm
  le_total := le_total
  lt_iff := fun _ _ => lt_iff_le_not_ge
  compare_ge a b := by
    simp only [compare_eq, Ordering.isGE_iff_ne_lt, compare_lt_iff_lt, not_lt, le_iff]
  add_le_iff := fun _ _ _ => add_le_add_iff_right _ |>.symm
  zero_lt_one := zero_lt_one
  mul_lt_left := mul_lt_mul_of_pos_left
  mul_lt_right := mul_lt_mul_of_pos_right

/--
info: 'Hex.RealAlgebraicNumber.instLaws' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms instLaws

-- These examples have no extra law hypothesis after importing the companion.
example (a b : RealAlgebraicNumber) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have := Lean.Grind.OrderedRing.mul_lt_mul_of_pos_left hb ha
  grind

example (a b c : RealAlgebraicNumber) (h : a ≤ b) : a + c ≤ b + c := by
  grind

end Hex.RealAlgebraicNumber
