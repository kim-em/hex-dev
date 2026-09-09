/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraic.Order
public import Init.Grind

public section

/-!
Mathlib-free law adapters. The proof-only package refers to the executable
operations; the companion supplies its concrete witness by real interpretation.
-/

namespace Hex.RealAlgebraicNumber

/-- Laws of the executable operations, without alternative data or a field
instance assumption. The Mathlib companion proves this package unconditionally. -/
class Laws : Prop where
  /-- Boolean equality recognizes structural equality. -/
  beq_iff : ∀ a b : RealAlgebraicNumber, (a == b) = true ↔ a = b
  /-- Addition has right identity zero. -/
  add_zero : ∀ a : RealAlgebraicNumber, a + 0 = a
  /-- Addition is commutative. -/
  add_comm : ∀ a b : RealAlgebraicNumber, a + b = b + a
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : RealAlgebraicNumber, a + b + c = a + (b + c)
  /-- Multiplication is associative. -/
  mul_assoc : ∀ a b c : RealAlgebraicNumber, a * b * c = a * (b * c)
  /-- Multiplication has right identity one. -/
  mul_one : ∀ a : RealAlgebraicNumber, a * 1 = a
  /-- Multiplication has left identity one. -/
  one_mul : ∀ a : RealAlgebraicNumber, 1 * a = a
  /-- Left distributivity. -/
  left_distrib : ∀ a b c : RealAlgebraicNumber, a * (b + c) = a * b + a * c
  /-- Right distributivity. -/
  right_distrib : ∀ a b c : RealAlgebraicNumber, (a + b) * c = a * c + b * c
  /-- Zero annihilates multiplication on the left. -/
  zero_mul : ∀ a : RealAlgebraicNumber, 0 * a = 0
  /-- Zero annihilates multiplication on the right. -/
  mul_zero : ∀ a : RealAlgebraicNumber, a * 0 = 0
  /-- Zeroth natural powers are one. -/
  pow_zero : ∀ a : RealAlgebraicNumber, a ^ (0 : Nat) = 1
  /-- Successor law for the repeated-squaring implementation. -/
  pow_succ : ∀ (a : RealAlgebraicNumber) (n : Nat), a ^ (n + 1) = a ^ n * a
  /-- Natural zero casts to zero. -/
  natCast_zero : ((0 : Nat) : RealAlgebraicNumber) = 0
  /-- Natural one casts to one. -/
  natCast_one : ((1 : Nat) : RealAlgebraicNumber) = 1
  /-- Natural casts preserve successors. -/
  natCast_succ : ∀ n : Nat, ((n + 1 : Nat) : RealAlgebraicNumber) = (n : RealAlgebraicNumber) + 1
  /-- Natural scalar multiplication agrees with multiplication by the cast. -/
  nsmul_eq_mul : ∀ (n : Nat) (a : RealAlgebraicNumber), n • a = (n : RealAlgebraicNumber) * a
  /-- Negation cancels addition. -/
  neg_add_cancel : ∀ a : RealAlgebraicNumber, -a + a = 0
  /-- Subtraction is addition of the negative. -/
  sub_eq_add_neg : ∀ a b : RealAlgebraicNumber, a - b = a + -b
  /-- Integer scalar multiplication preserves negation. -/
  neg_zsmul : ∀ (n : Int) (a : RealAlgebraicNumber), (-n) • a = -(n • a)
  /-- Integer casts preserve negation. -/
  intCast_neg : ∀ n : Int, ((-n : Int) : RealAlgebraicNumber) = -(n : RealAlgebraicNumber)
  /-- Multiplication is commutative. -/
  mul_comm : ∀ a b : RealAlgebraicNumber, a * b = b * a
  /-- Division agrees with multiplication by an inverse. -/
  div_eq_mul_inv : ∀ a b : RealAlgebraicNumber, a / b = a * b⁻¹
  /-- The field is nontrivial. -/
  zero_ne_one : (0 : RealAlgebraicNumber) ≠ 1
  /-- Zero has inverse zero. -/
  inv_zero : (0 : RealAlgebraicNumber)⁻¹ = 0
  /-- Nonzero elements have multiplicative inverses. -/
  mul_inv_cancel : ∀ {a : RealAlgebraicNumber}, a ≠ 0 → a * a⁻¹ = 1
  /-- Zeroth integer powers are one. -/
  zpow_zero : ∀ a : RealAlgebraicNumber, a ^ (0 : Int) = 1
  /-- Integer powers obey the successor law at natural exponents. -/
  zpow_succ : ∀ (a : RealAlgebraicNumber) (n : Nat), a ^ (n + 1 : Int) = a ^ (n : Int) * a
  /-- Integer powers preserve negation as inversion. -/
  zpow_neg : ∀ (a : RealAlgebraicNumber) (n : Int), a ^ (-n) = (a ^ n)⁻¹
  /-- Order is reflexive. -/
  le_refl : ∀ a : RealAlgebraicNumber, a ≤ a
  /-- Order is transitive. -/
  le_trans : ∀ a b c : RealAlgebraicNumber, a ≤ b → b ≤ c → a ≤ c
  /-- Order is antisymmetric. -/
  le_antisymm : ∀ a b : RealAlgebraicNumber, a ≤ b → b ≤ a → a = b
  /-- Order is total. -/
  le_total : ∀ a b : RealAlgebraicNumber, a ≤ b ∨ b ≤ a
  /-- Strict order is induced by non-strict order. -/
  lt_iff : ∀ a b : RealAlgebraicNumber, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  /-- The reverse comparison agrees with non-strict order. -/
  compare_ge : ∀ a b : RealAlgebraicNumber, (compare a b).isGE = true ↔ b ≤ a
  /-- Translation preserves and reflects order. -/
  add_le_iff : ∀ (a b c : RealAlgebraicNumber), a ≤ b ↔ a + c ≤ b + c
  /-- Zero is strictly below one. -/
  zero_lt_one : (0 : RealAlgebraicNumber) < 1
  /-- Positive left multiplication preserves strict order. -/
  mul_lt_left : ∀ {a b c : RealAlgebraicNumber}, a < b → 0 < c → c * a < c * b
  /-- Positive right multiplication preserves strict order. -/
  mul_lt_right : ∀ {a b c : RealAlgebraicNumber}, a < b → 0 < c → a * c < b * c

instance [Laws] : LawfulBEq RealAlgebraicNumber where
  eq_of_beq := (Laws.beq_iff _ _).mp
  rfl := (Laws.beq_iff _ _).mpr rfl

instance [Laws] : DecidableEq RealAlgebraicNumber := instDecidableEqOfLawfulBEq

instance [Laws] : Std.IsLinearOrder RealAlgebraicNumber where
  le_refl := Laws.le_refl
  le_trans := Laws.le_trans
  le_antisymm := Laws.le_antisymm
  le_total := Laws.le_total

instance [Laws] : Std.LawfulOrderLT RealAlgebraicNumber := ⟨Laws.lt_iff⟩

instance [Laws] : Std.LawfulOrderBEq RealAlgebraicNumber where
  beq_iff_le_and_ge a b := by
    rw [Laws.beq_iff]
    exact ⟨fun h => by subst b; exact ⟨Laws.le_refl a, Laws.le_refl a⟩,
      fun h => Laws.le_antisymm _ _ h.1 h.2⟩

instance [Laws] : Std.LawfulOrderOrd RealAlgebraicNumber where
  isLE_compare a b := by
    change (compare a b).isLE = true ↔ compare a b ≠ .gt
    cases compare a b <;> decide
  isGE_compare := Laws.compare_ge

instance : Std.LawfulOrderLeftLeaningMin RealAlgebraicNumber where
  min_eq_left _ _ h := ite_eq_left h
  min_eq_right _ _ h := ite_eq_right h

instance : Std.LawfulOrderLeftLeaningMax RealAlgebraicNumber where
  max_eq_left _ _ h := ite_eq_left h
  max_eq_right _ _ h := ite_eq_right h

instance [Laws] : Lean.Grind.Field RealAlgebraicNumber where
  add := (· + ·)
  mul := (· * ·)
  natCast := inferInstance
  ofNat | 0 | 1 | n + 2 => inferInstance
  nsmul := inferInstance
  npow := inferInstance
  add_zero := Laws.add_zero
  add_comm := Laws.add_comm
  add_assoc := Laws.add_assoc
  mul_assoc := Laws.mul_assoc
  mul_one := Laws.mul_one
  one_mul := Laws.one_mul
  left_distrib := Laws.left_distrib
  right_distrib := Laws.right_distrib
  zero_mul := Laws.zero_mul
  mul_zero := Laws.mul_zero
  pow_zero := Laws.pow_zero
  pow_succ := Laws.pow_succ
  ofNat_eq_natCast n := by
    cases n with
    | zero => exact Laws.natCast_zero.symm
    | succ n => cases n with
      | zero => exact Laws.natCast_one.symm
      | succ n => rfl
  ofNat_succ n := by
    cases n with
    | zero =>
      change 1 = 0 + (1 : RealAlgebraicNumber)
      rw [Laws.add_comm, Laws.add_zero]
    | succ n => cases n with
      | zero =>
        change ofRat 2 = ofRat 1 + (1 : RealAlgebraicNumber)
        exact Laws.natCast_succ 1
      | succ n => exact Laws.natCast_succ (n + 2)
  nsmul_eq_natCast_mul := Laws.nsmul_eq_mul
  neg := (- ·)
  sub := (· - ·)
  intCast := inferInstance
  zsmul := inferInstance
  neg_add_cancel := Laws.neg_add_cancel
  sub_eq_add_neg := Laws.sub_eq_add_neg
  neg_zsmul := Laws.neg_zsmul
  intCast_ofNat n := by
    cases n with
    | zero => exact Laws.natCast_zero
    | succ n => cases n with
      | zero => exact Laws.natCast_one
      | succ n => rfl
  intCast_neg := Laws.intCast_neg
  mul_comm := Laws.mul_comm
  inv := (·⁻¹)
  div := (· / ·)
  zpow := inferInstance
  div_eq_mul_inv := Laws.div_eq_mul_inv
  zero_ne_one := Laws.zero_ne_one
  inv_zero := Laws.inv_zero
  mul_inv_cancel := Laws.mul_inv_cancel
  zpow_zero := Laws.zpow_zero
  zpow_succ := Laws.zpow_succ
  zpow_neg := Laws.zpow_neg

instance [Laws] : Lean.Grind.OrderedRing RealAlgebraicNumber where
  add_le_left_iff c := Laws.add_le_iff _ _ c
  zero_lt_one := Laws.zero_lt_one
  mul_lt_mul_of_pos_left := Laws.mul_lt_left
  mul_lt_mul_of_pos_right := Laws.mul_lt_right

end Hex.RealAlgebraicNumber
