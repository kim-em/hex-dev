/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Correspondence between checked natural modular orders and Mathlib's
unit-group order. -/

namespace Hex

namespace Nat

private theorem unit_pow_iff {a n k : Nat} (ha : Nat.Coprime a n) :
    (ZMod.unitOfCoprime a ha) ^ k = 1 ↔ a ^ k % n = 1 % n := by
  constructor
  · intro h
    have hv := congrArg Units.val h
    have hv' : ((a ^ k : Nat) : ZMod n) = ((1 : Nat) : ZMod n) := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one,
        ZMod.coe_unitOfCoprime, Nat.cast_pow, Nat.cast_one] using hv
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hv'
  · intro h
    apply Units.ext
    have hv : ((a ^ k : Nat) : ZMod n) = ((1 : Nat) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    simpa only [Units.val_pow_eq_pow_val, Units.val_one,
      ZMod.coe_unitOfCoprime, Nat.cast_pow, Nat.cast_one] using hv

/-- The Mathlib order of a residue-class unit agrees with the Mathlib-free
natural order. -/
theorem orderOf_unitOfCoprime {a n : Nat} (hn : 1 < n)
    (ha : Nat.Coprime a n) :
    _root_.orderOf (ZMod.unitOfCoprime a ha) = Hex.Nat.orderOf a n := by
  have hpos : 0 < Hex.Nat.orderOf a n := Hex.Nat.orderOf_pos hn ha
  apply (_root_.orderOf_eq_iff hpos).2
  constructor
  · exact (unit_pow_iff ha).2 (Hex.Nat.orderOf_pow_mod hpos)
  · intro k hkn hk hpow
    exact Hex.Nat.orderOf_min hpos k hk hkn ((unit_pow_iff ha).1 hpow)

/-- The Mathlib order of a natural-number residue agrees with the Mathlib-free
natural order, including the zero value for nonunits. -/
theorem orderOf_natCast {a n : Nat} (hn : 1 < n) :
    _root_.orderOf (a : ZMod n) = Hex.Nat.orderOf a n := by
  by_cases ha : Nat.Coprime a n
  · rw [← orderOf_unitOfCoprime hn ha]
    simpa only [ZMod.coe_unitOfCoprime] using
      (_root_.orderOf_units (y := ZMod.unitOfCoprime a ha))
  · have hz : Hex.Nat.orderOf a n = 0 :=
      Nat.eq_zero_of_not_pos fun h => ha (coprime_of_orderOf_pos h)
    rw [hz, _root_.orderOf_eq_zero_iff]
    exact fun h => ha ((ZMod.isUnit_iff_coprime a n).1 h.isUnit)

/-- A checked natural order is the order of the corresponding Mathlib unit. -/
theorem orderOf_eq {c : OrderCert} (h : checkOrder c = true) :
    _root_.orderOf
        (ZMod.unitOfCoprime c.base (coprime_of_checkOrder h)) = c.order := by
  rw [orderOf_unitOfCoprime (checkOrder_one_lt_modulus h)
    (coprime_of_checkOrder h), order_eq_of_checkOrder h]

end Nat

end Hex
