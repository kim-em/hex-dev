/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles.Order
public import HexPermGroupMathlib.Perm
public import HexPermGroupMathlib.Cycles.Sign
public import HexPermGroupMathlib.Cycles.Type
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace Hex.Perm

/-- The executable lcm is the order of the corresponding Mathlib permutation. -/
theorem order_eq_orderOf (p : Perm n) : p.order = orderOf p.toEquiv := by
  apply Nat.dvd_antisymm
  · apply (p.order_dvd_iff_pow _).mpr
    apply equiv.injective
    change (p.pow _).toEquiv = (Perm.id n).toEquiv
    simp
  · apply orderOf_dvd_iff_pow_eq_one.mpr
    rw [← toEquiv_pow, p.pow_order, toEquiv_id]

end Hex.Perm
