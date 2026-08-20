/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Stable names for conditional reduction lemmas across the Lean 4.33/4.34 transition.
-/

namespace HexPoly

/-- Reduce an `if` when its condition holds. -/
theorem ite_eq_left {c : Prop} {_ : Decidable c} (hc : c) {α : Sort u} {t e : α} :
    (if c then t else e) = t := by
  simp [hc]

/-- Reduce an `if` when its condition does not hold. -/
theorem ite_eq_right {c : Prop} {_ : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} :
    (if c then t else e) = e := by
  simp [hc]

/-- Reduce a dependent `if` when its condition holds. -/
theorem dite_eq_left {c : Prop} {_ : Decidable c} (hc : c) {α : Sort u}
    {t : c → α} {e : ¬c → α} : dite c t e = t hc := by
  simp [hc]

/-- Reduce a dependent `if` when its condition does not hold. -/
theorem dite_eq_right {c : Prop} {_ : Decidable c} (hc : ¬c) {α : Sort u}
    {t : c → α} {e : ¬c → α} : dite c t e = e hc := by
  simp [hc]

/-- Reduce an `if` whose condition is `True`. -/
theorem ite_true {_ : Decidable True} (t e : α) : (if True then t else e) = t := by
  simp

/-- Reduce an `if` whose condition is `False`. -/
theorem ite_false {_ : Decidable False} (t e : α) : (if False then t else e) = e := by
  simp

end HexPoly
