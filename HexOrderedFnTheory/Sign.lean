/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Basic.Sign.Basic

/-!
Integer-valued sign comparisons for ordered subjects. Both the real and
infinitesimal interpretations use these laws without real interval assumptions.
The namespace retains the existing public theorem names.
-/

@[expose] public section

namespace Hex.OrderedFn.Oracle

/-- The integer image of a sign is negative exactly when its subject is negative. -/
theorem cast_sign_neg {L : Type*} [Zero L] [LinearOrder L] (a : L) :
    (SignType.sign a : Int) < 0 ↔ a < 0 := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [ha]
  · simp
  · simp [ha, ha.not_gt]

/-- The integer image of a sign is nonpositive exactly when its subject is nonpositive. -/
theorem cast_sign_nonpos {L : Type*} [Zero L] [LinearOrder L] (a : L) :
    (SignType.sign a : Int) ≤ 0 ↔ a ≤ 0 := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [ha, ha.le]
  · simp
  · simp [ha, ha.not_ge]

end Hex.OrderedFn.Oracle
