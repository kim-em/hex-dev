/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPTheory.NativeFixtures

/-! Kernel replay of a complete native output. -/

theorem result : Nat.Prime 79115478805960826808549622107591358196461499795534342671326167515356343483999 := by
  ecpp using Hex.ECPP.NativeFixtures.holdout_256_1

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
