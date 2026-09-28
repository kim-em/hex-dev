/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.NativeFixtures

/-! Kernel replay of a complete native output. -/

theorem result : Nat.Prime 58462043247721851837374720714032783167040048430751222127700100782042467564843 := by
  ecpp using Hex.ECPP.NativeFixtures.tuning_256_1

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
