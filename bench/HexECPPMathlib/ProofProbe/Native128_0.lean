/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib.NativeFixtures

public section

/-! Kernel replay of a complete native output. -/

theorem result : Nat.Prime 177080666831933235355717939809840315427 := by
  ecpp using Hex.ECPP.NativeFixtures.tuning_128_0

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
