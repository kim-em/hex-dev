/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib.NativeFixtures

public section

/-! Kernel replay of a complete native output. -/

theorem result : Nat.Prime 69720056183201689673043526946867998580043318488979852658170286968852334279321 := by
  ecpp using Hex.ECPP.NativeFixtures.tuning_256_2

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
