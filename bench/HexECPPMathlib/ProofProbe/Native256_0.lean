/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.NativeFixtures

/-! Kernel replay of a complete native output. -/

theorem result : Nat.Prime 69199437377629051939477864552334532767081794053034238723740032946332041487367 := by
  ecpp using Hex.ECPP.NativeFixtures.tuning_256_0

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
