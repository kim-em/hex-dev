/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPTheory.NativeFixtures

/-! Kernel replay of a complete native output. -/

set_option maxRecDepth 65536 in
theorem result : Nat.Prime 69199437377629051939477864552334532767081794053034238723740032946332041487367 :=
  Hex.ECPP.natPrime_of_checkAt (cert := Hex.ECPP.NativeFixtures.tuning_256_0) (by decide)

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
