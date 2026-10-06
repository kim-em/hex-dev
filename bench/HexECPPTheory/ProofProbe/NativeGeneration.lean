/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPTheory.Native

/-! Native proof generation from a subject and seed, without supplied data. -/

theorem generated128 : Nat.Prime 177080666831933235355717939809840315427 := by
  primality? (method := ecpp) (seed := 0)

/-- info: 'generated128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generated128
