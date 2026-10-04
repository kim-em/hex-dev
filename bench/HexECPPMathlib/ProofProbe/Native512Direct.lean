/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib.Tests.Frozen512

public section

/-! Fresh-module proof phases for the frozen native 512-bit endpoint. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem result : Nat.Prime 12655077169514309177840953837335225568096061334897322610772679501937608896257370675750838605329022124937902809437637812352386386288931562255682923262789457 :=
  Hex.ECPP.natPrime_of_checkAt (cert := Hex.ECPP.Tests.certificate512) (by decide)

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
