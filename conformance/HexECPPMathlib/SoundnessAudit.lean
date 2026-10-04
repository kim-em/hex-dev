/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib.Soundness

public section

/-- info: 'Hex.ECPP.natPrime_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.ECPP.natPrime_of_check

/-- info: 'Hex.ECPP.natPrime_of_checkAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.ECPP.natPrime_of_checkAt
