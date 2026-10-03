/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public section

namespace Hex.RCF.ProofProbe.Production
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

theorem closeSections : ∃ x : ℝ, x = Real.sqrt 2 ∧ x < Real.sqrt 2 +
    1 / (5444517870735015415413993718908291383296 : ℝ) := by rcf

/-- info: 'Hex.RCF.ProofProbe.Production.closeSections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closeSections

#print axioms closeSections
end Hex.RCF.ProofProbe.Production
