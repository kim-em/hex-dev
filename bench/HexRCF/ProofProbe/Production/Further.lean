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

theorem furtherSection : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf

/-- info: 'Hex.RCF.ProofProbe.Production.furtherSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms furtherSection

#print axioms furtherSection
end Hex.RCF.ProofProbe.Production
