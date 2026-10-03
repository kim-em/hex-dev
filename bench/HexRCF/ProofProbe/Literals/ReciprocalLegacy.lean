/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public section

namespace Hex.RCF.ProofProbe.Literals.ReciprocalLegacy
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.reducedLiterals false

theorem witness : ∃ x : ℝ, x ^ 2 = 1 / (Real.sqrt 2 + 1) ∧ 0 < x ∧ x < 1 := by rcf

/-- info: 'Hex.RCF.ProofProbe.Literals.ReciprocalLegacy.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness

#print axioms witness
end Hex.RCF.ProofProbe.Literals.ReciprocalLegacy
