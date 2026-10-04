/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Validation.Support
public meta import HexRCF.ProofProbe.Validation.Support
public section

namespace Hex.RCF.ProofProbe.Validation.SeveralFresh
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option rcf.algebraic.validateFresh false

theorem positive : ∀ x : ℝ, x ^ 2 + 3 * Real.sqrt 2 > 0 ∧
    Real.sqrt 2 > 0 ∧ 2 * Real.sqrt 2 > 0 ∧ 3 * Real.sqrt 2 > 0 := by rcf

/-- info: 'Hex.RCF.ProofProbe.Validation.SeveralFresh.positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positive

#print axioms positive
end Hex.RCF.ProofProbe.Validation.SeveralFresh
