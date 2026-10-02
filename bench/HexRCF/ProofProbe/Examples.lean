/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Tactic
public meta import HexRCF.Tactic

public section

namespace Hex.RCF.ProofExamples

theorem quadratic : ∀ x : ℝ, x ^ 2 + 1 > 0 := by rcf
theorem witness : ∃ x : ℝ, x ^ 2 = 2 := by rcf

/-- info: 'Hex.RCF.ProofExamples.quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadratic

end Hex.RCF.ProofExamples
