/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Registered.Support
public meta import HexRCF.ProofProbe.Registered.Support

public section

namespace Hex.RCF.ProofProbe.Registered

theorem piSquare : ∀ x : ℝ, x ^ 2 > Real.pi - 4 := by rcf
theorem expSquare : ∀ x : ℝ, x ^ 2 + Real.exp 1 > 2 := by rcf
theorem expWitness : ∃ x : ℝ, x = Real.exp 1 ∧ 2 < x ∧ x < 3 := by rcf
theorem piInverse : ∀ x : ℝ, x ^ 2 + 1 / (4 - Real.pi) > 0 := by rcf

/-- info: 'Hex.RCF.ProofProbe.Registered.piSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms piSquare
/-- info: 'Hex.RCF.ProofProbe.Registered.expSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSquare
/-- info: 'Hex.RCF.ProofProbe.Registered.expWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expWitness
/-- info: 'Hex.RCF.ProofProbe.Registered.piInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms piInverse

-- The measurement harness inventories the actual quoted theorem dependencies.
#print axioms piSquare
#print axioms expSquare
#print axioms expWitness
#print axioms piInverse

end Hex.RCF.ProofProbe.Registered
