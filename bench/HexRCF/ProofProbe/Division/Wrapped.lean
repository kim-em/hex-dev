/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Division.Support
public meta import HexRCF.ProofProbe.Division.Support

public section

namespace Hex.RCF.ProofProbe.Division
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

theorem reciprocalWrapped : ∀ x : ℝ, x / alpha.toReal = beta.toReal * x := by rcf

/-- info: 'Hex.RCF.ProofProbe.Division.reciprocalWrapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalWrapped

#print axioms reciprocalWrapped
end Hex.RCF.ProofProbe.Division
