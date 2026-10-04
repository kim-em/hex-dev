/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public section

namespace Hex.RCF.ProofProbe.Scaling.Bits128
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

theorem positive : ∀ x : ℝ, x ^ 2 + 170141183460469231731687303715884105728 * Real.sqrt 2 > 0 := by rcf

/-- info: 'Hex.RCF.ProofProbe.Scaling.Bits128.positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positive

#print axioms positive
end Hex.RCF.ProofProbe.Scaling.Bits128
