/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public section

namespace Hex.RCF.ProofProbe.Profiling
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

set_option profiler true in
set_option profiler.threshold 0 in
theorem witness : ∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < Real.sqrt 3 := by rcf

/-- info: 'Hex.RCF.ProofProbe.Profiling.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness

#print axioms witness
end Hex.RCF.ProofProbe.Profiling
