/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.Center

public section

/-! Direct mathematical proof of the centered-product benchmark statement. -/

namespace Hex.Interval.Experiment.Center

theorem centerDirect (valuation : Valuation)
    (_hprogram : extendedProgram.Holds valuation)
    (hsource : 0 ≤ valuation (node 0) ∧ valuation (node 0) ≤ 1) :
    0 ≤ valuation (node 0) * (1 - valuation (node 0)) ∧
      valuation (node 0) * (1 - valuation (node 0)) ≤ (1 / 4 : ℝ) := by
  constructor
  · exact mul_nonneg hsource.1 (sub_nonneg.mpr hsource.2)
  · rw [centerV1_identity]
    exact sub_le_self _ (sq_nonneg _)

/-- info: 'Hex.Interval.Experiment.Center.centerDirect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms centerDirect

-- The sweep harness parses this unguarded copy from Lake's captured output.
#print axioms centerDirect

end Hex.Interval.Experiment.Center
