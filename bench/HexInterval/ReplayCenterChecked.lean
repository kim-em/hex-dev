/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Center

public section

/-! Ordinary-kernel replay of the fixed nine-node centered-product trace. -/

namespace Hex.Interval.Experiment.Center

theorem fixtureAccepted : checkFixture = true := by
  decide +kernel

/-- info: 'Hex.Interval.Experiment.Center.fixtureAccepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fixtureAccepted

-- The sweep harness parses this unguarded copy from Lake's captured output.
#print axioms fixtureAccepted

end Hex.Interval.Experiment.Center
