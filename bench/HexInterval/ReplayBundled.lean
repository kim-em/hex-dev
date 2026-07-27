/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Representation

public section

/-! Ordinary-kernel replay probe for the bundled interval candidate. -/

namespace Hex.Interval.Experiment

theorem replayBundled433 : replayBundledWork 433 = 5801550 := by
  decide +kernel

/-- info: 'Hex.Interval.Experiment.replayBundled433' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms replayBundled433

#print axioms replayBundled433

end Hex.Interval.Experiment
