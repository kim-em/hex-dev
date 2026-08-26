/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Rational

public section

/-! Ordinary-kernel replay of 433 exposed Core-rational additions. -/

namespace Hex.Interval.Experiment.Rational

theorem directFold433 : directFold 433 = 1 := by
  decide +kernel

/-- info: 'Hex.Interval.Experiment.Rational.directFold433' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms directFold433

-- The sweep harness parses this unguarded copy from Lake's captured output.
#print axioms directFold433

end Hex.Interval.Experiment.Rational
