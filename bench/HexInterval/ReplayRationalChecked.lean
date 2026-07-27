/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Rational

public section

/-! Ordinary-kernel replay of 433 rational cross-product checks. -/

namespace Hex.Interval.Experiment.Rational

theorem checkedFold433 : checkedFold 433 = true := by
  decide +kernel

/-- info: 'Hex.Interval.Experiment.Rational.checkedFold433' does not depend on any axioms -/
#guard_msgs in
#print axioms checkedFold433

#print axioms checkedFold433

end Hex.Interval.Experiment.Rational
