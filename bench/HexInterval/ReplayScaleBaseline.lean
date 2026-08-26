/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Scale

public section

/-! Import-matched fixed-statement baseline for maximum scale replay. -/

namespace Hex.Interval.Experiment.Scale

open Center

theorem scaleReplay : checkFixture = true := checkFixture_eq_true

/-- info: 'Hex.Interval.Experiment.Scale.scaleReplay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scaleReplay

#print axioms scaleReplay

end Hex.Interval.Experiment.Scale
