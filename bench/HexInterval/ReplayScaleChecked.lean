/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Scale

public section

/-!
Ordinary-kernel boundary proof for the largest committed workload in every
Stage-1 family. The exported theorem statement is identical to the import-
matched baseline; only its local proof construction performs the scale replay.
-/

namespace Hex.Interval.Experiment.Scale

open Center

private def maximumBoundary : Bool :=
  checksSome (deadNodes? 2000) && checksSome (adjacent? 491) &&
    checksSome (far? 491) && (sourcePad 490).checksBoundary

private theorem consumeBoundary (_ : maximumBoundary = true) :
    checkFixture = true :=
  checkFixture_eq_true

theorem scaleReplay : checkFixture = true :=
  consumeBoundary (by decide +kernel)

/-- info: 'Hex.Interval.Experiment.Scale.scaleReplay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scaleReplay

#print axioms scaleReplay

end Hex.Interval.Experiment.Scale
