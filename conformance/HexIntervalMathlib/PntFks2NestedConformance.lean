/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntFks2Nested

/-!
# Source-pinned FKS2 nested-log conformance

The sole source row authenticates the exact theorem-6.2 premise before the
ordinary-kernel natural-log provider is reused.
-/

namespace Hex.IntervalMathlib.PntFks2NestedConformance

open Hex.Interval.Experiment.PntFks2Nested

#guard certificates.length == 1
#guard certificates == sourceRows
#guard firstFailure? 0 certificates == none
#guard sourceRows[0]? == some
  ⟨⟨3605⟩, 14, 3, 3, 11, 8, 2, 3, 1⟩

/-- Structural consistency alone does not authenticate the audited source
literal or establish its semantic logarithm window. -/
def shapeOnly : Certificate :=
  ⟨⟨3605⟩, 100, 3, 23, 27, 8, 2, 3, 1⟩

#guard checkShape shapeOnly
#guard !validCertificate 0 shapeOnly

def wrongThreshold : List Certificate :=
  [{ sourceRows[0] with threshold := 5 }]

#guard firstFailure? 0 wrongThreshold == some ⟨3605⟩
#guard !checkShape wrongThreshold[0]
#guard !validCertificate 0 wrongThreshold[0]

def wrongShift : List Certificate :=
  [{ sourceRows[0] with shift := 4 }]

#guard firstFailure? 0 wrongShift == some ⟨3605⟩
#guard !checkShape wrongShift[0]
#guard !validCertificate 0 wrongShift[0]

def wrongXNum : List Certificate :=
  [{ sourceRows[0] with xNum := 4 }]

#guard firstFailure? 0 wrongXNum == some ⟨3605⟩
#guard !checkShape wrongXNum[0]
#guard !validCertificate 0 wrongXNum[0]

def wrongCoordinate : List Certificate :=
  [{ sourceRows[0] with coordinate := ⟨3606⟩ }]

#guard firstFailure? 0 wrongCoordinate == some ⟨3605⟩
#guard checkShape wrongCoordinate[0]
#guard !validCertificate 0 wrongCoordinate[0]

theorem theorem62Premise :
    (0 : ℝ) < Real.log 14 + Real.log (Real.log 14) - 1 := by
  have checked :=
    certificateHolds 0 sourceRows[0] (by decide)
  norm_num [sourceRows, Holds] at checked
  linarith

example :
    ¬ (0 : ℝ) < Real.log 14 + Real.log (Real.log 14) - 5 :=
  rejectThresholdFive

/-- info: 'Hex.Interval.Experiment.PntFks2Nested.certificateHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificateHolds

/-- info: 'Hex.IntervalMathlib.PntFks2NestedConformance.theorem62Premise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms theorem62Premise

/-- info: 'Hex.Interval.Experiment.PntFks2Nested.rejectThresholdFive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejectThresholdFive

end Hex.IntervalMathlib.PntFks2NestedConformance
