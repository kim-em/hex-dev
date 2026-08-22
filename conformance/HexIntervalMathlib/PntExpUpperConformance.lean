/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntExpUpper

/-!
# Source-pinned positive exponential conformance

The FKS2-floor and Goldbach leaves authenticate their exact source row before
entering one bounded ordinary-kernel provider.
-/

namespace Hex.IntervalMathlib.PntExpUpperConformance

open Hex.Interval.Experiment.PntExpUpper

#guard certificates.length == 3
#guard certificates == sourceRows
#guard firstFailure? 0 certificates == none
#guard sourceRows[0]? == some
  ⟨⟨.fks2Floor, 11⟩, .strict, 10, 0, 22027⟩
#guard sourceRows[1]? == some
  ⟨⟨.goldbach, 250⟩, .weak, 59, 5, 113250000000000000000000000⟩
#guard sourceRows[2]? == some
  ⟨⟨.goldbach, 267⟩, .weak, 60, 5, 7785131284000000000000000004⟩

def wrongEndpoint : List Certificate :=
  { sourceRows[0] with target := 22026 } :: sourceRows.drop 1

#guard firstFailure? 0 wrongEndpoint == some ⟨.fks2Floor, 11⟩
#guard !checkComparison wrongEndpoint[0]
#guard !validCertificate 0 wrongEndpoint[0]

def wrongGoldbach : List Certificate :=
  sourceRows.take 1 ++ { sourceRows[1] with target := 64 } :: sourceRows.drop 2

#guard firstFailure? 0 wrongGoldbach == some ⟨.goldbach, 250⟩
#guard !checkComparison wrongGoldbach[1]
#guard !validCertificate 1 wrongGoldbach[1]

def wrongCoordinate : List Certificate :=
  { sourceRows[0] with coordinate := ⟨.fks2Floor, 12⟩ } :: sourceRows.drop 1

#guard firstFailure? 0 wrongCoordinate == some ⟨.fks2Floor, 11⟩
#guard checkComparison wrongCoordinate[0]
#guard !validCertificate 0 wrongCoordinate[0]

theorem exp10Lt : Real.exp 10 < 22027 := by
  have checked := certificateHolds 0 sourceRows[0]
    (by set_option maxRecDepth 100000 in decide)
  norm_num [sourceRows, Holds] at checked ⊢
  exact checked

theorem exp59Cut :
    Real.exp 59 + 4 + 1 ≤ 11325 * 10 ^ 22 := by
  have checked := certificateHolds 1 sourceRows[1]
    (by set_option maxRecDepth 100000 in decide)
  norm_num [sourceRows, Holds] at checked
  linarith

theorem exp60Cut :
    Real.exp 60 + 4 + 1 ≤ 7785131284000000000000000004 := by
  have checked := certificateHolds 2 sourceRows[2]
    (by set_option maxRecDepth 100000 in decide)
  norm_num [sourceRows, Holds] at checked
  linarith

example : ¬ Real.exp 10 < (22026 : ℝ) := reject22026
example : ¬ Real.exp 59 + 4 + 1 ≤ (64 : ℝ) := rejectGoldbachTarget

/-- info: 'Hex.Interval.Experiment.PntExpUpper.certificateHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificateHolds

/-- info: 'Hex.IntervalMathlib.PntExpUpperConformance.exp10Lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp10Lt

/-- info: 'Hex.IntervalMathlib.PntExpUpperConformance.exp59Cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp59Cut

/-- info: 'Hex.IntervalMathlib.PntExpUpperConformance.exp60Cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp60Cut

/-- info: 'Hex.Interval.Experiment.PntExpUpper.reject22026' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reject22026

/-- info: 'Hex.Interval.Experiment.PntExpUpper.rejectGoldbachTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejectGoldbachTarget

end Hex.IntervalMathlib.PntExpUpperConformance
