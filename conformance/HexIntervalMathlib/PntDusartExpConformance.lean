/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntDusartExp
import HexIntervalMathlib.Experiment.PntExpPoint

/-!
# Source-pinned Dusart exponential conformance

Seven exact numerical leaves in the pinned PNT+ proofs are authenticated
against one table and discharged by one bounded range-reduced Taylor kernel.
The eighth uses the stronger checked `PntExpPoint.one_e9_le_exp_22` theorem.
-/

namespace Hex.IntervalMathlib.PntDusartExpConformance

open Hex.Interval.Experiment.PntDusartExp

#guard certificates.length == 7
#guard certificates == sourceRows
#guard certificates.all validCertificate
#guard firstFailure? certificates == none
#guard sourceRows[0]? ==
  some ⟨0, 29, 1, 4000000000000000000, .upperLe, 64, 12⟩
#guard sourceRows[6]? == some ⟨6, 43, 1, 4000000000000000000, .lowerLe, 64, 12⟩

def wrongLower : List Certificate :=
  certificates.map fun value =>
    if value.sourceIndex == 2 then { value with target := 400000 } else value

#guard firstFailure? wrongLower == some 2
#guard !validCertificate ⟨2, 1283, 100, 400000, .lowerLe, 64, 12⟩

theorem exp29Upper : Real.exp (29 : ℝ) ≤ (4e18 : ℝ) := by
  have bound : Real.exp (29 : ℝ) ≤ (4000000000000000000 : ℝ) := by
    simpa [certificates, sourceRows, Holds] using
      certificateHolds sourceRows[0] (by set_option maxRecDepth 100000 in decide)
  norm_num [OfScientific.ofScientific] at bound ⊢
  exact bound

theorem exp10Upper : Real.exp (10 : ℝ) < (4e18 : ℝ) := by
  have bound : Real.exp (10 : ℝ) < (4000000000000000000 : ℝ) := by
    simpa [certificates, sourceRows, Holds] using
      certificateHolds sourceRows[1] (by set_option maxRecDepth 100000 in decide)
  norm_num [OfScientific.ofScientific] at bound ⊢
  exact bound

theorem exp1283Lower : (370261 : Real) ≤ Real.exp (1283 / 100) := by
  simpa [certificates, sourceRows, Holds] using
    certificateHolds sourceRows[2] (by set_option maxRecDepth 100000 in decide)

theorem exp1312Lower : (492113 : Real) ≤ Real.exp (1312 / 100) := by
  simpa [certificates, sourceRows, Holds] using
    certificateHolds sourceRows[3] (by set_option maxRecDepth 100000 in decide)

theorem exp1452Lower : (2010733 : Real) ≤ Real.exp (1452 / 100) := by
  simpa [certificates, sourceRows, Holds] using
    certificateHolds sourceRows[4] (by set_option maxRecDepth 100000 in decide)

theorem exp1666Lower : (17051707 : Real) ≤ Real.exp (1666 / 100) := by
  simpa [certificates, sourceRows, Holds] using
    certificateHolds sourceRows[5] (by set_option maxRecDepth 100000 in decide)

theorem exp43Lower : (4e18 : ℝ) ≤ Real.exp (43 : ℝ) := by
  have bound : (4000000000000000000 : ℝ) ≤ Real.exp (43 : ℝ) := by
    simpa [certificates, sourceRows, Holds] using
      certificateHolds sourceRows[6] (by set_option maxRecDepth 100000 in decide)
  norm_num [OfScientific.ofScientific] at bound ⊢
  exact bound

theorem exp22Lower : (117352333 : Real) ≤ Real.exp 22 := by
  exact le_trans (by norm_num)
    Hex.Interval.Experiment.PntExpPoint.one_e9_le_exp_22

example : Real.exp (29 : ℝ) ≤ (4e18 : ℝ) := exp29Upper
example : Real.exp (10 : ℝ) < (4e18 : ℝ) := exp10Upper
example : (4e18 : ℝ) ≤ Real.exp (43 : ℝ) := exp43Lower

example : ¬ (400000 : Real) ≤ Real.exp (1283 / 100) := rejectWrongLower

/-- info: 'Hex.Interval.Experiment.PntDusartExp.certificateHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificateHolds

/-- info: 'Hex.IntervalMathlib.PntDusartExpConformance.exp29Upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp29Upper

/-- info: 'Hex.IntervalMathlib.PntDusartExpConformance.exp43Lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp43Lower

/-- info: 'Hex.IntervalMathlib.PntDusartExpConformance.exp22Lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp22Lower

/-- info: 'Hex.Interval.Experiment.PntDusartExp.rejectWrongLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejectWrongLower

end Hex.IntervalMathlib.PntDusartExpConformance
