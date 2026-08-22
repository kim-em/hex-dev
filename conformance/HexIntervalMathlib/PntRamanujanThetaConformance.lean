/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntRamanujanTheta

/-!
# Source-pinned Ramanujan theta conformance

The two source rows authenticate the complete range through 598 and the exact
point at 599 before their direct ordinary-kernel theorems are used.
-/

namespace Hex.IntervalMathlib.PntRamanujanThetaConformance

open Hex.Interval.Experiment.PntRamanujanTheta

set_option exponentiation.threshold 1024

#guard primeList.length == 109
#guard primeList.getLast? == some 599
#guard primeList.prod == primeProduct
#guard certificates.length == 1
#guard firstFailure? 0 certificates == none
#guard sourceRows[0]? == some ⟨⟨505⟩, 599, 65, 1000, 20, 812, 813⟩
#guard rangeRows[0]? == some ⟨⟨500⟩, 3, 599, 768, 1000, 20⟩
#guard checkRange 3 599
#guard validRangeCertificate 0 rangeRows[0]
#guard firstRangeFailure? 0 rangeRows == none

def wrongTolerance : List Certificate :=
  [{ sourceRows[0] with toleranceNumerator := 49 }]

def wrongUpperExponent : List Certificate :=
  [{ sourceRows[0] with upperExponent := 812 }]

def wrongCoordinate : List Certificate :=
  [{ sourceRows[0] with coordinate := ⟨506⟩ }]

def wrongRangeShift : List RangeCertificate :=
  [{ rangeRows[0] with start := 4 }]

def wrongRangeTolerance : List RangeCertificate :=
  [{ rangeRows[0] with toleranceNumerator := 767 }]

def wrongRangeCoordinate : List RangeCertificate :=
  [{ rangeRows[0] with coordinate := ⟨501⟩ }]

#guard firstFailure? 0 wrongTolerance == some ⟨505⟩
#guard !checkPointShape wrongTolerance[0]
#guard !validCertificate 0 wrongTolerance[0]
#guard firstFailure? 0 wrongUpperExponent == some ⟨505⟩
#guard !checkPointShape wrongUpperExponent[0]
#guard !validCertificate 0 wrongUpperExponent[0]
#guard checkPointShape wrongCoordinate[0]
#guard firstFailure? 0 wrongCoordinate == some ⟨505⟩
#guard !validCertificate 0 wrongCoordinate[0]
#guard firstRangeFailure? 0 wrongRangeShift == some ⟨500⟩
#guard !validRangeCertificate 0 wrongRangeShift[0]
#guard firstRangeFailure? 0 wrongRangeTolerance == some ⟨500⟩
#guard !validRangeCertificate 0 wrongRangeTolerance[0]
#guard RangeCertificate.checkShape wrongRangeCoordinate[0]
#guard firstRangeFailure? 0 wrongRangeCoordinate == some ⟨500⟩
#guard !validRangeCertificate 0 wrongRangeCoordinate[0]

theorem thetaRange (x : ℝ) (hx : x ∈ Set.Ico (3 : ℝ) 599) :
    |Chebyshev.theta x - x| ≤ (768 / 1000 : ℝ) * x := by
  have checked := rangeCertificateHolds 0 rangeRows[0] (by
    set_option maxRecDepth 100000 in
      decide)
  norm_num [rangeRows, RangeHolds] at checked ⊢
  exact checked x hx.1 hx.2

theorem theta599Error :
    |Chebyshev.theta 599 - 599| ≤ (65 / 1000 : ℝ) * 599 := by
  have checked := certificateHolds 0 sourceRows[0] (by
    set_option maxRecDepth 100000 in
      decide)
  norm_num [sourceRows, Holds] at checked ⊢
  exact checked

example :
    ¬ |Chebyshev.theta 599 - 599| ≤ (49 / 1000 : ℝ) * 599 :=
  rejectTolerance49

/-- info: 'Hex.Interval.Experiment.PntRamanujanTheta.certificateHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificateHolds

/--
info: 'Hex.Interval.Experiment.PntRamanujanTheta.rangeCertificateHolds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rangeCertificateHolds

/--
info: 'Hex.IntervalMathlib.PntRamanujanThetaConformance.theta599Error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms theta599Error

/-- info: 'Hex.IntervalMathlib.PntRamanujanThetaConformance.thetaRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thetaRange

/-- info: 'Hex.Interval.Experiment.PntRamanujanTheta.rejectTolerance49' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejectTolerance49

end Hex.IntervalMathlib.PntRamanujanThetaConformance
