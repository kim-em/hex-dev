/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntFks2Mu

/-!
# Source-pinned FKS2 mu-asymptotic conformance

Four exact source coordinates reuse two package-owned numerical facts. Each
adapter still authenticates its own file and line before entering the shared
ordinary-kernel proof.
-/

namespace Hex.IntervalMathlib.PntFks2MuConformance

open Hex.Interval.Experiment.PntFks2Mu

#guard certificates.length == 4
#guard certificates == sourceRows
#guard firstFailure? 0 certificates == none
#guard sourceRows[0]? == some
  ⟨⟨.fks2, 4274⟩, .sqrtLower, 20000, 1, 1414213562, 10000000⟩
#guard sourceRows[1]? == some
  ⟨⟨.fks2, 4282⟩, .expUpper, 13689, 1000000, 10138790, 10000000⟩
#guard sourceRows[2]? == some
  ⟨⟨.cor14, 24⟩, .sqrtLower, 20000, 1, 1414213562, 10000000⟩
#guard sourceRows[3]? == some
  ⟨⟨.cor14, 32⟩, .expUpper, 13689, 1000000, 10138790, 10000000⟩

def wrongSqrt : List Certificate :=
  { sourceRows[0] with targetNum := 142, targetDen := 1 } :: sourceRows.drop 1

def wrongExp : List Certificate :=
  sourceRows.take 1 ++
    [{ sourceRows[1] with targetNum := 1, targetDen := 1 }] ++ sourceRows.drop 2

#guard firstFailure? 0 wrongSqrt == some ⟨.fks2, 4274⟩
#guard !checkComparison wrongSqrt[0]
#guard !validCertificate 0 wrongSqrt[0]
#guard firstFailure? 0 wrongExp == some ⟨.fks2, 4282⟩
#guard !checkComparison wrongExp[1]
#guard !validCertificate 1 wrongExp[1]

def wrongCoordinate : List Certificate :=
  { sourceRows[0] with coordinate := ⟨.fks2, 4275⟩ } :: sourceRows.drop 1

#guard firstFailure? 0 wrongCoordinate == some ⟨.fks2, 4274⟩
#guard checkComparison wrongCoordinate[0]
#guard !validCertificate 0 wrongCoordinate[0]

theorem fks2SqrtLower :
    (141.4213562 : ℝ) ≤ Real.sqrt 20000 := by
  have checked :=
    certificateHolds 0 sourceRows[0] (by set_option maxRecDepth 100000 in decide)
  norm_num [sourceRows, Holds] at checked ⊢
  exact checked

theorem fks2ExpUpper :
    Real.exp ((0.117 : ℝ) ^ 2) ≤ (1.0138790 : ℝ) := by
  have checked :=
    certificateHolds 1 sourceRows[1] (by set_option maxRecDepth 100000 in decide)
  norm_num [sourceRows, Holds] at checked ⊢
  exact checked

theorem cor14SqrtLower :
    (141.4213562 : ℝ) ≤ Real.sqrt 20000 := by
  have checked :=
    certificateHolds 2 sourceRows[2] (by set_option maxRecDepth 100000 in decide)
  norm_num [sourceRows, Holds] at checked ⊢
  exact checked

theorem cor14ExpUpper :
    Real.exp ((0.117 : ℝ) ^ 2) ≤ (1.0138790 : ℝ) := by
  have checked :=
    certificateHolds 3 sourceRows[3] (by set_option maxRecDepth 100000 in decide)
  norm_num [sourceRows, Holds] at checked ⊢
  exact checked

example : ¬ (142 : ℝ) ≤ Real.sqrt 20000 := rejectWrongSqrt

/-- info: 'Hex.Interval.Experiment.PntFks2Mu.certificateHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificateHolds

/-- info: 'Hex.IntervalMathlib.PntFks2MuConformance.fks2SqrtLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fks2SqrtLower

/-- info: 'Hex.IntervalMathlib.PntFks2MuConformance.fks2ExpUpper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fks2ExpUpper

/-- info: 'Hex.IntervalMathlib.PntFks2MuConformance.cor14SqrtLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cor14SqrtLower

/-- info: 'Hex.IntervalMathlib.PntFks2MuConformance.cor14ExpUpper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cor14ExpUpper

/-- info: 'Hex.Interval.Experiment.PntFks2Mu.rejectWrongSqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejectWrongSqrt

end Hex.IntervalMathlib.PntFks2MuConformance
