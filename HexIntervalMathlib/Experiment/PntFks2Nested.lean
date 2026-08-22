/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntLogNatural
public import HexInterval.Experiment.PntFks2Nested

@[expose] public section

/-!
# Checked semantics for the FKS2 nested-log premise

The merged natural-log atanh provider checks `2 < log 14 < 3`. The strict
lower cut makes the second logarithm positive, yielding the exact source
positivity statement without importing the PNT+ or LeanCert theorem.
-/

namespace Hex.Interval.Experiment.PntFks2Nested

open Finset

def Holds (value : Certificate) : Prop :=
  (value.threshold : ℝ) <
    Real.log value.input + Real.log (Real.log value.input)

private theorem log14Window :
    (2 : ℝ) < Real.log 14 ∧ Real.log 14 < 3 := by
  apply PntLogNatural.rangeWindow 14 3 (3 / 11 : ℝ) 2 3 <;>
    norm_num [PntLogNatural.partialSum, PntLogNatural.tailBound,
      Finset.sum_range_succ]

private theorem sourceHolds : Holds sourceRows[0] := by
  have innerPositive : 0 < Real.log (Real.log 14) :=
    Real.log_pos (by linarith [log14Window.1])
  norm_num [Holds, sourceRows]
  linarith [log14Window.1]

/-- Every authenticated source row proves the exact nested-log premise. The
fixed payload fields are source constants, not general checked parameters. -/
theorem certificateHolds (index : Nat) (value : Certificate)
    (valid : validCertificate index value = true) : Holds value := by
  simp only [validCertificate, Bool.and_eq_true] at valid
  cases index with
  | zero =>
      have accepted := valid.1
      simp [sourceRows] at accepted
      subst value
      exact sourceHolds
  | succ index =>
      simp [sourceRows] at valid

/-- Raising the source threshold from `1` to `5` makes the claim false. -/
theorem rejectThresholdFive :
    ¬ (0 : ℝ) < Real.log 14 + Real.log (Real.log 14) - 5 := by
  intro wrong
  have inputPositive : 0 < Real.log 14 := by linarith [log14Window.1]
  have nestedUpper : Real.log (Real.log 14) < Real.log 3 :=
    (Real.log_lt_log_iff inputPositive (by norm_num)).2 log14Window.2
  have expLower := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
  have logThreeUpper : Real.log 3 < 2 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 (by norm_num at expLower ⊢; exact expLower)
  linarith [log14Window.2]

end Hex.Interval.Experiment.PntFks2Nested

end
