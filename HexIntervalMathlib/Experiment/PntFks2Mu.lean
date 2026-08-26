/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import HexIntervalMathlib.Experiment.PntFks2Shard
public import HexInterval.Experiment.PntFks2Mu

@[expose] public section

/-!
# Checked semantics for the FKS2 mu-asymptotic leaves

The existing FKS2 rational Taylor remainder proves the exponential rows. An
exact square comparison proves the square-root rows.
-/

namespace Hex.Interval.Experiment.PntFks2Mu

open PntFks2Shard

def Holds (value : Certificate) : Prop :=
  match value.relation with
  | .sqrtLower =>
      (value.targetNum : ℝ) / value.targetDen ≤
        Real.sqrt ((value.inputNum : ℝ) / value.inputDen)
  | .expUpper =>
      Real.exp ((value.inputNum : ℝ) / value.inputDen) ≤
        (value.targetNum : ℝ) / value.targetDen

theorem checkedHolds (value : Certificate)
    (checked : checkComparison value = true) : Holds value := by
  have inputValue : value.inputQ.value =
      (value.inputNum : ℝ) / value.inputDen := by
    exact PntFks2Shard.divInt_value value.inputNum value.inputDen
  have targetValue : value.targetQ.value =
      (value.targetNum : ℝ) / value.targetDen := by
    exact PntFks2Shard.divInt_value value.targetNum value.targetDen
  unfold checkComparison at checked
  unfold Holds
  generalize relationEq : value.relation = relation at checked ⊢
  cases relation with
  | sqrtLower =>
      simp only [Bool.and_eq_true] at checked
      have targetNonnegative := (PntFks2Shard.qLe_iff 0 value.targetQ).mp checked.1
      have square :=
        (PntFks2Shard.qLe_iff (qmul value.targetQ value.targetQ) value.inputQ).mp
          checked.2
      have targetNonnegative' :
          0 ≤ (value.targetNum : ℝ) / value.targetDen := by
        rw [← targetValue]
        simpa [PntFks2Shard.Q.value] using targetNonnegative
      rw [PntFks2Shard.qmul_value, inputValue, targetValue] at square
      apply (Real.le_sqrt targetNonnegative'
        (le_trans (mul_self_nonneg ((value.targetNum : ℝ) / value.targetDen))
          square)).2
      simpa [pow_two] using square
  | expUpper =>
      simp only [Bool.and_eq_true] at checked
      have inputNonnegative := (PntFks2Shard.qLe_iff 0 value.inputQ).mp checked.1.1
      have inputAtMostOne := (PntFks2Shard.qLe_iff value.inputQ 1).mp checked.1.2
      have final :=
        (PntFks2Shard.qLe_iff (taylorUpper value.inputQ) value.targetQ).mp checked.2
      have analytic := PntFks2Shard.exp_le_taylorUpper value.inputQ
        (by simpa [PntFks2Shard.Q.value] using inputNonnegative)
        (by simpa [PntFks2Shard.Q.value] using inputAtMostOne)
      rw [inputValue] at analytic
      rw [targetValue] at final
      exact analytic.trans final

/-- Every authenticated source row proves its exact numerical leaf. -/
theorem certificateHolds (index : Nat) (value : Certificate)
    (valid : validCertificate index value = true) : Holds value := by
  simp only [validCertificate, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact checkedHolds value valid.2

/-- Raising the source square-root lower endpoint to `142` is false. -/
theorem rejectWrongSqrt : ¬ (142 : ℝ) ≤ Real.sqrt 20000 := by
  intro wrong
  have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 20000)
  have nonnegative := Real.sqrt_nonneg (20000 : ℝ)
  nlinarith

end Hex.Interval.Experiment.PntFks2Mu

end
