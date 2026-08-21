/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Shard
public import HexIntervalMathlib.Experiment.PntExpPoint
public import HexInterval.Experiment.PntExpUpper

@[expose] public section

/-!
# Checked semantics for pinned positive exponential upper bounds

The shared analytic proof is applied after authenticating the source row.
The reduction denominator, Taylor degree, and seven-squaring path are fixed
package constants, not general checked parameters.
-/

namespace Hex.Interval.Experiment.PntExpUpper

open PntFks2Shard

def Holds (value : Certificate) : Prop :=
  match value.relation with
  | .strict => Real.exp value.exponent + value.additive < value.target
  | .weak => Real.exp value.exponent + value.additive ≤ value.target

theorem checkedHolds (value : Certificate)
    (checked : checkComparison value = true) : Holds value := by
  have reducedValue : value.reducedQ.value =
      (value.exponent : ℝ) / 128 := by
    exact PntFks2Shard.divInt_value value.exponent 128
  have additiveValue : value.additiveQ.value = value.additive := by
    rw [Certificate.additiveQ, PntFks2Shard.divInt_value]
    norm_num
  have targetValue : value.targetQ.value = value.target := by
    rw [Certificate.targetQ, PntFks2Shard.divInt_value]
    norm_num
  simp only [checkComparison, Bool.and_eq_true] at checked
  have reducedNonnegative :=
    (PntFks2Shard.qLe_iff 0 value.reducedQ).mp checked.1.1
  have reducedAtMostOne :=
    (PntFks2Shard.qLe_iff value.reducedQ 1).mp checked.1.2
  have taylor := PntFks2Shard.exp_le_taylorUpper value.reducedQ
    (by simpa [PntFks2Shard.Q.value] using reducedNonnegative)
    (by simpa [PntFks2Shard.Q.value] using reducedAtMostOne)
  have power := pow_le_pow_left₀ (Real.exp_pos _).le taylor 128
  rw [← Real.exp_nat_mul] at power
  have split : ((128 : Nat) : ℝ) * value.reducedQ.value = value.exponent := by
    rw [reducedValue]
    ring
  rw [split] at power
  have upper :
      Real.exp value.exponent + value.additive ≤
        (qadd (qpow128 (taylorUpper value.reducedQ)) value.additiveQ).value := by
    rw [PntFks2Shard.qadd_value, PntFks2Shard.qpow128_value, additiveValue]
    simpa [add_comm] using add_le_add_right power value.additive
  unfold Holds
  generalize relationEq : value.relation = relation at checked ⊢
  cases relation with
  | strict =>
    have final := (PntFks2Shard.qLt_iff
      (qadd (qpow128 (taylorUpper value.reducedQ)) value.additiveQ)
      value.targetQ).mp checked.2
    rw [targetValue] at final
    exact upper.trans_lt final
  | weak =>
    have final := (PntFks2Shard.qLe_iff
      (qadd (qpow128 (taylorUpper value.reducedQ)) value.additiveQ)
      value.targetQ).mp checked.2
    rw [targetValue] at final
    exact upper.trans final

/-- Every authenticated source row proves its exact numerical leaf. -/
theorem certificateHolds (index : Nat) (value : Certificate)
    (valid : validCertificate index value = true) : Holds value := by
  simp only [validCertificate, Bool.and_eq_true] at valid
  exact checkedHolds value valid.2

/-- The immediately smaller integer endpoint for the FKS2 row is false. -/
theorem reject22026 : ¬ Real.exp 10 < (22026 : ℝ) := by
  have lower : (22026 : ℝ) < Real.exp 10 := by
    apply PntExpPoint.poweredLower 10 (1 / 2) (20609 / 12500) 22026 20 <;>
      norm_num [PntExpPoint.partialSum, PntExpPoint.tailBound,
        Finset.sum_range_succ]
  linarith

/-- A grossly low replacement endpoint for the first Goldbach row is false. -/
theorem rejectGoldbachTarget :
    ¬ Real.exp 59 + 4 + 1 ≤ (64 : ℝ) := by
  intro wrong
  have lower := Real.add_one_lt_exp (show (59 : ℝ) ≠ 0 by norm_num)
  norm_num at lower wrong
  linarith

end Hex.Interval.Experiment.PntExpUpper

end
