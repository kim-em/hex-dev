/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntBKLNWExp
public import HexIntervalMathlib.Experiment.PntBKLNWPow
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics

@[expose] public section

namespace Hex.Interval.Experiment.PntBKLNWExp

open Real Finset

noncomputable def expSum (b N : Nat) : ℝ :=
  ∑ k ∈ Icc 3 N, Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3))

noncomputable def lowerBaseValue (k : Nat) : ℝ :=
  lowerBaseNumerator k / baseDenominator

noncomputable def upperBaseValue (k : Nat) : ℝ :=
  upperBaseNumerator k / baseDenominator

private theorem expWindow (x lower upper : ℝ) (bound : |x| ≤ 1)
    (checkedLower :
      lower < ∑ k ∈ Finset.range 14, x ^ k / Nat.factorial k -
        |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)))
    (checkedUpper :
      ∑ k ∈ Finset.range 14, x ^ k / Nat.factorial k +
        |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) < upper) :
    lower < Real.exp x ∧ Real.exp x < upper := by
  have remainder := Real.exp_bound (x := x) (n := 14) bound (by norm_num)
  rw [abs_le] at remainder
  constructor <;> linarith

set_option maxHeartbeats 1200000 in
theorem baseWindow {k : Nat} (lower : 4 ≤ k) (upper : k ≤ 64) :
    lowerBaseValue k < Real.exp ((1 : ℝ) / k - 1 / 3) ∧
      Real.exp ((1 : ℝ) / k - 1 / 3) < upperBaseValue k := by
  interval_cases k <;>
    apply expWindow <;>
    norm_num [lowerBaseValue, upperBaseValue, lowerBaseNumerator,
      upperBaseNumerator, baseDenominator, Finset.sum_range_succ]

noncomputable def lowerBand (b stop : Nat) : ℝ :=
  ∑ k ∈ Icc 4 stop, lowerBaseValue k ^ b

noncomputable def upperBand (b stop : Nat) : ℝ :=
  ∑ k ∈ Icc 4 stop, upperBaseValue k ^ b

private theorem bandRatio (numerator : Nat → Nat) (b stop : Nat) :
    (∑ k ∈ Icc 4 stop,
        ((numerator k : ℝ) / baseDenominator) ^ b) =
      (bandPowerSum numerator b stop : ℝ) / baseDenominator ^ b := by
  induction stop with
  | zero => simp [bandPowerSum]
  | succ stop ih =>
      by_cases h : 4 ≤ stop + 1
      · rw [sum_Icc_succ_top h, bandPowerSum, ite_eq_left h, ih]
        rw [div_pow]
        push_cast
        field_simp
      · have empty : Icc 4 (stop + 1) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro k member
          have bounds := mem_Icc.mp member
          omega
        rw [empty]
        simp [bandPowerSum, h]

private theorem lowerBandRatio (b stop : Nat) :
    lowerBand b stop =
      (bandPowerSum lowerBaseNumerator b stop : ℝ) /
        baseDenominator ^ b := by
  exact bandRatio lowerBaseNumerator b stop

private theorem upperBandRatio (b stop : Nat) :
    upperBand b stop =
      (bandPowerSum upperBaseNumerator b stop : ℝ) /
        baseDenominator ^ b := by
  exact bandRatio upperBaseNumerator b stop

private theorem termThree (b : Nat) :
    Real.exp ((b : ℝ) * ((1 : ℝ) / 3 - 1 / 3)) = 1 := by
  norm_num

private theorem termWindow {b k : Nat} (lower : 4 ≤ k) (upper : k ≤ 64) :
    lowerBaseValue k ^ b ≤
        Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) ∧
      Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
        upperBaseValue k ^ b := by
  rw [Real.exp_nat_mul]
  constructor
  · exact pow_le_pow_left₀
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (baseWindow lower upper).1.le b
  · exact pow_le_pow_left₀ (by positivity) (baseWindow lower upper).2.le b

private theorem tailTerm {b k : Nat} (lower : 64 ≤ k) :
    Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
      upperBaseValue 64 ^ b := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by positivity)
  calc
    Real.exp ((1 : ℝ) / k - 1 / 3) ≤
        Real.exp ((1 : ℝ) / 64 - 1 / 3) := by
      apply Real.exp_le_exp.mpr
      have reciprocal : (1 : ℝ) / k ≤ 1 / 64 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast lower)
      linarith
    _ ≤ upperBaseValue 64 := (baseWindow (by decide) (by decide)).2.le

theorem expSumNoTail {b N : Nat} (atLeast : 4 ≤ N) (atMost : N ≤ 63) :
    1 + lowerBand b N ≤ expSum b N ∧
      expSum b N ≤ 1 + upperBand b N := by
  unfold expSum
  rw [← insert_Icc_add_one_left_eq_Icc (show 3 ≤ N by omega), sum_insert (by simp)]
  simp only [Nat.reduceAdd]
  have term3 :
      Real.exp ((b : ℝ) * ((1 : ℝ) / (3 : Nat) - 1 / 3)) = 1 := by
    norm_num
  rw [term3]
  constructor
  · gcongr
    apply sum_le_sum
    intro k member
    exact (termWindow (mem_Icc.mp member).1
      ((mem_Icc.mp member).2.trans (atMost.trans (by decide)))).1
  · gcongr
    apply sum_le_sum
    intro k member
    exact (termWindow (mem_Icc.mp member).1
      ((mem_Icc.mp member).2.trans (atMost.trans (by decide)))).2

theorem expSumWithTail {b N : Nat} (atLeast : 64 ≤ N) :
    1 + lowerBand b 63 ≤ expSum b N ∧
      expSum b N ≤ 1 + upperBand b 63 +
        ((N - 63 : Nat) : ℝ) * upperBaseValue 64 ^ b := by
  unfold expSum
  rw [← insert_Icc_add_one_left_eq_Icc (show 3 ≤ N by omega), sum_insert (by simp)]
  simp only [Nat.reduceAdd]
  have term3 :
      Real.exp ((b : ℝ) * ((1 : ℝ) / (3 : Nat) - 1 / 3)) = 1 := by
    norm_num
  rw [term3]
  have union : Icc (4 : Nat) N = Icc 4 63 ∪ Icc 64 N := by
    ext k
    simp only [mem_Icc, mem_union]
    omega
  have disjoint : Disjoint (Icc (4 : Nat) 63) (Icc 64 N) := by
    simp only [Finset.disjoint_left, mem_Icc]
    omega
  rw [union, sum_union disjoint]
  have bandLower : lowerBand b 63 ≤
      ∑ k ∈ Icc (4 : Nat) 63,
        Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) := by
    unfold lowerBand
    apply sum_le_sum
    intro k member
    exact (termWindow (mem_Icc.mp member).1
      ((mem_Icc.mp member).2.trans (by decide))).1
  have bandUpper :
      (∑ k ∈ Icc (4 : Nat) 63,
        Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3))) ≤
        upperBand b 63 := by
    unfold upperBand
    apply sum_le_sum
    intro k member
    exact (termWindow (mem_Icc.mp member).1
      ((mem_Icc.mp member).2.trans (by decide))).2
  have tailUpper :
      (∑ k ∈ Icc (64 : Nat) N,
        Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3))) ≤
        ((N - 63 : Nat) : ℝ) * upperBaseValue 64 ^ b := by
    calc
      ∑ k ∈ Icc (64 : Nat) N,
          Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
          ∑ _k ∈ Icc (64 : Nat) N, upperBaseValue 64 ^ b := by
        apply sum_le_sum
        intro k member
        exact tailTerm (mem_Icc.mp member).1
      _ = ((Icc (64 : Nat) N).card : ℝ) * upperBaseValue 64 ^ b := by simp
      _ = ((N - 63 : Nat) : ℝ) * upperBaseValue 64 ^ b := by
        congr 2
        norm_num [Nat.card_Icc]
        omega
  constructor
  · calc
      1 + lowerBand b 63 ≤
          1 + ∑ k ∈ Icc (4 : Nat) 63,
            Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) :=
        by simpa [add_comm] using add_le_add_left bandLower 1
      _ ≤ 1 + (∑ k ∈ Icc (4 : Nat) 63,
            Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) +
          ∑ k ∈ Icc (64 : Nat) N,
            Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3))) := by
        have tailNonneg : 0 ≤ ∑ k ∈ Icc (64 : Nat) N,
            Real.exp ((b : ℝ) * ((1 : ℝ) / k - 1 / 3)) :=
          sum_nonneg fun _ _ => Real.exp_nonneg _
        linarith
  · simpa [add_assoc, add_comm, add_left_comm] using
      add_le_add_left (add_le_add bandUpper tailUpper) 1

private theorem floorFromLogWindow (b N : Nat)
    (lowerCheck : N * 69314718055994530942 ≤ b * 10 ^ 20)
    (upperCheck : b * 10 ^ 20 < (N + 1) * 69314718055994530941) :
    ⌊(b : ℝ) / Real.log 2⌋₊ = N := by
  rw [Nat.floor_eq_iff (div_nonneg (by positivity) (Real.log_nonneg (by norm_num)))]
  have logWindow :=
    Hex.IntervalMathlib.Experiment.LogTablePrecision.decimal20
  constructor
  · apply (le_div_iff₀ (Real.log_pos (by norm_num))).2
    have checked : (N : ℝ) *
        69314718055994530942 ≤ b * 10 ^ 20 := by
      exact_mod_cast lowerCheck
    norm_num at checked ⊢
    nlinarith [logWindow.2]
  · apply (div_lt_iff₀ (Real.log_pos (by norm_num))).2
    have checked : (b : ℝ) * 10 ^ 20 < (N + 1 : Nat) *
        69314718055994530941 := by
      exact_mod_cast upperCheck
    norm_num at checked ⊢
    nlinarith [logWindow.1]

private theorem sourceFloor (value : Certificate) (valid : Valid value) :
    ⌊Real.log (Real.exp value.argument) / Real.log 2⌋₊ = value.floor := by
  rw [Real.log_exp]
  rcases valid with ⟨sourceIndex, source, _⟩
  interval_cases value.sourceIndex <;>
    simp [sourceRecord?] at source <;>
    rcases source with ⟨argument, floor, _⟩ <;>
    rw [← argument, ← floor] <;>
    apply floorFromLogWindow <;> norm_num

private theorem floorAtLeast (value : Certificate) (valid : Valid value) :
    4 ≤ value.floor := by
  rcases valid with ⟨sourceIndex, source, _⟩
  interval_cases value.sourceIndex <;>
    simp [sourceRecord?] at source <;> omega

theorem sourceExp (value : Certificate) (valid : Valid value) :
    PntBKLNWPow.sourceF (Real.exp value.argument) =
      expSum value.argument value.floor := by
  unfold PntBKLNWPow.sourceF expSum
  rw [sourceFloor value valid]
  apply sum_congr rfl
  intro k _member
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]

private theorem alphaRatio :
    (1 + 193571378 / (10 : ℝ) ^ 16) =
      (alphaNumerator : ℝ) / alphaDenominator := by
  norm_num [alphaNumerator, alphaDenominator]

private theorem lowerSumRatio (value : Certificate)
    (denominator : value.baseDenominator = baseDenominator) :
    1 + lowerBand value.argument value.exactStop =
      (lowerSumNumerator value : ℝ) / sumDenominator value := by
  unfold lowerSumNumerator sumDenominator
  rw [denominator, lowerBandRatio]
  push_cast
  field_simp [baseDenominator]

private theorem upperSumRatio (value : Certificate)
    (denominator : value.baseDenominator = baseDenominator) :
    1 + upperBand value.argument value.exactStop +
        value.tailCardinality *
          upperBaseValue value.tailStart ^ value.argument =
      (upperSumNumerator value : ℝ) / sumDenominator value := by
  unfold upperSumNumerator sumDenominator upperBaseValue
  rw [denominator, upperBandRatio, div_pow]
  push_cast
  field_simp [baseDenominator]

private theorem sumWindow (value : Certificate) (valid : Valid value) :
    1 + lowerBand value.argument value.exactStop ≤
        expSum value.argument value.floor ∧
      expSum value.argument value.floor ≤
        1 + upperBand value.argument value.exactStop +
          value.tailCardinality *
            upperBaseValue value.tailStart ^ value.argument := by
  rcases valid with
    ⟨sourceIndex, source, exactStop, tailStart, tailCardinality,
      denominator, targetPositive, lowerTarget, upperTarget⟩
  by_cases small : value.floor ≤ 63
  · have stop : value.exactStop = value.floor := by
      rw [exactStop, Nat.min_eq_left small]
    have noTail : value.tailCardinality = 0 := by omega
    rw [stop, noTail]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact expSumNoTail (floorAtLeast value
      ⟨sourceIndex, source, exactStop, tailStart, tailCardinality,
        denominator, targetPositive, lowerTarget, upperTarget⟩) small
  · have large : 64 ≤ value.floor := by omega
    have stop : value.exactStop = 63 := by
      rw [exactStop, Nat.min_eq_right (by omega)]
    have start : value.tailStart = 64 := by omega
    have count : value.floor - 63 = value.tailCardinality := by omega
    rw [stop, start, ← count]
    exact expSumWithTail large

/-- Sound two-sided result for every certificate accepted by the pure-natural
checker. The selected source row, finite split, table scale, and both target
cuts all remain hypotheses of this one reusable theorem. -/
theorem certificateWindow (value : Certificate) (valid : Valid value) :
    (value.lowerNumerator : ℝ) / value.targetDenominator ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp value.argument) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp value.argument) ≤
        (value.upperNumerator : ℝ) / value.targetDenominator := by
  rcases valid with
    ⟨sourceIndex, source, exactStop, tailStart, tailCardinality,
      denominator, targetPositive, lowerTarget, upperTarget⟩
  have valid' : Valid value :=
    ⟨sourceIndex, source, exactStop, tailStart, tailCardinality,
      denominator, targetPositive, lowerTarget, upperTarget⟩
  have analytic := sumWindow value valid'
  rw [sourceExp value valid']
  constructor
  · calc
      (value.lowerNumerator : ℝ) / value.targetDenominator ≤
          ((alphaNumerator : ℝ) * lowerSumNumerator value) /
            (alphaDenominator * sumDenominator value) := by
        have denominatorPositive :
            (0 : ℝ) < alphaDenominator * sumDenominator value := by
          unfold alphaDenominator sumDenominator
          rw [denominator]
          unfold baseDenominator
          positivity
        apply (div_le_div_iff₀ (by exact_mod_cast targetPositive)
          denominatorPositive).2
        exact_mod_cast lowerTarget
      _ = (1 + 193571378 / (10 : ℝ) ^ 16) *
          (1 + lowerBand value.argument value.exactStop) := by
        rw [alphaRatio, lowerSumRatio value denominator, div_mul_div_comm]
      _ ≤ (1 + 193571378 / (10 : ℝ) ^ 16) *
          expSum value.argument value.floor := by
        gcongr
        exact analytic.1
  · calc
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          expSum value.argument value.floor ≤
          (1 + 193571378 / (10 : ℝ) ^ 16) *
            (1 + upperBand value.argument value.exactStop +
              value.tailCardinality *
                upperBaseValue value.tailStart ^ value.argument) := by
        gcongr
        exact analytic.2
      _ = ((alphaNumerator : ℝ) * upperSumNumerator value) /
          (alphaDenominator * sumDenominator value) := by
        rw [alphaRatio, upperSumRatio value denominator, div_mul_div_comm]
      _ ≤ (value.upperNumerator : ℝ) / value.targetDenominator := by
        have denominatorPositive :
            (0 : ℝ) < alphaDenominator * sumDenominator value := by
          unfold alphaDenominator sumDenominator
          rw [denominator]
          unfold baseDenominator
          positivity
        apply (div_le_div_iff₀ denominatorPositive
          (by exact_mod_cast targetPositive)).2
        exact_mod_cast upperTarget

theorem exp20Provider :
    (14262 : ℝ) / 10000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 20) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 20) ≤ (14263 : ℝ) / 10000 :=
  certificateWindow exp20 (by set_option exponentiation.threshold 500 in decide)

theorem exp25Provider :
    (12195 : ℝ) / 10000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 25) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 25) ≤ (12196 : ℝ) / 10000 :=
  certificateWindow exp25 (by set_option exponentiation.threshold 500 in decide)

theorem exp30Provider :
    (11210 : ℝ) / 10000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 30) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 30) ≤ (11211 : ℝ) / 10000 :=
  certificateWindow exp30 (by set_option exponentiation.threshold 500 in decide)

theorem exp35Provider :
    (107086 : ℝ) / 100000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 35) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 35) ≤ (107087 : ℝ) / 100000 :=
  certificateWindow exp35 (by set_option exponentiation.threshold 500 in decide)

theorem exp40Provider :
    (104319 : ℝ) / 100000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 40) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 40) ≤ (104320 : ℝ) / 100000 :=
  certificateWindow exp40 (by set_option exponentiation.threshold 500 in decide)

theorem exp43Provider :
    (103252 : ℝ) / 100000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 43) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 43) ≤ (103253 : ℝ) / 100000 :=
  certificateWindow exp43 (by set_option exponentiation.threshold 500 in decide)

theorem exp100Provider :
    (10002420 : ℝ) / 10000000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 100) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 100) ≤
        (10002421 : ℝ) / 10000000 :=
  certificateWindow exp100 (by set_option exponentiation.threshold 500 in decide)

theorem exp150Provider :
    (1000003748 : ℝ) / 1000000000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 150) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 150) ≤
        (1000003758 : ℝ) / 1000000000 :=
  certificateWindow exp150 (by set_option exponentiation.threshold 500 in decide)

theorem exp200Provider :
    (100000007713 : ℝ) / 100000000000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 200) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 200) ≤
        (100000007813 : ℝ) / 100000000000 :=
  certificateWindow exp200 (by set_option exponentiation.threshold 500 in decide)

theorem exp250Provider :
    (100000002025 : ℝ) / 100000000000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 250) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 250) ≤
        (100000002125 : ℝ) / 100000000000 :=
  certificateWindow exp250 (by set_option exponentiation.threshold 500 in decide)

theorem exp300Provider :
    (100000001937 : ℝ) / 100000000000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 300) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 300) ≤
        (100000002037 : ℝ) / 100000000000 :=
  certificateWindow exp300 (by set_option exponentiation.threshold 500 in decide)

/-! Exact statement shapes of the 22 source declarations. -/

theorem a2Exp20Lower : (1.4262 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 20) := by
  convert exp20Provider.1 using 1; norm_num
theorem a2Exp20Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 20) ≤
      (1.4262 : ℝ) + 1 / 10 ^ 4 := by
  convert exp20Provider.2 using 1; norm_num

theorem a2Exp25Lower : (1.2195 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 25) := by
  convert exp25Provider.1 using 1; norm_num
theorem a2Exp25Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 25) ≤
      (1.2195 : ℝ) + 1 / 10 ^ 4 := by
  convert exp25Provider.2 using 1; norm_num

theorem a2Exp30Lower : (1.1210 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 30) := by
  convert exp30Provider.1 using 1; norm_num
theorem a2Exp30Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 30) ≤
      (1.1210 : ℝ) + 1 / 10 ^ 4 := by
  convert exp30Provider.2 using 1; norm_num

theorem a2Exp35Lower : (1.07086 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 35) := by
  convert exp35Provider.1 using 1; norm_num
theorem a2Exp35Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 35) ≤
      (1.07086 : ℝ) + 1 / 10 ^ 5 := by
  convert exp35Provider.2 using 1; norm_num

theorem a2Exp40Lower : (1.04319 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 40) := by
  convert exp40Provider.1 using 1; norm_num
theorem a2Exp40Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 40) ≤
      (1.04319 : ℝ) + 1 / 10 ^ 5 := by
  convert exp40Provider.2 using 1; norm_num

theorem a2Exp43Lower : (1.03252 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 43) := by
  convert exp43Provider.1 using 1; norm_num
theorem a2Exp43Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 43) ≤
      (1.03252 : ℝ) + 1 / 10 ^ 5 := by
  convert exp43Provider.2 using 1; norm_num

theorem a2Exp100Lower : (1.0002420 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 100) := by
  convert exp100Provider.1 using 1; norm_num
theorem a2Exp100Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 100) ≤
      (1.0002420 : ℝ) + 1 / 10 ^ 7 := by
  convert exp100Provider.2 using 1; norm_num

theorem a2Exp150Lower : (1.000003748 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 150) := by
  convert exp150Provider.1 using 1; norm_num
theorem a2Exp150Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 150) ≤
      (1.000003748 : ℝ) + 1 / 10 ^ 8 := by
  convert exp150Provider.2 using 1; norm_num

theorem a2Exp200Lower : (1.00000007713 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 200) := by
  convert exp200Provider.1 using 1; norm_num
theorem a2Exp200Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 200) ≤
      (1.00000007713 : ℝ) + 1 / 10 ^ 9 := by
  convert exp200Provider.2 using 1; norm_num

theorem a2Exp250Lower : (1.00000002025 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 250) := by
  convert exp250Provider.1 using 1; norm_num
theorem a2Exp250Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 250) ≤
      (1.00000002025 : ℝ) + 1 / 10 ^ 9 := by
  convert exp250Provider.2 using 1; norm_num

theorem a2Exp300Lower : (1.00000001937 : ℝ) ≤
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 300) := by
  convert exp300Provider.1 using 1; norm_num
theorem a2Exp300Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * PntBKLNWPow.sourceF (Real.exp 300) ≤
      (1.00000001937 : ℝ) + 1 / 10 ^ 9 := by
  convert exp300Provider.2 using 1; norm_num

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

/-! Parameterized runtime/proof boundary. -/

def Contains (expected : Certificate) : Bound → ℝ → Prop
  | .all, _ => True
  | .window, x =>
      (expected.lowerNumerator : ℝ) / expected.targetDenominator ≤ x ∧
        x ≤ (expected.upperNumerator : ℝ) / expected.targetDenominator
  | .empty, _ => False

theorem containsMeet (expected : Certificate) (left right : Bound) (x : ℝ) :
    Contains expected (Bound.meet left right) x ↔
      Contains expected left x ∧ Contains expected right x := by
  cases left <;> cases right <;> simp [Bound.meet, Contains]

def foldModel (expected : Certificate) : OperationSemantics.Model ℝ :=
  { operation := foldOperation
    relation := fun inputs output =>
      inputs = [] ∧
        output = (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp expected.argument) }

def operationModels (expected : Certificate) :
    Array (OperationSemantics.Model ℝ) := #[foldModel expected]

def semantics (expected : Certificate) : Semantics Bound :=
  OperationSemantics.semantics (operationModels expected) (Contains expected)

def boundSchema (expected : Certificate) : FactDomainSchema (semantics expected) :=
  { top := fun _ => .all
    topSound := by intros; trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact containsMeet expected previous proposed (valuation _) }
      else none }

def laws (expected : Certificate) : Laws (semantics expected) :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains expected fact (valuation left) ↔
        Contains expected fact (valuation right)
      rw [values] }

theorem checkedWindow (value : Certificate)
    (checked : validCertificate value = true) :
    (value.lowerNumerator : ℝ) / value.targetDenominator ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp value.argument) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp value.argument) ≤
        (value.upperNumerator : ℝ) / value.targetDenominator := by
  apply certificateWindow value
  exact of_decide_eq_true (by simpa [validCertificate] using checked)

theorem foldEntails (expected : Certificate)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (nodeValue : Node)
    (found : graph.node? output = some nodeValue)
    (operation : nodeValue.op = ({ index := 0 } : OpId))
    (_arguments : nodeValue.args = []) (_noAssumptions : assumptions = [])
    (value : Certificate) (same : value = expected)
    (checked : validCertificate value = true) :
    (semantics expected).Entails graph assumptions
      { node := output, fact := .window } := by
  subst value
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models (operationModels expected) graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains expected assumption.fact (valuation assumption.node)) →
      Contains expected .window (valuation output)
  intro valuation model _holds
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output nodeValue found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq :
      valuation output = (1 + 193571378 / (10 : ℝ) ^ 16) *
        PntBKLNWPow.sourceF (Real.exp expected.argument) := by
    simpa [foldModel, _arguments, List.map] using related.2
  change (expected.lowerNumerator : ℝ) / expected.targetDenominator ≤
      valuation output ∧
    valuation output ≤
      (expected.upperNumerator : ℝ) / expected.targetDenominator
  rw [outputEq]
  exact checkedWindow expected checked

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- Generic replay checks equality with the package-selected source record, so
a valid certificate cannot be replayed against another row's model. -/
def foldFactSchema (expected : Certificate) :
    PackedFactSchema (semantics expected) where
  rule := foldRuleKey
  schema := 1
  Certificate := Certificate
  decode := decodeCertificate?
  replay := fun _ _ context value =>
    if checked : validCertificate value = true then
      if same : value = expected then
        if proposedFact : context.proposed.fact = .window then
          match found : context.program.node? context.proposed.node with
          | some nodeValue =>
              if operation : nodeValue.op = ({ index := 0 } : OpId) then
                if arguments : nodeValue.args = [] then
                  if noAssumptions : context.assumptions = [] then
                    some
                      { proof := by
                          have proposedEq : context.proposed =
                              { node := context.proposed.node, fact := .window } :=
                            factWith context.proposed proposedFact
                          rw [proposedEq]
                          exact foldEntails expected context.program
                            context.assumptions context.proposed.node nodeValue found
                            operation arguments noAssumptions value same checked }
                  else none
                else none
              else none
          | none => none
        else none
      else none
    else none

def stableLaw (expected : Certificate) : StableLaw (semantics expected) :=
  OperationSemantics.stableLaw (operationModels expected) (Contains expected)

def emitPackage (expected : Certificate) : EmitPackage Lean.Name :=
  let schema := foldFactSchema expected
  { schemas := [{ key := schema.key, handle := ``foldFactSchema }] }

def proofPackage (expected : Certificate) :
    ProofRegistry.Package (semantics expected) Lean.Name :=
  { semantic := { factSchemas := #[foldFactSchema expected] }
    emit := emitPackage expected }

def proofPackages (expected : Certificate) :
    Array (ProofRegistry.Package (semantics expected) Lean.Name) :=
  #[proofPackage expected]

/- `ProofFrontend` resolves replay schemas by a quoted top-level name. This
fixed-name adapter supplies that quotation for the representative row while
the checker and replay theorem themselves remain source-parameterized. -/
def exp20FactSchema : PackedFactSchema (semantics exp20) := foldFactSchema exp20

def exp20EmitPackage : EmitPackage Lean.Name :=
  { schemas := [{ key := exp20FactSchema.key, handle := ``exp20FactSchema }] }

def exp20ProofPackage : ProofRegistry.Package (semantics exp20) Lean.Name :=
  { semantic := { factSchemas := #[exp20FactSchema] }
    emit := exp20EmitPackage }

def exp20ProofPackages :
    Array (ProofRegistry.Package (semantics exp20) Lean.Name) :=
  #[exp20ProofPackage]

def baseFacts : List (NodeFact Bound) := [{ node, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all]
    target := { node, fact := .window } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  simp [program, node]

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl

def initialExtension (expected : Certificate) :
    Evidence ((semantics expected).Extends program program) :=
  extendRefl (semantics expected) program

noncomputable def valuation (expected : Certificate) : NodeId → ℝ
  | ⟨0⟩ => (1 + 193571378 / (10 : ℝ) ^ 16) *
      PntBKLNWPow.sourceF (Real.exp expected.argument)
  | _ => 0

theorem valuationModels (expected : Certificate) :
    (semantics expected).models program (valuation expected) := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, foldModel]
  rintro ⟨index⟩ nodeValue found
  cases index with
  | zero =>
      simp [Program.node?, program, instruction] at found
      subst nodeValue
      exact ⟨foldModel expected, by rfl, by simp [foldModel, valuation]⟩
  | succ index => simp [Program.node?, program] at found

/-- Convert generic replay evidence into the exact rational source window. -/
theorem closeWindow (expected : Certificate) (result : Evidence
    ((semantics expected).Entails program baseFacts checkerInput.target)) :
    (expected.lowerNumerator : ℝ) / expected.targetDenominator ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp expected.argument) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp expected.argument) ≤
        (expected.upperNumerator : ℝ) / expected.targetDenominator := by
  exact result.proof (valuation expected) (valuationModels expected) (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    trivial)

end Hex.Interval.Experiment.PntBKLNWExp
