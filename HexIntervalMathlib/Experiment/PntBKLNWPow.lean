/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases
public import HexInterval.Experiment.PntBKLNWPow
public import HexInterval.Experiment.ProofRegistry
public import HexInterval.Experiment.OperationSemantics
public import HexIntervalMathlib.Experiment.LogTablePrecision

@[expose] public section

namespace Hex.Interval.Experiment.PntBKLNWPow

open Real Finset

/-- Exact PNT+ definition copied from the pinned `BKLNW.lean` definition used
by `BKLNW_a2_bounds.lean`. -/
noncomputable def sourceF (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3)

/-- The same sum after authenticating the upper index for `x = 2^M`. -/
noncomputable def powSum (M : Nat) : ℝ :=
  ∑ k ∈ Icc 3 M, (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3))

theorem floorLogTwoPow (M : Nat) :
    ⌊log ((2 : ℝ) ^ M) / log 2⌋₊ = M := by
  rw [log_pow, mul_div_cancel_right₀ _ (ne_of_gt (log_pos one_lt_two))]
  exact Nat.floor_natCast M

theorem sourcePow (M : Nat) : sourceF ((2 : ℝ) ^ M) = powSum M := by
  unfold sourceF powSum
  rw [floorLogTwoPow]
  apply sum_congr rfl
  intro k hk
  rw [Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2)]

private theorem termThree (M : Nat) :
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / 3 - 1 / 3)) = 1 := by
  norm_num

private theorem termFour {M a : Nat} (ha : 12 * a ≤ M) :
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / 4 - 1 / 3)) ≤
      1 / (2 : ℝ) ^ a := by
  rw [show (1 : ℝ) / 4 - 1 / 3 = -(1 / 12) by norm_num]
  have exponent : (M : ℝ) * (-(1 / 12)) ≤ -(a : ℝ) := by
    have haReal : (12 : ℝ) * a ≤ M := by exact_mod_cast ha
    nlinarith
  calc
    (2 : ℝ) ^ ((M : ℝ) * (-(1 / 12))) ≤ (2 : ℝ) ^ (-(a : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent
    _ = 1 / (2 : ℝ) ^ a := by
      rw [Real.rpow_neg_natCast]
      norm_num [zpow_neg]

private theorem termTail {M b k : Nat} (hk : 5 ≤ k) (hb : 15 * b ≤ 2 * M) :
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
      1 / (2 : ℝ) ^ b := by
  have kpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) hk)
  have reciprocal : (1 : ℝ) / k ≤ 1 / 5 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk)
  have exponent :
      (M : ℝ) * ((1 : ℝ) / k - 1 / 3) ≤ -(b : ℝ) := by
    have mnonneg : (0 : ℝ) ≤ M := by positivity
    calc
      (M : ℝ) * ((1 : ℝ) / k - 1 / 3) ≤
          (M : ℝ) * ((1 : ℝ) / 5 - 1 / 3) := by gcongr
      _ ≤ -(b : ℝ) := by
        have hbReal : (15 : ℝ) * b ≤ 2 * M := by exact_mod_cast hb
        norm_num
        nlinarith
  calc
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
        (2 : ℝ) ^ (-(b : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent
    _ = 1 / (2 : ℝ) ^ b := by
      rw [Real.rpow_neg_natCast]
      norm_num [zpow_neg]

/-- A parameterized fold bound.  The certificate isolates the `k = 4` term
and bounds every `k ≥ 5` term uniformly; the finite cardinality remains part
of the kernel proof rather than a trusted planner calculation. -/
theorem powSumUpper {M a b : Nat} (hM : 5 ≤ M)
    (ha : 12 * a ≤ M) (hb : 15 * b ≤ 2 * M) :
    powSum M ≤ 1 + 1 / (2 : ℝ) ^ a +
      ((M - 4 : Nat) : ℝ) / (2 : ℝ) ^ b := by
  unfold powSum
  rw [← insert_Icc_add_one_left_eq_Icc (show 3 ≤ M by omega), sum_insert (by simp)]
  simp only [Nat.reduceAdd]
  rw [← insert_Icc_add_one_left_eq_Icc (show 4 ≤ M by omega), sum_insert (by simp)]
  simp only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [termThree, add_assoc]
  gcongr
  · exact termFour ha
  calc
    ∑ k ∈ Icc 5 M, (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
        ∑ _k ∈ Icc 5 M, 1 / (2 : ℝ) ^ b := by
      apply sum_le_sum
      intro k hk
      exact termTail (mem_Icc.mp hk).1 hb
    _ = ((Icc 5 M).card : ℝ) / (2 : ℝ) ^ b := by
      simp [nsmul_eq_mul, div_eq_mul_inv]
    _ = ((M - 4 : Nat) : ℝ) / (2 : ℝ) ^ b := by
      congr 2
      norm_num [Nat.card_Icc]
      omega

private theorem alphaRatio :
    (1 + 193571378 / (10 : ℝ) ^ 16) =
      (alphaNumerator : ℝ) / alphaDenominator := by
  norm_num [alphaNumerator, alphaDenominator]

private theorem sumRatio (value : FoldCertificate) :
    1 + 1 / (2 : ℝ) ^ value.isolatedExponent +
        value.tailCardinality / (2 : ℝ) ^ value.tailExponent =
      (sumNumerator value : ℝ) / sumDenominator value := by
  unfold sumNumerator sumDenominator
  rw [pow_add]
  push_cast
  field_simp

/-- Soundness theorem for every certificate accepted by the pure-natural
checker.  The provider may choose tighter dyadic exponents or a different
rational output cut; replay relies only on `Valid`. -/
theorem certificateUpper (value : FoldCertificate) (valid : Valid value) :
    (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ value.limit) ≤
      (value.targetNumerator : ℝ) / value.targetDenominator := by
  rcases valid with
    ⟨limit, isolated, tailStart, tailCardinality, isolatedExponent,
      tailExponent, targetPositive, targetEnough, targetWithinSource⟩
  have limitAtLeast : 5 ≤ value.limit := by omega
  have count : value.limit - 4 = value.tailCardinality := by omega
  have sumBound :
      powSum value.limit ≤
        1 + 1 / (2 : ℝ) ^ value.isolatedExponent +
          value.tailCardinality / (2 : ℝ) ^ value.tailExponent := by
    simpa [count] using
      powSumUpper limitAtLeast isolatedExponent tailExponent
  rw [sourcePow]
  calc
    (1 + 193571378 / (10 : ℝ) ^ 16) * powSum value.limit ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          (1 + 1 / (2 : ℝ) ^ value.isolatedExponent +
            value.tailCardinality / (2 : ℝ) ^ value.tailExponent) := by
      gcongr
    _ = ((alphaNumerator : ℝ) * sumNumerator value) /
        (alphaDenominator * sumDenominator value) := by
      rw [alphaRatio, sumRatio, div_mul_div_comm]
    _ ≤ (value.targetNumerator : ℝ) / value.targetDenominator := by
      have denominatorPositive :
          (0 : ℝ) < alphaDenominator * sumDenominator value := by
        unfold alphaDenominator sumDenominator
        positivity
      apply (div_le_div_iff₀ denominatorPositive
        (by exact_mod_cast targetPositive)).2
      exact_mod_cast targetEnough

/-- Strong package-owned bound used to replace LeanCert's native-decide-backed
`pow433_upper`. -/
theorem pow433Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (100000001948 : ℝ) / 100000000000 := by
  exact certificateUpper certificate (by decide)

/-- Exact theorem shape of PNT+ `cert_pow433_upper`; its final decimal cut is
weaker than the authenticated provider cut. -/
theorem certPow433Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 := by
  exact pow433Provider.trans (by norm_num)

theorem oneLeSourcePow {M : Nat} (hM : 3 ≤ M) :
    1 ≤ sourceF ((2 : ℝ) ^ M) := by
  rw [sourcePow]
  unfold powSum
  rw [← insert_Icc_add_one_left_eq_Icc hM, sum_insert (by simp)]
  simp only [Nat.cast_ofNat, Nat.reduceAdd, termThree]
  exact le_add_of_nonneg_right
    (sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)

/-- A too-small rational endpoint is mathematically false, not merely
unsupported by the runtime decoder. -/
theorem rejectWrongEndpoint :
    ¬ (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (100000001900 : ℝ) / 100000000000 := by
  have lower :
      (1 + 193571378 / (10 : ℝ) ^ 16) ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          sourceF ((2 : ℝ) ^ (433 : Nat)) := by
    nlinarith [oneLeSourcePow (M := 433) (by norm_num)]
  norm_num at lower ⊢
  linarith

/-! Shared fine-grained provider for the complete power ladder. -/

private theorem expUpper (x upper : ℝ) (bound : |x| ≤ 1) (checked :
    ∑ k ∈ Finset.range 14, x ^ k / Nat.factorial k +
        |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) < upper) :
    Real.exp x < upper := by
  have remainder := Real.exp_bound (x := x) (n := 14) bound (by norm_num)
  rw [abs_le] at remainder
  linarith

def baseNumerator : Nat → Nat
  | 4 => 94387432
  | 5 => 91172249
  | 6 => 89089872
  | 7 => 87631643
  | 8 => 86553657
  | 9 => 85724399
  | 10 => 85066717
  | 11 => 84532368
  | 12 => 84089642
  | 13 => 83716839
  | 14 => 83398610
  | 15 => 83123790
  | 16 => 82884066
  | 17 => 82673118
  | 18 => 82486060
  | 19 => 82319051
  | 20 => 82169032
  | 21 => 82033536
  | _ => 0

noncomputable def baseValue (k : Nat) : ℝ :=
  baseNumerator k / baseDenominator

/-- Every package-owned decimal is proved from the 20-digit log-2 series
window and the same checked exponential remainder theorem. -/
theorem baseUpper {k : Nat} (lower : 4 ≤ k) (upper : k ≤ 21) :
    (2 : ℝ) ^ ((1 : ℝ) / k - 1 / 3) < baseValue k := by
  have logLower := Hex.IntervalMathlib.Experiment.LogTablePrecision.decimal20.1
  have kpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) lower)
  have exponentNegative : (1 : ℝ) / k - 1 / 3 < 0 := by
    have : (3 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 3 < 4) lower)
    have reciprocal : (1 : ℝ) / k < 1 / 3 :=
      one_div_lt_one_div_of_lt (by norm_num) this
    linarith
  have exponentLt :
      Real.log 2 * ((1 : ℝ) / k - 1 / 3) <
        (69314718055994530941 / 10 ^ 20 : ℝ) * ((1 : ℝ) / k - 1 / 3) := by
    nlinarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply lt_trans (Real.exp_lt_exp.mpr exponentLt)
  interval_cases k <;>
    apply expUpper <;>
    norm_num [baseValue, baseNumerator, baseDenominator, Finset.sum_range_succ]

noncomputable def exactBaseSum (M : Nat) : ℝ :=
  ∑ k ∈ Icc 4 20, baseValue k ^ M

private theorem termBase {M k : Nat} (lower : 4 ≤ k) (upper : k ≤ 20) :
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
      baseValue k ^ M := by
  rw [mul_comm, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
    (le_of_lt (baseUpper lower (upper.trans (by decide)))) M

private theorem termFineTail {M k : Nat} (lower : 21 ≤ k) :
    (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
      baseValue 21 ^ M := by
  rw [mul_comm, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  apply pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
  calc
    (2 : ℝ) ^ ((1 : ℝ) / k - 1 / 3) ≤
        (2 : ℝ) ^ ((1 : ℝ) / 21 - 1 / 3) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have kpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 21) lower)
      have reciprocal : (1 : ℝ) / k ≤ 1 / 21 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast lower)
      linarith
    _ ≤ baseValue 21 := le_of_lt (baseUpper (by decide) (by decide))

/-- Shared analytic fold for every source limit in the BKLNW power ladder.
The 17 explicit cells and the tail cardinality remain visible to replay. -/
theorem finePowSumUpper {M : Nat} (hM : 21 ≤ M) :
    powSum M ≤ 1 + exactBaseSum M +
      ((M - 20 : Nat) : ℝ) * baseValue 21 ^ M := by
  unfold powSum
  rw [← insert_Icc_add_one_left_eq_Icc (show 3 ≤ M by omega), sum_insert (by simp)]
  simp only [Nat.reduceAdd]
  have term3 :
      (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / (3 : Nat) - 1 / 3)) = 1 := by
    norm_num
  rw [term3]
  have union : Icc 4 M = Icc 4 20 ∪ Icc 21 M := by
    ext k
    simp only [mem_Icc, mem_union]
    omega
  have disjoint : Disjoint (Icc 4 20) (Icc 21 M) := by
    simp only [Finset.disjoint_left, mem_Icc]
    omega
  rw [union, sum_union disjoint]
  rw [add_assoc]
  gcongr
  · unfold exactBaseSum
    apply sum_le_sum
    intro k member
    exact termBase (mem_Icc.mp member).1 (mem_Icc.mp member).2
  · calc
      ∑ k ∈ Icc 21 M,
          (2 : ℝ) ^ ((M : ℝ) * ((1 : ℝ) / k - 1 / 3)) ≤
          ∑ _k ∈ Icc 21 M, baseValue 21 ^ M := by
        apply sum_le_sum
        intro k member
        exact termFineTail (mem_Icc.mp member).1
      _ = ((Icc 21 M).card : ℝ) * baseValue 21 ^ M := by simp
      _ = ((M - 20 : Nat) : ℝ) * baseValue 21 ^ M := by
        congr 2
        norm_num [Nat.card_Icc]
        omega

private theorem exactBaseRatio (M : Nat) :
    exactBaseSum M =
      (sumPowers M exactBaseNumerators : ℝ) / baseDenominator ^ M := by
  have rangeEq : Icc 4 20 = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
      14, 15, 16, 17, 18, 19, 20} := by decide
  unfold exactBaseSum
  rw [rangeEq]
  norm_num [baseValue, baseNumerator, baseDenominator,
    exactBaseNumerators, baseNumerators, sumPowers, div_pow]
  ring

set_option maxHeartbeats 800000 in
private theorem fineSumRatio (value : LadderCertificate)
    (denominator : value.baseDenominator = baseDenominator) :
    1 + exactBaseSum value.limit +
        value.tailCardinality * baseValue 21 ^ value.limit =
      (ladderSumNumerator value : ℝ) / ladderSumDenominator value := by
  unfold ladderSumNumerator ladderSumDenominator
  rw [denominator]
  rw [exactBaseRatio]
  norm_num [baseValue, baseNumerator, baseDenominator, ladderSumNumerator,
    ladderSumDenominator, tailBaseNumerator, baseNumerators, div_pow]
  field_simp
  rw [show (82033536 : ℝ) = 640887 * 128 by norm_num,
    show (100000000 : ℝ) = 781250 * 128 by norm_num]
  simp only [mul_pow]
  ring

/-- Soundness for every certificate accepted by the parameterized ladder
checker.  No source row is selected outside `LadderValid`. -/
theorem ladderCertificateUpper (value : LadderCertificate)
    (valid : LadderValid value) :
    (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ value.limit) ≤
      (value.targetNumerator : ℝ) / value.targetDenominator := by
  rcases valid with
    ⟨source, limitAtLeast, exactStart, exactStop, tailStart, tailCardinality,
      denominator, targetPositive, targetEnough⟩
  have sumBound :
      powSum value.limit ≤ 1 + exactBaseSum value.limit +
        value.tailCardinality * baseValue 21 ^ value.limit := by
    have count : value.limit - 20 = value.tailCardinality := by omega
    simpa [count] using finePowSumUpper limitAtLeast
  rw [sourcePow]
  calc
    (1 + 193571378 / (10 : ℝ) ^ 16) * powSum value.limit ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          (1 + exactBaseSum value.limit +
            value.tailCardinality * baseValue 21 ^ value.limit) := by
      gcongr
    _ = ((alphaNumerator : ℝ) * ladderSumNumerator value) /
        (alphaDenominator * ladderSumDenominator value) := by
      rw [alphaRatio, fineSumRatio value denominator, div_mul_div_comm]
    _ ≤ (value.targetNumerator : ℝ) / value.targetDenominator := by
      have denominatorPositive :
          (0 : ℝ) < alphaDenominator * ladderSumDenominator value := by
        unfold ladderSumDenominator
        rw [denominator]
        unfold alphaDenominator baseDenominator
        positivity
      apply (div_le_div_iff₀ denominatorPositive
        (by exact_mod_cast targetPositive)).2
      exact_mod_cast targetEnough

theorem pow29Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (29 : Nat)) ≤
      (14263 : ℝ) / 10000 :=
  ladderCertificateUpper ladder29 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow37Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (37 : Nat)) ≤
      (12196 : ℝ) / 10000 :=
  ladderCertificateUpper ladder37 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow44Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (44 : Nat)) ≤
      (11211 : ℝ) / 10000 :=
  ladderCertificateUpper ladder44 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow51Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (51 : Nat)) ≤
      (107087 : ℝ) / 100000 :=
  ladderCertificateUpper ladder51 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow58Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (58 : Nat)) ≤
      (104320 : ℝ) / 100000 :=
  ladderCertificateUpper ladder58 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow63Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (63 : Nat)) ≤
      (103253 : ℝ) / 100000 :=
  ladderCertificateUpper ladder63 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow145Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (145 : Nat)) ≤
      (10002421 : ℝ) / 10000000 :=
  ladderCertificateUpper ladder145 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow217Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (217 : Nat)) ≤
      (1000003758 : ℝ) / 1000000000 :=
  ladderCertificateUpper ladder217 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow289Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (289 : Nat)) ≤
      (100000007813 : ℝ) / 100000000000 :=
  ladderCertificateUpper ladder289 (by
    set_option exponentiation.threshold 500 in decide)

theorem pow361Provider :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (361 : Nat)) ≤
      (100000002125 : ℝ) / 100000000000 :=
  ladderCertificateUpper ladder361 (by
    set_option exponentiation.threshold 500 in decide)

/-! Exact theorem shapes of the ten remaining source declarations. -/

theorem certPow29Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (29 : Nat)) ≤
      (1.4262 : ℝ) + 1 / 10 ^ 4 := by
  convert pow29Provider using 1
  norm_num

theorem certPow37Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (37 : Nat)) ≤
      (1.2195 : ℝ) + 1 / 10 ^ 4 := by
  convert pow37Provider using 1
  norm_num

theorem certPow44Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (44 : Nat)) ≤
      (1.1210 : ℝ) + 1 / 10 ^ 4 := by
  convert pow44Provider using 1
  norm_num

theorem certPow51Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (51 : Nat)) ≤
      (1.07086 : ℝ) + 1 / 10 ^ 5 := by
  convert pow51Provider using 1
  norm_num

theorem certPow58Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (58 : Nat)) ≤
      (1.04319 : ℝ) + 1 / 10 ^ 5 := by
  convert pow58Provider using 1
  norm_num

theorem certPow63Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (63 : Nat)) ≤
      (1.03252 : ℝ) + 1 / 10 ^ 5 := by
  convert pow63Provider using 1
  norm_num

theorem certPow145Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (145 : Nat)) ≤
      (1.0002420 : ℝ) + 1 / 10 ^ 7 := by
  convert pow145Provider using 1
  norm_num

theorem certPow217Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (217 : Nat)) ≤
      (1.000003748 : ℝ) + 1 / 10 ^ 8 := by
  convert pow217Provider using 1
  norm_num

theorem certPow289Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (289 : Nat)) ≤
      (1.00000007713 : ℝ) + 1 / 10 ^ 9 := by
  convert pow289Provider using 1
  norm_num

theorem certPow361Upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (361 : Nat)) ≤
      (1.00000002025 : ℝ) + 1 / 10 ^ 9 := by
  convert pow361Provider using 1
  norm_num

/-- A decoded endpoint mutation to `1` is mathematically false already from
the authenticated `k = 3` term. -/
theorem rejectPow29Endpoint :
    ¬ (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ (29 : Nat)) ≤ 1 := by
  intro upper
  have lower :
      (1 + 193571378 / (10 : ℝ) ^ 16) ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          sourceF ((2 : ℝ) ^ (29 : Nat)) := by
    have alphaNonnegative :
        (0 : ℝ) ≤ 1 + 193571378 / (10 : ℝ) ^ 16 := by norm_num
    simpa using mul_le_mul_of_nonneg_left
      (oneLeSourcePow (M := 29) (by norm_num)) alphaNonnegative
  have alphaGreater : (1 : ℝ) < 1 + 193571378 / (10 : ℝ) ^ 16 := by
    norm_num
  linarith

open Propagator SemanticReplay ChronologicalReplay ProofEmitter ProofRegistry
open GenericInstanceReconstruction OperationSemantics

/-! The parameterized runtime/proof boundary for the fine ladder. -/

def LadderContains (expected : LadderCertificate) : Bound → ℝ → Prop
  | .all, _ => True
  | .upper, x =>
      x ≤ (expected.targetNumerator : ℝ) / expected.targetDenominator
  | .empty, _ => False

theorem ladderContainsMeet (expected : LadderCertificate) (left right : Bound)
    (x : ℝ) :
    LadderContains expected (Bound.meet left right) x ↔
      LadderContains expected left x ∧ LadderContains expected right x := by
  cases left <;> cases right <;> simp [Bound.meet, LadderContains]

def ladderFoldModel (expected : LadderCertificate) : OperationSemantics.Model ℝ :=
  { operation := foldOperation
    relation := fun inputs output =>
      inputs = [] ∧
        output = (1 + 193571378 / (10 : ℝ) ^ 16) *
          sourceF ((2 : ℝ) ^ expected.limit) }

def ladderOperationModels (expected : LadderCertificate) :
    Array (OperationSemantics.Model ℝ) := #[ladderFoldModel expected]

def ladderSemantics (expected : LadderCertificate) : Semantics Bound :=
  OperationSemantics.semantics (ladderOperationModels expected)
    (LadderContains expected)

def ladderBoundSchema (expected : LadderCertificate) :
    FactDomainSchema (ladderSemantics expected) :=
  { top := fun _ => .all
    topSound := by intros; trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact ladderContainsMeet expected previous proposed (valuation _) }
      else none }

def ladderLaws (expected : LadderCertificate) : Laws (ladderSemantics expected) :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change LadderContains expected fact (valuation left) ↔
        LadderContains expected fact (valuation right)
      rw [values] }

theorem checkedLadderUpper (value : LadderCertificate)
    (checked : validLadderCertificate value = true) :
    (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ value.limit) ≤
      (value.targetNumerator : ℝ) / value.targetDenominator := by
  apply ladderCertificateUpper value
  exact of_decide_eq_true (by simpa [validLadderCertificate] using checked)

theorem ladderFoldEntails (expected : LadderCertificate)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (nodeValue : Node)
    (found : graph.node? output = some nodeValue)
    (operation : nodeValue.op = ({ index := 0 } : OpId))
    (_arguments : nodeValue.args = []) (_noAssumptions : assumptions = [])
    (value : LadderCertificate) (same : value = expected)
    (checked : validLadderCertificate value = true) :
    (ladderSemantics expected).Entails graph assumptions
      { node := output, fact := .upper } := by
  subst value
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models (ladderOperationModels expected) graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        LadderContains expected assumption.fact (valuation assumption.node)) →
      LadderContains expected .upper (valuation output)
  intro valuation model _holds
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output nodeValue found
  simp [ladderOperationModels, operation] at meaningAt
  subst meaning
  have outputEq :
      valuation output = (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ expected.limit) := by
    simpa [ladderFoldModel, _arguments, List.map] using related.2
  change valuation output ≤
    (expected.targetNumerator : ℝ) / expected.targetDenominator
  rw [outputEq]
  exact checkedLadderUpper expected checked

private theorem ladderFactWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- Generic kernel replay for schema 2.  Equality with the package-selected
certificate is checked explicitly, so a valid row cannot be replayed against
another row's operation model. -/
def ladderFoldFactSchema (expected : LadderCertificate) :
    PackedFactSchema (ladderSemantics expected) where
  rule := foldRuleKey
  schema := 2
  Certificate := LadderCertificate
  decode := decodeLadderCertificate?
  replay := fun _ _ context value =>
    if checked : validLadderCertificate value = true then
      if same : value = expected then
        if proposedFact : context.proposed.fact = .upper then
          match found : context.program.node? context.proposed.node with
          | some nodeValue =>
              if operation : nodeValue.op = ({ index := 0 } : OpId) then
                if arguments : nodeValue.args = [] then
                  if noAssumptions : context.assumptions = [] then
                    some
                      { proof := by
                          have proposedEq : context.proposed =
                              { node := context.proposed.node, fact := .upper } :=
                            ladderFactWith context.proposed proposedFact
                          rw [proposedEq]
                          exact ladderFoldEntails expected context.program
                            context.assumptions context.proposed.node nodeValue found
                            operation arguments noAssumptions value same checked }
                  else none
                else none
              else none
          | none => none
        else none
      else none
    else none

def ladderStableLaw (expected : LadderCertificate) :
    StableLaw (ladderSemantics expected) :=
  OperationSemantics.stableLaw (ladderOperationModels expected)
    (LadderContains expected)

def ladderEmitPackage (expected : LadderCertificate) : EmitPackage Lean.Name :=
  let schema := ladderFoldFactSchema expected
  { schemas := [{ key := schema.key, handle := ``ladderFoldFactSchema }] }

def ladderProofPackage (expected : LadderCertificate) :
    ProofRegistry.Package (ladderSemantics expected) Lean.Name :=
  { semantic := { factSchemas := #[ladderFoldFactSchema expected] }
    emit := ladderEmitPackage expected }

def ladderProofPackages (expected : LadderCertificate) :
    Array (ProofRegistry.Package (ladderSemantics expected) Lean.Name) :=
  #[ladderProofPackage expected]

/-- Meaning of the runtime fact lattice. -/
def Contains : Bound → ℝ → Prop
  | .all, _ => True
  | .upper, x => x ≤ (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8
  | .empty, _ => False

theorem containsMeet (left right : Bound) (x : ℝ) :
    Contains (Bound.meet left right) x ↔ Contains left x ∧ Contains right x := by
  cases left <;> cases right <;> simp [Bound.meet, Contains]

def foldModel : OperationSemantics.Model ℝ :=
  { operation := foldOperation
    relation := fun inputs output =>
      inputs = [] ∧
        output = (1 + 193571378 / (10 : ℝ) ^ 16) *
          sourceF ((2 : ℝ) ^ (433 : Nat)) }

def operationModels : Array (OperationSemantics.Model ℝ) := #[foldModel]

def semantics : Semantics Bound :=
  OperationSemantics.semantics operationModels Contains

def boundSchema : FactDomainSchema semantics :=
  { top := fun _ => .all
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact containsMeet previous proposed (valuation _) }
      else
        none }

def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

theorem checkedUpper (value : FoldCertificate)
    (checked : validCertificate value = true) :
    (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ value.limit) ≤
      (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 := by
  have valid : Valid value := of_decide_eq_true (by
    simpa [validCertificate] using checked)
  have provider := certificateUpper value valid
  have denominatorPositive : (0 : ℝ) < value.targetDenominator := by
    exact_mod_cast valid.2.2.2.2.2.2.1
  have targetWithin :
      (value.targetNumerator : ℝ) / value.targetDenominator ≤
        (100000002937 : ℝ) / 100000000000 := by
    apply (div_le_div_iff₀ denominatorPositive (by norm_num)).2
    exact_mod_cast valid.2.2.2.2.2.2.2.2
  calc
    _ ≤ (value.targetNumerator : ℝ) / value.targetDenominator := provider
    _ ≤ (100000002937 : ℝ) / 100000000000 := targetWithin
    _ = (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 := by norm_num

theorem foldEntails (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (nodeValue : Node)
    (found : graph.node? output = some nodeValue)
    (operation : nodeValue.op = ({ index := 0 } : OpId))
    (_arguments : nodeValue.args = []) (_noAssumptions : assumptions = [])
    (value : FoldCertificate) (checked : validCertificate value = true) :
    semantics.Entails graph assumptions { node := output, fact := .upper } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models operationModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .upper (valuation output)
  intro valuation model _holds
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output nodeValue found
  simp [operationModels, operation] at meaningAt
  subst meaning
  have outputEq :
      valuation output = (1 + 193571378 / (10 : ℝ) ^ 16) *
        sourceF ((2 : ℝ) ^ (433 : Nat)) := by
    simpa [foldModel, _arguments, List.map] using related.2
  change valuation output ≤ (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8
  rw [outputEq]
  have valid : Valid value := of_decide_eq_true (by
    simpa [validCertificate] using checked)
  simpa [valid.1] using checkedUpper value checked

private theorem factWith {Fact : Type} (fact : NodeFact Fact) {value : Fact}
    (equal : fact.fact = value) : fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

/-- Replay checks the graph, the empty assumption list, every certificate
field, and the proposed fact before constructing evidence. -/
def foldFactSchema : PackedFactSchema semantics where
  rule := foldRuleKey
  schema := 1
  Certificate := FoldCertificate
  decode := decodeCertificate?
  replay := fun _ _ context value =>
    if checked : validCertificate value = true then
      if proposedFact : context.proposed.fact = .upper then
        match found : context.program.node? context.proposed.node with
        | some nodeValue =>
            if operation : nodeValue.op = ({ index := 0 } : OpId) then
              if arguments : nodeValue.args = [] then
                if noAssumptions : context.assumptions = [] then
                  some
                    { proof := by
                        have proposedEq :
                            context.proposed =
                              { node := context.proposed.node, fact := .upper } :=
                          factWith context.proposed proposedFact
                        rw [proposedEq]
                        exact foldEntails context.program context.assumptions
                          context.proposed.node nodeValue found operation arguments
                          noAssumptions value checked }
                else none
              else none
            else none
        | none => none
      else none
    else none

def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw operationModels Contains

def emitPackage : EmitPackage Lean.Name :=
  { schemas := [{ key := foldFactSchema.key, handle := ``foldFactSchema }] }

def proofPackage : ProofRegistry.Package semantics Lean.Name :=
  { semantic := { factSchemas := #[foldFactSchema] }
    emit := emitPackage }

def proofPackages : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[proofPackage]

def baseFacts : List (NodeFact Bound) := [{ node, fact := .all }]

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all]
    target := { node, fact := .upper } }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  simp [program, node]

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => (1 + 193571378 / (10 : ℝ) ^ 16) *
      sourceF ((2 : ℝ) ^ (433 : Nat))
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, foldModel]
  rintro ⟨index⟩ nodeValue found
  cases index with
  | zero =>
      simp [Program.node?, program, instruction] at found
      subst nodeValue
      exact ⟨foldModel, by rfl, by simp [foldModel, valuation]⟩
  | succ index => simp [Program.node?, program] at found

/-- Convert generic replay evidence into the exact PNT+ theorem shape. -/
theorem closePow (result : Evidence
    (semantics.Entails program baseFacts checkerInput.target)) :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 := by
  exact result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    trivial)

end Hex.Interval.Experiment.PntBKLNWPow
