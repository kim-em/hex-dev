/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import HexIntervalMathlib.Experiment.LogTablePrecision
public import HexInterval.Experiment.PntRamanujanTheta

@[expose] public section

/-!
# Checked semantics for the Ramanujan theta family

The exact primorial bracket converts the package-owned `log 2` enclosure into
a direct relative-error theorem at 599. A bounded prefix-product check gives
the complete real-variable range theorem on `[3, 599)`.
-/

namespace Hex.Interval.Experiment.PntRamanujanTheta

open Finset

set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1024

set_option maxRecDepth 100000 in
private theorem primeSet : Nat.primesLE 599 = primeList.toFinset := by
  decide

def Holds (value : Certificate) : Prop :=
  |Chebyshev.theta value.input - value.input| ≤
    ((value.toleranceNumerator : ℝ) / value.toleranceDenominator) * value.input

set_option maxRecDepth 100000 in
private theorem primorialValue : primorial 599 = primeProduct := by
  rw [primorial_eq_prod_primesLE, primeSet]
  norm_num [primeList, primeProduct]

private theorem logTwoWindow :
    (69 / 100 : ℝ) < Real.log 2 ∧ Real.log 2 < 7 / 10 := by
  have precise := Hex.IntervalMathlib.Experiment.LogTablePrecision.decimal20
  norm_num at precise ⊢
  constructor <;> linarith [precise.1, precise.2]

private theorem primeNodup : primeList.Nodup := by decide

private theorem prefixSet (n : Nat) (hn : n ≤ 599) :
    Nat.primesLE n = (primeList.filter fun p => p ≤ n).toFinset := by
  ext p
  have primeListIff : p ∈ primeList ↔ p ≤ 599 ∧ p.Prime := by
    rw [← List.mem_toFinset, ← primeSet, Nat.mem_primesLE]
  rw [Nat.mem_primesLE, List.mem_toFinset, List.mem_filter, primeListIff]
  constructor
  · rintro ⟨pn, prime⟩
    exact ⟨⟨pn.trans hn, prime⟩, decide_eq_true pn⟩
  · rintro ⟨⟨_, prime⟩, pn⟩
    exact ⟨of_decide_eq_true pn, prime⟩

private theorem productThrough_eq_primorial (n : Nat) (hn : n ≤ 599) :
    productThrough n = primorial n := by
  rw [primorial_eq_prod_primesLE, prefixSet n hn]
  simpa [productThrough] using
    (List.prod_toFinset id (primeNodup.filter (fun p => p ≤ n))).symm

private theorem checkRangeAt_of_checkRange {start limit n : Nat}
    (checked : checkRange start limit = true)
    (lower : start ≤ n) (upper : n < limit) : checkRangeAt n = true := by
  have member : n - start ∈ List.range (limit - start) := by
    rw [List.mem_range]
    omega
  have selected := List.all_eq_true.mp checked (n - start) member
  simpa [checkRange, Nat.add_sub_of_le lower] using selected

private theorem thetaLower (n : Nat) (hn599 : n < 599)
    (checked : checkRangeAt n = true) :
    (232 / 1000 : ℝ) * (n + 1) ≤ Chebyshev.theta n := by
  have arithmetic : 232 * (n + 1) ≤
      690 * Nat.log2 (productThrough n) := by
    simpa [checkRangeAt] using of_decide_eq_true checked
  have productEq := productThrough_eq_primorial n hn599.le
  have productPositive : 0 < productThrough n := by
    rw [productEq]
    exact primorial_pos n
  have powerLe : 2 ^ Nat.log2 (productThrough n) ≤ productThrough n := by
    simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 productPositive.ne'
  have powerLeReal :
      ((2 : ℝ) ^ Nat.log2 (productThrough n)) ≤ productThrough n := by
    exact_mod_cast powerLe
  have logPowerLe :
      (Nat.log2 (productThrough n) : ℝ) * Real.log 2 ≤
        Real.log (productThrough n) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) powerLeReal
  have thetaProduct : Chebyshev.theta n = Real.log (productThrough n) := by
    rw [productEq]
    simpa using Chebyshev.theta_eq_log_primorial (n : ℝ)
  rw [thetaProduct]
  have arithmeticReal : (232 : ℝ) * (n + 1) ≤
      690 * Nat.log2 (productThrough n) := by
    exact_mod_cast arithmetic
  have lowerLog : (69 / 100 : ℝ) < Real.log 2 := logTwoWindow.1
  nlinarith

def RangeHolds (value : RangeCertificate) : Prop :=
  ∀ x ∈ Set.Ico (value.start : ℝ) value.limit,
    |Chebyshev.theta x - x| ≤
      ((value.toleranceNumerator : ℝ) / value.toleranceDenominator) * x

private theorem sourceRangeHolds
    (checked : checkRange 3 599 = true) : RangeHolds rangeRows[0] := by
  norm_num [RangeHolds, rangeRows]
  intro x hx3 hx599
  have xNonnegative : 0 ≤ x := by linarith
  let n := ⌊x⌋₊
  have n3 : 3 ≤ n := Nat.le_floor hx3
  have n599 : n < 599 := (Nat.floor_lt xNonnegative).mpr (by exact_mod_cast hx599)
  have floorLower : (n : ℝ) ≤ x := Nat.floor_le xNonnegative
  have floorUpper : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have rangeAt := checkRangeAt_of_checkRange checked n3 n599
  have lowerTheta := thetaLower n n599 rangeAt
  have thetaFloor : Chebyshev.theta x = Chebyshev.theta n :=
    Chebyshev.theta_eq_theta_coe_floor x
  have logFourUpper : Real.log 4 < (7 / 5 : ℝ) := by
    calc
      Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
        norm_num
      _ < 2 * (7 / 10 : ℝ) := by gcongr; exact logTwoWindow.2
      _ = 7 / 5 := by ring
  have upperTheta := Chebyshev.theta_le_log4_mul_x xNonnegative
  have upperThetaFloor : Chebyshev.theta n ≤ Real.log 4 * x := by
    simpa [thetaFloor] using upperTheta
  rw [abs_le, thetaFloor]
  constructor
  · nlinarith
  · nlinarith

/-- Every authenticated range row proves the complete direct theta-error
statement used after the localized predicate-eliminating PNT+ rewrite. -/
theorem rangeCertificateHolds (index : Nat) (value : RangeCertificate)
    (valid : validRangeCertificate index value = true) : RangeHolds value := by
  simp only [validRangeCertificate, Bool.and_eq_true] at valid
  cases index with
  | zero =>
      have accepted := valid.1.1
      simp [rangeRows] at accepted
      subst value
      exact sourceRangeHolds valid.2
  | succ index =>
      simp [rangeRows] at valid

set_option maxRecDepth 100000 in
private theorem thetaPowerWindow :
    (812 : ℝ) * (69 / 100) < Chebyshev.theta 599 ∧
      Chebyshev.theta 599 < (813 : ℝ) * (7 / 10) := by
  have lowerPower : (2 : ℝ) ^ (812 : Nat) < primeProduct := by
    exact_mod_cast (show 2 ^ (812 : Nat) < primeProduct by decide)
  have upperPower : (primeProduct : ℝ) < 2 ^ (813 : Nat) := by
    exact_mod_cast (show primeProduct < 2 ^ (813 : Nat) by decide)
  have productPositive : (0 : ℝ) < primeProduct := by norm_num [primeProduct]
  have lowerLog : (812 : ℝ) * (69 / 100) < Real.log primeProduct := by
    calc
      (812 : ℝ) * (69 / 100) < 812 * Real.log 2 := by
        gcongr
        exact logTwoWindow.1
      _ = Real.log ((2 : ℝ) ^ (812 : Nat)) := by rw [Real.log_pow]; norm_num
      _ < Real.log primeProduct := Real.log_lt_log (by positivity) lowerPower
  have upperLog : Real.log primeProduct < (813 : ℝ) * (7 / 10) := by
    calc
      Real.log primeProduct < Real.log ((2 : ℝ) ^ (813 : Nat)) :=
        Real.log_lt_log productPositive upperPower
      _ = 813 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ < (813 : ℝ) * (7 / 10) := by
        gcongr
        exact logTwoWindow.2
  have thetaPrimorial :
      Chebyshev.theta 599 = Real.log (primorial 599) := by
    simpa using Chebyshev.theta_eq_log_primorial (599 : ℝ)
  rw [thetaPrimorial, primorialValue]
  exact ⟨lowerLog, upperLog⟩

private theorem thetaWindow :
    (599 : ℝ) * (1 - 65 / 1000) < Chebyshev.theta 599 ∧
      Chebyshev.theta 599 < (599 : ℝ) * (1 + 65 / 1000) := by
  have powerWindow := thetaPowerWindow
  norm_num at powerWindow ⊢
  constructor <;> linarith [powerWindow.1, powerWindow.2]

private theorem sourceHolds : Holds sourceRows[0] := by
  norm_num [Holds, sourceRows]
  rw [abs_le]
  constructor <;> linarith [thetaWindow.1, thetaWindow.2]

/-- Every authenticated source row proves the direct theta-error theorem used
after the localized predicate-eliminating PNT+ rewrite. -/
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

/-- Tightening the relative tolerance from `0.065` to `0.049` is false. -/
theorem rejectTolerance49 :
    ¬ |Chebyshev.theta 599 - 599| ≤ (49 / 1000 : ℝ) * 599 := by
  intro wrong
  rw [abs_le] at wrong
  have upper : Chebyshev.theta 599 < (813 : ℝ) * (7 / 10) := thetaPowerWindow.2
  norm_num at wrong upper
  linarith

end Hex.Interval.Experiment.PntRamanujanTheta

end
