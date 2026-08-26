/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import HexIntervalMathlib.Experiment.LogTablePrecision

@[expose] public section

/-!
# Small-prime logarithm leaves from PNT+

The pinned PNT+ proofs of `RS_prime_helper.p_n_lower_small` and
`Rosser1938.p_n_gt_1` each contain the same thirty `interval_auto` leaves.
This module replaces those sixty calls by two ordinary kernel theorems.  The
only transcendental input is the package-owned checked enclosure for
`Real.log 2`; a five-term atanh remainder supplies the one additional bound
for `Real.log 3`.

The table records the exact `(n, m)` coordinates passed to the source helper
whose arithmetic premise is either `n * log n < m` or
`n * (log n + log (log n) - 3 / 2) < m`.  It does not reproduce LeanCert's
tactic API or PNT+'s separate prime-counting lemmas.
-/

namespace Hex.IntervalMathlib.Experiment.PntPrimeLogSmall

open Finset

/-- The exact upper-prime coordinates used in both pinned source proofs. -/
def sourceCut : Nat → Nat
  | 2 => 3
  | 3 => 5
  | 4 => 7
  | 5 => 11
  | 6 => 13
  | 7 => 17
  | 8 => 19
  | 9 => 23
  | 10 => 29
  | 11 => 31
  | 12 => 37
  | 13 => 41
  | 14 => 43
  | 15 => 47
  | 16 => 53
  | 17 => 59
  | 18 => 61
  | 19 => 67
  | 20 => 71
  | 21 => 73
  | 22 => 79
  | 23 => 83
  | 24 => 89
  | 25 => 97
  | 26 => 101
  | 27 => 103
  | 28 => 107
  | 29 => 109
  | 30 => 113
  | 31 => 127
  | _ => 0

/-- Source-pinned coordinate table, kept as data for correspondence guards. -/
def sourceRows : Array (Nat × Nat) :=
  #[(2, 3), (3, 5), (4, 7), (5, 11), (6, 13), (7, 17), (8, 19),
    (9, 23), (10, 29), (11, 31), (12, 37), (13, 41), (14, 43),
    (15, 47), (16, 53), (17, 59), (18, 61), (19, 67), (20, 71),
    (21, 73), (22, 79), (23, 83), (24, 89), (25, 97), (26, 101),
    (27, 103), (28, 107), (29, 109), (30, 113), (31, 127)]

private theorem logTwoUpper : Real.log 2 < (7 / 10 : ℝ) := by
  have bound :=
    Hex.IntervalMathlib.Experiment.LogTablePrecision.decimal20.2
  norm_num at bound ⊢
  linarith

private theorem logTwoLower : (69 / 100 : ℝ) < Real.log 2 := by
  have bound :=
    Hex.IntervalMathlib.Experiment.LogTablePrecision.decimal20.1
  norm_num at bound ⊢
  linarith

private theorem logThreeUpper : Real.log 3 < (11 / 10 : ℝ) := by
  have bound := Real.log_div_le_sum_range_add
    (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at bound
  linarith

private theorem logFourUpper : Real.log 4 < (7 / 5 : ℝ) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  linarith [logTwoUpper]

private theorem logEightUpper : Real.log 8 < (21 / 10 : ℝ) := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  norm_num
  linarith [logTwoUpper]

private theorem logNineUpper : Real.log 9 < (11 / 5 : ℝ) := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  norm_num
  linarith [logThreeUpper]

private theorem logSixteenUpper : Real.log 16 < (14 / 5 : ℝ) := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  norm_num
  linarith [logTwoUpper]

private theorem logEighteenUpper : Real.log 18 < (29 / 10 : ℝ) := by
  rw [show (18 : ℝ) = 2 * 3 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  norm_num
  linarith [logTwoUpper, logThreeUpper]

private theorem logThirtyTwoUpper : Real.log 32 < (7 / 2 : ℝ) := by
  rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
  norm_num
  linarith [logTwoUpper]

private theorem logLeOfNatLe {n bound : Nat} (hn : 0 < n) (h : n ≤ bound) :
    Real.log n ≤ Real.log bound := by
  exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast h)

private theorem globalNestedUpper {n : Nat} (hn : 2 ≤ n) (hn31 : n ≤ 31) :
    Real.log (Real.log n) < (7 / 5 : ℝ) := by
  have logPositive : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have logNUpper : Real.log (n : ℝ) < (7 / 2 : ℝ) :=
    (logLeOfNatLe (show 0 < n by omega) (show n ≤ 32 by omega)).trans_lt
      logThirtyTwoUpper
  have nested : Real.log (Real.log (n : ℝ)) < Real.log (7 / 2 : ℝ) :=
    Real.log_lt_log logPositive logNUpper
  have compare : Real.log (7 / 2 : ℝ) < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  exact nested.trans (compare.trans logFourUpper)

private noncomputable def logCap (n : Nat) : ℝ :=
  if n = 2 then 7 / 10
  else if n = 3 then 11 / 10
  else if n = 4 then 7 / 5
  else if n ≤ 8 then 21 / 10
  else if n = 9 then 11 / 5
  else if n ≤ 16 then 14 / 5
  else if n ≤ 18 then 29 / 10
  else if n = 21 then 16 / 5
  else 7 / 2

private theorem logCapUpper {n : Nat} (hn : 2 ≤ n) (hn31 : n ≤ 31) :
    Real.log n < logCap n := by
  by_cases n2 : n = 2
  · subst n; simpa [logCap] using logTwoUpper
  by_cases n3 : n = 3
  · subst n; simpa [logCap] using logThreeUpper
  by_cases n4 : n = 4
  · subst n; simpa [logCap] using logFourUpper
  by_cases n8 : n ≤ 8
  · have bound := (logLeOfNatLe (show 0 < n by omega) n8).trans_lt logEightUpper
    simpa [logCap, n2, n3, n4, n8] using bound
  by_cases n9 : n = 9
  · subst n; simpa [logCap] using logNineUpper
  by_cases n16 : n ≤ 16
  · have bound := (logLeOfNatLe (show 0 < n by omega) n16).trans_lt logSixteenUpper
    simpa [logCap, n2, n3, n4, n8, n9, n16] using bound
  by_cases n18 : n ≤ 18
  · have bound := (logLeOfNatLe (show 0 < n by omega) n18).trans_lt logEighteenUpper
    simpa [logCap, n2, n3, n4, n8, n9, n16, n18] using bound
  by_cases n21 : n = 21
  · subst n
    have logSeven : Real.log 7 < (21 / 10 : ℝ) :=
      (logLeOfNatLe (n := 7) (bound := 8) (by norm_num) (by norm_num)).trans_lt
        logEightUpper
    change Real.log (21 : ℝ) < 16 / 5
    rw [show (21 : ℝ) = 3 * 7 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith [logThreeUpper]
  · have bound :=
      (logLeOfNatLe (show 0 < n by omega) (show n ≤ 32 by omega)).trans_lt
        logThirtyTwoUpper
    simpa [logCap, n2, n3, n4, n8, n9, n16, n18, n21] using bound

/-- Exact arithmetic leaves used by `Rosser1938.p_n_gt_1` for `2 ≤ n ≤ 31`. -/
theorem logLeaf (n : Nat) (hn : 2 ≤ n) (hn31 : n ≤ 31) :
    (n : ℝ) * Real.log n < sourceCut n := by
  have bound := logCapUpper hn hn31
  interval_cases n
  all_goals norm_num [sourceCut, logCap] at bound ⊢; nlinarith

private noncomputable def nestedCap (n : Nat) : ℝ :=
  if n = 2 then 0
  else if n = 3 then 1 / 10
  else if n = 4 then 2 / 5
  else if n ≤ 8 then 11 / 10
  else if n = 9 then 6 / 5
  else 7 / 5

private theorem nestedCapUpper {n : Nat} (hn : 2 ≤ n) (hn31 : n ≤ 31) :
    Real.log (Real.log n) < nestedCap n := by
  by_cases n2 : n = 2
  · subst n
    have positive : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have upper : Real.log 2 < (1 : ℝ) := logTwoUpper.trans (by norm_num)
    have nested := Real.log_lt_log positive upper
    simpa [nestedCap] using nested
  by_cases n3 : n = 3
  · subst n
    have positive : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have upper := Real.log_lt_log positive logThreeUpper
    have endpoint := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 10 by norm_num)
    have result := upper.trans_le endpoint
    norm_num [nestedCap] at result ⊢
    exact result
  by_cases n4 : n = 4
  · subst n
    have positive : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have upper := Real.log_lt_log positive logFourUpper
    have endpoint := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 5 by norm_num)
    have result := upper.trans_le endpoint
    norm_num [nestedCap] at result ⊢
    exact result
  by_cases n8 : n ≤ 8
  · have logBound := logCapUpper hn hn31
    have logBound' : Real.log n < (21 / 10 : ℝ) := by
      simpa [logCap, n2, n3, n4, n8] using logBound
    have positive : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have upper := Real.log_lt_log positive logBound'
    have endpoint := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 21 / 10 by norm_num)
    have result := upper.trans_le endpoint
    norm_num [nestedCap, n2, n3, n4, n8] at result ⊢
    exact result
  by_cases n9 : n = 9
  · subst n
    have positive : 0 < Real.log 9 := Real.log_pos (by norm_num)
    have upper := Real.log_lt_log positive logNineUpper
    have endpoint := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 5 by norm_num)
    have result := upper.trans_le endpoint
    norm_num [nestedCap] at result ⊢
    exact result
  · simpa [nestedCap, n2, n3, n4, n8, n9] using globalNestedUpper hn hn31

/-- Exact arithmetic leaves used by `RS_prime_helper.p_n_lower_small` for
`2 ≤ n ≤ 31`. -/
theorem nestedLogLeaf (n : Nat) (hn : 2 ≤ n) (hn31 : n ≤ 31) :
    (n : ℝ) * (Real.log n + Real.log (Real.log n) - 3 / 2) < sourceCut n := by
  have logBound := logCapUpper hn hn31
  have nestedBound := nestedCapUpper hn hn31
  interval_cases n
  all_goals
    norm_num [sourceCut, logCap, nestedCap] at logBound nestedBound ⊢
    nlinarith

/-- A coordinate endpoint cannot be weakened arbitrarily and then recovered by
asking the logarithm provider for more precision. -/
theorem rejectWrongCut :
    ¬ ((31 : ℝ) * Real.log 31 < 20) := by
  have monotone : Real.log 2 < Real.log 31 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have lower : (69 / 100 : ℝ) < Real.log 31 := logTwoLower.trans monotone
  norm_num at lower ⊢
  nlinarith

end Hex.IntervalMathlib.Experiment.PntPrimeLogSmall

end
