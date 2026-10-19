/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum
public import HexInterval.Experiment.PntDusartExp

@[expose] public section

/-!
# Checked semantics for the Dusart exponential leaves

One range-reduced Taylor theorem proves every exact comparison accepted by the
Mathlib-free source table and rational checker.
-/

namespace Hex.Interval.Experiment.PntDusartExp

open Finset Real

noncomputable def Q.value (value : Q) : Real := value

theorem qLe_iff (left right : Q) :
    qLe left right = true ↔ left.value ≤ right.value := by
  simp only [qLe, decide_eq_true_eq, Q.value, Rat.cast_le]
  exact (Rat.le_iff left right).symm

theorem qLt_iff (left right : Q) :
    qLt left right = true ↔ left.value < right.value := by
  simp only [qLt, decide_eq_true_eq, Q.value, Rat.cast_lt]
  exact (Rat.lt_iff left right).symm

theorem qadd_value (left right : Q) :
    (qadd left right).value = left.value + right.value := by
  simp [qadd, Q.value, Rational.add_eq]

theorem qmul_value (left right : Q) :
    (qmul left right).value = left.value * right.value := by
  simp [qmul, Q.value, Rational.mul_eq]

theorem divInt_value (numerator denominator : Int) :
    Q.value (Rat.divInt numerator denominator) =
      (numerator : Real) / (denominator : Real) := by
  simp [Q.value, Rat.cast_divInt]

theorem qpow_value (value : Q) (degree : Nat) :
    (qpow value degree).value = value.value ^ degree := by
  induction degree with
  | zero => simp [qpow, Q.value]
  | succ degree induction =>
      simp [qpow, qmul_value, induction, pow_succ]

theorem qpow64_value (value : Q) :
    (qpow64 value).value = value.value ^ (64 : Nat) := by
  simp only [qpow64, qmul_value]
  ring

theorem factorial_eq (degree : Nat) : factorial degree = degree.factorial := by
  induction degree with
  | zero => rfl
  | succ degree induction => simp [factorial, Nat.factorial, induction]

theorem term_value (value : Q) (degree : Nat) :
    (term value degree).value = value.value ^ degree / degree.factorial := by
  rw [term, qmul_value, qpow_value, factorial_eq]
  rw [divInt_value]
  simp [div_eq_mul_inv]

theorem sumTerms_value (value : Q) (count : Nat) :
    (sumTerms value count).value =
      ∑ degree ∈ Finset.range count, value.value ^ degree / degree.factorial := by
  induction count with
  | zero => simp [sumTerms, Q.value]
  | succ count induction =>
      rw [sumTerms, qadd_value, induction, sum_range_succ, term_value]

theorem taylorUpper_value (value : Q) :
    (taylorUpper value).value =
      (∑ degree ∈ Finset.range 12,
        value.value ^ degree / degree.factorial) +
      value.value ^ 12 * (13 / ((12 : Nat).factorial * 12) : Real) := by
  rw [taylorUpper, qadd_value, sumTerms_value, qmul_value, qpow_value]
  rw [divInt_value]
  norm_num [Q.value, factorial_eq]

theorem reduced_value (value : Certificate) (denominator : value.argumentDen ≠ 0)
    (split : value.split = 64) :
    value.reduced.value =
      (value.argumentNum : Real) / value.argumentDen / 64 := by
  rw [Certificate.reduced, divInt_value, split]
  push_cast
  field_simp

private theorem expWindow (value : Certificate)
    (denominator : value.argumentDen ≠ 0) (split : value.split = 64)
    (nonnegative : Q.value 0 ≤ value.reduced.value)
    (atMostOne : value.reduced.value ≤ Q.value 1) :
    (sumTerms value.reduced 12).value ^ (64 : Nat) ≤
        Real.exp ((value.argumentNum : Real) / value.argumentDen) ∧
      Real.exp ((value.argumentNum : Real) / value.argumentDen) ≤
        (taylorUpper value.reduced).value ^ (64 : Nat) := by
  have reducedNonnegative : 0 ≤ value.reduced.value := by
    simpa [Q.value] using nonnegative
  have reducedAtMostOne : value.reduced.value ≤ 1 := by
    simpa [Q.value] using atMostOne
  have lowerBase :
      (sumTerms value.reduced 12).value ≤ Real.exp value.reduced.value := by
    rw [sumTerms_value]
    exact Real.sum_le_exp_of_nonneg reducedNonnegative 12
  have upperBase :
      Real.exp value.reduced.value ≤ (taylorUpper value.reduced).value := by
    rw [taylorUpper_value]
    have bound := Real.exp_bound' reducedNonnegative reducedAtMostOne
      (n := 12) (by norm_num)
    convert bound using 1
    all_goals ring
  have lowerNonnegative : 0 ≤ (sumTerms value.reduced 12).value := by
    rw [sumTerms_value]
    apply Finset.sum_nonneg
    intro degree _membership
    positivity
  have denominatorReal : (value.argumentDen : Real) ≠ 0 := by
    exact_mod_cast denominator
  have splitIdentity :
      (64 : Real) * value.reduced.value =
        (value.argumentNum : Real) / value.argumentDen := by
    rw [reduced_value value denominator split]
    field_simp [denominatorReal]
  have natSplitIdentity :
      ((64 : Nat) : Real) * value.reduced.value =
        (value.argumentNum : Real) / value.argumentDen := by
    simpa using splitIdentity
  constructor
  · calc
      (sumTerms value.reduced 12).value ^ (64 : Nat) ≤
          Real.exp value.reduced.value ^ (64 : Nat) :=
        pow_le_pow_left₀ lowerNonnegative lowerBase 64
      _ = Real.exp ((value.argumentNum : Real) / value.argumentDen) := by
        rw [← Real.exp_nat_mul, natSplitIdentity]
  · calc
      Real.exp ((value.argumentNum : Real) / value.argumentDen) =
          Real.exp value.reduced.value ^ (64 : Nat) := by
        rw [← Real.exp_nat_mul, natSplitIdentity]
      _ ≤ (taylorUpper value.reduced).value ^ (64 : Nat) :=
        pow_le_pow_left₀ (Real.exp_pos _).le upperBase 64

def Holds (value : Certificate) : Prop :=
  match value.relation with
  | .upperLe =>
      Real.exp ((value.argumentNum : Real) / value.argumentDen) ≤ value.target
  | .upperLt =>
      Real.exp ((value.argumentNum : Real) / value.argumentDen) < value.target
  | .lowerLe =>
      (value.target : Real) ≤ Real.exp ((value.argumentNum : Real) / value.argumentDen)

/-- The semantic kernel for a bounded Taylor certificate.  The source-table
authentication remains a separate premise of `certificateHolds`. -/
theorem checkedHolds (value : Certificate) (denominator : value.argumentDen ≠ 0)
    (split : value.split = 64) (terms : value.terms = 12)
    (nonnegative : qLe 0 value.reduced = true)
    (atMostOne : qLe value.reduced 1 = true)
    (checked : comparisonHolds value = true) :
    Holds value := by
  have window := expWindow value denominator split
    ((qLe_iff 0 value.reduced).mp nonnegative)
    ((qLe_iff value.reduced 1).mp atMostOne)
  have targetValue : value.targetQ.value = (value.target : Real) := by
    simp [Certificate.targetQ, Q.value]
  unfold comparisonHolds at checked
  rw [terms] at checked
  unfold Holds
  generalize relationEq : value.relation = relation at checked ⊢
  cases relation with
  | upperLe =>
      have final := (qLe_iff _ _).mp checked
      rw [qpow64_value, targetValue] at final
      exact window.2.trans final
  | upperLt =>
      have final := (qLt_iff _ _).mp checked
      rw [qpow64_value, targetValue] at final
      exact window.2.trans_lt final
  | lowerLe =>
      have final := (qLe_iff _ _).mp checked
      rw [qpow64_value, targetValue] at final
      exact final.trans window.1

/-- Every source-correlated certificate accepted by the bounded exact checker
proves its recorded exponential comparison. -/
theorem certificateHolds (value : Certificate) (valid : validCertificate value = true) :
    Holds value := by
  simp only [validCertificate, Bool.and_eq_true, decide_eq_true_eq] at valid
  have denominator : value.argumentDen ≠ 0 := valid.1.1.1.1.1.2
  have split : value.split = 64 := by
    simpa using valid.1.1.1.1.2
  have terms : value.terms = 12 := by
    simpa using valid.1.1.1.2
  exact checkedHolds value denominator split terms valid.1.1.2 valid.1.2 valid.2

private def wrongLowerUpper : Certificate :=
  ⟨2, 1283, 100, 400000, .upperLt, 64, 12⟩

/-- The deliberately raised `12.83` lower target is genuinely false; the
same bounded provider proves the incompatible strict upper enclosure. -/
theorem rejectWrongLower : ¬ (400000 : Real) ≤ Real.exp (1283 / 100) := by
  have upper := checkedHolds wrongLowerUpper (by decide) (by decide) (by decide)
    (by decide) (by decide) (by set_option maxRecDepth 100000 in decide)
  simp only [Holds, wrongLowerUpper, Nat.cast_ofNat] at upper
  exact not_le_of_gt upper

end Hex.Interval.Experiment.PntDusartExp

end
