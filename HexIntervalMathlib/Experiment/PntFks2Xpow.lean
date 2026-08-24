/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Shard
public import HexInterval.Experiment.PntFks2Xpow

@[expose] public section

namespace Hex.Interval.Experiment.PntFks2Xpow

open Finset Real
open PntFks2Shard

/-- The real inequality asserted by the source `checkXpowCell` predicate. -/
def XpowHolds (value : Prefix) (cell : Cell) : Prop :=
  cell.eps.value ≤ Real.exp (-(cell.b' : ℝ) / value.n)

/-- Exact rational obligations for an upper Taylor witness. -/
def UpperValid (value : Prefix) (cell : Cell) : Prop :=
  (((Q.value 0 < cell.eps.value ∧ Q.value 0 ≤ (value.reducedQ cell).value) ∧
    (value.reducedQ cell).value ≤ Q.value 1) ∧
    (qmul cell.eps (qpow128 (taylorUpper (value.reducedQ cell)))).value ≤ Q.value 1)

/-- Exact rational obligations for a lower Taylor witness. -/
def LowerValid (value : Prefix) (cell : Cell) : Prop :=
  (((Q.value 0 < cell.eps.value ∧ Q.value 0 ≤ (value.reducedQ cell).value) ∧
    (value.reducedQ cell).value ≤ Q.value 1) ∧
    Q.value 1 <
      (qmul cell.eps (qpow128 (sumTerms (value.reducedQ cell) 12))).value)

theorem check_of_upperValid (value : Prefix) (cell : Cell)
    (valid : UpperValid value cell) : checkCell value cell = true := by
  simp only [checkCell, Bool.and_eq_true, qLt_iff, qLe_iff]
  simpa only [UpperValid] using valid

theorem checkBoundary_of_lowerValid (value : Prefix) (cell : Cell)
    (valid : LowerValid value cell) : checkBoundary value cell = true := by
  simp only [checkBoundary, Bool.and_eq_true, qLt_iff, qLe_iff]
  simpa only [LowerValid] using valid

private theorem splitIdentity (value : Prefix) (cell : Cell) (positive : 0 < value.n) :
    (128 : ℝ) * (value.reducedQ cell).value =
      (cell.b' : ℝ) / value.n := by
  rw [Prefix.reducedQ, divInt_value]
  push_cast
  field_simp [Nat.ne_of_gt positive]

theorem xpowHolds_of_upperValid (value : Prefix) (cell : Cell)
    (positive : 0 < value.n) (valid : UpperValid value cell) :
    XpowHolds value cell := by
  obtain ⟨⟨⟨epsPositive, reducedNonnegative⟩, reducedAtMostOne⟩, final⟩ := valid
  let reduced := value.reducedQ cell
  have reducedNonnegative' : 0 ≤ reduced.value := by
    simpa [reduced, Q.value] using reducedNonnegative
  have reducedAtMostOne' : reduced.value ≤ 1 := by
    simpa [reduced, Q.value] using reducedAtMostOne
  have epsPositive' : 0 < cell.eps.value := by simpa [Q.value] using epsPositive
  have taylor := exp_le_taylorUpper reduced reducedNonnegative' reducedAtMostOne'
  have power := pow_le_pow_left₀ (Real.exp_pos _).le taylor 128
  rw [← Real.exp_nat_mul] at power
  have split : ((128 : Nat) : ℝ) * reduced.value =
      (cell.b' : ℝ) / value.n := by
    simpa [reduced] using splitIdentity value cell positive
  rw [split] at power
  have product :
      cell.eps.value * Real.exp ((cell.b' : ℝ) / value.n) ≤ 1 := by
    have bounded := mul_le_mul_of_nonneg_left power epsPositive'.le
    rw [qmul_value, qpow128_value] at final
    exact le_trans bounded (by simpa [Q.value] using final)
  unfold XpowHolds
  rw [show -(cell.b' : ℝ) / value.n =
    -((cell.b' : ℝ) / value.n) by ring]
  rw [Real.exp_neg]
  simpa [div_eq_mul_inv] using
    (le_div_iff₀ (Real.exp_pos ((cell.b' : ℝ) / value.n))).mpr product

private theorem bNonnegative_of_upperValid (value : Prefix) (cell : Cell)
    (positive : 0 < value.n) (valid : UpperValid value cell) :
    0 ≤ (cell.b' : ℝ) := by
  have reducedNonnegative : 0 ≤ (value.reducedQ cell).value := by
    simpa [Q.value] using valid.1.1.2
  have quotient : 0 ≤ (cell.b' : ℝ) / value.n := by
    rw [← splitIdentity value cell positive]
    exact mul_nonneg (by norm_num) reducedNonnegative
  rcases (div_nonneg_iff.mp quotient) with nonnegative | nonpositive
  · exact nonnegative.1
  · exact False.elim ((not_le_of_gt (Nat.cast_pos.mpr positive)) nonpositive.2)

/-- A cell authenticated at a smaller positive exponent denominator remains
valid at every larger denominator. -/
theorem xpowHolds_mono_of_upperValid (source target : Prefix) (cell : Cell)
    (sourcePositive : 0 < source.n) (targetPositive : 0 < target.n)
    (ordered : source.n ≤ target.n) (valid : UpperValid source cell) :
    XpowHolds target cell := by
  have sourceHolds := xpowHolds_of_upperValid source cell sourcePositive valid
  have bNonnegative := bNonnegative_of_upperValid source cell sourcePositive valid
  apply sourceHolds.trans
  apply Real.exp_le_exp.mpr
  rw [show -(cell.b' : ℝ) / source.n =
    -((cell.b' : ℝ) / source.n) by ring]
  rw [show -(cell.b' : ℝ) / target.n =
    -((cell.b' : ℝ) / target.n) by ring]
  apply neg_le_neg
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr targetPositive)
    (Nat.cast_pos.mpr sourcePositive)).mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast ordered) bNonnegative

private theorem sumTerms_nonnegative (value : Q) (nonnegative : 0 ≤ value.value) :
    0 ≤ (sumTerms value 12).value := by
  rw [sumTerms_value]
  exact sum_nonneg fun degree _ => div_nonneg (pow_nonneg nonnegative degree) (by positivity)

theorem not_xpowHolds_of_lowerValid (value : Prefix) (cell : Cell)
    (positive : 0 < value.n) (valid : LowerValid value cell) :
    ¬ XpowHolds value cell := by
  obtain ⟨⟨⟨epsPositive, reducedNonnegative⟩, _reducedAtMostOne⟩, lower⟩ := valid
  let reduced := value.reducedQ cell
  have reducedNonnegative' : 0 ≤ reduced.value := by
    simpa [reduced, Q.value] using reducedNonnegative
  have epsPositive' : 0 < cell.eps.value := by simpa [Q.value] using epsPositive
  have lowerTaylor : (sumTerms reduced 12).value ≤ Real.exp reduced.value := by
    simpa [sumTerms_value] using Real.sum_le_exp_of_nonneg reducedNonnegative' 12
  have lowerNonnegative := sumTerms_nonnegative reduced reducedNonnegative'
  have power := pow_le_pow_left₀ lowerNonnegative lowerTaylor 128
  rw [← Real.exp_nat_mul] at power
  have split : ((128 : Nat) : ℝ) * reduced.value =
      (cell.b' : ℝ) / value.n := by
    simpa [reduced] using splitIdentity value cell positive
  rw [split] at power
  have product : 1 < cell.eps.value * Real.exp ((cell.b' : ℝ) / value.n) := by
    have lower' : 1 < cell.eps.value * (sumTerms reduced 12).value ^ 128 := by
      rw [qmul_value, qpow128_value] at lower
      simpa [reduced, Q.value] using lower
    have bounded := lt_of_lt_of_le lower'
      (mul_le_mul_of_nonneg_left power epsPositive'.le)
    exact bounded
  intro holds
  unfold XpowHolds at holds
  rw [show -(cell.b' : ℝ) / value.n =
    -((cell.b' : ℝ) / value.n) by ring] at holds
  rw [Real.exp_neg] at holds
  have atMostOne : cell.eps.value * Real.exp ((cell.b' : ℝ) / value.n) ≤ 1 :=
    calc
      cell.eps.value * Real.exp ((cell.b' : ℝ) / value.n)
          ≤ (Real.exp ((cell.b' : ℝ) / value.n))⁻¹ *
              Real.exp ((cell.b' : ℝ) / value.n) :=
        mul_le_mul_of_nonneg_right holds (Real.exp_pos _).le
      _ = 1 := inv_mul_cancel₀ (Real.exp_ne_zero _)
  exact (not_lt_of_ge atMostOne) product

end Hex.Interval.Experiment.PntFks2Xpow

end
