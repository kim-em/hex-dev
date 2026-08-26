/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Basic
public import Mathlib.Algebra.Polynomial.Taylor

public section

/-!
# Taylor coefficient correspondence

This module identifies the exact Gaussian-dyadic coefficients computed by
`Hex.taylor` with Mathlib's coefficients of `p.comp (X + C z)`.  The executable
fold semantics are encapsulated by `Hex.ZPoly.taylor_getD`; this companion only
casts its closed binomial sum into `ℂ`.
-/

open Polynomial Finset

namespace HexRootsMathlib

noncomputable section

/-- The Mathlib and Mathlib-free Pascal recursions define the same binomial
coefficient. -/
theorem choose_eq_choose (n k : Nat) : Hex.Nat.choose n k = Nat.choose n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k => rw [Hex.Nat.choose_succ_succ, Nat.choose_succ_succ, ih, ih]

/-- Casting the executable finite Gaussian-dyadic sum gives a `Finset` sum in
`ℂ`. -/
theorem toComplex_gaussSum (n : Nat) (f : Nat → Hex.GaussDyadic) :
    GaussDyadic.toComplex (Hex.gaussSum n f) =
      ∑ i ∈ Finset.range n, GaussDyadic.toComplex (f i) := by
  induction n with
  | zero =>
      simp only [Hex.gaussSum, List.range_zero, List.foldl_nil, Finset.range_zero,
        Finset.sum_empty]
      apply Complex.ext <;> simp [GaussDyadic.toComplex]
  | succ n ih =>
      rw [Hex.gaussSum_succ, GaussDyadic.toComplex_add, ih,
        Finset.sum_range_succ]

/-- The executable closed-form Taylor coefficient casts to its ordinary
complex binomial sum. -/
theorem toComplex_taylorCoeff (p : Hex.ZPoly) (z : Hex.GaussDyadic) (k : Nat) :
    GaussDyadic.toComplex (Hex.taylorCoeff p z k) =
      ∑ r ∈ Finset.range (p.size - k),
        ((k + r).choose k : ℂ) * (p.coeff (k + r) : ℂ) *
          GaussDyadic.toComplex z ^ r := by
  unfold Hex.taylorCoeff
  rw [toComplex_gaussSum]
  apply Finset.sum_congr rfl
  intro r _
  simp [Hex.Nat.binom_eq_choose, choose_eq_choose]
  ring

/-- A nonempty executable polynomial has complex-cast degree strictly below
its stored coefficient count. -/
private theorem natDegree_lt_size (p : Hex.ZPoly) (hp : 0 < p.size) :
    (toPolyℂ p).natDegree < p.size := by
  rw [natDegree_toPolyℂ]
  have hdegree : p.degree? = some (p.size - 1) := by
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hp]
  rw [hdegree, Option.getD_some]
  omega

/-- Coefficient `k` of the Mathlib Taylor shift is the same finite binomial
sum used by the executable implementation. -/
theorem coeff_shift (p : Hex.ZPoly) (z : Hex.GaussDyadic) (k : Nat) :
    ((toPolyℂ p).comp (X + C (GaussDyadic.toComplex z))).coeff k =
      ∑ r ∈ Finset.range (p.size - k),
        ((k + r).choose k : ℂ) * (p.coeff (k + r) : ℂ) *
          GaussDyadic.toComplex z ^ r := by
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff]
  by_cases hk : k < p.size
  · have hp : 0 < p.size := Nat.zero_lt_of_lt hk
    have hdegree : (Polynomial.hasseDeriv k (toPolyℂ p)).natDegree < p.size - k :=
      lt_of_le_of_lt (Polynomial.natDegree_hasseDeriv_le (toPolyℂ p) k) (by
        have := natDegree_lt_size p hp
        omega)
    rw [Polynomial.eval_eq_sum_range' hdegree]
    apply Finset.sum_congr rfl
    intro r _
    rw [Polynomial.hasseDeriv_coeff, coeff_toPolyℂ]
    simp only [Nat.add_comm r k]
  · have hksize : p.size ≤ k := Nat.le_of_not_gt hk
    rw [Nat.sub_eq_zero_of_le hksize]
    simp only [Finset.range_zero, Finset.sum_empty]
    by_cases hp : p.size = 0
    · have hp0 : p = 0 := by
        apply Hex.DensePoly.ext_coeff
        intro i
        rw [Hex.DensePoly.coeff_zero]
        exact Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)
      simp [hp0, toPolyℂ]
    · have hdegree : (toPolyℂ p).natDegree < k :=
        (natDegree_lt_size p (Nat.pos_of_ne_zero hp)).trans_le hksize
      rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree (toPolyℂ p) k hdegree]
      exact Polynomial.eval_zero

/-- **Taylor bridge.** Every executable Taylor array entry, including an
out-of-bounds `getD`, casts to the corresponding coefficient of the exact
Mathlib shift `p(X + z)`. -/
theorem taylor_coeff (p : Hex.ZPoly) (z : Hex.GaussDyadic) (k : Nat) :
    GaussDyadic.toComplex ((Hex.taylor p z).getD k (0, 0)) =
      ((toPolyℂ p).comp (X + C (GaussDyadic.toComplex z))).coeff k := by
  rw [Hex.taylor_getD]
  by_cases hk : k < p.size
  · rw [if_pos hk, toComplex_taylorCoeff, coeff_shift]
  · rw [if_neg hk, coeff_shift,
      Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hk)]
    simp only [Finset.range_zero, Finset.sum_empty]
    apply Complex.ext <;> simp [GaussDyadic.toComplex]

end

end HexRootsMathlib
