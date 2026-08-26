/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Lazy

public section

/-!
# Semantic algebraic-coefficient polynomials

The executable representation stores coefficients in increasing degree order.
Horner interpretation into `Polynomial ℂ` makes semantic trailing-zero
normalization explicit without adding structural equality to algebraic
numbers.
-/

namespace Hex.AlgebraicPoly

/-- Interpret a normalized executable algebraic polynomial in `Polynomial ℂ`. -/
@[expose]
noncomputable def toPolynomial (f : AlgebraicPoly) : Polynomial ℂ :=
  f.coeffs.foldr
    (fun a value => Polynomial.C a.toComplex + Polynomial.X * value) 0

private theorem coeff_horner (coeffs : List AlgebraicNumber) (n : Nat) :
    (coeffs.foldr
        (fun (a : AlgebraicNumber) (value : Polynomial ℂ) =>
          Polynomial.C a.toComplex + Polynomial.X * value) 0).coeff n =
      (coeffs.getD n 0).toComplex := by
  induction coeffs generalizing n with
  | nil => simp [AlgebraicNumber.zero_toComplex]
  | cons a coeffs ih =>
      cases n with
      | zero => simp
      | succ n => simpa using ih n

private theorem array_toList_getD (coeffs : Array AlgebraicNumber) (n : Nat) :
    coeffs.toList.getD n 0 = coeffs.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]

/-- Semantic coefficients agree with the executable coefficient accessor. -/
theorem coeff_toPolynomial (f : AlgebraicPoly) (n : Nat) :
    f.toPolynomial.coeff n = (f.coeff n).toComplex := by
  rw [toPolynomial, ← Array.foldr_toList, coeff_horner, array_toList_getD]
  rfl

/-- The stored leading coefficient of a nonzero normalized algebraic
polynomial is canonically nonzero. -/
theorem last_isZero_false (f : AlgebraicPoly) (h : !f.isZero) :
    (f.coeff (f.size - 1)).isZero = false := by
  have hsize : 0 < f.coeffs.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    have hempty : f.coeffs = #[] := Array.eq_empty_of_size_eq_zero hsize
    change f.data = #[] at hempty
    have hne : f.data ≠ #[] := by
      simpa [AlgebraicPoly.isZero] using h
    exact hne hempty
  have hlast : f.coeffs.toList.getLast? =
      some (f.coeff (f.size - 1)) := by
    rw [List.getLast?_eq_getElem?, Array.length_toList,
      Array.getElem?_toList]
    have hi : f.coeffs.size - 1 < f.coeffs.size := by omega
    rw [Array.getElem?_eq_getElem hi]
    change some f.coeffs[f.coeffs.size - 1] =
      some (f.coeffs.getD (f.coeffs.size - 1) 0)
    rw [Array.getElem_eq_getD]
  have hnormalized := f.normalized
  rw [AlgebraicPolyNormalized,
    ← List.getLast?_eq_head?_reverse] at hnormalized
  change
    (match f.coeffs.toList.getLast? with
    | some a => a.isZero = false
    | none => True) at hnormalized
  rw [hlast] at hnormalized
  exact hnormalized

/-- Executable semantic-zero detection is exact. -/
theorem isZero_iff (f : AlgebraicPoly) :
    f.isZero ↔ f.toPolynomial = 0 := by
  constructor
  · intro hzero
    have hcoeffs : f.coeffs = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      exact Array.isEmpty_iff_size_eq_zero.mp hzero
    simp [toPolynomial, hcoeffs]
  · intro hpoly
    by_contra hzero
    have hnonzero : !f.isZero := by
      cases hz : f.isZero <;> simp_all
    have hlastZero : (f.coeff (f.size - 1)).toComplex = 0 := by
      rw [← coeff_toPolynomial, hpoly]
      simp
    have hisZero : (f.coeff (f.size - 1)).isZero = true :=
      (AlgebraicNumber.isZero_iff _).mpr hlastZero
    rw [last_isZero_false f hnonzero] at hisZero
    contradiction

/-- A nonzero executable polynomial has the same natural degree as its
semantic interpretation. -/
theorem natDegree_toPolynomial (f : AlgebraicPoly) (h : !f.isZero) :
    f.toPolynomial.natDegree = f.degree?.getD 0 := by
  have hdegree : f.toPolynomial.natDegree = f.size - 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [coeff_toPolynomial]
      have hbound : f.data.size ≤ n := by
        change f.size ≤ n
        omega
      change
        (if hi : n < f.data.size then f.data[n] else 0).toComplex = 0
      split
      · omega
      · exact AlgebraicNumber.zero_toComplex
    · intro hcoeff
      have hvalue : (f.coeff (f.size - 1)).toComplex = 0 := by
        rw [← coeff_toPolynomial]
        exact hcoeff
      have hisZero : (f.coeff (f.size - 1)).isZero = true :=
        (AlgebraicNumber.isZero_iff _).mpr hvalue
      rw [last_isZero_false f h] at hisZero
      contradiction
  rw [hdegree]
  have hfalse : f.isZero = false := by
    cases hz : f.isZero <;> simp_all
  simp [AlgebraicPoly.degree?, hfalse]

/-- Canonical coefficientwise Boolean equality is faithful to the semantic
polynomial interpretation. -/
theorem beq_iff (f g : AlgebraicPoly) :
    f == g ↔ f.toPolynomial = g.toPolynomial := by
  constructor
  · intro h
    change f.data == g.data at h
    have hdata : f.data = g.data := eq_of_beq h
    cases f
    cases g
    cases hdata
    rfl
  · intro hpoly
    have hzero : f.isZero = g.isZero := by
      apply Bool.eq_iff_iff.mpr
      rw [isZero_iff, isZero_iff, hpoly]
    have hsize : f.size = g.size := by
      by_cases hf : f.isZero
      · have hg : g.isZero := by simpa [hzero] using hf
        have hfsize := Array.isEmpty_iff_size_eq_zero.mp hf
        have hgsize := Array.isEmpty_iff_size_eq_zero.mp hg
        change f.data.size = g.data.size
        omega
      · have hg : g.isZero ≠ true := by simpa [hzero] using hf
        have hfn : !f.isZero := by
          cases hz : f.isZero <;> simp_all
        have hgn : !g.isZero := by
          cases hz : g.isZero <;> simp_all
        have hdegree := congrArg Polynomial.natDegree hpoly
        rw [natDegree_toPolynomial f hfn,
          natDegree_toPolynomial g hgn] at hdegree
        have hfsize : 0 < f.size := by
          apply Nat.pos_of_ne_zero
          intro h
          apply hf
          exact Array.isEmpty_iff_size_eq_zero.mpr h
        have hgsize : 0 < g.size := by
          apply Nat.pos_of_ne_zero
          intro h
          apply hg
          exact Array.isEmpty_iff_size_eq_zero.mpr h
        have hffalse : f.isZero = false := Bool.eq_false_iff.mpr hf
        have hgfalse : g.isZero = false := Bool.eq_false_iff.mpr hg
        simp [AlgebraicPoly.degree?, hffalse, hgfalse] at hdegree
        omega
    change f.data == g.data
    apply beq_iff_eq.mpr
    apply Array.ext
    · exact hsize
    · intro i hif hig
      apply AlgebraicNumber.toComplex_injective
      have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff i) hpoly
      rw [coeff_toPolynomial, coeff_toPolynomial] at hcoeff
      simpa [AlgebraicPoly.coeff, Array.getD, hif, hig] using hcoeff

end Hex.AlgebraicPoly
