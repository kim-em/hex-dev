/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPolyMathlib.EvalVec
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

public section

/-! Identification of the executable matrix minimal polynomial with Mathlib's. -/

open Matrix Polynomial

namespace HexMinPolyMathlib

open HexMatrixMathlib HexPolyMathlib

universe u

variable {F : Type u} [Field F] [DecidableEq F] {n : Nat}

omit [DecidableEq F] in
private theorem vectorEquiv_zero :
    vectorEquiv (0 : Vector F n) = (0 : Fin n → F) := by
  funext i
  rw [vectorEquiv_apply]
  simp

/-- The executable minimal polynomial is Mathlib's minimal polynomial of the
corresponding matrix. -/
theorem equiv_minPoly (A : Hex.Matrix F n n) :
    equiv (Hex.Matrix.minPoly A) = minpoly F (matrixEquiv A) := by
  apply minpoly.unique F (matrixEquiv A)
  · rw [Polynomial.Monic.def, equiv_apply, leadingCoeff_toPolynomial]
    exact Hex.Matrix.minPoly_monic A
  · apply (Matrix.ext_iff_mulVec).2
    intro w
    have h := vectorEquiv_evalVec (Hex.Matrix.minPoly A) A (vectorEquiv.symm w)
    rw [Hex.Matrix.evalVec_minPoly, vectorEquiv_zero,
      Equiv.apply_symm_apply] at h
    simpa using h.symm
  · intro q hq hroot
    have hall : ∀ v : Vector F n,
        Hex.Matrix.evalVec (equiv.symm q) A v = 0 := by
      intro v
      apply vectorEquiv.injective
      rw [vectorEquiv_evalVec, RingEquiv.apply_symm_apply, hroot,
        Matrix.zero_mulVec, vectorEquiv_zero]
    have hdense := Hex.Matrix.minPoly_dvd A (equiv.symm q) hall
    have hpoly := toPolynomial_dvd hdense
    exact Polynomial.degree_le_of_dvd (by simpa using hpoly) hq.ne_zero

omit [DecidableEq F] in
private theorem transpose_aeval (p : Polynomial F) (A : Matrix (Fin n) (Fin n) F) :
    (Polynomial.aeval A p)ᵀ = Polynomial.aeval Aᵀ p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def,
    Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range]
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Algebra.smul_def, Matrix.transpose_smul, Matrix.transpose_pow,
    Algebra.smul_def]

omit [DecidableEq F] in
private theorem minpoly_transpose (A : Matrix (Fin n) (Fin n) F) :
    minpoly F Aᵀ = minpoly F A := by
  have hforward : minpoly F Aᵀ ∣ minpoly F A := by
    apply minpoly.dvd
    rw [← transpose_aeval, minpoly.aeval, Matrix.transpose_zero]
  have hback : minpoly F A ∣ minpoly F Aᵀ := by
    apply minpoly.dvd
    apply Matrix.transpose_injective
    rw [transpose_aeval, minpoly.aeval, Matrix.transpose_zero]
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (Matrix.isIntegral Aᵀ))
    (minpoly.monic (Matrix.isIntegral A)) hforward
  exact Polynomial.natDegree_le_of_dvd hback
    (minpoly.ne_zero (Matrix.isIntegral Aᵀ))

/-- Transposition preserves the executable minimal polynomial. -/
theorem minPoly_transpose (A : Hex.Matrix F n n) :
    Hex.Matrix.minPoly (Hex.Matrix.transpose A) = Hex.Matrix.minPoly A := by
  apply equiv.injective
  rw [equiv_minPoly, equiv_minPoly, matrixEquiv_transpose, minpoly_transpose]

private theorem equiv_minPoly_self (A : Hex.Matrix F n n) :
    equiv (Hex.Matrix.minPoly A) = minpoly F A := by
  rw [equiv_minPoly]
  exact minpoly.algEquiv_eq (matrixAlgEquiv (R := F) (n := n)) A

/-- Conjugation by an invertible matrix preserves the executable minimal
polynomial. This is the similarity-invariance law. -/
theorem minPoly_conj (A : Hex.Matrix F n n) (P : (Hex.Matrix F n n)ˣ) :
    Hex.Matrix.minPoly ((ConjAct.toConjAct P) • A) = Hex.Matrix.minPoly A := by
  apply equiv.injective
  rw [equiv_minPoly_self, equiv_minPoly_self]
  exact minpoly.algEquiv_eq
    (MulSemiringAction.toAlgEquiv F (Hex.Matrix F n n) (ConjAct.toConjAct P)) A

end HexMinPolyMathlib
