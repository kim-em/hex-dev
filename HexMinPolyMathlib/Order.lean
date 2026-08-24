/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPolyMathlib.Basic

public section

/-! Polynomial-facing contracts for vector orders and executable LCM. -/

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

/-- The order polynomial generates the annihilator of its vector, transported
to Mathlib polynomials. -/
theorem vecMinPoly_dvd_iff (A : Hex.Matrix F n n) (v : Vector F n)
    (p : Polynomial F) :
    equiv (Hex.Matrix.vecMinPoly A v) ∣ p ↔
      (Polynomial.aeval (matrixEquiv A) p).mulVec (vectorEquiv v) = 0 := by
  constructor
  · intro hdvd
    have hdense : Hex.Matrix.vecMinPoly A v ∣ equiv.symm p :=
      toPolynomial_dvd_iff.mp (by simpa using hdvd)
    have heval := Hex.Matrix.evalVec_of_dvd A v hdense
      (Hex.Matrix.evalVec_vecMinPoly A v)
    have h := vectorEquiv_evalVec (equiv.symm p) A v
    rw [heval, vectorEquiv_zero, RingEquiv.apply_symm_apply] at h
    exact h.symm
  · intro hroot
    have heval : Hex.Matrix.evalVec (equiv.symm p) A v = 0 := by
      apply vectorEquiv.injective
      rw [vectorEquiv_evalVec, RingEquiv.apply_symm_apply, hroot,
        vectorEquiv_zero]
    have hdense := Hex.Matrix.vecMinPoly_dvd A v (equiv.symm p) heval
    simpa using toPolynomial_dvd hdense

/-- The executable monic LCM agrees exactly with Mathlib's normalized LCM. -/
theorem equiv_lcm (p q : Hex.DensePoly F) :
    equiv (Hex.DensePoly.lcm p q) = lcm (equiv p) (equiv q) := by
  by_cases hp : p = 0
  · subst p
    simp [Hex.DensePoly.lcm_zero_left]
  by_cases hq : q = 0
  · subst q
    simp [Hex.DensePoly.lcm_zero_right]
  apply dvd_antisymm_of_normalize_eq
  · apply Polynomial.Monic.normalize_eq_self
    rw [Polynomial.Monic.def, equiv_apply, leadingCoeff_toPolynomial]
    exact Hex.DensePoly.lcm_monic hp hq
  · exact normalize_lcm _ _
  · have hp' : p ∣ equiv.symm (lcm (equiv p) (equiv q)) :=
      toPolynomial_dvd_iff.mp (by simpa using dvd_lcm_left (equiv p) (equiv q))
    have hq' : q ∣ equiv.symm (lcm (equiv p) (equiv q)) :=
      toPolynomial_dvd_iff.mp (by simpa using dvd_lcm_right (equiv p) (equiv q))
    have h := Hex.DensePoly.lcm_dvd p q
      (equiv.symm (lcm (equiv p) (equiv q))) hp' hq'
    simpa using toPolynomial_dvd h
  · apply lcm_dvd
    · simpa using toPolynomial_dvd (Hex.DensePoly.dvd_lcm_left p q)
    · simpa using toPolynomial_dvd (Hex.DensePoly.dvd_lcm_right p q)

end HexMinPolyMathlib
