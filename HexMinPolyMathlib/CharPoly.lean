/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPolyMathlib.Order
public import HexCharPolyMathlib
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

public section

/-! Consequences of Cayley--Hamilton for the executable minimal polynomial. -/

open Polynomial

namespace HexMinPolyMathlib

open HexMatrixMathlib HexPolyMathlib

universe u

variable {F : Type u} [Field F] [DecidableEq F] {n : Nat}

/-- The executable minimal polynomial divides the executable characteristic
polynomial. -/
theorem minPoly_dvd_charPoly (A : Hex.Matrix F n n) :
    Hex.Matrix.minPoly A ∣ Hex.Matrix.charPoly A := by
  have h := Matrix.minpoly_dvd_charpoly (matrixEquiv A)
  rw [← equiv_minPoly A, ← HexCharPolyMathlib.equiv_charPoly A] at h
  exact toPolynomial_dvd_iff.mp (by simpa [equiv_apply] using h)

/-- The degree of the executable minimal polynomial is at most the matrix
dimension. -/
theorem degree?_minPoly_le (A : Hex.Matrix F n n) :
    (Hex.Matrix.minPoly A).degree?.getD 0 ≤ n := by
  rw [← natDegree_toPolynomial]
  change (equiv (Hex.Matrix.minPoly A)).natDegree ≤ n
  rw [equiv_minPoly]
  calc
    (minpoly F (matrixEquiv A)).natDegree ≤
        (matrixEquiv A).charpoly.natDegree :=
      Polynomial.natDegree_le_of_dvd
        (Matrix.minpoly_dvd_charpoly (matrixEquiv A))
        (Matrix.charpoly_monic (matrixEquiv A)).ne_zero
    _ = n := by simp

end HexMinPolyMathlib
