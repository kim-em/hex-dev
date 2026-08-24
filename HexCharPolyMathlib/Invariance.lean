/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPolyMathlib.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

/-!
Transpose and similarity invariance of the executable characteristic
polynomial.
-/

open Matrix Polynomial

namespace HexCharPolyMathlib

open HexMatrixMathlib HexPolyMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n : Nat}

/-- Transposition preserves the executable characteristic polynomial. -/
theorem charPoly_transpose (A : Hex.Matrix R n n) :
    Hex.Matrix.charPoly A.transpose = Hex.Matrix.charPoly A := by
  apply HexPolyMathlib.equiv.injective
  rw [equiv_charPoly, equiv_charPoly, HexMatrixMathlib.matrixEquiv_transpose,
    Matrix.charpoly_transpose]

/-- Conjugation by a pair of mutually inverse square matrices preserves the
executable characteristic polynomial. -/
theorem charPoly_conj (A U V : Hex.Matrix R n n)
    (h : U * V = Hex.Matrix.identity n) :
    Hex.Matrix.charPoly (U * A * V) = Hex.Matrix.charPoly A := by
  apply HexPolyMathlib.equiv.injective
  rw [equiv_charPoly, equiv_charPoly,
    HexMatrixMathlib.matrixEquiv_mul, HexMatrixMathlib.matrixEquiv_mul]
  have huv : matrixEquiv U * matrixEquiv V =
      (1 : Matrix (Fin n) (Fin n) R) := by
    have hm := congrArg matrixEquiv h
    have hid : matrixEquiv (Hex.Matrix.identity (R := R) n) =
        (1 : Matrix (Fin n) (Fin n) R) := by
      ext i j
      rw [HexMatrixMathlib.matrixEquiv_apply, Hex.Matrix.getElem_identity,
        Matrix.one_apply]
    rw [HexMatrixMathlib.matrixEquiv_mul] at hm
    rw [hid] at hm
    exact hm
  have hvu : matrixEquiv V * matrixEquiv U =
      (1 : Matrix (Fin n) (Fin n) R) := mul_eq_one_comm.mp huv
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hvu, one_mul]

end HexCharPolyMathlib
