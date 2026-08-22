/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPolyMathlib.Basic

public section

/-!
Matrix evaluation correspondence and the executable Cayley--Hamilton theorem.
-/

open Matrix Polynomial
open scoped BigOperators

namespace HexCharPolyMathlib

open HexMatrixMathlib HexPolyMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n : Nat}

-- Keep the kernel-facing Horner specification on the computational matrix
-- instances used when `Hex.Matrix.evalMatrix` was defined.
local instance : Add (Hex.Matrix R n n) := Hex.Matrix.instAdd

omit [DecidableEq R] in
private theorem matrixEquiv_evalCoeffList (cs : List R) (A : Hex.Matrix R n n) :
    matrixEquiv (Hex.DensePoly.evalCoeffList
      (cs.map fun c => c • Hex.Matrix.identity n) A) =
      Hex.DensePoly.evalCoeffList
        (cs.map fun c => algebraMap R (Matrix (Fin n) (Fin n) R) c)
        (matrixEquiv A) := by
  have hadd (X Y : Hex.Matrix R n n) :
      matrixEquiv (Hex.Matrix.add X Y) = matrixEquiv X + matrixEquiv Y := by
    ext i j
    simp only [HexMatrixMathlib.matrixEquiv_apply, Matrix.add_apply]
    exact Hex.Matrix.getElem_add X Y i j
  have hmul (X Y : Hex.Matrix R n n) :
      matrixEquiv (Hex.Matrix.mul X Y) = matrixEquiv X * matrixEquiv Y := by
    ext i j
    rw [HexMatrixMathlib.matrixEquiv_apply, Matrix.mul_apply]
    show (Hex.Matrix.mul X Y)[i][j] =
      ∑ q, matrixEquiv X i q * matrixEquiv Y q j
    rw [Hex.Matrix.mul, Hex.Matrix.getElem_ofFn, HexMatrixMathlib.dotProduct_eq]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro q hq
    simp only [HexMatrixMathlib.vectorEquiv_apply]
    rw [Hex.Matrix.getElem_row, Hex.Matrix.getElem_col,
      HexMatrixMathlib.matrixEquiv_apply, HexMatrixMathlib.matrixEquiv_apply]
  induction cs with
  | nil =>
      change matrixEquiv (0 : Hex.Matrix R n n) =
        (0 : Matrix (Fin n) (Fin n) R)
      exact HexMatrixMathlib.matrixEquiv_zero
  | cons c cs ih =>
      simp only [List.map_cons, Hex.DensePoly.evalCoeffList]
      change matrixEquiv (Hex.Matrix.add
        (Hex.Matrix.mul
          (Hex.DensePoly.evalCoeffList
            (cs.map fun c => c • Hex.Matrix.identity n) A) A)
        (c • Hex.Matrix.identity n)) = _
      rw [hadd, hmul, ih,
        HexMatrixMathlib.matrixEquiv_smul]
      have hid : matrixEquiv (Hex.Matrix.identity (R := R) n) = 1 := by
        exact HexMatrixMathlib.matrixEquiv_one
      rw [hid]
      simp only [Algebra.algebraMap_eq_smul_one]

omit [DecidableEq R] in
private theorem evalCoeffList_eq_sum (cs : List (Matrix (Fin n) (Fin n) R))
    (A : Matrix (Fin n) (Fin n) R) :
    Hex.DensePoly.evalCoeffList cs A =
      ∑ i ∈ Finset.range cs.length, cs.getD i 0 * A ^ i := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [Hex.DensePoly.evalCoeffList, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
      have hpow (i : Nat) : A ^ (i + 1) = A ^ i * A :=
        Lean.Grind.Semiring.pow_succ A i
      simp_rw [hpow, ← mul_assoc]
      rw [← Finset.sum_mul, ← ih]

/-- Horner evaluation of an executable dense polynomial agrees with Mathlib's
polynomial evaluation at the corresponding matrix. -/
theorem equiv_evalMatrix (p : Hex.DensePoly R) (A : Hex.Matrix R n n) :
    matrixEquiv (Hex.Matrix.evalMatrix p A) =
      Polynomial.aeval (matrixEquiv A) (HexPolyMathlib.equiv p) := by
  rw [Hex.Matrix.evalMatrix]
  calc
    matrixEquiv (Hex.DensePoly.evalCoeffList
        (p.toList.map fun c => c • Hex.Matrix.identity n) A) =
        Hex.DensePoly.evalCoeffList
          (p.toList.map fun c => algebraMap R (Matrix (Fin n) (Fin n) R) c)
          (matrixEquiv A) := matrixEquiv_evalCoeffList p.toList A
    _ = Polynomial.aeval (matrixEquiv A) (HexPolyMathlib.equiv p) := by
      rw [evalCoeffList_eq_sum, Polynomial.aeval_def, HexPolyMathlib.equiv_apply,
        HexPolyMathlib.eval₂_toPolynomial]
      simp only [List.length_map, Hex.DensePoly.length_toList]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (0 : Matrix (Fin n) (Fin n) R) =
          algebraMap R (Matrix (Fin n) (Fin n) R) (0 : R) by simp,
        List.getD_map, show (0 : R) = (Zero.zero : R) from rfl,
        Hex.DensePoly.toList_getD_eq_coeff]

/-- Cayley--Hamilton for the executable characteristic polynomial and matrix
objects. -/
theorem evalMatrix_charPoly (A : Hex.Matrix R n n) :
    Hex.Matrix.evalMatrix (Hex.Matrix.charPoly A) A = 0 := by
  apply matrixEquiv.injective
  rw [equiv_evalMatrix, equiv_charPoly, Matrix.aeval_self_charpoly,
    HexMatrixMathlib.matrixEquiv_zero]

end HexCharPolyMathlib
