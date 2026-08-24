/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPolyMathlib.Basic

public section

/-!
Coefficient, trace, determinant, and scalar-evaluation consequences of the
characteristic-polynomial correspondence.
-/

open Matrix Polynomial

namespace HexCharPolyMathlib

open HexMatrixMathlib HexPolyMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n : Nat}

/-- The executable trace agrees with Mathlib's matrix trace. -/
theorem matrixEquiv_trace (A : Hex.Matrix R n n) :
    Hex.Matrix.trace A = Matrix.trace (matrixEquiv A) := by
  cases n with
  | zero =>
      simp [Hex.Matrix.trace, Hex.Matrix.traceFold, Matrix.trace]
  | succ n =>
      have hcoeff : (Hex.Matrix.charPoly A).coeff n =
          (matrixEquiv A).charpoly.coeff n := by
        calc
          (Hex.Matrix.charPoly A).coeff n =
              (HexPolyMathlib.equiv (Hex.Matrix.charPoly A)).coeff n := by
                rw [HexPolyMathlib.equiv_apply, HexPolyMathlib.coeff_toPolynomial]
          _ = (matrixEquiv A).charpoly.coeff n := by rw [equiv_charPoly]
      have hhex := Hex.Matrix.coeff_charPoly_pred A (by omega)
      have hmath := Matrix.trace_eq_neg_charpoly_coeff (matrixEquiv A)
      simp only [Fintype.card_fin, Nat.succ_sub_one] at hmath hhex
      rw [hhex] at hcoeff
      calc
        Hex.Matrix.trace A = -(-Hex.Matrix.trace A) := by ring
        _ = -(matrixEquiv A).charpoly.coeff n := by rw [hcoeff]
        _ = Matrix.trace (matrixEquiv A) := hmath.symm

/-- The constant characteristic-polynomial coefficient is the signed
determinant. -/
theorem coeff_zero_charPoly (A : Hex.Matrix R n n) :
    (Hex.Matrix.charPoly A).coeff 0 = (-1) ^ n * Hex.Matrix.det A := by
  have hcoeff : (Hex.Matrix.charPoly A).coeff 0 =
      (matrixEquiv A).charpoly.coeff 0 := by
    calc
      (Hex.Matrix.charPoly A).coeff 0 =
          (HexPolyMathlib.equiv (Hex.Matrix.charPoly A)).coeff 0 := by
            rw [HexPolyMathlib.equiv_apply, HexPolyMathlib.coeff_toPolynomial]
      _ = (matrixEquiv A).charpoly.coeff 0 := by rw [equiv_charPoly]
  rw [hcoeff, HexMatrixMathlib.det_eq]
  have hdet := Matrix.det_eq_sign_charpoly_coeff (matrixEquiv A)
  simp only [Fintype.card_fin] at hdet
  calc
    (matrixEquiv A).charpoly.coeff 0 =
        (-1 : R) ^ n * ((-1 : R) ^ n * (matrixEquiv A).charpoly.coeff 0) := by
          rw [← mul_assoc, ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul]
    _ = (-1 : R) ^ n * Matrix.det (matrixEquiv A) := by rw [hdet]

omit [DecidableEq R] in
private theorem evalCoeffList_eq_sum (cs : List R) (x : R) :
    Hex.DensePoly.evalCoeffList cs x =
      ∑ i ∈ Finset.range cs.length, cs.getD i 0 * x ^ i := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [Hex.DensePoly.evalCoeffList, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ,
        pow_zero, mul_one]
      have hpow (i : Nat) : x ^ (i + 1) = x ^ i * x :=
        Lean.Grind.Semiring.pow_succ x i
      simp_rw [hpow]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, ← ih]

/-- Evaluating the executable characteristic polynomial is taking the
determinant of the scalar shift. -/
theorem eval_charPoly (A : Hex.Matrix R n n) (t : R) :
    (Hex.Matrix.charPoly A).eval t =
      Hex.Matrix.det (t • Hex.Matrix.identity n - A) := by
  calc
    (Hex.Matrix.charPoly A).eval t =
        (HexPolyMathlib.toPolynomial (Hex.Matrix.charPoly A)).eval t := by
          rw [Hex.DensePoly.eval, evalCoeffList_eq_sum,
            Polynomial.eval, HexPolyMathlib.eval₂_toPolynomial]
          simp only [Hex.DensePoly.length_toList, RingHom.id_apply]
          apply Finset.sum_congr rfl
          intro i hi
          rw [show (0 : R) = (Zero.zero : R) from rfl,
            Hex.DensePoly.toList_getD_eq_coeff]
    _ = (matrixEquiv A).charpoly.eval t := by rw [← HexPolyMathlib.equiv_apply, equiv_charPoly]
    _ = Matrix.det (Matrix.scalar (Fin n) t - matrixEquiv A) := Matrix.eval_charpoly _ _
    _ = Hex.Matrix.det (t • Hex.Matrix.identity n - A) := by
      rw [HexMatrixMathlib.det_eq]
      congr 1
      rw [HexMatrixMathlib.matrixEquiv_sub, HexMatrixMathlib.matrixEquiv_smul]
      congr 1
      ext i j
      rw [Matrix.scalar_apply, Matrix.smul_apply, smul_eq_mul,
        HexMatrixMathlib.matrixEquiv_apply]
      change Matrix.diagonal (fun _ : Fin n => t) i j =
        t * (Hex.Matrix.identity n)[i][j]
      rw [Matrix.diagonal_apply, Hex.Matrix.getElem_identity]
      split <;> simp_all

end HexCharPolyMathlib
