/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPoly
public import HexMatrixMathlib
public import HexPolyMathlib
public import Mathlib.Algebra.Polynomial.Eval.Degree

public section

/-! Transport of direct matrix-vector polynomial evaluation to Mathlib. -/

open Matrix Polynomial
open scoped BigOperators

namespace HexMinPolyMathlib

open HexMatrixMathlib HexPolyMathlib

universe u

variable {F : Type u} [Field F] [DecidableEq F] {n : Nat}

omit [DecidableEq F] in
private theorem vectorEquiv_krylovVec (A : Hex.Matrix F n n) (v : Vector F n)
    (j : Nat) :
    vectorEquiv (Hex.Matrix.krylovVec A v j) =
      ((matrixEquiv A) ^ j).mulVec (vectorEquiv v) := by
  induction j with
  | zero => simp [Hex.Matrix.krylovVec.eq_def]
  | succ j ih =>
      rw [Hex.Matrix.krylovVec.eq_def, vectorEquiv_mulVec, ih]
      rw [Matrix.mulVec_mulVec (vectorEquiv v) (matrixEquiv A)
        (matrixEquiv A ^ j), ← pow_succ']

omit [DecidableEq F] in
private theorem finset_sum_mulVec (s : Finset Nat)
    (f : Nat → Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    (∑ i ∈ s, f i).mulVec v = ∑ i ∈ s, (f i).mulVec v := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]

omit [DecidableEq F] in
private theorem vectorEquiv_vecMul_krylov {r : Nat} (c : Vector F r)
    (A : Hex.Matrix F n n) (v : Vector F n) :
    vectorEquiv (Hex.Matrix.vecMul c (Hex.Matrix.krylovMat A v r)) =
      ∑ j : Fin r, c[j] • vectorEquiv (Hex.Matrix.krylovVec A v j) := by
  funext k
  unfold Hex.Matrix.vecMul
  rw [vectorEquiv_mulVec, HexMatrixMathlib.matrixEquiv_transpose]
  unfold Matrix.mulVec dotProduct
  simp only [Finset.sum_apply, Matrix.transpose_apply, matrixEquiv_apply,
    vectorEquiv_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change (Hex.Matrix.getRow (Hex.Matrix.krylovMat A v r) j)[k] * c[j] =
    c[j] * (Hex.Matrix.krylovVec A v j)[k]
  rw [Hex.Matrix.getRow_krylovMat]
  exact mul_comm _ _

/-- Horner evaluation at a matrix applied to a vector is Mathlib's `aeval`
followed by `mulVec`. -/
theorem vectorEquiv_evalVec (p : Hex.DensePoly F) (A : Hex.Matrix F n n)
    (v : Vector F n) :
    vectorEquiv (Hex.Matrix.evalVec p A v) =
      (Polynomial.aeval (matrixEquiv A) (equiv p)).mulVec (vectorEquiv v) := by
  by_cases hp : p = 0
  · subst p
    simp [Hex.Matrix.evalVec_zero_poly]
    funext i
    rw [vectorEquiv_apply]
    simp
  · have hpPos : 0 < p.size := by
      by_cases h : 0 < p.size
      · exact h
      · exact False.elim (hp ((Hex.DensePoly.size_eq_zero_iff p).mp
          (Nat.eq_zero_of_not_pos h)))
    have hsize : (equiv p).natDegree + 1 = p.size := by
      rw [equiv_apply, natDegree_toPolynomial]
      have hdegree := Hex.DensePoly.degree?_eq_some_of_pos_size p hpPos
      rw [hdegree, Option.getD_some]
      omega
    rw [Hex.Matrix.evalVec_eq_vecMul_krylov p A v p.size (Nat.le_refl _)]
    rw [vectorEquiv_vecMul_krylov]
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, hsize]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul, one_mul]
    rw [finset_sum_mulVec]
    simp only [Matrix.smul_mulVec, equiv_apply, coeff_toPolynomial]
    simp_rw [vectorEquiv_krylovVec]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    change (p.coeffVec p.size).get j •
        ((matrixEquiv A) ^ j.val).mulVec (vectorEquiv v) =
      p.coeff j.val • ((matrixEquiv A) ^ j.val).mulVec (vectorEquiv v)
    rw [Hex.DensePoly.coeffVec_get]

end HexMinPolyMathlib
