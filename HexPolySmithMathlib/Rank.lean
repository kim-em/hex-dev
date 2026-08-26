/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmithMathlib.Quotient
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

/-! Rank of the executable Smith form over the rational-function field. -/

namespace HexPolySmithMathlib

universe u

open Hex Hex.PolyMatrix

noncomputable section

private def ratMatrix {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Matrix (Fin n) (Fin m) (RatFunc F) :=
  (polyMatrixEquiv A).map (algebraMap (Polynomial F) (RatFunc F))

@[simp]
private theorem ratMatrix_mul {F : Type u} [Field F] [DecidableEq F]
    {n m k : Nat} (A : Hex.Matrix (DensePoly F) n m)
    (B : Hex.Matrix (DensePoly F) m k) :
    ratMatrix (A * B) = ratMatrix A * ratMatrix B := by
  simp [ratMatrix, polyMatrixEquiv_mul, Matrix.map_mul]

private theorem ratMatrix_identity {F : Type u} [Field F] [DecidableEq F]
    (n : Nat) :
    ratMatrix (Hex.Matrix.identity n : Hex.Matrix (DensePoly F) n n) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [ratMatrix, Matrix.map_apply, polyMatrixEquiv_apply,
      Hex.Matrix.getElem_identity]
    simp [HexPolyMathlib.toPolynomial_one]
  · rw [ratMatrix, Matrix.map_apply, polyMatrixEquiv_apply,
      Hex.Matrix.getElem_identity]
    simp [hij, HexPolyMathlib.toPolynomial_zero]

private theorem rank_mul_left_of_inverse {K : Type*} [Field K]
    {n m : Nat} (L Li : Matrix (Fin n) (Fin n) K)
    (A : Matrix (Fin n) (Fin m) K) (h : Li * L = 1) :
    (L * A).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right L A)
  have hback : Li * (L * A) = A := by
    calc
      Li * (L * A) = (Li * L) * A := (Matrix.mul_assoc Li L A).symm
      _ = 1 * A := congrArg (fun Q => Q * A) h
      _ = A := Matrix.one_mul A
  calc
    A.rank = (Li * (L * A)).rank := congrArg Matrix.rank hback.symm
    _ ≤ (L * A).rank := Matrix.rank_mul_le_right _ _

private theorem rank_mul_right_of_inverse {K : Type*} [Field K]
    {n m : Nat} (A : Matrix (Fin n) (Fin m) K)
    (R Ri : Matrix (Fin m) (Fin m) K) (h : R * Ri = 1) :
    (A * R).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left A R)
  have hback : (A * R) * Ri = A := by
    calc
      (A * R) * Ri = A * (R * Ri) := Matrix.mul_assoc A R Ri
      _ = A * 1 := congrArg (fun Q => A * Q) h
      _ = A := Matrix.mul_one A
  calc
    A.rank = ((A * R) * Ri).rank := congrArg Matrix.rank hback.symm
    _ ≤ (A * R).rank := Matrix.rank_mul_le_left _ _

private theorem rank_ratMatrix_diag {F : Type u} [Field F] [DecidableEq F]
    {r n m : Nat} (d : Vector (DensePoly F) r)
    (hrn : r ≤ n) (hrm : r ≤ m)
    (hd : ∀ i : Fin r, DensePoly.Monic d[i]) :
    (ratMatrix (Hex.Matrix.diagMatrix d n m)).rank = r := by
  classical
  let D := ratMatrix (Hex.Matrix.diagMatrix d n m)
  let rows : Fin r → Fin n := Fin.castLE hrn
  let cols : Fin r → Fin m := Fin.castLE hrm
  let w : Fin r → RatFunc F := fun i =>
    algebraMap (Polynomial F) (RatFunc F) (HexPolyMathlib.toPolynomial d[i])
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    apply RatFunc.algebraMap_ne_zero
    apply Polynomial.Monic.ne_zero
    rw [Polynomial.Monic, HexPolyMathlib.leadingCoeff_toPolynomial]
    exact hd i
  have hsub : D.submatrix rows cols = Matrix.diagonal w := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.submatrix_apply, Matrix.diagonal_apply_eq]
      simp only [D, ratMatrix, Matrix.map_apply, polyMatrixEquiv_apply]
      rw [Hex.Matrix.getElem_diagMatrix_of_eq d (rows i) (cols i) (by rfl) i.isLt]
      rfl
    · rw [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hij]
      simp only [D, ratMatrix, Matrix.map_apply, polyMatrixEquiv_apply]
      rw [Hex.Matrix.getElem_diagMatrix_of_ne d (rows i) (cols j) (by
        intro hval
        apply hij
        apply Fin.ext
        exact hval)]
      simp [HexPolyMathlib.toPolynomial_zero]
  have hlower : r ≤ D.rank := by
    have h := Matrix.rank_submatrix_le D rows cols
    rw [hsub, Matrix.rank_diagonal] at h
    simpa [hw] using h
  have hupper : D.rank ≤ r := by
    let s : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
    have hsupp : Function.support D.row ⊆ s := by
      intro i hi
      simp only [Function.mem_support] at hi
      simp only [s]
      by_contra hir
      have hir' : ¬ i.val < r := by
        intro hlt
        apply hir
        simpa [s] using hlt
      apply hi
      funext j
      change D i j = 0
      simp only [D, ratMatrix, Matrix.map_apply, polyMatrixEquiv_apply]
      unfold Hex.Matrix.diagMatrix
      rw [Hex.Matrix.getElem_ofFn]
      simp [hir', HexPolyMathlib.toPolynomial_zero]
    have hrank := Matrix.rank_le_card_of_support_subset D s hsupp
    have hcard : s.card = r := by
      have hs : s = Finset.univ.map (Fin.castLEEmb hrn) := by
        ext i
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_map]
        constructor
        · intro hi
          exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
        · rintro ⟨j, _, rfl⟩
          exact j.isLt
      rw [hs, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    simpa [hcard] using hrank
  exact Nat.le_antisymm hupper hlower

/-- The executable rank is the rank after extending scalars from `F[x]`
to the field `F(x)`. -/
theorem rank_eq_ratFunc_rank {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    snfRank A =
      ((polyMatrixEquiv A).map
        (algebraMap (Polynomial F) (RatFunc F))).rank := by
  let S := snfData A
  have hS := snfData_isSNF A
  have hleft : ratMatrix S.leftInv * ratMatrix S.left = 1 := by
    have hcomm := Hex.Matrix.mul_eq_one_comm hS.left_inv
    rw [← ratMatrix_mul, hcomm, ratMatrix_identity]
  have hright : ratMatrix S.right * ratMatrix S.rightInv = 1 := by
    rw [← ratMatrix_mul, hS.right_inv, ratMatrix_identity]
  have hsnf : ratMatrix (Hex.Matrix.diagMatrix S.diag n m) =
      ratMatrix S.left * ratMatrix A * ratMatrix S.right := by
    rw [← ratMatrix_mul, ← ratMatrix_mul, hS.mul_eq]
  rw [snfRank_eq A]
  calc
    (snfData A).rank =
        (ratMatrix (Hex.Matrix.diagMatrix S.diag n m)).rank :=
      (rank_ratMatrix_diag S.diag (snfData_isSNF A).rank_le_n
        (snfData_isSNF A).rank_le_m (snfData_isSNF A).diag_monic).symm
    _ = (ratMatrix S.left * ratMatrix A * ratMatrix S.right).rank :=
      congrArg Matrix.rank hsnf
    _ = (ratMatrix S.left * ratMatrix A).rank :=
      rank_mul_right_of_inverse _ _ _ hright
    _ = (ratMatrix A).rank := rank_mul_left_of_inverse _ _ _ hleft

end

end HexPolySmithMathlib
