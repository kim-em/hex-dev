/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Invariant

public section

/-!
Consequences of the loop invariant for the finished pass: the reduced-form
contract `rowReduceWith_spec`, the all-column identity that makes the first
pass a rank certificate with `adjugate B`, and `rankWith_eq`.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n m : Nat}

namespace RowReduce

omit [DecidableEq R] in
/-- The all-column identity `p • A = A[·, cols] * (adjugate B * P)` of a state
whose non-pivot rows are cleared on every column. -/
theorem Inv.identity {A : Matrix (Fin n) (Fin m) R} {S : Hex.Matrix.ReducedForm R n m}
    (hS : Inv A m S) :
    S.denom • A = A.submatrix id S.profile.cols.get * coeff A S := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.submatrix_apply, id_eq]
  by_cases hi : i ∈ S.profile.rows.toList
  · obtain ⟨k, rfl⟩ := (mem_toList_iff _ _).mp hi
    have h := congrFun (congrFun (block_mul_coeff A S) k) j
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp only [block, Matrix.submatrix_apply, id_eq] at h
    rw [h, hS.denom_eq]
    rfl
  · have h0 := hS.cleared i hi j j.isLt
    have h := congrFun (hS.other_row i hi) j
    rw [h0] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] at h
    exact sub_eq_zero.mp h.symm

omit [DecidableEq R] in
/-- The pivot rows of a state are distinct. -/
theorem Inv.rows_injective [IsDomain R] {A : Matrix (Fin n) (Fin m) R} {t : Nat}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A t S) :
    Function.Injective S.profile.rows.get := by
  intro a b hab
  by_contra hne
  apply hS.denom_ne
  rw [hS.denom_eq]
  exact Matrix.det_zero_of_row_eq hne (by funext l; simp [block, hab])

omit [DecidableEq R] in
/-- The rank of a state's source matrix, from the invariant after every column. -/
theorem Inv.rank_eq [IsDomain R] {A : Matrix (Fin n) (Fin m) R}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A m S) : A.rank = S.profile.rank :=
  rank_eq_of_cert A S.profile.rows.get S.profile.cols.get S.denom (block A S).adjugate
    hS.denom_ne (by rw [hS.denom_eq]; exact Matrix.mul_adjugate _) hS.identity

/-- If column `j` is skipped when scanned, it is a combination of the earlier
pivot columns with the current denominator. -/
theorem col_skipped_dependent {A : Matrix (Fin n) (Fin m) R} {t : Nat}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A t S) {j : Fin m}
    (hp : Hex.Matrix.findPivotRow? S.matrix S.profile.rows.toList j = none) :
    ∀ i, S.denom * A i j = ∑ l, A i (S.profile.cols.get l) * coeff A S l j := by
  intro i
  by_cases hi : i ∈ S.profile.rows.toList
  · obtain ⟨k, rfl⟩ := (mem_toList_iff _ _).mp hi
    have h := congrFun (congrFun (block_mul_coeff A S) k) j
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp only [block, Matrix.submatrix_apply, id_eq] at h
    rw [h, hS.denom_eq]
    rfl
  · have h0 : matrixEquiv S.matrix i j = 0 := by
      rw [matrixEquiv_apply]
      exact Hex.Matrix.findPivotRow?_none hp i hi
    have h := congrFun (hS.other_row i hi) j
    rw [h0] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] at h
    exact sub_eq_zero.mp h.symm

end RowReduce

open RowReduce

variable {quot : R → R → R}

/-- The reduced-form contract: the denominator is the determinant of the pivot
block, each pivot row is the corresponding row of `adjugate B * P`, and every
non-pivot row is zero. -/
theorem rowReduceWith_spec (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (h1 : (1 : R) ≠ 0)
    (A : Hex.Matrix R n m) :
    let D := Hex.Matrix.rowReduceWith quot A
    let B := (matrixEquiv A).submatrix D.profile.rows.get D.profile.cols.get
    D.denom = B.det ∧
    (∀ k : Fin D.profile.rank,
      matrixEquiv D.matrix (D.profile.rows.get k) =
        (B.adjugate * (matrixEquiv A).submatrix D.profile.rows.get id) k) ∧
    (∀ i, i ∉ D.profile.rows.toList → matrixEquiv D.matrix i = 0) := by
  have hS := inv_rowReduceWith hquot h1 A
  refine ⟨hS.denom_eq, hS.pivot_row, ?_⟩
  intro i hi
  funext j
  exact hS.cleared i hi j j.isLt

/-- The first pass is itself a rank certificate with `adjugate B` and `det B`. -/
theorem rowReduceWith_identity (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (A : Hex.Matrix R n m) :
    let D := Hex.Matrix.rowReduceWith quot A
    let B := (matrixEquiv A).submatrix D.profile.rows.get D.profile.cols.get
    D.denom • matrixEquiv A =
      (matrixEquiv A).submatrix id D.profile.cols.get *
        (B.adjugate * (matrixEquiv A).submatrix D.profile.rows.get id) :=
  (inv_rowReduceWith hquot h1 A).identity

/-- The pivot rows of the pass are distinct. -/
theorem rowReduceWith_rows_injective (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (A : Hex.Matrix R n m) :
    Function.Injective (Hex.Matrix.rowReduceWith quot A).profile.rows.get :=
  have := isDomain_of_quot quot hquot h1
  (inv_rowReduceWith hquot h1 A).rows_injective

/-- The pivot columns of the pass are strictly increasing. -/
theorem rowReduceWith_cols_strictMono (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (A : Hex.Matrix R n m) :
    StrictMono (Hex.Matrix.rowReduceWith quot A).profile.cols.get :=
  (inv_rowReduceWith hquot h1 A).cols_mono

/-- The unchecked rank is `Matrix.rank`. -/
theorem rankWith_eq (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (h1 : (1 : R) ≠ 0)
    (A : Hex.Matrix R n m) :
    Hex.Matrix.rankWith quot A = (matrixEquiv A).rank :=
  have := isDomain_of_quot quot hquot h1
  (inv_rowReduceWith hquot h1 A).rank_eq.symm

/-- The integer rank is `Matrix.rank`. -/
theorem rank_eq (A : Hex.Matrix Int n m) : Hex.Matrix.rank A = (matrixEquiv A).rank :=
  rankWith_eq (quot := HexArith.Int.exactDiv) (fun a b hb => Int.mul_ediv_cancel a hb)
    (by decide) A

end HexMatrixMathlib
