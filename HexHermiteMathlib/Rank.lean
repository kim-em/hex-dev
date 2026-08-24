/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermiteMathlib.Kernel
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

/-! The executable HNF rank agrees with Mathlib's integer matrix rank. -/

namespace HexHermiteMathlib

open HexMatrixMathlib

private theorem echelon_rank (A : Hex.Matrix Int n m) :
    (matrixEquiv (Hex.Matrix.hnfData A).echelon).rank =
      (Hex.Matrix.hnfData A).rank := by
  let D := Hex.Matrix.hnfData A
  let H := matrixEquiv D.echelon
  have hform := Hex.Matrix.hnfData_isHNF A
  let s : Finset (Fin n) := Finset.univ.filter fun i => i.val < D.rank
  have hs : Function.support H.row ⊆ s := by
    intro i hi
    change i ∈ s
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hir
    apply hi
    rw [matrixEquiv_row]
    have hzero : D.echelon[i] = 0 := by
      simpa only [D] using
        hform.toIsEchelonForm.zero_row i (Nat.le_of_not_gt hir)
    calc
      vectorEquiv (D.echelon.row i) = vectorEquiv D.echelon[i] := rfl
      _ = vectorEquiv 0 := congrArg vectorEquiv hzero
      _ = 0 := vectorEquiv_zero
  have hupper : H.rank ≤ D.rank := by
    have hle := _root_.Matrix.rank_le_card_of_support_subset H s hs
    dsimp only [s] at hle
    rw [Fin.card_filter_val_lt,
      min_eq_right hform.toIsEchelonForm.rank_le_n] at hle
    exact hle
  let B : _root_.Matrix (Fin D.rank) (Fin D.rank) Int :=
    H.submatrix hform.toIsEchelonForm.pivotRow D.pivotCols.get
  have htri : B.IsUpperTriangular := by
    intro i j hji
    let row : Fin n := hform.toIsEchelonForm.pivotRow i
    change D.echelon[(row, D.pivotCols.get j)] = 0
    have hp := hform.pivot_leading i (D.pivotCols.get j)
      (hform.toIsEchelonForm.pivotCols_sorted j i hji)
    change (D.echelon[i.val]'(Nat.lt_of_lt_of_le i.isLt
      hform.toIsEchelonForm.rank_le_n))[D.pivotCols.get j] = 0 at hp
    have hrow : row = ⟨i.val, Nat.lt_of_lt_of_le i.isLt
        hform.toIsEchelonForm.rank_le_n⟩ := Fin.ext rfl
    rw [hrow, Hex.Matrix.getElem_pair_eq_nested,
      Hex.Matrix.getElem_eq_getRow]
    exact hp
  have hdiag : ∀ i, B i i ≠ 0 := by
    intro i
    let row : Fin n := hform.toIsEchelonForm.pivotRow i
    change D.echelon[(row, D.pivotCols.get i)] ≠ 0
    have hp := hform.pivot_pos i
    change 0 < (D.echelon[i.val]'(Nat.lt_of_lt_of_le i.isLt
      hform.toIsEchelonForm.rank_le_n))[D.pivotCols.get i] at hp
    have hrow : row = ⟨i.val, Nat.lt_of_lt_of_le i.isLt
        hform.toIsEchelonForm.rank_le_n⟩ := Fin.ext rfl
    rw [hrow, Hex.Matrix.getElem_pair_eq_nested,
      Hex.Matrix.getElem_eq_getRow]
    exact ne_of_gt hp
  have hdet : B.det ≠ 0 := by
    rw [_root_.Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_ne_zero_iff.mpr fun i _hi => hdiag i
  have hrankB : B.rank = D.rank := by
    simpa using _root_.Matrix.rank_of_det_ne_zero hdet
  have hlower : D.rank ≤ H.rank := by
    have hle := _root_.Matrix.rank_submatrix_le H
      hform.toIsEchelonForm.pivotRow D.pivotCols.get
    change B.rank ≤ H.rank at hle
    rwa [hrankB] at hle
  exact le_antisymm hupper hlower

/-- The executable HNF rank is Mathlib's module rank over `ℤ`. -/
theorem hnfRank_eq_rank (A : Hex.Matrix Int n m) :
    Hex.Matrix.hnfRank A = (matrixEquiv A).rank := by
  let D := Hex.Matrix.hnfData A
  have hmul : matrixEquiv D.echelon =
      matrixEquiv D.transform * matrixEquiv A := by
    rw [← matrixEquiv_mul, Hex.Matrix.hnfData_transform_mul]
  have hunit : IsUnit (matrixEquiv D.transform) := by
    exact isUnit_transform A
  have hdet : IsUnit (matrixEquiv D.transform).det :=
    (_root_.Matrix.isUnit_iff_isUnit_det _).mp hunit
  calc
    Hex.Matrix.hnfRank A = D.rank := Hex.Matrix.hnfRank_eq A
    _ = (matrixEquiv D.echelon).rank := (echelon_rank A).symm
    _ = (matrixEquiv D.transform * matrixEquiv A).rank := congrArg _ hmul
    _ = (matrixEquiv A).rank :=
      _root_.Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet

end HexHermiteMathlib
