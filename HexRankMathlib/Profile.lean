/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Cert

public section

/-!
The column rank profile.

The producer's pivot columns are the column rank profile: column `j` is a
pivot column exactly when the rank of the first `j + 1` columns exceeds the
rank of the first `j`. Both ranks are read off the invariant after `j` and
`j + 1` columns, since the state after `t` columns is a rank certificate for
the first `t` columns of `A`.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n m : Nat}

/-- `J` is the column rank profile of `M`: column `j` lies in `J` exactly when
it raises the rank of the columns before it, that is, when it is not in their
span over the fraction field. -/
@[expose]
def IsColRankProfile (M : Matrix (Fin n) (Fin m) R) (J : List (Fin m)) : Prop :=
  ∀ j : Fin m, j ∈ J ↔
    (M.submatrix id (Fin.castLE (Nat.succ_le_of_lt j.isLt))).rank =
      (M.submatrix id (Fin.castLE j.isLt.le)).rank + 1

/-- `I` is the row rank profile of `M`: row `i` lies in `I` exactly when it
raises the rank of the rows before it, that is, when it is not in their span
over the fraction field. -/
@[expose]
def IsRowRankProfile (M : Matrix (Fin n) (Fin m) R) (I : List (Fin n)) : Prop :=
  ∀ i : Fin n, i ∈ I ↔
    (M.submatrix (Fin.castLE (Nat.succ_le_of_lt i.isLt)) id).rank =
      (M.submatrix (Fin.castLE i.isLt.le) id).rank + 1

namespace RowReduce

omit [DecidableEq R] in
/-- On a column where every non-pivot row is cleared, the state's coefficients
express the column with denominator `S.denom`. -/
theorem Inv.col_identity {A : Matrix (Fin n) (Fin m) R} {t : Nat}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A t S) {j : Fin m}
    (hcl : ∀ i, i ∉ S.profile.rows.toList → matrixEquiv S.matrix i j = 0) :
    ∀ i, S.denom * A i j = ∑ l, A i (S.profile.cols.get l) * coeff A S l j := by
  intro i
  by_cases hi : i ∈ S.profile.rows.toList
  · obtain ⟨k, rfl⟩ := (mem_toList_iff _ _).mp hi
    have h := congrFun (congrFun (block_mul_coeff A S) k) j
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp only [block, Matrix.submatrix_apply, id_eq] at h
    rw [h, hS.denom_eq]
    rfl
  · have h := congrFun (hS.other_row i hi) j
    rw [hcl i hi] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] at h
    exact sub_eq_zero.mp h.symm

omit [DecidableEq R] in
/-- The state after `t` columns is a rank certificate for the first `t`
columns, so their rank is the number of pivots so far. -/
theorem Inv.rank_take [IsDomain R] {A : Matrix (Fin n) (Fin m) R} {t : Nat}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A t S) (ht : t ≤ m) :
    (A.submatrix id (Fin.castLE ht)).rank = S.profile.rank := by
  let cols' : Fin S.profile.rank → Fin t := fun l => ⟨(S.profile.cols.get l).val, hS.cols_lt l⟩
  have hcols' : ∀ l, Fin.castLE ht (cols' l) = S.profile.cols.get l := fun l => Fin.ext rfl
  refine rank_eq_of_cert (A.submatrix id (Fin.castLE ht)) S.profile.rows.get cols' S.denom
    (block A S).adjugate hS.denom_ne ?_ ?_
  · have h : (A.submatrix id (Fin.castLE ht)).submatrix S.profile.rows.get cols' = block A S := by
      ext a b
      simp [block, hcols']
    rw [h, hS.denom_eq]
    exact Matrix.mul_adjugate _
  · ext i j
    have hcl : ∀ i, i ∉ S.profile.rows.toList → matrixEquiv S.matrix i (Fin.castLE ht j) = 0 :=
      fun i hi => hS.cleared i hi _ (by simp)
    have h := hS.col_identity hcl i
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    simp only [Matrix.submatrix_apply, id_eq, hcols']
    rw [h]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [coeff, block, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]

/-- The pivot columns after `t` columns are pivot columns after `t' ≥ t`. -/
theorem reduceCols_cols_mono (quot : R → R → R) (A : Hex.Matrix R n m) {t t' : Nat}
    (h : t ≤ t') (ht' : t' ≤ m) :
    (reduceCols quot A t).profile.cols.toList ⊆ (reduceCols quot A t').profile.cols.toList := by
  induction t' with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact List.Subset.refl _
  | succ t' ih =>
    rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
    · rw [reduceCols_succ quot A (by omega)]
      exact List.Subset.trans (ih (by omega) (by omega)) (cols_subset_reduceStep _ _)
    · have : t = t' + 1 := by omega
      subst this
      exact List.Subset.refl _

/-- A pivot column below `t` was already a pivot column after `t` columns. -/
theorem mem_reduceCols_cols_of_lt {quot : R → R → R}
    (A : Hex.Matrix R n m) {t t' : Nat} (h : t ≤ t') (ht' : t' ≤ m) {x : Fin m}
    (hx : x.val < t) (hmem : x ∈ (reduceCols quot A t').profile.cols.toList) :
    x ∈ (reduceCols quot A t).profile.cols.toList := by
  induction t' with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact hmem
  | succ t' ih =>
    rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
    · apply ih (by omega) (by omega)
      rw [reduceCols_succ quot A (by omega)] at hmem
      cases hp : Hex.Matrix.findPivotRow? (reduceCols quot A t').matrix
          (reduceCols quot A t').profile.rows.toList ⟨t', by omega⟩ with
      | none =>
        rw [Hex.Matrix.reduceStep_skip hp] at hmem
        exact hmem
      | some p =>
        rw [Hex.Matrix.reduceStep_pivot_profile hp] at hmem
        simp only [Vector.toList_push, List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact hmem
        · have := congrArg Fin.val hmem
          simp at this
          omega
    · have : t = t' + 1 := by omega
      subst this
      exact hmem

/-- Column `j` is recorded exactly when scanning it finds a pivot. -/
theorem mem_cols_iff_pivot {quot : R → R → R}
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (h1 : (1 : R) ≠ 0)
    (A : Hex.Matrix R n m) (j : Fin m) :
    j ∈ (Hex.Matrix.rowReduceWith quot A).profile.cols.toList ↔
      (Hex.Matrix.findPivotRow? (reduceCols quot A j.val).matrix
        (reduceCols quot A j.val).profile.rows.toList j).isSome := by
  have hS := inv_reduceCols hquot h1 A (t := j.val) j.isLt.le
  have hstep := reduceCols_succ quot A j.isLt
  have hj : (⟨j.val, j.isLt⟩ : Fin m) = j := rfl
  rw [hj] at hstep
  have hnot : j ∉ (reduceCols quot A j.val).profile.cols.toList := by
    intro hmem
    obtain ⟨l, hl⟩ := (mem_toList_iff _ _).mp hmem
    have := hS.cols_lt l
    rw [hl] at this
    exact lt_irrefl _ this
  constructor
  · intro hmem
    rw [rowReduceWith_eq_reduceCols] at hmem
    have hmem' := mem_reduceCols_cols_of_lt A (t := j.val + 1) j.isLt (le_refl _)
      (Nat.lt_succ_self _) hmem
    rw [hstep] at hmem'
    cases hp : Hex.Matrix.findPivotRow? (reduceCols quot A j.val).matrix
        (reduceCols quot A j.val).profile.rows.toList j with
    | none =>
      rw [Hex.Matrix.reduceStep_skip hp] at hmem'
      exact absurd hmem' hnot
    | some p => rfl
  · intro hsome
    cases hp : Hex.Matrix.findPivotRow? (reduceCols quot A j.val).matrix
        (reduceCols quot A j.val).profile.rows.toList j with
    | none => rw [hp] at hsome; exact absurd hsome (by simp)
    | some p =>
      rw [rowReduceWith_eq_reduceCols]
      refine reduceCols_cols_mono quot A (t := j.val + 1) j.isLt (le_refl _) ?_
      rw [hstep]
      exact mem_cols_reduceStep hp

/-- The rank of the state after one more column. -/
theorem rank_reduceCols_succ {quot : R → R → R} (A : Hex.Matrix R n m) (j : Fin m) :
    (reduceCols quot A (j.val + 1)).profile.rank =
      (reduceCols quot A j.val).profile.rank +
        (if (Hex.Matrix.findPivotRow? (reduceCols quot A j.val).matrix
          (reduceCols quot A j.val).profile.rows.toList j).isSome then 1 else 0) := by
  have hstep := reduceCols_succ quot A j.isLt
  have hj : (⟨j.val, j.isLt⟩ : Fin m) = j := rfl
  rw [hj] at hstep
  rw [hstep]
  cases hp : Hex.Matrix.findPivotRow? (reduceCols quot A j.val).matrix
      (reduceCols quot A j.val).profile.rows.toList j with
  | none => rw [Hex.Matrix.reduceStep_skip hp]; simp
  | some p => rw [Hex.Matrix.reduceStep_pivot_profile hp]; simp

end RowReduce

open RowReduce

variable {quot : R → R → R}

/-- The producer's pivot columns are the column rank profile. -/
theorem rowReduceWith_cols_eq_colProfile (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (A : Hex.Matrix R n m) :
    IsColRankProfile (matrixEquiv A) (Hex.Matrix.rowReduceWith quot A).profile.cols.toList := by
  have := isDomain_of_quot quot hquot h1
  intro j
  rw [mem_cols_iff_pivot hquot h1 A j,
    (inv_reduceCols hquot h1 A (t := j.val + 1) j.isLt).rank_take,
    (inv_reduceCols hquot h1 A (t := j.val) j.isLt.le).rank_take, rank_reduceCols_succ]
  cases (Hex.Matrix.findPivotRow? (reduceCols quot A j.val).matrix
      (reduceCols quot A j.val).profile.rows.toList j).isSome <;> simp

end HexMatrixMathlib
