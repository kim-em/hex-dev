/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdeal.Minors
public import HexRowReduce

public section

/-!
The rank-versus-minors theorem: a matrix over a field has rank below `r`
exactly when every `r × r` minor vanishes, for the rank computed by
`rowReduce`.

The vanishing direction is Cauchy-Binet through the factorization
`A = C * B` supplied by `rowReduce_rank_factorization`: the middle enumeration
`selectedColumnTuples r ρ` is empty once `ρ < r`. The nonzero-minor direction
first exhibits a nonzero `ρ × ρ` minor on the pivot columns (the first `ρ`
rows of the reduction transform are a left inverse of the pivot columns, and
rectangular Cauchy-Binet writes `1` as a sum of products of minors), then
descends one size at a time through the Laplace expansion along the first
column.
-/

namespace Hex
universe u v
namespace Matrix

/-- A fold of additions from `0` with a nonzero total has a nonzero summand. -/
theorem exists_ne_zero_of_foldl_add_ne_zero {α : Type v} {R : Type u} [Lean.Grind.Semiring R]
    (xs : List α) (f : α → R) (h : xs.foldl (fun acc x => acc + f x) 0 ≠ 0) :
    ∃ x ∈ xs, f x ≠ 0 := by
  induction xs with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    by_cases hx : f x = 0
    · rw [List.foldl_cons, hx, Lean.Grind.Semiring.add_zero] at h
      rcases ih h with ⟨y, hy, hfy⟩
      exact ⟨y, List.mem_cons_of_mem x hy, hfy⟩
    · exact ⟨x, List.mem_cons_self, hx⟩

variable {R : Type u} {n m : Nat}

/-- Column selection commutes with left multiplication. -/
theorem selectCols_mul [Mul R] [Add R] [OfNat R 0] {q k : Nat}
    (P : Matrix R q n) (X : Matrix R n m) (cols : Vector (Fin m) k) :
    selectCols (P * X) cols = P * selectCols X cols := by
  apply ext_getElem
  intro i j
  rw [getElem_selectCols, getElem_mul, getElem_mul]
  congr 1
  ext t ht
  let tt : Fin n := ⟨t, ht⟩
  show (col X cols[j])[tt] = (col (selectCols X cols) j)[tt]
  rw [getElem_col, getElem_col, getElem_selectCols]

variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]

/-- Vanishing direction: below the rank, every minor is zero. -/
theorem minors_eq_zero_of_rank_lt (A : Matrix K n m) {r : Nat} (h : rowReduce_rank A < r) :
    ∀ M ∈ minors r A, M = 0 := by
  intro M hM
  rcases (mem_minors_iff A r M).mp hM with ⟨rows, _, cols, _, rfl⟩
  rcases rowReduce_rank_factorization A with ⟨C, B, hA⟩
  have hexp := det_minor_mul C B rows cols
  rw [← hA, selectedColumnTuples_eq_nil_of_lt h] at hexp
  exact hexp

/-- `Vector.get` is entry access. -/
private theorem vector_get_eq {α : Type v} {k : Nat} (v : Vector α k) (i : Fin k) :
    v.get i = v[i] := rfl

/-- The pivot columns of the reduced echelon form, restricted to the pivot
rows, form the identity. -/
private theorem takeRows_selectCols_echelon_pivotCols (A : Matrix K n m) :
    takeRows (selectCols (rowReduce A).echelon (rowReduce A).pivotCols) (rowReduce A).rank
        (rowReduce_isRowReduced A).toIsEchelonForm.rank_le_n =
      Matrix.identity (R := K) (rowReduce A).rank := by
  let E := rowReduce_isRowReduced A
  apply ext_getElem
  intro i j
  rw [getElem_takeRows, getElem_selectCols, getElem_identity]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    simpa [Matrix.IsEchelonForm.pivotRow, vector_get_eq] using E.pivot_one i
  · rw [ite_eq_right hij]
    cases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with
    | inl hlt =>
        simpa [Matrix.IsEchelonForm.pivotRow, vector_get_eq] using
          E.above_pivot_zero j (⟨i.val, Nat.lt_of_lt_of_le i.isLt E.toIsEchelonForm.rank_le_n⟩ : Fin n)
            hlt
    | inr hgt =>
        simpa [Matrix.IsEchelonForm.pivotRow, vector_get_eq] using
          E.toIsEchelonForm.below_pivot_zero j
            (⟨i.val, Nat.lt_of_lt_of_le i.isLt E.toIsEchelonForm.rank_le_n⟩ : Fin n) hgt

/-- The pivot columns are a strictly increasing tuple. -/
private theorem pivotCols_mem_selectedColumnTuples (A : Matrix K n m) :
    (rowReduce A).pivotCols ∈ selectedColumnTuples (rowReduce A).rank m := by
  apply (mem_selectedColumnTuples_iff _).mpr
  intro i j hij
  have h := (rowReduce_isRowReduced A).toIsEchelonForm.pivotCols_sorted i j (Fin.lt_def.mpr hij)
  simpa [vector_get_eq, Fin.lt_def] using h

/-- Nonzero-minor direction, at the rank itself: some `ρ × ρ` minor is
nonzero, where `ρ` is the rank. -/
theorem exists_minor_ne_zero_rank (A : Matrix K n m) :
    ∃ M ∈ minors (rowReduce_rank A) A, M ≠ 0 := by
  let E := rowReduce_isRowReduced A
  have hρn : (rowReduce A).rank ≤ n := E.toIsEchelonForm.rank_le_n
  let J : Vector (Fin m) (rowReduce A).rank := (rowReduce A).pivotCols
  let C : Matrix K n (rowReduce A).rank := selectCols A J
  let T₀ : Matrix K (rowReduce A).rank n := takeRows (rowReduce A).transform (rowReduce A).rank hρn
  have hTC : T₀ * C = Matrix.identity (R := K) (rowReduce A).rank := by
    rw [← takeRows_mul, ← selectCols_mul, E.toIsEchelonForm.transform_mul]
    exact takeRows_selectCols_echelon_pivotCols A
  have hdet : det (T₀ * C) = 1 := by rw [hTC, det_identity]
  have hsum := det_mul_rectangular T₀ C
  rw [hdet] at hsum
  have hne : (selectedColumnTuples (rowReduce A).rank n).foldl (fun acc I => acc +
      det (columnTupleMatrix C.transpose (columnTupleVectorFn I)) *
        det (columnTupleMatrix T₀ (columnTupleVectorFn I))) 0 ≠ 0 := by
    rw [← hsum]
    exact fun h => Lean.Grind.Field.zero_ne_one h.symm
  rcases exists_ne_zero_of_foldl_add_ne_zero _ _ hne with ⟨I, hI, hprod⟩
  have hminor : det (columnTupleMatrix C.transpose (columnTupleVectorFn I)) ≠ 0 := by
    intro h0
    apply hprod
    rw [h0, Lean.Grind.Semiring.zero_mul]
  have hCT : columnTupleMatrix C.transpose (columnTupleVectorFn I) =
      (selectedSubmatrix A I J).transpose := by
    apply ext_getElem
    intro a b
    rw [getElem_columnTupleMatrix, getElem_transpose, getElem_transpose,
      getElem_selectedSubmatrix, columnTupleVectorFn_apply]
    show (selectCols A J)[I[b]][a] = A[I[b]][J[a]]
    rw [getElem_selectCols]
  rw [hCT, det_transpose] at hminor
  exact ⟨det (selectedSubmatrix A I J),
    (mem_minors_iff A _ _).mpr ⟨I, hI, J, pivotCols_mem_selectedColumnTuples A, rfl⟩, hminor⟩

/-- Descent by one: a nonzero `(k + 1) × (k + 1)` minor has a nonzero `k × k`
minor inside it, by Laplace expansion along the first column. -/
theorem exists_minor_ne_zero_of_succ [Lean.Grind.CommRing R] (A : Matrix R n m) {k : Nat}
    (h : ∃ M ∈ minors (k + 1) A, M ≠ 0) : ∃ M ∈ minors k A, M ≠ 0 := by
  rcases h with ⟨M, hM, hne⟩
  rcases (mem_minors_iff A (k + 1) M).mp hM with ⟨rows, hrows, cols, hcols, rfl⟩
  rw [det_eq_foldl_laplace_col (selectedSubmatrix A rows cols) ⟨0, Nat.succ_pos k⟩] at hne
  rcases exists_ne_zero_of_foldl_add_ne_zero _ _ hne with ⟨i, _, hterm⟩
  have hcof : det (deleteRowCol (selectedSubmatrix A rows cols) i ⟨0, Nat.succ_pos k⟩) ≠ 0 := by
    intro h0
    apply hterm
    unfold cofactor
    rw [h0, Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.mul_zero]
  rw [deleteRowCol_selectedSubmatrix] at hcof
  refine ⟨_, (mem_minors_iff A k _).mpr ⟨rows.eraseIdx i, ?_, cols.eraseIdx 0, ?_, rfl⟩, hcof⟩
  · exact (mem_selectedColumnTuples_iff _).mpr
      (isStrictlyIncreasingColumnTuple_eraseIdx ((mem_selectedColumnTuples_iff _).mp hrows) i)
  · exact (mem_selectedColumnTuples_iff _).mpr
      (isStrictlyIncreasingColumnTuple_eraseIdx ((mem_selectedColumnTuples_iff _).mp hcols)
        ⟨0, Nat.succ_pos k⟩)

/-- Nonzero-minor direction: at or below the rank, some minor is nonzero. -/
theorem exists_minor_ne_zero_of_le (A : Matrix K n m) {r : Nat} (h : r ≤ rowReduce_rank A) :
    ∃ M ∈ minors r A, M ≠ 0 := by
  obtain ⟨d, hd⟩ : ∃ d, r + d = rowReduce_rank A := ⟨rowReduce_rank A - r, by omega⟩
  induction d generalizing r with
  | zero =>
      rw [Nat.add_zero] at hd
      rw [hd]
      exact exists_minor_ne_zero_rank A
  | succ d ih =>
      exact exists_minor_ne_zero_of_succ A (ih (by omega) (by omega))

/-! # The rank-versus-minors theorem -/

/-- The rank is below `r` exactly when every `r × r` minor vanishes. -/
theorem rank_lt_iff_minors_eq_zero (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A < r ↔ ∀ M ∈ minors r A, M = 0 := by
  constructor
  · exact minors_eq_zero_of_rank_lt A
  · intro h
    apply Nat.lt_of_not_le
    intro hle
    rcases exists_minor_ne_zero_of_le A hle with ⟨M, hM, hne⟩
    exact hne (h M hM)

/-- `r` is at most the rank exactly when some `r × r` minor is nonzero. -/
theorem le_rank_iff_exists_minor_ne_zero (A : Matrix K n m) (r : Nat) :
    r ≤ rowReduce_rank A ↔ ∃ M ∈ minors r A, M ≠ 0 := by
  constructor
  · exact exists_minor_ne_zero_of_le A
  · rintro ⟨M, hM, hne⟩
    apply Nat.le_of_not_lt
    intro hlt
    exact hne (minors_eq_zero_of_rank_lt A hlt M hM)

/-- The rank is at most `r` exactly when every `(r + 1) × (r + 1)` minor
vanishes. -/
theorem rank_le_iff_minors_succ_eq_zero (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A ≤ r ↔ ∀ M ∈ minors (r + 1) A, M = 0 := by
  rw [← rank_lt_iff_minors_eq_zero]
  exact Nat.lt_succ_iff.symm

/-- The rank is `r` exactly when some `r × r` minor is nonzero and every
`(r + 1) × (r + 1)` minor vanishes. -/
theorem rank_eq_iff_minors (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A = r ↔
      (∃ M ∈ minors r A, M ≠ 0) ∧ ∀ M ∈ minors (r + 1) A, M = 0 := by
  rw [← le_rank_iff_exists_minor_ne_zero, ← rank_le_iff_minors_succ_eq_zero]
  constructor
  · intro h
    exact ⟨h ▸ Nat.le_refl _, h ▸ Nat.le_refl _⟩
  · intro ⟨h1, h2⟩
    exact Nat.le_antisymm h2 h1

end Matrix
end Hex
