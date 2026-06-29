/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.Pivot
import all HexRowReduce.Pivot

public section

/-!
Correctness of the Gauss-Jordan `rowReduceLoop` for `hex-matrix`.

This module runs `rowReduceLoop` to a finished `rowReduce` and proves it meets the
`IsRowReduced` contract. It tracks the loop's proof-only invariants through each
pivot step: the shape invariant (`rowReduceLoop_shape`), the canonical-column
invariant (`rowReduceLoop_canonical`), the no-pivot-zero invariant
(`rowReduceLoop_no_pivot_zero`), the same-operation transform equation
(`rowReduceLoop_transform_preserve`), and existence of left/right inverses for the
transform, then specializes each to the full run. The headline `def rowReduce`
packages the result, with `rowReduce_isRowReduced` assembling the
`IsEchelonForm`/`IsRowReduced` fields and `rowReduce_transform_mul`, `rowReduce_rank_le_n`,
`rowReduce_pivotCols_sorted` exposing the wrapper-level projections.
-/

namespace Hex
universe u
namespace Matrix
variable {R : Type u} {n m : Nat}

section FieldAlgorithms
variable [Lean.Grind.Field R] [DecidableEq R]

omit [DecidableEq R] in
/-- The empty-pivot initial state trivially satisfies the canonical-column
invariant. -/
private theorem rowReduceLoop_initial_canonical (M : Matrix R n m) :
    RowReduceCanonicalInvariant (R := R) (n := n) (m := m)
      { row := 0, echelon := M, transform := 1, pivots := [] } where
  pivot_entry_one := by intro i hi _; exact absurd hi (by simp)
  other_entry_zero := by intro i hi _ _; exact absurd hi (by simp)

/-- One pivot iteration of `rowReduceLoop` preserves the canonical-column
invariant: every previously processed pivot column remains canonical, and
the newly added pivot column is canonical with the just-discovered pivot
row. -/
private theorem rowReduceCanonicalInvariant_pivot_step
    {col : Nat} {state : RowReduceState R n m}
    (hshape : RowReduceShapeInvariant (R := R) (n := n) (m := m) col state)
    (hcanon : RowReduceCanonicalInvariant (R := R) (n := n) (m := m) state)
    (hRow : state.row < n) (hCol : col < m) {pivot : Fin n}
    (hpivot : findPivot? state.echelon ⟨col, hCol⟩ state.row = some pivot) :
    let colFin : Fin m := ⟨col, hCol⟩
    let target : Fin n := ⟨state.row, hRow⟩
    let swappedEchelon := rowSwap state.echelon target pivot
    let swappedTransform := rowSwap state.transform target pivot
    let pivotVal := swappedEchelon[target][colFin]
    let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
    let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
    let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
    RowReduceCanonicalInvariant (R := R) (n := n) (m := m)
      { row := state.row + 1
        echelon := eliminated.1
        transform := eliminated.2
        pivots := state.pivots.concat colFin } := by
  -- Set up names.
  intro colFin target swappedEchelon swappedTransform pivotVal scaledEchelon
    scaledTransform eliminated
  -- The pivot row of an old pivot at index `i` is below the new pivot row `target`.
  have hpivots_lt_row : ∀ (i : Nat), i < state.pivots.length → i < state.row := by
    intro i hi
    rw [hshape.row_eq_length]; exact hi
  -- The pivot row `pivot` returned by `findPivot?` is ≥ state.row.
  have hpivot_ge : state.row ≤ pivot.val :=
    findPivot?_some_ge state.echelon colFin hpivot
  -- The pivot column is nonzero.
  have hpivotVal_ne : pivotVal ≠ 0 := by
    have hentry : pivotVal = state.echelon[pivot][colFin] := by
      simpa [pivotVal, swappedEchelon] using
        getElem_rowSwap_target_pivot state.echelon target pivot colFin
    rw [hentry]
    exact findPivot?_some_nonzero state.echelon colFin hpivot
  -- Step A: for each OLD pivot index `i`, canonical column is preserved by
  -- the rowSwap → rowScale → eliminateColumn chain at column `state.pivots[i]`.
  have hold : ∀ (i : Nat) (hi : i < state.pivots.length) (hin : i < n),
      eliminated.1[(⟨i, hin⟩ : Fin n)][state.pivots[i]] = 1 ∧
      ∀ r : Fin n, r.val ≠ i →
        eliminated.1[r][state.pivots[i]] = 0 := by
    intro i hi hin
    let pivotRow : Fin n := ⟨i, hin⟩
    have hi_lt_row : i < state.row := hpivots_lt_row i hi
    have hpivotRow_ne_target : pivotRow ≠ target := by
      intro hEq
      have hval : i = state.row := congrArg Fin.val hEq
      omega
    have hpivotRow_ne_pivot : pivotRow ≠ pivot := by
      intro hEq
      have hval : i = pivot.val := congrArg Fin.val hEq
      omega
    -- Original canonical at oldCol = state.pivots[i].
    have hOne₀ :
        state.echelon[pivotRow][state.pivots[i]] = 1 :=
      hcanon.pivot_entry_one i hi hin
    have hZero₀ :
        ∀ r : Fin n, r.val ≠ i →
          state.echelon[r][state.pivots[i]] = 0 :=
      hcanon.other_entry_zero i hi
    have hZero₀_fin :
        ∀ r : Fin n, r ≠ pivotRow →
          state.echelon[r][state.pivots[i]] = 0 := by
      intro r hr
      apply hZero₀ r
      intro hval
      apply hr
      apply Fin.ext
      exact hval
    have hTarget₀ : state.echelon[target][state.pivots[i]] = 0 :=
      hZero₀_fin target hpivotRow_ne_target.symm
    have hPivot₀ : state.echelon[pivot][state.pivots[i]] = 0 :=
      hZero₀_fin pivot hpivotRow_ne_pivot.symm
    -- After rowSwap.
    have hSwap :=
      rowSwap_preserve_canonical_column state.echelon pivotRow target pivot
        state.pivots[i] hTarget₀ hPivot₀ hpivotRow_ne_target hpivotRow_ne_pivot
        hOne₀ hZero₀_fin
    have hSwap_one : swappedEchelon[pivotRow][state.pivots[i]] = 1 := hSwap.1
    have hSwap_zero :
        ∀ r : Fin n, r ≠ pivotRow → swappedEchelon[r][state.pivots[i]] = 0 :=
      hSwap.2
    have hTarget₁ : swappedEchelon[target][state.pivots[i]] = 0 :=
      hSwap_zero target hpivotRow_ne_target.symm
    -- After rowScale.
    have hScale :=
      rowScale_preserve_canonical_column swappedEchelon pivotRow target
        state.pivots[i] pivotVal⁻¹ hTarget₁ hpivotRow_ne_target hSwap_one
        hSwap_zero
    have hScale_one : scaledEchelon[pivotRow][state.pivots[i]] = 1 := hScale.1
    have hScale_zero :
        ∀ r : Fin n, r ≠ pivotRow → scaledEchelon[r][state.pivots[i]] = 0 :=
      hScale.2
    have hTarget₂ : scaledEchelon[target][state.pivots[i]] = 0 :=
      hScale_zero target hpivotRow_ne_target.symm
    -- After eliminateColumn.
    have hElim :=
      eliminateColumn_preserve_canonical_column scaledEchelon scaledTransform
        pivotRow target state.pivots[i] colFin hpivotRow_ne_target hTarget₂
        hScale_one hScale_zero
    refine ⟨hElim.1, ?_⟩
    intro r hrval
    apply hElim.2 r
    intro hEq
    apply hrval
    exact congrArg Fin.val hEq
  -- Step B: for the NEW pivot at column colFin, the canonical property holds
  -- with pivot row = target.
  have hnew :
      eliminated.1[target][colFin] = 1 ∧
      ∀ r : Fin n, r ≠ target → eliminated.1[r][colFin] = 0 := by
    -- After rowScale, target's entry in colFin is 1.
    have hScaled_pivot : scaledEchelon[target][colFin] = 1 := by
      have hEntry : scaledEchelon[target][colFin] = pivotVal⁻¹ * pivotVal := by
        simpa [scaledEchelon, pivotVal] using
          getElem_rowScale swappedEchelon target target pivotVal⁻¹ colFin
      rw [hEntry]
      exact Lean.Grind.Field.inv_mul_cancel hpivotVal_ne
    -- eliminateColumn_pivotRow: target's row is unchanged at colFin.
    have hElim_pivot : eliminated.1[target][colFin] = 1 := by
      have := eliminateColumn_pivotRow scaledEchelon scaledTransform target colFin colFin
      change eliminated.1[target][colFin] = scaledEchelon[target][colFin] at this
      rw [this, hScaled_pivot]
    -- eliminateColumn_zero: every other row is 0 at colFin.
    have hElim_zero :
        ∀ r : Fin n, r ≠ target → eliminated.1[r][colFin] = 0 := by
      intro r hr
      exact eliminateColumn_zero scaledEchelon scaledTransform target colFin
        hScaled_pivot r hr
    exact ⟨hElim_pivot, hElim_zero⟩
  -- Concat indexing helper: for i ≤ state.pivots.length, get the i-th pivot.
  have hconcat_get_old : ∀ (i : Nat) (_hi : i < state.pivots.length)
      (_hi' : i < (state.pivots.concat colFin).length),
      (state.pivots.concat colFin)[i] = state.pivots[i] := by
    intro i hi _hi'
    simp [List.concat_eq_append, List.getElem_append_left hi]
  have hconcat_get_new :
      ∀ (_hi : state.pivots.length < (state.pivots.concat colFin).length),
        (state.pivots.concat colFin)[state.pivots.length] = colFin := by
    intro _hi
    simp [List.concat_eq_append]
  -- Length of concat:
  have hconcat_len : (state.pivots.concat colFin).length = state.pivots.length + 1 := by
    simp
  -- Build the invariant.
  refine { pivot_entry_one := ?_, other_entry_zero := ?_ }
  · -- pivot_entry_one
    intro i hi hin
    have hi' : i < state.pivots.length + 1 := by
      rw [hconcat_len] at hi; exact hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi') with hlt | heq
    · -- Old pivot
      have hget := hconcat_get_old i hlt hi
      simp only [hget]
      exact (hold i hlt hin).1
    · -- New pivot
      subst heq
      have hget := hconcat_get_new hi
      simp only [hget]
      -- Pivot row index = state.pivots.length = state.row = target.val.
      have htarget_eq : (⟨state.pivots.length, hin⟩ : Fin n) = target := by
        apply Fin.ext
        change state.pivots.length = state.row
        exact hshape.row_eq_length.symm
      simp only [htarget_eq]
      exact hnew.1
  · -- other_entry_zero
    intro i hi r hrval
    have hi' : i < state.pivots.length + 1 := by
      rw [hconcat_len] at hi; exact hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi') with hlt | heq
    · -- Old pivot column
      have hget := hconcat_get_old i hlt hi
      simp only [hget]
      exact (hold i hlt (Nat.lt_trans (hpivots_lt_row i hlt) hRow)).2 r hrval
    · -- New pivot column
      subst heq
      have hget := hconcat_get_new hi
      simp only [hget]
      have hr_ne_target : r ≠ target := by
        intro hEq
        apply hrval
        change r.val = state.pivots.length
        have hval : r.val = state.row := congrArg Fin.val hEq
        rw [hval, ← hshape.row_eq_length]
      exact hnew.2 r hr_ne_target

/-- `rowReduceLoop_shape`: `rowReduceLoop` preserves the shape invariant, advancing the
column bound from `col` to `col + fuel`. -/
private theorem rowReduceLoop_shape :
    ∀ (fuel col : Nat) (state : RowReduceState R n m),
      RowReduceShapeInvariant (R := R) (n := n) (m := m) col state →
      RowReduceShapeInvariant (R := R) (n := n) (m := m) (col + fuel)
        (rowReduceLoop (R := R) (n := n) (m := m) col fuel state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro col state h
      simpa [rowReduceLoop] using h
  | succ fuel ih =>
      intro col state h
      unfold rowReduceLoop
      by_cases hRow : state.row < n
      · rw [dif_pos hRow]
        by_cases hCol : col < m
        · rw [dif_pos hCol]
          cases hpivot : findPivot? state.echelon ⟨col, hCol⟩ state.row with
          | none =>
              simpa [hpivot, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (col + 1) state (h.mono_col (Nat.le_succ col))
          | some pivot =>
              let colFin : Fin m := ⟨col, hCol⟩
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              let nextState : RowReduceState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              have hnext :
                  RowReduceShapeInvariant (R := R) (n := n) (m := m) (col + 1) nextState := by
                simpa [nextState, colFin] using rowReduceShapeInvariant_concat (R := R) (n := n) (m := m)
                  (col := col) (state := state) h hRow hCol eliminated.1 eliminated.2
              simpa [hpivot, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, nextState, colFin, target,
                swappedEchelon, swappedTransform, pivotVal, scaledEchelon, scaledTransform,
                eliminated] using ih (col + 1) nextState hnext
        · rw [dif_neg hCol]
          exact h.mono_col (by omega)
      · rw [dif_neg hRow]
        exact h.mono_col (by omega)

omit [DecidableEq R] in
/-- `rowReduceLoop_initial_shape`: the initial RREF state (row 0, no pivots) satisfies
the shape invariant at column bound 0. -/
private theorem rowReduceLoop_initial_shape (M : Matrix R n m) :
    RowReduceShapeInvariant (R := R) (n := n) (m := m) 0
      { row := 0
        echelon := M
        transform := 1
        pivots := [] } where
  row_eq_length := rfl
  row_le_n := Nat.zero_le n
  length_le_col := Nat.le_refl 0
  pivots_sorted := by
    intro i _ hi
    cases hi
  pivots_lt_col := by
    intro p hp
    cases hp

/-- `rowReduce_final_shape`: the matrix produced by the full `rowReduceLoop` run over all
`m` columns satisfies the shape invariant at column bound `m`. -/
private theorem rowReduce_final_shape (M : Matrix R n m) :
    RowReduceShapeInvariant (R := R) (n := n) (m := m) m
      (rowReduceLoop 0 m
        { row := 0
          echelon := M
          transform := 1
          pivots := [] }) := by
  simpa using rowReduceLoop_shape (R := R) (n := n) (m := m) m 0
    { row := 0
      echelon := M
      transform := 1
      pivots := [] } (rowReduceLoop_initial_shape M)

/-- The canonical-column invariant is preserved through `rowReduceLoop`. -/
private theorem rowReduceLoop_canonical :
    ∀ (fuel col : Nat) (state : RowReduceState R n m),
      RowReduceShapeInvariant (R := R) (n := n) (m := m) col state →
      RowReduceCanonicalInvariant (R := R) (n := n) (m := m) state →
      RowReduceCanonicalInvariant (R := R) (n := n) (m := m)
        (rowReduceLoop (R := R) (n := n) (m := m) col fuel state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro col state _hshape hcanon
      simpa [rowReduceLoop] using hcanon
  | succ fuel ih =>
      intro col state hshape hcanon
      unfold rowReduceLoop
      by_cases hRow : state.row < n
      · rw [dif_pos hRow]
        by_cases hCol : col < m
        · rw [dif_pos hCol]
          cases hpivot : findPivot? state.echelon ⟨col, hCol⟩ state.row with
          | none =>
              simpa [hpivot] using
                ih (col + 1) state (hshape.mono_col (Nat.le_succ col)) hcanon
          | some pivot =>
              let colFin : Fin m := ⟨col, hCol⟩
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              let nextState : RowReduceState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              have hnext_shape :
                  RowReduceShapeInvariant (R := R) (n := n) (m := m) (col + 1) nextState := by
                simpa [nextState, colFin] using
                  rowReduceShapeInvariant_concat (R := R) (n := n) (m := m)
                    (col := col) (state := state) hshape hRow hCol
                    eliminated.1 eliminated.2
              have hnext_canon :
                  RowReduceCanonicalInvariant (R := R) (n := n) (m := m) nextState := by
                simpa [nextState, colFin, target, swappedEchelon,
                  swappedTransform, pivotVal, scaledEchelon, scaledTransform,
                  eliminated] using
                  rowReduceCanonicalInvariant_pivot_step (R := R) (n := n) (m := m)
                    (col := col) (state := state) hshape hcanon hRow hCol hpivot
              simpa [hpivot, nextState, colFin, target, swappedEchelon,
                swappedTransform, pivotVal, scaledEchelon, scaledTransform,
                eliminated] using
                ih (col + 1) nextState hnext_shape hnext_canon
        · rw [dif_neg hCol]
          exact hcanon
      · rw [dif_neg hRow]
        exact hcanon

/-- `rowReduce_final_canonical`: the matrix produced by the full `rowReduceLoop` run over
all `m` columns satisfies the canonical-column invariant. -/
private theorem rowReduce_final_canonical (M : Matrix R n m) :
    RowReduceCanonicalInvariant (R := R) (n := n) (m := m)
      (rowReduceLoop 0 m
        { row := 0
          echelon := M
          transform := 1
          pivots := [] }) := by
  exact rowReduceLoop_canonical (R := R) (n := n) (m := m) m 0
    { row := 0, echelon := M, transform := 1, pivots := [] }
    (rowReduceLoop_initial_shape M) (rowReduceLoop_initial_canonical M)

omit [DecidableEq R] in
/-- If two row indices lie at or above `start` and column `k` is zero on every
row from `start` onward, then `rowSwap` at those indices preserves the
zero-column property. -/
private theorem rowSwap_zero_column_preserve {M : Matrix R n m}
    (i j : Fin n) (k : Fin m) {start : Nat}
    (hi : start ≤ i.val) (hj : start ≤ j.val)
    (h : ∀ r : Fin n, start ≤ r.val → M[r][k] = 0) :
    ∀ r : Fin n, start ≤ r.val → (rowSwap M i j)[r][k] = 0 := by
  intro r hr
  rw [getElem_rowSwap]
  by_cases hrj : r = j
  · subst r; rw [if_pos rfl]; exact h i hi
  · rw [if_neg hrj]
    by_cases hri : r = i
    · subst r; rw [if_pos rfl]; exact h j hj
    · rw [if_neg hri]; exact h r hr

omit [DecidableEq R] in
/-- Scaling row `i` by `c` preserves any zero-column property on rows from
`start` onward: the scaled row stays zero because the original value is zero,
and any other row is unchanged. -/
private theorem rowScale_zero_column_preserve {M : Matrix R n m}
    (i : Fin n) (c : R) (k : Fin m) {start : Nat}
    (h : ∀ r : Fin n, start ≤ r.val → M[r][k] = 0) :
    ∀ r : Fin n, start ≤ r.val → (rowScale M i c)[r][k] = 0 := by
  intro r hr
  rw [getElem_rowScale]
  by_cases hri : r = i
  · subst r
    rw [if_pos rfl, h i hr]
    grind
  · rw [if_neg hri]; exact h r hr

/-- Folding `eliminateColumn`'s step function over any list preserves every
row's entry at column `k`, provided the pivot row is zero at column `k`. -/
private theorem eliminateColumn_foldl_other_column
    (pivotRow : Fin n) (col : Fin m) (k : Fin m) :
    ∀ (xs : List (Fin n)) (s : Matrix R n m × Matrix R n n) (r : Fin n),
      s.1[pivotRow][k] = 0 →
      (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
        if _h : j = pivotRow then state
        else
          let coeff := -state.1[j][col]
          if coeff = 0 then state
          else (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
        s).1[r][k]
        = s.1[r][k] := by
  intro xs
  induction xs with
  | nil => intro s r _; rfl
  | cons x xs ih =>
      intro s r hs
      simp only [List.foldl_cons]
      have hstep_pivot :
          (if _h : x = pivotRow then s
            else
              let coeff := -s.1[x][col]
              if coeff = 0 then s
              else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff)).1[pivotRow][k]
            = 0 := by
        rw [eliminateColumn_step_pivotRow_unchanged s pivotRow x col k]
        exact hs
      rw [ih _ r hstep_pivot]
      by_cases hxp : x = pivotRow
      · rw [dif_pos hxp]
      · rw [dif_neg hxp]
        by_cases hcoeff : -s.1[x][col] = 0
        · rw [if_pos hcoeff]
        · rw [if_neg hcoeff]
          by_cases hrx : r = x
          · subst r
            rw [rowAdd_get_dst, hs]
            grind
          · exact rowAdd_get_other s.1 pivotRow x _ hrx k

/-- `eliminateColumn` preserves every row's entry at column `k`, provided the
pivot row is zero at column `k`. -/
private theorem eliminateColumn_other_column
    (M : Matrix R n m) (T : Matrix R n n)
    (pivotRow : Fin n) (col : Fin m) (k : Fin m)
    (hpivot : M[pivotRow][k] = 0) (r : Fin n) :
    (eliminateColumn M T pivotRow col).1[r][k] = M[r][k] := by
  unfold eliminateColumn
  exact eliminateColumn_foldl_other_column pivotRow col k (List.finRange n) (M, T) r hpivot

/-- Proof-only invariant tracking the no-pivot branch of `rowReduceLoop`: every
already-processed column that has not been recorded as a pivot is zero on every
row at or below `state.row`. -/
private structure RowReduceNoPivotZero (col : Nat) (state : RowReduceState R n m) : Prop where
  zero_unrecorded :
    ∀ (c : Fin m), c.val < col → c ∉ state.pivots →
      ∀ (r : Fin n), state.row ≤ r.val → state.echelon[r][c] = 0

omit [DecidableEq R] in
/-- `rowReduceNoPivotZero_initial`: the initial RREF state satisfies the
no-pivot-zero invariant at column bound 0, vacuously. -/
private theorem rowReduceNoPivotZero_initial (M : Matrix R n m) :
    RowReduceNoPivotZero (R := R) (n := n) (m := m) 0
      { row := 0
        echelon := M
        transform := 1
        pivots := [] } where
  zero_unrecorded := by
    intro c hc _ _ _
    exact absurd hc (Nat.not_lt_zero _)

omit [DecidableEq R] in
/-- When the loop exits with `m ≤ col`, the invariant extends vacuously to any
larger column bound: every column index lies below `m ≤ col`, so the old
zero-column facts cover all relevant columns. -/
private theorem RowReduceNoPivotZero.widen_col_at_m {col col' : Nat}
    {state : RowReduceState R n m}
    (h : RowReduceNoPivotZero (R := R) (n := n) (m := m) col state) (hcol : m ≤ col) :
    RowReduceNoPivotZero (R := R) (n := n) (m := m) col' state where
  zero_unrecorded := fun c _ hcnot r hr =>
    h.zero_unrecorded c (Nat.lt_of_lt_of_le c.isLt hcol) hcnot r hr

omit [DecidableEq R] in
/-- When the loop exits with `n ≤ state.row`, the invariant extends vacuously
to any column bound: no row index satisfies the hypothesis. -/
private theorem RowReduceNoPivotZero.widen_col_at_n {col col' : Nat}
    {state : RowReduceState R n m}
    (_h : RowReduceNoPivotZero (R := R) (n := n) (m := m) col state) (hrow : n ≤ state.row) :
    RowReduceNoPivotZero (R := R) (n := n) (m := m) col' state where
  zero_unrecorded := fun _ _ _ r hr => by
    have hge : n ≤ r.val := Nat.le_trans hrow hr
    exact absurd r.isLt (Nat.not_lt_of_ge hge)

/-- `rowReduceLoop_no_pivot_zero`: `rowReduceLoop` preserves the no-pivot-zero invariant,
advancing the column bound from `col` to `col + fuel`. -/
private theorem rowReduceLoop_no_pivot_zero :
    ∀ (fuel col : Nat) (state : RowReduceState R n m),
      RowReduceNoPivotZero col state →
      RowReduceNoPivotZero (col + fuel)
        (rowReduceLoop (R := R) (n := n) (m := m) col fuel state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro col state h
      simpa [rowReduceLoop] using h
  | succ fuel ih =>
      intro col state h
      unfold rowReduceLoop
      by_cases hRow : state.row < n
      · rw [dif_pos hRow]
        by_cases hCol : col < m
        · rw [dif_pos hCol]
          cases hpivot : findPivot? state.echelon ⟨col, hCol⟩ state.row with
          | none =>
              have hnext : RowReduceNoPivotZero (R := R) (n := n) (m := m) (col + 1) state := by
                refine ⟨?_⟩
                intro c hc hcnot r hr
                rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hold | heq
                · exact h.zero_unrecorded c hold hcnot r hr
                · have hc_eq : c = ⟨col, hCol⟩ := Fin.ext heq
                  subst hc_eq
                  exact findPivot?_none state.echelon ⟨col, hCol⟩ hpivot r hr
              simpa [hpivot, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (col + 1) state hnext
          | some pivot =>
              let colFin : Fin m := ⟨col, hCol⟩
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              let nextState : RowReduceState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              have hpivot_ge : state.row ≤ pivot.val :=
                findPivot?_some_ge state.echelon colFin hpivot
              have htarget_val : (target : Fin n).val = state.row := rfl
              have hnext :
                  RowReduceNoPivotZero (R := R) (n := n) (m := m) (col + 1) nextState := by
                refine ⟨?_⟩
                intro c hc hcnot r hr
                have hcnot_concat : c ∉ state.pivots.concat colFin := hcnot
                have hcnot_old : c ∉ state.pivots := by
                  intro hin
                  apply hcnot_concat
                  rw [List.concat_eq_append]
                  exact List.mem_append.mpr (Or.inl hin)
                have hcne_colFin : c ≠ colFin := by
                  intro heq
                  apply hcnot_concat
                  rw [List.concat_eq_append]
                  exact List.mem_append.mpr (Or.inr (by simp [heq]))
                have hclt_col : c.val < col := by
                  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hold | heq
                  · exact hold
                  · exact absurd (Fin.ext heq : c = colFin) hcne_colFin
                have hzero_state :
                    ∀ s : Fin n, state.row ≤ s.val → state.echelon[s][c] = 0 :=
                  fun s hs => h.zero_unrecorded c hclt_col hcnot_old s hs
                have hzero_swap :
                    ∀ s : Fin n, state.row ≤ s.val → swappedEchelon[s][c] = 0 :=
                  rowSwap_zero_column_preserve (M := state.echelon)
                    target pivot c (start := state.row)
                    (Nat.le_of_eq htarget_val.symm) hpivot_ge hzero_state
                have hzero_scaled :
                    ∀ s : Fin n, state.row ≤ s.val → scaledEchelon[s][c] = 0 :=
                  rowScale_zero_column_preserve (M := swappedEchelon)
                    target pivotVal⁻¹ c (start := state.row) hzero_swap
                have hzero_pivot_at_c : scaledEchelon[target][c] = 0 :=
                  hzero_scaled target (Nat.le_of_eq htarget_val.symm)
                have hzero_elim : eliminated.1[r][c] = scaledEchelon[r][c] :=
                  eliminateColumn_other_column scaledEchelon scaledTransform target colFin c
                    hzero_pivot_at_c r
                have hr_old : state.row ≤ r.val := by
                  have : state.row + 1 ≤ r.val := hr
                  omega
                show eliminated.1[r][c] = 0
                rw [hzero_elim]
                exact hzero_scaled r hr_old
              simpa [hpivot, colFin, target, swappedEchelon, swappedTransform,
                pivotVal, scaledEchelon, scaledTransform, eliminated, nextState,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (col + 1) nextState hnext
        · rw [dif_neg hCol]
          exact h.widen_col_at_m (by omega)
      · rw [dif_neg hRow]
        exact h.widen_col_at_n (by omega)

/-- `rowReduce_final_no_pivot_zero`: the matrix produced by the full `rowReduceLoop` run
over all `m` columns satisfies the no-pivot-zero invariant at column bound `m`. -/
private theorem rowReduce_final_no_pivot_zero (M : Matrix R n m) :
    RowReduceNoPivotZero (R := R) (n := n) (m := m) m
      (rowReduceLoop 0 m
        { row := 0
          echelon := M
          transform := 1
          pivots := [] }) := by
  simpa using rowReduceLoop_no_pivot_zero (R := R) (n := n) (m := m) m 0
    { row := 0
      echelon := M
      transform := 1
      pivots := [] } (rowReduceNoPivotZero_initial M)

/-- `rowReduceLoop` preserves existence of a left inverse for the transform. -/
private theorem rowReduceLoop_left_inverse_preserve (col fuel : Nat)
    (state : RowReduceState R n m)
    (h : ∃ Tinv : Matrix R n n, Tinv * state.transform = 1) :
    ∃ Tinv' : Matrix R n n,
      Tinv' * (rowReduceLoop col fuel state).transform = 1 := by
  induction fuel generalizing col state with
  | zero =>
      simpa [rowReduceLoop] using h
  | succ fuel ih =>
      by_cases hRow : state.row < n
      · by_cases hCol : col < m
        ·
          let colFin : Fin m := ⟨col, hCol⟩
          cases hpivot : findPivot? state.echelon colFin state.row with
          | none =>
              simpa [rowReduceLoop, hRow, hCol, colFin, hpivot] using ih (col + 1) state h
          | some pivot =>
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              let nextState : RowReduceState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              have hswap :
                  ∃ Tinv : Matrix R n n, Tinv * swappedTransform = 1 :=
                rowSwap_left_inverse_preserve state.transform target pivot h
              have hpivotVal : pivotVal ≠ 0 := by
                have hpivotNonzero := findPivot?_some_nonzero state.echelon colFin hpivot
                have hentry : pivotVal = state.echelon[pivot][colFin] := by
                  simpa [pivotVal, swappedEchelon] using
                    (getElem_rowSwap_target_pivot state.echelon target pivot colFin)
                simpa [hentry] using hpivotNonzero
              have hscale :
                  ∃ Tinv : Matrix R n n, Tinv * scaledTransform = 1 :=
                rowScale_left_inverse_preserve swappedTransform target
                  (show pivotVal⁻¹ ≠ 0 by grind) hswap
              have helim :
                  ∃ Tinv : Matrix R n n, Tinv * eliminated.2 = 1 :=
                eliminateColumn_left_inverse_preserve scaledTransform scaledEchelon target colFin hscale
              simpa [rowReduceLoop, hRow, hCol, colFin, hpivot, target, swappedEchelon,
                swappedTransform, pivotVal, scaledEchelon, scaledTransform, eliminated,
                nextState] using ih (col + 1) nextState helim
        · simpa [rowReduceLoop, hRow, hCol] using h
      · simpa [rowReduceLoop, hRow] using h

/-- `rowReduceLoop` preserves existence of a right inverse for the transform. -/
private theorem rowReduceLoop_right_inverse_preserve (col fuel : Nat)
    (state : RowReduceState R n m)
    (h : ∃ Tinv : Matrix R n n, state.transform * Tinv = 1) :
    ∃ Tinv' : Matrix R n n,
      (rowReduceLoop col fuel state).transform * Tinv' = 1 := by
  induction fuel generalizing col state with
  | zero =>
      simpa [rowReduceLoop] using h
  | succ fuel ih =>
      by_cases hRow : state.row < n
      · by_cases hCol : col < m
        ·
          let colFin : Fin m := ⟨col, hCol⟩
          cases hpivot : findPivot? state.echelon colFin state.row with
          | none =>
              simpa [rowReduceLoop, hRow, hCol, colFin, hpivot] using ih (col + 1) state h
          | some pivot =>
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              let nextState : RowReduceState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              have hswap :
                  ∃ Tinv : Matrix R n n, swappedTransform * Tinv = 1 :=
                rowSwap_right_inverse_preserve state.transform target pivot h
              have hpivotVal : pivotVal ≠ 0 := by
                have hpivotNonzero := findPivot?_some_nonzero state.echelon colFin hpivot
                have hentry : pivotVal = state.echelon[pivot][colFin] := by
                  simpa [pivotVal, swappedEchelon] using
                    (getElem_rowSwap_target_pivot state.echelon target pivot colFin)
                simpa [hentry] using hpivotNonzero
              have hscale :
                  ∃ Tinv : Matrix R n n, scaledTransform * Tinv = 1 :=
                rowScale_right_inverse_preserve swappedTransform target
                  (show pivotVal⁻¹ ≠ 0 by grind) hswap
              have helim :
                  ∃ Tinv : Matrix R n n, eliminated.2 * Tinv = 1 :=
                eliminateColumn_right_inverse_preserve scaledTransform scaledEchelon target colFin hscale
              simpa [rowReduceLoop, hRow, hCol, colFin, hpivot, target, swappedEchelon,
                swappedTransform, pivotVal, scaledEchelon, scaledTransform, eliminated,
                nextState] using ih (col + 1) nextState helim
        · simpa [rowReduceLoop, hRow, hCol] using h
      · simpa [rowReduceLoop, hRow] using h

/-- The Gauss-Jordan loop preserves the same-operation transform invariant:
the recorded transform applied to the original matrix is the current echelon
matrix. -/
private theorem rowReduceLoop_transform_preserve (M : Matrix R n m) :
    ∀ (col fuel : Nat) (state : RowReduceState R n m),
      state.transform * M = state.echelon →
      (rowReduceLoop col fuel state).transform * M = (rowReduceLoop col fuel state).echelon := by
  intro col fuel
  induction fuel generalizing col with
  | zero =>
      intro state h
      simp [rowReduceLoop, h]
  | succ fuel ih =>
      intro state h
      unfold rowReduceLoop
      by_cases hRow : state.row < n
      · rw [dif_pos hRow]
        by_cases hCol : col < m
        · rw [dif_pos hCol]
          let colFin : Fin m := ⟨col, hCol⟩
          cases hp : findPivot? state.echelon colFin state.row with
          | none =>
              simpa [colFin, hp] using ih (col + 1) state h
          | some pivot =>
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              have hswap : swappedTransform * M = swappedEchelon := by
                simpa [swappedTransform, swappedEchelon] using
                  rowSwap_transform_mul_preserve target pivot h
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              have hscale : scaledTransform * M = scaledEchelon := by
                simpa [scaledTransform, scaledEchelon] using
                  rowScale_transform_mul_preserve target pivotVal⁻¹ hswap
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              have helim : eliminated.2 * M = eliminated.1 := by
                simpa [eliminated] using
                  eliminateColumn_transform_preserve scaledTransform scaledEchelon target colFin hscale
              have hnext := ih (col + 1)
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin } helim
              simpa [colFin, hp, target, swappedEchelon, swappedTransform, pivotVal,
                scaledEchelon, scaledTransform, eliminated]
                using hnext
        · rw [dif_neg hCol]
          exact h
      · rw [dif_neg hRow]
        exact h

/-- Reduced row echelon form data computed by Gauss-Jordan elimination. -/
@[expose]
def rowReduce (M : Matrix R n m) : RowEchelonData R n m :=
  let final := rowReduceLoop 0 m
    { row := 0
      echelon := M
      transform := 1
      pivots := [] }
  { rank := final.pivots.length
    echelon := final.echelon
    transform := final.transform
    pivotCols := ⟨final.pivots.toArray, by simp⟩ }

/-- Wrapper-level projection of the rank row bound from `rowReduce_isRowReduced M`. -/
theorem rowReduce_rank_le_n (M : Matrix R n m) : (rowReduce M).rank ≤ n := by
  unfold rowReduce
  change (rowReduceLoop 0 m { row := 0, echelon := M, transform := 1, pivots := [] }).pivots.length ≤ n
  rw [← (rowReduce_final_shape M).row_eq_length]
  exact (rowReduce_final_shape M).row_le_n

/-- Wrapper-level projection of the rank column bound from `rowReduce_isRowReduced M`. -/
theorem rowReduce_rank_le_m (M : Matrix R n m) : (rowReduce M).rank ≤ m := by
  unfold rowReduce
  exact (rowReduce_final_shape M).length_le_col

/-- Wrapper-level projection of pivot-column sortedness from `rowReduce_isRowReduced M`. -/
theorem rowReduce_pivotCols_sorted (M : Matrix R n m) :
    ∀ i j, i < j → (rowReduce M).pivotCols.get i < (rowReduce M).pivotCols.get j := by
  intro i j hij
  unfold rowReduce
  let final := rowReduceLoop 0 m
    { row := 0
      echelon := M
      transform := 1
      pivots := [] }
  have hshape : RowReduceShapeInvariant (R := R) (n := n) (m := m) m final := by
    simpa [final] using rowReduce_final_shape M
  change (⟨final.pivots.toArray, by simp⟩ : Vector (Fin m) final.pivots.length).get i <
    (⟨final.pivots.toArray, by simp⟩ : Vector (Fin m) final.pivots.length).get j
  simp only [Vector.get, List.getElem_toArray]
  exact hshape.pivots_sorted i.val j.val i.isLt j.isLt hij

/-- Final `rowReduce` row transform has a left inverse. -/
private theorem rowReduce_transform_left_inverse (M : Matrix R n m) :
    ∃ Tinv : Matrix R n n, Tinv * (rowReduce M).transform = 1 := by
  unfold rowReduce
  exact rowReduceLoop_left_inverse_preserve 0 m
    { row := 0, echelon := M, transform := 1, pivots := [] }
    ⟨1, by rw [one_mul]⟩

/-- Final `rowReduce` row transform has a right inverse. -/
private theorem rowReduce_transform_right_inverse (M : Matrix R n m) :
    ∃ Tinv : Matrix R n n, (rowReduce M).transform * Tinv = 1 := by
  unfold rowReduce
  exact rowReduceLoop_right_inverse_preserve 0 m
    { row := 0, echelon := M, transform := 1, pivots := [] }
    ⟨1, by rw [one_mul]⟩

/-- Wrapper-level projection of the transform equation from `rowReduce_isRowReduced M`. -/
theorem rowReduce_transform_mul (M : Matrix R n m) :
    (rowReduce M).transform * M = (rowReduce M).echelon := by
  unfold rowReduce
  exact rowReduceLoop_transform_preserve M 0 m
    { row := 0
      echelon := M
      transform := 1
      pivots := [] }
    (by rw [Matrix.one_mul])

/-- The computed `rowReduce` data satisfies the `IsRowReduced` contract. -/
theorem rowReduce_isRowReduced (M : Matrix R n m) : IsRowReduced M (rowReduce M) := by
  let final := rowReduceLoop 0 m
    { row := 0, echelon := M, transform := 1, pivots := [] }
  have hcanon : RowReduceCanonicalInvariant (R := R) (n := n) (m := m) final := by
    simpa [final] using rowReduce_final_canonical M
  have hshape : RowReduceShapeInvariant (R := R) (n := n) (m := m) m final := by
    simpa [final] using rowReduce_final_shape M
  have hrank_eq : (rowReduce M).rank = final.pivots.length := by simp [rowReduce, final]
  have hechelon_eq : (rowReduce M).echelon = final.echelon := by simp [rowReduce, final]
  have hpivotCol_get : ∀ (i : Fin (rowReduce M).rank)
      (hi : i.val < final.pivots.length),
      ((rowReduce M).pivotCols.get i).val = (final.pivots[i.val]'hi).val := by
    intro i _hi
    simp [rowReduce, final, Vector.get, List.getElem_toArray]
  refine
    { toIsEchelonForm :=
        { transform_mul := rowReduce_transform_mul M
          transform_inv := rowReduce_transform_left_inverse M
          transform_right_inv := rowReduce_transform_right_inverse M
          rank_le_n := rowReduce_rank_le_n M
          rank_le_m := rowReduce_rank_le_m M
          pivotCols_sorted := rowReduce_pivotCols_sorted M
          below_pivot_zero := ?bpz
          zero_row := ?zr }
      pivot_one := ?po
      above_pivot_zero := ?apz }
  case po =>
    intro i
    have hi_lt_len : i.val < final.pivots.length := hrank_eq ▸ i.isLt
    have hin : i.val < n := by
      have hrow_le : final.row ≤ n := hshape.row_le_n
      have hrow_eq : final.row = final.pivots.length := hshape.row_eq_length
      omega
    have hentry := hcanon.pivot_entry_one i.val hi_lt_len hin
    have hcol_eq : (rowReduce M).pivotCols.get i = final.pivots[i.val] :=
      Fin.ext (hpivotCol_get i hi_lt_len)
    have hech : (rowReduce M).echelon[i][(rowReduce M).pivotCols.get i] =
        final.echelon[(⟨i.val, hin⟩ : Fin n)][final.pivots[i.val]] := by
      simp only [hechelon_eq, hcol_eq]
      rfl
    rw [hech]
    exact hentry
  case apz =>
    intro i j hji
    have hi_lt_len : i.val < final.pivots.length := hrank_eq ▸ i.isLt
    have hentry := hcanon.other_entry_zero i.val hi_lt_len j (Nat.ne_of_lt hji)
    have hcol_eq : (rowReduce M).pivotCols.get i = final.pivots[i.val] :=
      Fin.ext (hpivotCol_get i hi_lt_len)
    have hech : (rowReduce M).echelon[j][(rowReduce M).pivotCols.get i] =
        final.echelon[j][final.pivots[i.val]] := by
      simp only [hcol_eq, hechelon_eq]
    rw [hech]
    exact hentry
  case bpz =>
    intro i j hij
    have hi_lt_len : i.val < final.pivots.length := hrank_eq ▸ i.isLt
    have hentry := hcanon.other_entry_zero i.val hi_lt_len j (Nat.ne_of_gt hij)
    have hcol_eq : (rowReduce M).pivotCols.get i = final.pivots[i.val] :=
      Fin.ext (hpivotCol_get i hi_lt_len)
    have hech : (rowReduce M).echelon[j][(rowReduce M).pivotCols.get i] =
        final.echelon[j][final.pivots[i.val]] := by
      simp only [hcol_eq, hechelon_eq]
    rw [hech]
    exact hentry
  case zr =>
    intro i hi
    have hno_pivot : RowReduceNoPivotZero (R := R) (n := n) (m := m) m final := by
      simpa [final] using rowReduce_final_no_pivot_zero M
    have hi_ge : final.pivots.length ≤ i.val := hrank_eq ▸ hi
    have hrow_le_i : final.row ≤ i.val := hshape.row_eq_length ▸ hi_ge
    rw [hechelon_eq]
    ext c hc
    rw [Vector.getElem_zero c hc]
    let cFin : Fin m := ⟨c, hc⟩
    show final.echelon[i][cFin] = 0
    by_cases hmem : cFin ∈ final.pivots
    · obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp hmem
      have hi_ne_k : i.val ≠ k := by omega
      have hentry := hcanon.other_entry_zero k hk_lt i hi_ne_k
      have heq : final.echelon[i][cFin] = final.echelon[i][final.pivots[k]'hk_lt] :=
        congrArg (fun x : Fin m => final.echelon[i][x]) hk_eq.symm
      rw [heq]
      exact hentry
    · exact hno_pivot.zero_unrecorded cFin cFin.isLt hmem i hrow_le_i


end FieldAlgorithms
end Matrix
end Hex
