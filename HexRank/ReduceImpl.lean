/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Reduce

public section

/-!
The in-place implementation of `rowReduceWith` on `Array (Array R)` row
storage, registered by `@[csimp]`. The public `rowReduceWith` is the
kernel-facing definition; compiled code runs `rowReduceWithImpl`, which keeps
the working matrix in mutable rows and updates each row in place. The two are
related entry by entry: the array pass keeps every row of length `m`, and one
step of it reads back, through `getEntry`, as one step of the `ofFn` form.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} {n m : Nat}

/-- Pack a rectangular matrix as `n` rows of `m` entries. -/
@[expose]
def matrixToRowsRect [Zero R] (M : Matrix R n m) : Array (Array R) :=
  (Array.range n).map fun row =>
    (Array.range m).map fun col =>
      if hrow : row < n then
        if hcol : col < m then M[((⟨row, hrow⟩ : Fin n), (⟨col, hcol⟩ : Fin m))] else 0
      else 0

/-- Unpack row storage into a rectangular matrix, reading through `getEntry`. -/
@[expose]
def rowsToMatrixRect [Zero R] (rows : Array (Array R)) (n m : Nat) : Matrix R n m :=
  ofFn fun i j => getEntry rows i.val j.val

/-- Row storage of `n` rows of `m` entries. -/
def RowsShaped (rows : Array (Array R)) (n m : Nat) : Prop :=
  rows.size = n ∧ ∀ (i : Nat) (hi : i < rows.size), rows[i].size = m

theorem getEntry_matrixToRowsRect [Zero R] (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    getEntry (matrixToRowsRect M) i.val j.val = M[i][j] := by
  simp [getEntry, matrixToRowsRect]

theorem rowsToMatrixRect_matrixToRowsRect [Zero R] (M : Matrix R n m) :
    rowsToMatrixRect (matrixToRowsRect M) n m = M := by
  apply ext_getElem
  intro i j
  rw [rowsToMatrixRect, getElem_ofFn, getEntry_matrixToRowsRect]

theorem matrixToRowsRect_shaped [Zero R] (M : Matrix R n m) :
    RowsShaped (matrixToRowsRect M) n m := by
  refine ⟨by simp [matrixToRowsRect], ?_⟩
  intro i hi
  simp [matrixToRowsRect]

theorem getElem_rowsToMatrixRect [Zero R] (rows : Array (Array R)) (i : Fin n) (j : Fin m) :
    (rowsToMatrixRect rows n m)[i][j] = getEntry rows i.val j.val := by
  rw [rowsToMatrixRect, getElem_ofFn]

/-- The array-storage state of the pass. -/
structure ReducedRows (R : Type u) (n m : Nat) where
  /-- The rank profile. -/
  profile : RankProfile n m
  /-- The last pivot. -/
  denom : R
  /-- The working matrix, as rows. -/
  rows : Array (Array R)

/-- Read the array state back as a `ReducedForm`. -/
@[expose]
def ReducedRows.toForm [Zero R] (S : ReducedRows R n m) : ReducedForm R n m :=
  ⟨S.profile, S.denom, rowsToMatrixRect S.rows n m⟩

/-- The pivot search on row storage. -/
@[expose]
def findPivotRowArr? [Zero R] [DecidableEq R] (rows : Array (Array R)) (used : List (Fin n))
    (j : Fin m) : Option (Fin n) :=
  (List.finRange n).find? fun i => decide (i ∉ used) && decide (getEntry rows i.val j.val ≠ 0)

theorem findPivotRowArr?_eq [Zero R] [DecidableEq R] (rows : Array (Array R))
    (used : List (Fin n)) (j : Fin m) :
    findPivotRowArr? rows used j = findPivotRow? (rowsToMatrixRect rows n m) used j := by
  unfold findPivotRowArr? findPivotRow?
  congr 1
  funext i
  rw [getElem_pair_eq_nested, getElem_rowsToMatrixRect]

/-- One row of the in-place Bareiss update: every entry but the pivot column is
replaced by `quot (pivot * x - mij * pivotRow[j']) prev`, the pivot column by
`0`. -/
@[expose, specialize quot]
def updateRow [Zero R] [Sub R] [Mul R] (quot : R → R → R) (pivotRow : Array R)
    (pivot prev : R) (j : Nat) (row : Array R) : Array R :=
  let mij := row.getD j 0
  row.mapFinIdx fun j' x _ => if j' = j then 0 else quot (pivot * x - mij * pivotRow.getD j' 0) prev

/-- One column of the in-place pass. -/
@[expose, specialize quot]
def reduceStepImpl [Zero R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (S : ReducedRows R n m) (j : Fin m) : ReducedRows R n m :=
  match S with
  | ⟨profile, prev, rows⟩ =>
    match findPivotRowArr? rows profile.rows.toList j with
    | none => ⟨profile, prev, rows⟩
    | some p =>
      let pivotRow := rows.getD p.val #[]
      let pivot := pivotRow.getD j.val 0
      let rows' := Fin.foldl n (fun rs i =>
        if i = p then rs else rs.modify i.val (updateRow quot pivotRow pivot prev j.val)) rows
      ⟨{ rank := profile.rank + 1, rows := profile.rows.push p, cols := profile.cols.push j },
        pivot, rows'⟩

/-- The in-place pass: pack, scan every column, unpack. -/
@[expose, specialize quot]
def rowReduceWithImpl [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (A : Matrix R n m) : ReducedForm R n m :=
  let S := (List.finRange m).foldl (reduceStepImpl quot)
    ⟨{ rank := 0, rows := #v[], cols := #v[] }, 1, matrixToRowsRect A⟩
  S.toForm

section Correspondence

variable [Zero R] [Sub R] [Mul R] [DecidableEq R] {quot : R → R → R}

omit [DecidableEq R] in
theorem size_updateRow (pivotRow : Array R) (pivot prev : R) (j : Nat) (row : Array R) :
    (updateRow quot pivotRow pivot prev j row).size = row.size := by
  simp [updateRow]

omit [DecidableEq R] in
theorem getD_updateRow (pivotRow : Array R) (pivot prev : R) (j : Nat) (row : Array R)
    {j' : Nat} (hj' : j' < row.size) :
    (updateRow quot pivotRow pivot prev j row).getD j' 0 =
      if j' = j then 0 else quot (pivot * row.getD j' 0 - row.getD j 0 * pivotRow.getD j' 0) prev := by
  simp [updateRow, Array.getD_eq_getD_getElem?, hj']

omit [Zero R] [Sub R] [Mul R] [DecidableEq R] in
/-- Reading a modified row storage. -/
theorem getD_modify_rows (rows : Array (Array R)) (i : Nat) (f : Array R → Array R) (i' : Nat) :
    (rows.modify i f).getD i' #[] =
      if i' = i ∧ i < rows.size then f (rows.getD i #[]) else rows.getD i' #[] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hii : i = i'
  · subst hii
    by_cases hi : i < rows.size
    · simp [hi]
    · simp [hi]
  · have hii' : ¬ (i' = i) := fun h => hii h.symm
    simp [hii, hii']

omit [DecidableEq R] in
/-- The row loop of one pivot step, as a list fold over the rows visited. -/
theorem getEntry_rowLoop (pivotRow : Array R) (pivot prev : R) (j : Nat) (p : Fin n)
    (l : List (Fin n)) (hl : l.Nodup) (rows : Array (Array R)) (hshape : RowsShaped rows n m)
    (i : Fin n) (j' : Fin m) :
    getEntry (l.foldl (fun rs i =>
        if i = p then rs else rs.modify i.val (updateRow quot pivotRow pivot prev j)) rows)
      i.val j'.val =
      if i ∈ l ∧ i ≠ p then
        (if j'.val = j then 0 else
          quot (pivot * getEntry rows i.val j'.val - getEntry rows i.val j * pivotRow.getD j'.val 0)
            prev)
      else getEntry rows i.val j'.val := by
  induction l generalizing rows with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons]
    by_cases hap : a = p
    · subst hap
      rw [ite_eq_left rfl, ih hl.2 rows hshape]
      by_cases hia : i = a
      · subst hia
        simp
      · by_cases hi : i ∈ l
        · simp [hi, List.mem_cons, hia]
        · simp [hi, List.mem_cons, hia]
    · rw [ite_eq_right hap]
      have hshape' : RowsShaped (rows.modify a.val (updateRow quot pivotRow pivot prev j)) n m := by
        refine ⟨by simp [hshape.1], ?_⟩
        intro i' hi'
        rw [Array.size_modify] at hi'
        rw [Array.getElem_modify]
        split
        · rw [size_updateRow]
          exact hshape.2 _ _
        · exact hshape.2 _ _
      rw [ih hl.2 _ hshape']
      have hentry : ∀ (i₀ : Fin n) (j₀ : Nat),
          getEntry (rows.modify a.val (updateRow quot pivotRow pivot prev j)) i₀.val j₀ =
            if i₀ = a then (updateRow quot pivotRow pivot prev j (rows.getD a.val #[])).getD j₀ 0
            else getEntry rows i₀.val j₀ := by
        intro i₀ j₀
        simp only [getEntry]
        rw [getD_modify_rows]
        have ha : a.val < rows.size := hshape.1 ▸ a.isLt
        by_cases h : i₀ = a
        · subst h
          simp [ha]
        · have hv : i₀.val ≠ a.val := fun h' => h (Fin.ext h')
          simp [h, hv]
      have hrow : (rows.getD a.val #[]).size = m := by
        have ha : a.val < rows.size := hshape.1 ▸ a.isLt
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ha]
        exact hshape.2 _ _
      by_cases hia : i = a
      · subst hia
        have hnot : ¬ (i ∈ l ∧ i ≠ p) := fun h => hl.1 h.1
        have hin : i ∈ i :: l ∧ i ≠ p := ⟨List.mem_cons_self, hap⟩
        rw [ite_eq_right hnot, ite_eq_left hin, hentry i j', ite_eq_left rfl,
          getD_updateRow _ _ _ _ _ (hrow ▸ j'.isLt)]
        simp only [getEntry]
      · by_cases hi : i ∈ l
        · rw [hentry i j', ite_eq_right hia, hentry i j, ite_eq_right hia]
          by_cases hip : i = p
          · simp [hip]
          · have h1 : i ∈ l ∧ i ≠ p := ⟨hi, hip⟩
            have h2 : i ∈ a :: l ∧ i ≠ p := ⟨List.mem_cons_of_mem _ hi, hip⟩
            rw [ite_eq_left h1, ite_eq_left h2]
        · have h1 : ¬ (i ∈ l ∧ i ≠ p) := fun h => hi h.1
          have h2 : ¬ (i ∈ a :: l ∧ i ≠ p) := fun h => by
            rcases List.mem_cons.mp h.1 with h' | h'
            · exact hia h'
            · exact hi h'
          rw [ite_eq_right h1, ite_eq_right h2, hentry i j', ite_eq_right hia]

omit [DecidableEq R] in
/-- The row loop keeps every row of length `m`. -/
theorem rowLoop_shaped (pivotRow : Array R) (pivot prev : R) (j : Nat) (p : Fin n)
    (l : List (Fin n)) (rows : Array (Array R)) (hshape : RowsShaped rows n m) :
    RowsShaped (l.foldl (fun rs i =>
      if i = p then rs else rs.modify i.val (updateRow quot pivotRow pivot prev j)) rows) n m := by
  induction l generalizing rows with
  | nil => exact hshape
  | cons a l ih =>
    rw [List.foldl_cons]
    apply ih
    by_cases hap : a = p
    · rw [ite_eq_left hap]
      exact hshape
    · rw [ite_eq_right hap]
      refine ⟨by simp [hshape.1], ?_⟩
      intro i' hi'
      rw [Array.size_modify] at hi'
      rw [Array.getElem_modify]
      split
      · rw [size_updateRow]
        exact hshape.2 _ _
      · exact hshape.2 _ _

/-- One step of the array pass reads back as one step of the `ofFn` pass. -/
theorem toForm_reduceStepImpl (S : ReducedRows R n m) (hshape : RowsShaped S.rows n m)
    (j : Fin m) :
    (reduceStepImpl quot S j).toForm = reduceStep quot S.toForm j ∧
      RowsShaped (reduceStepImpl quot S j).rows n m := by
  obtain ⟨profile, prev, rows⟩ := S
  simp only [reduceStepImpl]
  have hfind := findPivotRowArr?_eq rows profile.rows.toList j
  cases hp : findPivotRowArr? rows profile.rows.toList j with
  | none =>
    rw [hp] at hfind
    refine ⟨?_, hshape⟩
    rw [reduceStep_skip hfind.symm]
  | some p =>
    rw [hp] at hfind
    have hfind' : findPivotRow? (ReducedRows.toForm ⟨profile, prev, rows⟩).matrix
        (ReducedRows.toForm ⟨profile, prev, rows⟩).profile.rows.toList j = some p := hfind.symm
    dsimp only
    refine ⟨?_, ?_⟩
    · have hpiv : (rows.getD p.val #[]).getD j.val 0 = getEntry rows p.val j.val := rfl
      show (⟨_, _, rowsToMatrixRect _ n m⟩ : ReducedForm R n m) = _
      cases hstep : reduceStep quot (ReducedRows.toForm ⟨profile, prev, rows⟩) j with
      | mk profile' denom' matrix' =>
        have hprof := reduceStep_pivot_profile (quot := quot) hfind'
        have hden := reduceStep_pivot_denom (quot := quot) hfind'
        have hM := getElem_reduceStep_pivot (quot := quot) hfind'
        rw [hstep] at hprof hden hM
        simp only at hprof hden hM
        subst hprof
        congr 1
        · rw [hden, hpiv]
          exact (getElem_rowsToMatrixRect rows p j).symm
        · apply ext_getElem
          intro i j'
          rw [hM i j', getElem_rowsToMatrixRect, Fin.foldl_eq_finRange_foldl,
            getEntry_rowLoop _ _ _ _ _ _ (List.nodup_finRange n) _ hshape]
          simp only [ReducedRows.toForm, getElem_rowsToMatrixRect, List.mem_finRange, true_and]
          by_cases hip : i = p
          · subst hip
            simp
          · simp only [hip, ne_eq, not_false_eq_true, ite_true, ite_false]
            by_cases hj : j' = j
            · subst hj
              simp
            · have hv : j'.val ≠ j.val := fun h => hj (Fin.ext h)
              simp only [hv, hj, ite_false, hpiv]
              rfl
    · rw [Fin.foldl_eq_finRange_foldl]
      exact rowLoop_shaped _ _ _ _ _ _ _ hshape

/-- The array pass agrees with the `ofFn` pass along any run of columns. -/
theorem toForm_foldl (l : List (Fin m)) (S : ReducedRows R n m) (hshape : RowsShaped S.rows n m) :
    (l.foldl (reduceStepImpl quot) S).toForm = l.foldl (reduceStep quot) S.toForm ∧
      RowsShaped (l.foldl (reduceStepImpl quot) S).rows n m := by
  induction l generalizing S with
  | nil => exact ⟨rfl, hshape⟩
  | cons j l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨h1, h2⟩ := toForm_reduceStepImpl S hshape j
    rw [← h1]
    exact ih _ h2

/-- The in-place pass computes the kernel-facing pass. -/
theorem rowReduceWithImpl_eq [One R] (quot : R → R → R) (A : Matrix R n m) :
    rowReduceWithImpl quot A = rowReduceWith quot A := by
  unfold rowReduceWithImpl rowReduceWith
  rw [(toForm_foldl _ _ (matrixToRowsRect_shaped A)).1]
  simp [ReducedRows.toForm, initialForm, rowsToMatrixRect_matrixToRowsRect]

end Correspondence

/-- Compiled code runs the in-place pass. -/
@[csimp]
theorem rowReduceWith_eq_rowReduceWithImpl : @rowReduceWith = @rowReduceWithImpl := by
  funext R n m _ _ _ _ _ quot A
  exact (rowReduceWithImpl_eq quot A).symm

end Hex.Matrix
