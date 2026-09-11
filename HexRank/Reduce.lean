/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Cert
public import HexBareiss.Bareiss

public section

/-!
Rectangular fraction-free Gauss-Jordan elimination with column pivoting and
skipped columns.

`rowReduceWith quot A` scans the columns of `A` in order. At each column it
searches the rows that are not yet pivot rows, in index order, for a nonzero
entry; if none exists the column is skipped, otherwise the row found becomes a
pivot row and every other row is updated by the Bareiss recurrence
`quot (pivot * M[i, j'] - M[i, j] * M[p, j']) prev` in every other column.
Rows are never moved. The pass returns the pivot rows in elimination order,
the pivot columns in increasing order, the last pivot (`det` of the pivot
block), and the reduced matrix.

The loop-step lemmas here are structural: they describe one step of the loop
without any hypothesis on `quot`. The invariant that makes every division
exact and identifies the output is proved in the Mathlib companion.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} {n m : Nat}

/-- The pivot rows, in elimination order, and the pivot columns, strictly
increasing. -/
structure RankProfile (n m : Nat) where
  /-- The number of pivots found. -/
  rank : Nat
  /-- The pivot rows, in elimination order. -/
  rows : Vector (Fin n) rank
  /-- The pivot columns, strictly increasing. -/
  cols : Vector (Fin m) rank

/-- Output of one fraction-free Gauss-Jordan pass. -/
structure ReducedForm (R : Type u) (n m : Nat) where
  /-- The rank profile. -/
  profile : RankProfile n m
  /-- The last pivot: the determinant of the pivot block with its rows in
  elimination order, or `1` when there is no pivot. -/
  denom : R
  /-- `denom` times the reduced row echelon form, rows left in place, with
  every non-pivot row zero. -/
  matrix : Matrix R n m

/-- The least-index row outside `used` whose entry in column `j` is nonzero. -/
@[expose]
def findPivotRow? [Zero R] [DecidableEq R] (M : Matrix R n m) (used : List (Fin n))
    (j : Fin m) : Option (Fin n) :=
  (List.finRange n).find? fun i => decide (i ∉ used) && decide (M[(i, j)] ≠ 0)

/-- A found pivot row is outside `used`, is nonzero in column `j`, and is the
least such row. -/
theorem findPivotRow?_some [Zero R] [DecidableEq R] {M : Matrix R n m} {used : List (Fin n)}
    {j : Fin m} {p : Fin n} (h : findPivotRow? M used j = some p) :
    p ∉ used ∧ M[p][j] ≠ 0 ∧ ∀ i : Fin n, i < p → i ∉ used → M[i][j] = 0 := by
  unfold findPivotRow? at h
  have hmem := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, getElem_pair_eq_nested] at hmem
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro i hi hused
  obtain ⟨_, js, ks, hsplit, hbefore⟩ := List.find?_eq_some_iff_append.mp h
  have hi_mem : i ∈ List.finRange n := List.mem_finRange i
  rw [hsplit, List.mem_append, List.mem_cons] at hi_mem
  rcases hi_mem with hi_js | hi_eq | hi_ks
  · have := hbefore i hi_js
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, getElem_pair_eq_nested, Classical.not_not] at this
    rcases this with h' | h'
    · exact absurd h' hused
    · exact h'
  · exact absurd hi_eq (Fin.ne_of_lt hi)
  · have hsorted := List.pairwise_lt_finRange n
    rw [hsplit] at hsorted
    have hlt := List.pairwise_append.mp hsorted
    have := (List.pairwise_cons.mp hlt.2.1).1 i hi_ks
    exact absurd hi (Fin.lt_asymm this)

/-- When no pivot row is found, every row outside `used` is zero in column `j`. -/
theorem findPivotRow?_none [Zero R] [DecidableEq R] {M : Matrix R n m} {used : List (Fin n)}
    {j : Fin m} (h : findPivotRow? M used j = none) :
    ∀ i : Fin n, i ∉ used → M[i][j] = 0 := by
  intro i hused
  unfold findPivotRow? at h
  have := List.find?_eq_none.mp h i (List.mem_finRange i)
  simp only [Bool.and_eq_true, decide_eq_true_eq, getElem_pair_eq_nested, not_and,
    Classical.not_not] at this
  exact this hused

/-- One column of fraction-free Gauss-Jordan elimination: skip the column if no
non-pivot row is nonzero there, otherwise eliminate every other row against
the pivot row found and record the pivot. -/
@[expose, specialize quot]
def reduceStep [Zero R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (S : ReducedForm R n m) (j : Fin m) : ReducedForm R n m :=
  match findPivotRow? S.matrix S.profile.rows.toList j with
  | none => S
  | some p =>
    let pivot := S.matrix[(p, j)]
    { profile :=
        { rank := S.profile.rank + 1
          rows := S.profile.rows.push p
          cols := S.profile.cols.push j }
      denom := pivot
      matrix := ofFn fun i j' =>
        if i = p then S.matrix[(i, j')]
        else if j' = j then 0
        else quot (pivot * S.matrix[(i, j')] - S.matrix[(i, j)] * S.matrix[(p, j')]) S.denom }

/-- The seed of the pass: no pivots, denominator `1`, the input matrix. -/
@[expose]
def initialForm [One R] (A : Matrix R n m) : ReducedForm R n m :=
  { profile := { rank := 0, rows := #v[], cols := #v[] }, denom := 1, matrix := A }

/-- Rectangular fraction-free Gauss-Jordan elimination with column pivoting and
skipped columns, scanning the columns in order. -/
@[expose, specialize quot]
def rowReduceWith [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (A : Matrix R n m) : ReducedForm R n m :=
  (List.finRange m).foldl (reduceStep quot) (initialForm A)

section StepLemmas

variable [Zero R] [Sub R] [Mul R] [DecidableEq R] {quot : R → R → R}

/-- A column with no pivot leaves the state unchanged. -/
theorem reduceStep_skip {S : ReducedForm R n m} {j : Fin m}
    (h : findPivotRow? S.matrix S.profile.rows.toList j = none) :
    reduceStep quot S j = S := by
  simp [reduceStep, h]

/-- The profile after a pivot step appends the pivot row and column. -/
theorem reduceStep_pivot_profile {S : ReducedForm R n m} {j : Fin m} {p : Fin n}
    (h : findPivotRow? S.matrix S.profile.rows.toList j = some p) :
    (reduceStep quot S j).profile =
      { rank := S.profile.rank + 1, rows := S.profile.rows.push p, cols := S.profile.cols.push j } := by
  simp [reduceStep, h]

/-- The denominator after a pivot step is the pivot entry. -/
theorem reduceStep_pivot_denom {S : ReducedForm R n m} {j : Fin m} {p : Fin n}
    (h : findPivotRow? S.matrix S.profile.rows.toList j = some p) :
    (reduceStep quot S j).denom = S.matrix[p][j] := by
  simp [reduceStep, h]

/-- Entry formula for the matrix after a pivot step. -/
theorem getElem_reduceStep_pivot {S : ReducedForm R n m} {j : Fin m} {p : Fin n}
    (h : findPivotRow? S.matrix S.profile.rows.toList j = some p) (i : Fin n) (j' : Fin m) :
    (reduceStep quot S j).matrix[i][j'] =
      if i = p then S.matrix[i][j']
      else if j' = j then 0
      else quot (S.matrix[p][j] * S.matrix[i][j'] - S.matrix[i][j] * S.matrix[p][j']) S.denom := by
  simp only [reduceStep, h]
  rw [getElem_ofFn]
  simp only [getElem_pair_eq_nested]

end StepLemmas

end Hex.Matrix
