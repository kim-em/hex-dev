/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermite.Contracts
public import HexHermite.Step
public import HexRowReduce.RowEchelon.Contracts

public section

/-! Total rectangular Hermite normal-form sweep. -/

namespace Hex.Matrix

namespace Hermite

/-- Internal result of the accumulator-parametric column sweep. -/
structure Result (α : Type) (n m : Nat) where
  matrix : Matrix Int n m
  pivots : List (Fin m)
  accumulator : α

/-- Search for the first nonzero entry at or below `start`. -/
@[expose]
def findPivot? (M : Matrix Int n m) (col : Fin m) (start : Nat) : Option (Fin n) :=
  (List.finRange n).find? fun i =>
    decide (start ≤ i.val) && decide (M[(i, col)] ≠ 0)

@[expose]
def swapStep (ops : Accumulator α n) (s : Result α n m) (i k : Fin n) :
    Result α n m :=
  if i = k then s else
    { s with
      matrix := Matrix.rowSwap s.matrix i k
      accumulator := ops.swap s.accumulator i k }

@[expose]
def gcdStep (ops : Accumulator α n) (col : Fin m) (i k : Fin n)
    (s : Result α n m) : Result α n m :=
  let b := s.matrix[(k, col)]
  if b = 0 then s else
    let a := s.matrix[(i, col)]
    let (x, y, z, w) := gcdCoeffs a b
    { s with
      matrix := combineRows s.matrix i k x y z w
      accumulator := ops.combine s.accumulator i k x y z w }

@[expose]
def signStep (ops : Accumulator α n) (col : Fin m) (i : Fin n)
    (s : Result α n m) : Result α n m :=
  if s.matrix[(i, col)] < 0 then
    { s with
      matrix := Matrix.rowScale s.matrix i (-1)
      accumulator := ops.negate s.accumulator i }
  else s

@[expose]
def reduceStep (ops : Accumulator α n) (col : Fin m) (pivot row : Fin n)
    (s : Result α n m) : Result α n m :=
  let p := s.matrix[(pivot, col)]
  let q := s.matrix[(row, col)] / p
  if q = 0 then s else
    { s with
      matrix := Matrix.rowAdd s.matrix pivot row (-q)
      accumulator := ops.add s.accumulator pivot row (-q) }

@[simp] theorem swapStep_pivots (ops : Accumulator α n) (s : Result α n m)
    (i k : Fin n) : (swapStep ops s i k).pivots = s.pivots := by
  rw [swapStep]
  split <;> rfl

@[simp] theorem gcdStep_pivots (ops : Accumulator α n) (col : Fin m)
    (i k : Fin n) (s : Result α n m) :
    (gcdStep ops col i k s).pivots = s.pivots := by
  rw [gcdStep]
  split <;> rfl

@[simp] theorem signStep_pivots (ops : Accumulator α n) (col : Fin m)
    (i : Fin n) (s : Result α n m) :
    (signStep ops col i s).pivots = s.pivots := by
  rw [signStep]
  split <;> rfl

@[simp] theorem reduceStep_pivots (ops : Accumulator α n) (col : Fin m)
    (pivot row : Fin n) (s : Result α n m) :
    (reduceStep ops col pivot row s).pivots = s.pivots := by
  rw [reduceStep]
  split <;> rfl

private theorem foldl_pivots {β : Type} (f : Result α n m → β → Result α n m)
    (xs : List β) (s : Result α n m)
    (hf : ∀ s x, (f s x).pivots = s.pivots) :
    (xs.foldl f s).pivots = s.pivots := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      exact hf s x

/-- Clear a chosen pivot column and reduce the entries above its pivot. -/
@[expose]
def clearColumn (ops : Accumulator α n) (s : Result α n m) (col : Fin m)
    (pivotRow found : Fin n) : Result α n m :=
  let s := swapStep ops s pivotRow found
  let s := (List.finRange n).foldl (fun s k =>
    if pivotRow.val < k.val then gcdStep ops col pivotRow k s else s) s
  let s := signStep ops col pivotRow s
  (List.finRange n).foldl (fun s k =>
    if k.val < pivotRow.val then reduceStep ops col pivotRow k s else s) s

@[simp] theorem clearColumn_pivots (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (pivotRow found : Fin n) :
    (clearColumn ops s col pivotRow found).pivots = s.pivots := by
  rw [clearColumn]
  rw [foldl_pivots]
  · rw [signStep_pivots, foldl_pivots]
    · exact swapStep_pivots ops s pivotRow found
    · intro state k
      split <;> simp
  · intro state k
    split <;> simp

/-- Process one column, creating at most one new pivot. -/
@[expose]
def columnStep (ops : Accumulator α n) (s : Result α n m) (col : Fin m) :
    Result α n m :=
  if hr : s.pivots.length < n then
    let pivotRow : Fin n := ⟨s.pivots.length, hr⟩
    match findPivot? s.matrix col s.pivots.length with
    | none => s
    | some found =>
        let s := clearColumn ops s col pivotRow found
        { s with pivots := s.pivots ++ [col] }
  else s

/-- Processing a column preserves the row bound on the pivot count. -/
theorem columnStep_rank_le (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (h : s.pivots.length ≤ n) :
    (columnStep ops s col).pivots.length ≤ n := by
  by_cases hr : s.pivots.length < n
  · rw [columnStep, dif_pos hr]
    cases hp : findPivot? s.matrix col s.pivots.length with
    | none => exact h
    | some found =>
        change ((clearColumn ops s col ⟨s.pivots.length, hr⟩ found).pivots ++ [col]).length ≤ n
        rw [clearColumn_pivots, List.length_append, List.length_singleton]
        omega
  · rw [columnStep, dif_neg hr]
    exact h

/-- The shared bounded Hermite sweep, parameterized by certificate state. -/
@[expose]
def run (ops : Accumulator α n) (A : Matrix Int n m) : Result α n m :=
  (List.finRange m).foldl (columnStep ops)
    { matrix := A, pivots := [], accumulator := ops.init }

/-- Two accumulator runs agree on the computational form and pivot schedule. -/
def Result.Same (s : Result α n m) (t : Result β n m) : Prop :=
  s.matrix = t.matrix ∧ s.pivots = t.pivots

private theorem swapStep_same (ops : Accumulator α n) (ops' : Accumulator β n)
    {s : Result α n m} {t : Result β n m} (h : s.Same t) (i k : Fin n) :
    (swapStep ops s i k).Same (swapStep ops' t i k) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Same] at h
  rcases h with ⟨rfl, rfl⟩
  rw [swapStep, swapStep]
  split <;> exact ⟨rfl, rfl⟩

private theorem gcdStep_same (ops : Accumulator α n) (ops' : Accumulator β n)
    {s : Result α n m} {t : Result β n m} (h : s.Same t)
    (col : Fin m) (i k : Fin n) :
    (gcdStep ops col i k s).Same (gcdStep ops' col i k t) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Same] at h
  rcases h with ⟨rfl, rfl⟩
  rw [gcdStep, gcdStep]
  split <;> exact ⟨rfl, rfl⟩

private theorem signStep_same (ops : Accumulator α n) (ops' : Accumulator β n)
    {s : Result α n m} {t : Result β n m} (h : s.Same t)
    (col : Fin m) (i : Fin n) :
    (signStep ops col i s).Same (signStep ops' col i t) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Same] at h
  rcases h with ⟨rfl, rfl⟩
  rw [signStep, signStep]
  split <;> exact ⟨rfl, rfl⟩

private theorem reduceStep_same (ops : Accumulator α n) (ops' : Accumulator β n)
    {s : Result α n m} {t : Result β n m} (h : s.Same t)
    (col : Fin m) (pivot row : Fin n) :
    (reduceStep ops col pivot row s).Same (reduceStep ops' col pivot row t) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Same] at h
  rcases h with ⟨rfl, rfl⟩
  rw [reduceStep, reduceStep]
  split <;> exact ⟨rfl, rfl⟩

private theorem foldl_same {γ : Type}
    (f : Result α n m → γ → Result α n m)
    (g : Result β n m → γ → Result β n m) (xs : List γ)
    {s : Result α n m} {t : Result β n m} (h : s.Same t)
    (hstep : ∀ {s t} x, s.Same t → (f s x).Same (g t x)) :
    (xs.foldl f s).Same (xs.foldl g t) := by
  induction xs generalizing s t with
  | nil => exact h
  | cons x xs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (hstep x h)

private theorem clearColumn_same (ops : Accumulator α n) (ops' : Accumulator β n)
    {s : Result α n m} {t : Result β n m} (h : s.Same t)
    (col : Fin m) (pivotRow found : Fin n) :
    (clearColumn ops s col pivotRow found).Same
      (clearColumn ops' t col pivotRow found) := by
  rw [clearColumn, clearColumn]
  apply foldl_same
  · exact signStep_same ops ops'
      (foldl_same _ _ _ (swapStep_same ops ops' h pivotRow found) (by
        intro state state' k hstate
        split
        · exact gcdStep_same ops ops' hstate col pivotRow k
        · exact hstate)) col pivotRow
  · intro state state' k hstate
    split
    · exact reduceStep_same ops ops' hstate col pivotRow k
    · exact hstate

private theorem columnStep_same (ops : Accumulator α n) (ops' : Accumulator β n)
    {s : Result α n m} {t : Result β n m} (h : s.Same t) (col : Fin m) :
    (columnStep ops s col).Same (columnStep ops' t col) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Same] at h
  rcases h with ⟨rfl, rfl⟩
  by_cases hr : pivots.length < n
  · rw [columnStep, columnStep, dif_pos hr, dif_pos hr]
    cases hp : findPivot? matrix col pivots.length with
    | none => exact ⟨rfl, rfl⟩
    | some found =>
        simp only
        have hclear := clearColumn_same ops ops'
          (s := { matrix := matrix, pivots := pivots, accumulator := acc })
          (t := { matrix := matrix, pivots := pivots, accumulator := acc' })
          ⟨rfl, rfl⟩ col ⟨pivots.length, hr⟩ found
        exact ⟨hclear.1, congrArg (fun ps => ps ++ [col]) hclear.2⟩
  · rw [columnStep, columnStep, dif_neg hr, dif_neg hr]
    exact ⟨rfl, rfl⟩

/-- The shared schedule produces the same matrix for every accumulator. -/
theorem run_matrix_agree (ops : Accumulator α n) (ops' : Accumulator β n)
    (A : Matrix Int n m) : (run ops A).matrix = (run ops' A).matrix := by
  exact (foldl_same _ _ _ (s :=
    { matrix := A, pivots := [], accumulator := ops.init }) (t :=
    { matrix := A, pivots := [], accumulator := ops'.init }) ⟨rfl, rfl⟩
      (fun col h => columnStep_same ops ops' h col)).1

/-- The shared schedule chooses the same pivots for every accumulator. -/
theorem run_pivots_agree (ops : Accumulator α n) (ops' : Accumulator β n)
    (A : Matrix Int n m) : (run ops A).pivots = (run ops' A).pivots := by
  exact (foldl_same _ _ _ (s :=
    { matrix := A, pivots := [], accumulator := ops.init }) (t :=
    { matrix := A, pivots := [], accumulator := ops'.init }) ⟨rfl, rfl⟩
      (fun col h => columnStep_same ops ops' h col)).2

/-- Convert the stored pivot list to the dependent vector expected by
`RowEchelonData`. -/
@[expose]
def Result.pivotVector (s : Result α n m) : Vector (Fin m) s.pivots.length :=
  ⟨s.pivots.toArray, by simp⟩

/-- The bounded sweep creates no more than one pivot per row. -/
theorem run_rank_le (ops : Accumulator α n) (A : Matrix Int n m) :
    (run ops A).pivots.length ≤ n := by
  rw [run]
  generalize hs : ({ matrix := A, pivots := [], accumulator := ops.init } : Result α n m) = s
  have hinit : s.pivots.length ≤ n := by simp [← hs]
  clear hs A
  induction List.finRange m generalizing s with
  | nil => exact hinit
  | cons col cols ih =>
      rw [List.foldl_cons]
      apply ih
      exact columnStep_rank_le ops s col hinit

end Hermite

/-- Hermite data with the inverse transform accumulated on the value path. -/
structure HermiteData (n m : Nat) where
  rowData : RowEchelonData Int n m
  inverse : Matrix Int n n

/-- The Hermite normal form of `A`. Does not compute the transform. -/
@[expose]
def hnf (A : Matrix Int n m) : Matrix Int n m :=
  (Hermite.run (Hermite.formAccumulator n) A).matrix

/-- The number of nonzero rows of `hnf A`. -/
@[expose]
def hnfRank (A : Matrix Int n m) : Nat :=
  (Hermite.run (Hermite.formAccumulator n) A).pivots.length

/-- The nonzero rows of `hnf A`. -/
@[expose]
def hnfBasis (A : Matrix Int n m) : Matrix Int (hnfRank A) m :=
  Matrix.ofFn fun i j =>
    (hnf A)[(Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i, j)]

/-- Hermite form with rank, pivot columns, and left transform. -/
@[expose]
def hnfData (A : Matrix Int n m) : RowEchelonData Int n m :=
  let result := Hermite.run (Hermite.transformAccumulator n) A
  { rank := result.pivots.length
    echelon := result.matrix
    transform := result.accumulator
    pivotCols := result.pivotVector }

/-- The form-only and transform paths run the same matrix schedule. -/
theorem hnf_eq_hnfData_echelon (A : Matrix Int n m) :
    hnf A = (hnfData A).echelon := by
  exact Hermite.run_matrix_agree (Hermite.formAccumulator n)
    (Hermite.transformAccumulator n) A

/-- The form-only and transform paths report the same rank. -/
theorem hnfRank_eq (A : Matrix Int n m) :
    hnfRank A = (hnfData A).rank := by
  exact congrArg List.length (Hermite.run_pivots_agree
    (Hermite.formAccumulator n) (Hermite.transformAccumulator n) A)

/-- Hermite data with both transform and inverse accumulated in one sweep. -/
@[expose]
def hnfWithInv (A : Matrix Int n m) : HermiteData n m :=
  let result := Hermite.run (Hermite.inverseAccumulator n) A
  { rowData :=
      { rank := result.pivots.length
        echelon := result.matrix
        transform := result.accumulator.transform
        pivotCols := result.pivotVector }
    inverse := result.accumulator.inverse }

end Hex.Matrix
