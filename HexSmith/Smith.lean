/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith.Contracts
public import HexHermite.Step

public section

/-! The accumulator-parametric classical Euclidean Smith pivot loop. -/

namespace Hex.Matrix
namespace Smith

/-- Companion operations run alongside the working-matrix schedule. -/
structure Accumulator (α : Type) (n m : Nat) where
  /-- Initial companion state. -/
  init : α
  /-- Update the companion for a row swap. -/
  rowSwap : α → Fin n → Fin n → α
  /-- Update the companion for a determinant-one two-row combination. -/
  rowCombine : α → Fin n → Fin n → Int → Int → Int → Int → α
  /-- Update the companion for row negation. -/
  rowNegate : α → Fin n → α
  /-- Update the companion for adding a row multiple. -/
  rowAdd : α → Fin n → Fin n → Int → α
  /-- Update the companion for a column swap. -/
  colSwap : α → Fin m → Fin m → α
  /-- Update the companion for adding a column multiple. -/
  colAdd : α → Fin m → Fin m → Int → α
  /-- Update the companion for a determinant-one two-column combination. -/
  colCombine : α → Fin m → Fin m → Int → Int → Int → Int → α

/-- The form-only companion. All operations erase to `Unit`, so this path
allocates no transform matrices. -/
@[expose]
def formAccumulator (n m : Nat) : Accumulator Unit n m where
  init := ()
  rowSwap acc _ _ := acc
  rowCombine acc _ _ _ _ _ _ := acc
  rowNegate acc _ := acc
  rowAdd acc _ _ _ := acc
  colSwap acc _ _ := acc
  colAdd acc _ _ _ := acc
  colCombine acc _ _ _ _ _ _ := acc

/-- The four transforms accumulated by the data-producing path. -/
structure Transforms (n m : Nat) where
  /-- Accumulated left transform. -/
  left : Matrix Int n n
  /-- Explicit inverse of the left transform. -/
  leftInv : Matrix Int n n
  /-- Accumulated right transform. -/
  right : Matrix Int m m
  /-- Explicit inverse of the right transform. -/
  rightInv : Matrix Int m m

/-- Companion which maintains `leftInv = left⁻¹` and
`rightInv = right⁻¹` by applying inverse elementary operations on the
opposite side. -/
@[expose]
def transformAccumulator (n m : Nat) : Accumulator (Transforms n m) n m where
  init :=
    { left := Matrix.identity n
      leftInv := Matrix.identity n
      right := Matrix.identity m
      rightInv := Matrix.identity m }
  rowSwap acc i k :=
    { acc with
      left := Matrix.rowSwap acc.left i k
      leftInv := Matrix.colSwap acc.leftInv i k }
  rowCombine acc i k a b c d :=
    { acc with
      left := Hermite.combineRows acc.left i k a b c d
      leftInv := Hermite.combineCols acc.leftInv i k d (-c) (-b) a }
  rowNegate acc i :=
    { acc with
      left := Matrix.rowScale acc.left i (-1)
      leftInv := Matrix.colScale acc.leftInv i (-1) }
  rowAdd acc src dst c :=
    { acc with
      left := Matrix.rowAdd acc.left src dst c
      leftInv := Matrix.colAdd acc.leftInv dst src (-c) }
  colSwap acc i k :=
    { acc with
      right := Matrix.colSwap acc.right i k
      rightInv := Matrix.rowSwap acc.rightInv i k }
  colAdd acc src dst c :=
    { acc with
      right := Matrix.colAdd acc.right src dst c
      rightInv := Matrix.rowAdd acc.rightInv dst src (-c) }
  colCombine acc i k a b c d :=
    { acc with
      right := Hermite.combineCols acc.right i k a b c d
      rightInv := Hermite.combineRows acc.rightInv i k d (-c) (-b) a }

/-- Internal result: the current matrix, completed diagonal entries, and the
optional companion state. -/
structure Result (α : Type) (n m : Nat) where
  /-- Current working matrix. -/
  matrix : Matrix Int n m
  /-- Completed positive diagonal prefix. -/
  diag : List Int
  /-- Companion state accumulated alongside the matrix operations. -/
  accumulator : α

/-- Row-major entries eligible to become the next pivot. -/
@[expose]
def pivotCandidates (M : Matrix Int n m) (start : Nat) : List (Fin n × Fin m) :=
  ((List.finRange n).flatMap fun i =>
    (List.finRange m).map fun j => (i, j)).filter fun q =>
      decide (start ≤ q.1.val) && decide (start ≤ q.2.val) &&
        decide (M[q] ≠ 0)

/-- Retain the earlier pivot unless the new candidate has strictly smaller
absolute value. -/
@[expose]
def choosePivot (M : Matrix Int n m) (best : Option (Fin n × Fin m))
    (q : Fin n × Fin m) : Option (Fin n × Fin m) :=
  match best with
  | none => some q
  | some old => if M[q].natAbs < M[old].natAbs then some q else best

/-- Choose a nonzero entry of least absolute value in the trailing block.
Ties retain the first entry in row-major order. -/
@[expose]
def findPivot? (M : Matrix Int n m) (start : Nat) : Option (Fin n × Fin m) :=
  (pivotCandidates M start).foldl (choosePivot M) none

private theorem foldl_choose_mem (M : Matrix Int n m) (xs : List (Fin n × Fin m))
    (best : Option (Fin n × Fin m)) (q : Fin n × Fin m)
    (h : xs.foldl (choosePivot M) best = some q) : q ∈ xs ∨ best = some q := by
  induction xs generalizing best with
  | nil => exact Or.inr h
  | cons x xs ih =>
      simp only [List.foldl_cons] at h
      rcases ih (choosePivot M best x) h with hmem | hchosen
      · exact Or.inl (List.mem_cons_of_mem x hmem)
      · unfold choosePivot at hchosen
        split at hchosen
        · exact Or.inl (by simp_all)
        · split at hchosen
          · exact Or.inl (by simp_all)
          · exact Or.inr hchosen

/-- A chosen pivot lies in the trailing block and is nonzero. -/
theorem findPivot?_some {M : Matrix Int n m} {start : Nat}
    {q : Fin n × Fin m} (h : findPivot? M start = some q) :
    start ≤ q.1.val ∧ start ≤ q.2.val ∧ M[q] ≠ 0 := by
  have hmem : q ∈ pivotCandidates M start := by
    rcases foldl_choose_mem M (pivotCandidates M start) none q h with hmem | hnone
    · exact hmem
    · contradiction
  simp only [pivotCandidates, List.mem_filter, List.mem_flatMap, List.mem_map,
    Bool.and_eq_true, decide_eq_true_eq] at hmem
  exact ⟨hmem.2.1.1, hmem.2.1.2, hmem.2.2⟩

/-- If no pivot is found, the entire trailing block is zero. -/
theorem findPivot?_none {M : Matrix Int n m} {start : Nat}
    (h : findPivot? M start = none) (row : Fin n) (col : Fin m)
    (hr : start ≤ row.val) (hc : start ≤ col.val) : M[(row, col)] = 0 := by
  apply Classical.not_not.mp
  intro hne
  have hmem : (row, col) ∈ pivotCandidates M start := by
    simp only [pivotCandidates, List.mem_filter, List.mem_flatMap, List.mem_map,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨row, List.mem_finRange row, col, List.mem_finRange col, rfl⟩,
      ⟨⟨hr, hc⟩, hne⟩⟩
  have hstep : ∀ best, choosePivot M best (row, col) ≠ none := by
    intro best
    cases best with
    | none => simp [choosePivot]
    | some old => simp only [choosePivot]; split <;> simp
  have hnotNone : ∀ (xs : List (Fin n × Fin m)) (best : Option (Fin n × Fin m)),
      best ≠ none → xs.foldl (choosePivot M) best ≠ none := by
    intro xs
    induction xs with
    | nil => simpa
    | cons x xs ih =>
        intro best hbest
        simp only [List.foldl_cons]
        apply ih
        cases best with
        | none => simp [choosePivot]
        | some old => simp only [choosePivot]; split <;> simp
  have hprefix : ∀ (before after : List (Fin n × Fin m)),
      before.foldl (choosePivot M) none ≠ none →
      (before ++ after).foldl (choosePivot M) none ≠ none := by
    intro before after hbefore
    rw [List.foldl_append]
    exact hnotNone after _ hbefore
  obtain ⟨before, after, heq⟩ := List.append_of_mem hmem
  unfold findPivot? at h
  rw [heq] at h
  simp only [List.foldl_append, List.foldl_cons] at h
  have hchosen : choosePivot M (before.foldl (choosePivot M) none) (row, col) ≠ none :=
    hstep _
  exact hnotNone after _ hchosen h

/-- First nonzero entry below the pivot in its column. -/
@[expose]
def findColumn? (M : Matrix Int n m) (pivotRow : Fin n) (pivotCol : Fin m) :
    Option (Fin n) :=
  (List.finRange n).find? fun i =>
    decide (pivotRow.val < i.val) && decide (M[(i, pivotCol)] ≠ 0)

/-- A successful column search returns a strictly lower nonzero entry. -/
theorem findColumn?_some {M : Matrix Int n m} {pivotRow : Fin n}
    {pivotCol : Fin m} {row : Fin n}
    (h : findColumn? M pivotRow pivotCol = some row) :
    pivotRow.val < row.val ∧ M[(row, pivotCol)] ≠ 0 := by
  have hp := List.find?_some h
  simpa [findColumn?, Bool.and_eq_true, decide_eq_true_eq] using hp

/-- A failed column search means the eligible part of the pivot column is
zero. -/
theorem findColumn?_none {M : Matrix Int n m} {pivotRow : Fin n}
    {pivotCol : Fin m} (h : findColumn? M pivotRow pivotCol = none)
    (row : Fin n) (hr : pivotRow.val < row.val) : M[(row, pivotCol)] = 0 := by
  have hp := List.find?_eq_none.mp h row (List.mem_finRange row)
  apply Classical.not_not.mp
  intro hne
  apply hp
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hr, hne⟩

/-- First nonzero entry to the right of the pivot in its row. -/
@[expose]
def findRow? (M : Matrix Int n m) (pivotRow : Fin n) (pivotCol : Fin m) :
    Option (Fin m) :=
  (List.finRange m).find? fun j =>
    decide (pivotCol.val < j.val) && decide (M[(pivotRow, j)] ≠ 0)

/-- A successful row search returns a strictly rightward nonzero entry. -/
theorem findRow?_some {M : Matrix Int n m} {pivotRow : Fin n}
    {pivotCol col : Fin m} (h : findRow? M pivotRow pivotCol = some col) :
    pivotCol.val < col.val ∧ M[(pivotRow, col)] ≠ 0 := by
  have hp := List.find?_some h
  simpa [findRow?, Bool.and_eq_true, decide_eq_true_eq] using hp

/-- A failed row search means the eligible part of the pivot row is zero. -/
theorem findRow?_none {M : Matrix Int n m} {pivotRow : Fin n}
    {pivotCol : Fin m} (h : findRow? M pivotRow pivotCol = none)
    (col : Fin m) (hc : pivotCol.val < col.val) : M[(pivotRow, col)] = 0 := by
  have hp := List.find?_eq_none.mp h col (List.mem_finRange col)
  apply Classical.not_not.mp
  intro hne
  apply hp
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hc, hne⟩

/-- First trailing entry not divisible by the cleared pivot. -/
@[expose]
def findBad? (M : Matrix Int n m) (pivotRow : Fin n) (pivotCol : Fin m)
    (p : Int) : Option (Fin n × Fin m) :=
  ((List.finRange n).flatMap fun i =>
    (List.finRange m).map fun j => (i, j)).find? fun q =>
      decide (pivotRow.val < q.1.val) &&
      decide (pivotCol.val < q.2.val) &&
      decide (M[(q.1, q.2)] % p ≠ 0)

/-- A successful divisibility search returns a strictly trailing entry which
is not divisible by the pivot. -/
theorem findBad?_some {M : Matrix Int n m} {pivotRow : Fin n}
    {pivotCol : Fin m} {p : Int} {q : Fin n × Fin m}
    (h : findBad? M pivotRow pivotCol p = some q) :
    pivotRow.val < q.1.val ∧ pivotCol.val < q.2.val ∧
      M[(q.1, q.2)] % p ≠ 0 := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

/-- A failed divisibility search means every strictly trailing entry is
divisible by the pivot. -/
theorem findBad?_none {M : Matrix Int n m} {pivotRow : Fin n}
    {pivotCol : Fin m} {p : Int}
    (h : findBad? M pivotRow pivotCol p = none)
    (row : Fin n) (col : Fin m) (hr : pivotRow.val < row.val)
    (hc : pivotCol.val < col.val) : p ∣ M[(row, col)] := by
  have hmem : (row, col) ∈ (List.finRange n).flatMap fun i =>
      (List.finRange m).map fun j => (i, j) := by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨row, List.mem_finRange row, col, List.mem_finRange col, rfl⟩
  have hp := List.find?_eq_none.mp h (row, col) hmem
  apply Int.dvd_of_emod_eq_zero
  apply Classical.not_not.mp
  intro hne
  apply hp
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hr, hc⟩, hne⟩

/-- Swap two working rows and update the companion state. -/
@[expose]
def swapRows (ops : Accumulator α n m) (s : Result α n m) (i k : Fin n) :
    Result α n m :=
  if i = k then s else
    { s with
      matrix := Matrix.rowSwap s.matrix i k
      accumulator := ops.rowSwap s.accumulator i k }

/-- Swap two working columns and update the companion state. -/
@[expose]
def swapCols (ops : Accumulator α n m) (s : Result α n m) (i k : Fin m) :
    Result α n m :=
  if i = k then s else
    { s with
      matrix := Matrix.colSwap s.matrix i k
      accumulator := ops.colSwap s.accumulator i k }

/-- Clear one entry below the pivot, using exact subtraction when possible
and the determinant-one extended-GCD step otherwise. -/
@[expose]
def clearColumn (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow row : Fin n) (pivotCol : Fin m) : Result α n m :=
  let p := s.matrix[(pivotRow, pivotCol)]
  let b := s.matrix[(row, pivotCol)]
  if b % p = 0 then
    let c := -(HexArith.Int.exactDiv b p)
    { s with
      matrix := Matrix.rowAdd s.matrix pivotRow row c
      accumulator := ops.rowAdd s.accumulator pivotRow row c }
  else
    let (a, b', c, d) := Hermite.gcdCoeffs p b
    { s with
      matrix := Hermite.combineRows s.matrix pivotRow row a b' c d
      accumulator := ops.rowCombine s.accumulator pivotRow row a b' c d }

/-- Clear one entry to the right of the pivot. -/
@[expose]
def clearRow (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow : Fin n) (pivotCol col : Fin m) : Result α n m :=
  let p := s.matrix[(pivotRow, pivotCol)]
  let b := s.matrix[(pivotRow, col)]
  if b % p = 0 then
    let c := -(HexArith.Int.exactDiv b p)
    { s with
      matrix := Matrix.colAdd s.matrix pivotCol col c
      accumulator := ops.colAdd s.accumulator pivotCol col c }
  else
    let (a, b', c, d) := Hermite.gcdCoeffs p b
    { s with
      matrix := Hermite.combineCols s.matrix pivotCol col a b' c d
      accumulator := ops.colCombine s.accumulator pivotCol col a b' c d }

/-- Fuse the divisibility repair with the column elimination which strictly
shrinks the pivot: add the offending row to the pivot row, then immediately
apply the extended-GCD column step. -/
@[expose]
def repair (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow row : Fin n) (pivotCol col : Fin m) : Result α n m :=
  let matrix := Matrix.rowAdd s.matrix row pivotRow 1
  let accumulator := ops.rowAdd s.accumulator row pivotRow 1
  let p := matrix[(pivotRow, pivotCol)]
  let b := matrix[(pivotRow, col)]
  let (a, b', c, d) := Hermite.gcdCoeffs p b
  { s with
    matrix := Hermite.combineCols matrix pivotCol col a b' c d
    accumulator := ops.colCombine accumulator pivotCol col a b' c d }

/-- Reduce one diagonal stage. Fuel makes the executable boundary visibly
total; the bound pays for every plain clearing step at every possible strict
decrease of the positive pivot. -/
@[expose]
def reduceFuel (ops : Accumulator α n m) (pivotRow : Fin n) (pivotCol : Fin m) :
    Nat → Result α n m → Result α n m
  | 0, s => s
  | fuel + 1, s =>
      let p := s.matrix[(pivotRow, pivotCol)]
      if p = 0 then s
      else
        match findColumn? s.matrix pivotRow pivotCol with
        | some row => reduceFuel ops pivotRow pivotCol fuel
            (clearColumn ops s pivotRow row pivotCol)
        | none =>
            match findRow? s.matrix pivotRow pivotCol with
            | some col => reduceFuel ops pivotRow pivotCol fuel
                (clearRow ops s pivotRow pivotCol col)
            | none =>
                if p < 0 then
                  let normalized := { s with
                    matrix := Matrix.rowScale s.matrix pivotRow (-1)
                    accumulator := ops.rowNegate s.accumulator pivotRow }
                  let p' := normalized.matrix[(pivotRow, pivotCol)]
                  match findBad? normalized.matrix pivotRow pivotCol p' with
                  | none => normalized
                  | some q => reduceFuel ops pivotRow pivotCol fuel
                      (repair ops normalized pivotRow q.1 pivotCol q.2)
                else
                  match findBad? s.matrix pivotRow pivotCol p with
                  | none => s
                  | some q => reduceFuel ops pivotRow pivotCol fuel
                      (repair ops s pivotRow q.1 pivotCol q.2)

/-- Run one pivot after it has been moved into place. -/
@[expose]
def reduce (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow : Fin n) (pivotCol : Fin m) : Result α n m :=
  let p := s.matrix[(pivotRow, pivotCol)]
  let fuel := (p.natAbs + 1) * (n + m + 1) + 1
  reduceFuel ops pivotRow pivotCol fuel s

/-- At most `min n m` leading positions can become pivots. -/
@[expose]
def runFuel (ops : Accumulator α n m) : Nat → Result α n m → Result α n m
  | 0, s => s
  | fuel + 1, s =>
      let k := s.diag.length
      if hn : k < n then
        if hm : k < m then
          match findPivot? s.matrix k with
          | none => s
          | some q =>
              let pivotRow : Fin n := ⟨k, hn⟩
              let pivotCol : Fin m := ⟨k, hm⟩
              let moved := swapCols ops (swapRows ops s pivotRow q.1) pivotCol q.2
              let reduced := reduce ops moved pivotRow pivotCol
              let p := reduced.matrix[(pivotRow, pivotCol)]
              if p = 0 then reduced
              else runFuel ops fuel { reduced with diag := reduced.diag ++ [p] }
        else s
      else s

/-- Run the deterministic Smith schedule with the requested companion. -/
@[expose]
def run (ops : Accumulator α n m) (A : Matrix Int n m) : Result α n m :=
  runFuel ops (Nat.min n m) { matrix := A, diag := [], accumulator := ops.init }

/-- Turn the completed diagonal list into its length-indexed vector. -/
@[expose]
def Result.diagVector (s : Result α n m) : Vector Int s.diag.length :=
  ⟨s.diag.toArray, by simp⟩

/-- Indexing the vector view returns the corresponding completed-list entry. -/
@[simp] theorem Result.diagVector_get (s : Result α n m)
    (i : Fin s.diag.length) : s.diagVector.get i = s.diag.get i := by
  change s.diag.toArray[i.val] = s.diag[i.val]
  apply List.getElem_toArray

end Smith

/-- The canonical Smith matrix, computed without allocating transforms. -/
@[expose]
def snf (A : Matrix Int n m) : Matrix Int n m :=
  (Smith.run (Smith.formAccumulator n m) A).matrix

/-- The number of nonzero diagonal entries in `snf A`. -/
@[expose]
def snfRank (A : Matrix Int n m) : Nat :=
  (Smith.run (Smith.formAccumulator n m) A).diag.length

/-- The positive invariant factors in divisibility-chain order. -/
@[expose]
def invariantFactors (A : Matrix Int n m) : Vector Int (snfRank A) :=
  (Smith.run (Smith.formAccumulator n m) A).diagVector

/-- Smith form together with both transforms and their explicit inverses. -/
@[expose]
def snfData (A : Matrix Int n m) : SmithData n m :=
  let result := Smith.run (Smith.transformAccumulator n m) A
  { rank := result.diag.length
    diag := result.diagVector
    left := result.accumulator.left
    leftInv := result.accumulator.leftInv
    right := result.accumulator.right
    rightInv := result.accumulator.rightInv }

end Hex.Matrix
