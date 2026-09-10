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

/-- Convert the stored pivot list to the dependent vector expected by
`RowEchelonData`. -/
@[expose]
def Result.pivotVector (s : Result α n m) : Vector (Fin m) s.pivots.length :=
  ⟨s.pivots.toArray, by simp⟩

@[simp] theorem Result.pivotVector_get (s : Result α n m)
    (i : Fin s.pivots.length) : s.pivotVector.get i = s.pivots.get i := by
  change s.pivots.toArray[i.val] = s.pivots[i.val]
  apply List.getElem_toArray

/-- Search for the first nonzero entry at or below `start`. -/
@[expose]
def findPivot? (M : Matrix Int n m) (col : Fin m) (start : Nat) : Option (Fin n) :=
  (List.finRange n).find? fun i =>
    decide (start ≤ i.val) && decide (M[(i, col)] ≠ 0)

/-- A successful pivot search returns an eligible nonzero row. -/
theorem findPivot?_some {M : Matrix Int n m} {col : Fin m} {start : Nat}
    {found : Fin n} (h : findPivot? M col start = some found) :
    start ≤ found.val ∧ M[(found, col)] ≠ 0 := by
  have hp := List.find?_some h
  simpa [findPivot?, Bool.and_eq_true, decide_eq_true_eq] using hp

/-- A failed pivot search means every eligible row is zero in that column. -/
theorem findPivot?_none {M : Matrix Int n m} {col : Fin m} {start : Nat}
    (h : findPivot? M col start = none) (row : Fin n) (hr : start ≤ row.val) :
    M[(row, col)] = 0 := by
  have hp := List.find?_eq_none.mp h row (List.mem_finRange row)
  have hnn : ¬M[(row, col)] ≠ 0 := by
    intro hne
    apply hp
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hr, hne⟩
  exact Classical.not_not.mp hnn

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

/-- Swapping a selected nonzero row into the pivot position leaves a nonzero
pivot entry. -/
theorem swapStep_pivot_ne (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (pivot found : Fin n) (hfound : s.matrix[(found, col)] ≠ 0) :
    (swapStep ops s pivot found).matrix[(pivot, col)] ≠ 0 := by
  rw [swapStep]
  split
  · rename_i h
    subst found
    exact hfound
  · rename_i hne
    dsimp only
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap]
    simp only [ite_eq_right hne, ite_eq_left]
    simpa only [Matrix.getElem_pair_eq_nested] using hfound

/-- Swapping two zero entries leaves the whole selected column unchanged. -/
theorem swapStep_zero (ops : Accumulator α n) (s : Result α n m)
    (j : Fin m) (i k row : Fin n) (hi : s.matrix[(i, j)] = 0)
    (hk : s.matrix[(k, j)] = 0) :
    (swapStep ops s i k).matrix[(row, j)] = s.matrix[(row, j)] := by
  have hi' : s.matrix[i][j] = 0 := by
    simpa only [Matrix.getElem_pair_eq_nested] using hi
  have hk' : s.matrix[k][j] = 0 := by
    simpa only [Matrix.getElem_pair_eq_nested] using hk
  rw [swapStep]
  split
  · rfl
  · dsimp only
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap]
    by_cases hrk : row = k
    · subst row
      simpa only [ite_eq_left, Matrix.getElem_pair_eq_nested] using hi'.trans hk'.symm
    · by_cases hri : row = i
      · subst row
        simp only [ite_eq_right hrk, ite_eq_left, Matrix.getElem_pair_eq_nested]
        exact hk'.trans hi'.symm
      · simp [hrk, hri, Matrix.getElem_pair_eq_nested]

/-- A nontrivial extended-GCD step makes the pivot positive and clears the
selected lower entry. -/
theorem gcdStep_column (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (i k : Fin n) (hik : i ≠ k) (hb : s.matrix[(k, col)] ≠ 0) :
    0 < (gcdStep ops col i k s).matrix[(i, col)] ∧
      (gcdStep ops col i k s).matrix[(k, col)] = 0 := by
  have hspec := gcdCoeffs_apply (a := s.matrix[(i, col)])
    (b := s.matrix[(k, col)]) hb
  rcases hc : gcdCoeffs s.matrix[(i, col)] s.matrix[(k, col)] with ⟨x, y, z, w⟩
  rw [hc] at hspec
  dsimp only at hspec
  rw [gcdStep, ite_eq_right hb]
  dsimp only
  rw [hc]
  dsimp only [Prod.fst, Prod.snd]
  change 0 < (combineRows s.matrix i k x y z w)[(i, col)] ∧
    (combineRows s.matrix i k x y z w)[(k, col)] = 0
  simp only [getElem_combineRows, Matrix.getElem_pair_eq_nested]
  simp only [Matrix.getElem_pair_eq_nested] at hspec
  simpa [hik.symm] using hspec

/-- An extended-GCD step preserves a nonzero pivot and clears its target row. -/
theorem gcdStep_ne_zero (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (i k : Fin n) (hik : i ≠ k)
    (hi : s.matrix[(i, col)] ≠ 0) :
    (gcdStep ops col i k s).matrix[(i, col)] ≠ 0 ∧
      (gcdStep ops col i k s).matrix[(k, col)] = 0 := by
  by_cases hb : s.matrix[(k, col)] = 0
  · rw [gcdStep, ite_eq_left hb]
    exact ⟨hi, hb⟩
  · have h := gcdStep_column ops s col i k hik hb
    exact ⟨Int.ne_of_gt h.1, h.2⟩

/-- A two-row gcd update does not alter any third row. -/
theorem gcdStep_other (ops : Accumulator α n) (s : Result α n m)
    (col j : Fin m) (i k row : Fin n) (hri : row ≠ i) (hrk : row ≠ k) :
    (gcdStep ops col i k s).matrix[(row, j)] = s.matrix[(row, j)] := by
  rw [gcdStep]
  split
  · rfl
  · dsimp only
    rw [Matrix.getElem_pair_eq_nested]
    rw [getElem_combineRows]
    simp [hri, hrk, Matrix.getElem_pair_eq_nested]

/-- A gcd update of two zero entries in another column leaves that column
unchanged. -/
theorem gcdStep_zero (ops : Accumulator α n) (s : Result α n m)
    (col j : Fin m) (i k row : Fin n) (hi : s.matrix[(i, j)] = 0)
    (hk : s.matrix[(k, j)] = 0) :
    (gcdStep ops col i k s).matrix[(row, j)] = s.matrix[(row, j)] := by
  rw [gcdStep]
  split
  · rfl
  · dsimp only
    rw [Matrix.getElem_pair_eq_nested]
    rw [getElem_combineRows]
    simp only [Matrix.getElem_pair_eq_nested] at hi hk ⊢
    by_cases hri : row = i <;> by_cases hrk : row = k <;>
      simp_all

/-- Sign normalization makes every nonzero selected pivot positive. -/
theorem signStep_column (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (i : Fin n) (hne : s.matrix[(i, col)] ≠ 0) :
    0 < (signStep ops col i s).matrix[(i, col)] := by
  rw [signStep]
  split
  · rename_i hneg
    dsimp only
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale]
    simp only [ite_eq_left]
    simp only [Matrix.getElem_pair_eq_nested] at hneg hne ⊢
    omega
  · rename_i hnneg
    simp only [Matrix.getElem_pair_eq_nested] at hnneg hne ⊢
    omega

/-- Sign normalization changes only the selected row. -/
theorem signStep_other (ops : Accumulator α n) (s : Result α n m)
    (col j : Fin m) (i row : Fin n) (hri : row ≠ i) :
    (signStep ops col i s).matrix[(row, j)] = s.matrix[(row, j)] := by
  rw [signStep]
  split
  · dsimp only
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale]
    simp [hri, Matrix.getElem_pair_eq_nested]
  · rfl

/-- Scaling a zero entry during sign normalization leaves it zero and hence
unchanged. -/
theorem signStep_zero (ops : Accumulator α n) (s : Result α n m)
    (col j : Fin m) (i : Fin n) (hi : s.matrix[(i, j)] = 0) (row : Fin n) :
    (signStep ops col i s).matrix[(row, j)] = s.matrix[(row, j)] := by
  have hi' : (s.matrix.getRow i)[j] = 0 := by
    simpa only [Matrix.getElem_pair_eq_nested, Matrix.getElem_eq_getRow] using hi
  by_cases hri : row = i
  · subst row
    rw [signStep]
    split
    · dsimp only
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale]
      simp only [ite_eq_left, Matrix.getElem_pair_eq_nested]
      simp [hi']
    · rfl
  · exact signStep_other ops s col j i row hri

/-- Reduction above a positive pivot replaces the selected entry by its
Euclidean remainder. -/
theorem reduceStep_column (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (pivot row : Fin n) :
    (reduceStep ops col pivot row s).matrix[(row, col)] =
      s.matrix[(row, col)] % s.matrix[(pivot, col)] := by
  let p := s.matrix[(pivot, col)]
  let x := s.matrix[(row, col)]
  let q := x / p
  have hdiv : q * p + x % p = x := by
    exact Int.ediv_mul_add_emod x p
  rw [reduceStep]
  change (if q = 0 then s else
    { s with
      matrix := Matrix.rowAdd s.matrix pivot row (-q)
      accumulator := ops.add s.accumulator pivot row (-q) }).matrix[(row, col)] =
      x % p
  split
  · rename_i hq
    change x = x % p
    rw [hq, Int.zero_mul, Int.zero_add] at hdiv
    exact hdiv.symm
  · dsimp only
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd]
    simp only [ite_eq_left]
    simp only [q, p, x, Matrix.getElem_pair_eq_nested] at hdiv ⊢
    calc
      s.matrix[row][col] +
          -(s.matrix[row][col] / s.matrix[pivot][col]) * s.matrix[pivot][col] =
          (s.matrix[row][col] / s.matrix[pivot][col] * s.matrix[pivot][col] +
            s.matrix[row][col] % s.matrix[pivot][col]) +
            -(s.matrix[row][col] / s.matrix[pivot][col]) * s.matrix[pivot][col] := by
              rw [hdiv]
      _ = s.matrix[row][col] % s.matrix[pivot][col] := by
        rw [Int.neg_mul]
        omega

/-- Reduction changes only its destination row. -/
theorem reduceStep_other (ops : Accumulator α n) (s : Result α n m)
    (col j : Fin m) (pivot target row : Fin n) (hrt : row ≠ target) :
    (reduceStep ops col pivot target s).matrix[(row, j)] = s.matrix[(row, j)] := by
  rw [reduceStep]
  split
  · rfl
  · dsimp only
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd]
    simp [hrt, Matrix.getElem_pair_eq_nested]

/-- Adding a multiple of a row whose selected entry is zero leaves that
column unchanged. -/
theorem reduceStep_zero (ops : Accumulator α n) (s : Result α n m)
    (col j : Fin m) (pivot target row : Fin n)
    (hp : s.matrix[(pivot, j)] = 0) :
    (reduceStep ops col pivot target s).matrix[(row, j)] = s.matrix[(row, j)] := by
  have hp' : (s.matrix.getRow pivot)[j] = 0 := by
    simpa only [Matrix.getElem_pair_eq_nested, Matrix.getElem_eq_getRow] using hp
  by_cases hrt : row = target
  · subst row
    rw [reduceStep]
    split
    · rfl
    · dsimp only
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd]
      simp only [ite_eq_left, Matrix.getElem_pair_eq_nested]
      simp [hp']
  · exact reduceStep_other ops s col j pivot target row hrt

/-- Entries reduced above a positive pivot lie in its canonical residue
interval. -/
theorem reduceStep_bounds (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (pivot row : Fin n) (hp : 0 < s.matrix[(pivot, col)]) :
    0 ≤ (reduceStep ops col pivot row s).matrix[(row, col)] ∧
      (reduceStep ops col pivot row s).matrix[(row, col)] <
        s.matrix[(pivot, col)] := by
  rw [reduceStep_column ops s col pivot row]
  exact ⟨Int.emod_nonneg _ (Int.ne_of_gt hp), Int.emod_lt_of_pos _ hp⟩

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

private def gcdSweepStep (ops : Accumulator α n) (col : Fin m) (pivot : Fin n)
    (s : Result α n m) (k : Fin n) : Result α n m :=
  if pivot.val < k.val then gcdStep ops col pivot k s else s

private theorem gcdSweep_other (ops : Accumulator α n) (col : Fin m)
    (pivot row : Fin n) (xs : List (Fin n)) (s : Result α n m)
    (hrp : row ≠ pivot) (hrxs : row ∉ xs) :
    (xs.foldl (gcdSweepStep ops col pivot) s).matrix[(row, col)] =
      s.matrix[(row, col)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons k xs ih =>
      rw [List.foldl_cons]
      have hrk : row ≠ k := by
        intro h
        subst k
        exact hrxs (List.mem_cons_self ..)
      have hrrest : row ∉ xs := by
        intro h
        exact hrxs (List.mem_cons_of_mem _ h)
      rw [ih _ hrrest]
      unfold gcdSweepStep
      split
      · exact gcdStep_other ops s col col pivot k row hrp hrk
      · rfl

private theorem gcdSweep_column (ops : Accumulator α n) (col : Fin m)
    (pivot : Fin n) (xs : List (Fin n)) (s : Result α n m)
    (hxs : xs.Nodup) (hp : s.matrix[(pivot, col)] ≠ 0) :
    let t := xs.foldl (gcdSweepStep ops col pivot) s
    t.matrix[(pivot, col)] ≠ 0 ∧
      ∀ k ∈ xs, pivot.val < k.val → t.matrix[(k, col)] = 0 := by
  induction xs generalizing s with
  | nil => exact ⟨hp, by simp⟩
  | cons k xs ih =>
      have hkxs : k ∉ xs := (List.nodup_cons.mp hxs).1
      have hrest : xs.Nodup := (List.nodup_cons.mp hxs).2
      rw [List.foldl_cons]
      unfold gcdSweepStep
      split
      · rename_i hpk
        have hstep := gcdStep_ne_zero ops s col pivot k (by omega) hp
        have htail := ih (gcdStep ops col pivot k s) hrest hstep.1
        refine ⟨htail.1, ?_⟩
        intro row hmem hprow
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst row
          exact (gcdSweep_other ops col pivot k xs
            (gcdStep ops col pivot k s) (by omega) hkxs).trans hstep.2
        · exact htail.2 row hmem hprow
      · rename_i hnot
        have htail := ih s hrest hp
        refine ⟨htail.1, ?_⟩
        intro row hmem hprow
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst row
          omega
        · exact htail.2 row hmem hprow

private theorem gcdSweep_prior (ops : Accumulator α n) (col j : Fin m)
    (pivot : Fin n) (xs : List (Fin n)) (s : Result α n m)
    (hz : ∀ row : Fin n, pivot.val ≤ row.val → s.matrix[(row, j)] = 0)
    (row : Fin n) :
    (xs.foldl (gcdSweepStep ops col pivot) s).matrix[(row, j)] =
      s.matrix[(row, j)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons k xs ih =>
      rw [List.foldl_cons]
      unfold gcdSweepStep
      split
      · rename_i hpk
        have hstep (r : Fin n) :
            (gcdStep ops col pivot k s).matrix[(r, j)] = s.matrix[(r, j)] :=
          gcdStep_zero ops s col j pivot k r (hz pivot (by omega)) (hz k (by omega))
        have hz' : ∀ r : Fin n, pivot.val ≤ r.val →
            (gcdStep ops col pivot k s).matrix[(r, j)] = 0 := by
          intro r hr
          exact (hstep r).trans (hz r hr)
        exact (ih (gcdStep ops col pivot k s) hz').trans (hstep row)
      · exact ih s hz

private def reduceSweepStep (ops : Accumulator α n) (col : Fin m) (pivot : Fin n)
    (s : Result α n m) (k : Fin n) : Result α n m :=
  if k.val < pivot.val then reduceStep ops col pivot k s else s

private theorem reduceSweep_other (ops : Accumulator α n) (col : Fin m)
    (pivot row : Fin n) (xs : List (Fin n)) (s : Result α n m)
    (hrxs : row ∉ xs) :
    (xs.foldl (reduceSweepStep ops col pivot) s).matrix[(row, col)] =
      s.matrix[(row, col)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons k xs ih =>
      rw [List.foldl_cons]
      have hrk : row ≠ k := by
        intro h
        subst k
        exact hrxs (List.mem_cons_self ..)
      have hrrest : row ∉ xs := by
        intro h
        exact hrxs (List.mem_cons_of_mem _ h)
      rw [ih _ hrrest]
      unfold reduceSweepStep
      split
      · exact reduceStep_other ops s col col pivot k row hrk
      · rfl

private theorem reduceSweep_pivot (ops : Accumulator α n) (col : Fin m)
    (pivot : Fin n) (xs : List (Fin n)) (s : Result α n m) :
    (xs.foldl (reduceSweepStep ops col pivot) s).matrix[(pivot, col)] =
      s.matrix[(pivot, col)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons k xs ih =>
      rw [List.foldl_cons, ih]
      unfold reduceSweepStep
      split
      · exact reduceStep_other ops s col col pivot k pivot (by omega)
      · rfl

private theorem reduceSweep_of_le (ops : Accumulator α n) (col : Fin m)
    (pivot row : Fin n) (xs : List (Fin n)) (s : Result α n m)
    (hpr : pivot.val ≤ row.val) :
    (xs.foldl (reduceSweepStep ops col pivot) s).matrix[(row, col)] =
      s.matrix[(row, col)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons k xs ih =>
      rw [List.foldl_cons, ih]
      unfold reduceSweepStep
      split
      · exact reduceStep_other ops s col col pivot k row (by omega)
      · rfl

private theorem reduceSweep_prior (ops : Accumulator α n) (col j : Fin m)
    (pivot : Fin n) (xs : List (Fin n)) (s : Result α n m)
    (hp : s.matrix[(pivot, j)] = 0) (row : Fin n) :
    (xs.foldl (reduceSweepStep ops col pivot) s).matrix[(row, j)] =
      s.matrix[(row, j)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons k xs ih =>
      rw [List.foldl_cons]
      unfold reduceSweepStep
      split
      · have hstep (r : Fin n) :
            (reduceStep ops col pivot k s).matrix[(r, j)] = s.matrix[(r, j)] :=
          reduceStep_zero ops s col j pivot k r hp
        have hp' : (reduceStep ops col pivot k s).matrix[(pivot, j)] = 0 :=
          (hstep pivot).trans hp
        exact (ih (reduceStep ops col pivot k s) hp').trans (hstep row)
      · exact ih s hp

private theorem reduceSweep_bounds (ops : Accumulator α n) (col : Fin m)
    (pivot : Fin n) (xs : List (Fin n)) (s : Result α n m)
    (hxs : xs.Nodup) (hp : 0 < s.matrix[(pivot, col)]) :
    let t := xs.foldl (reduceSweepStep ops col pivot) s
    0 < t.matrix[(pivot, col)] ∧
      ∀ k ∈ xs, k.val < pivot.val →
        0 ≤ t.matrix[(k, col)] ∧ t.matrix[(k, col)] < t.matrix[(pivot, col)] := by
  induction xs generalizing s with
  | nil => exact ⟨hp, by simp⟩
  | cons k xs ih =>
      have hkxs : k ∉ xs := (List.nodup_cons.mp hxs).1
      have hrest : xs.Nodup := (List.nodup_cons.mp hxs).2
      rw [List.foldl_cons]
      unfold reduceSweepStep
      split
      · rename_i hkp
        have hbound := reduceStep_bounds ops s col pivot k hp
        have hpstep : 0 < (reduceStep ops col pivot k s).matrix[(pivot, col)] := by
          rw [reduceStep_other ops s col col pivot k pivot (by omega)]
          exact hp
        have htail := ih (reduceStep ops col pivot k s) hrest hpstep
        refine ⟨htail.1, ?_⟩
        intro row hmem hrowp
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst row
          have hkeep := reduceSweep_other ops col pivot k xs
            (reduceStep ops col pivot k s) hkxs
          have hpkeep := reduceSweep_pivot ops col pivot xs
            (reduceStep ops col pivot k s)
          unfold reduceSweepStep at hkeep hpkeep
          rw [hkeep, hpkeep]
          rw [reduceStep_other ops s col col pivot k pivot (by omega)]
          exact hbound
        · exact htail.2 row hmem hrowp
      · rename_i hnot
        have htail := ih s hrest hp
        refine ⟨htail.1, ?_⟩
        intro row hmem hrowp
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst row
          omega
        · exact htail.2 row hmem hrowp

/-- Clearing a column establishes its positive pivot, zeros below, and
canonical residues above. -/
theorem clearColumn_column (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (pivot found : Fin n)
    (hfound : s.matrix[(found, col)] ≠ 0) :
    let t := clearColumn ops s col pivot found
    0 < t.matrix[(pivot, col)] ∧
      (∀ row : Fin n, pivot.val < row.val → t.matrix[(row, col)] = 0) ∧
      (∀ row : Fin n, row.val < pivot.val →
        0 ≤ t.matrix[(row, col)] ∧
          t.matrix[(row, col)] < t.matrix[(pivot, col)]) := by
  let s0 := swapStep ops s pivot found
  let s1 := (List.finRange n).foldl (gcdSweepStep ops col pivot) s0
  let s2 := signStep ops col pivot s1
  let s3 := (List.finRange n).foldl (reduceSweepStep ops col pivot) s2
  have hp0 : s0.matrix[(pivot, col)] ≠ 0 :=
    swapStep_pivot_ne ops s col pivot found hfound
  have hg := gcdSweep_column ops col pivot (List.finRange n) s0
    (List.nodup_finRange n) hp0
  have hp2 : 0 < s2.matrix[(pivot, col)] := signStep_column ops s1 col pivot hg.1
  have hr := reduceSweep_bounds ops col pivot (List.finRange n) s2
    (List.nodup_finRange n) hp2
  change 0 < s3.matrix[(pivot, col)] ∧
    (∀ row : Fin n, pivot.val < row.val → s3.matrix[(row, col)] = 0) ∧
    (∀ row : Fin n, row.val < pivot.val →
      0 ≤ s3.matrix[(row, col)] ∧ s3.matrix[(row, col)] < s3.matrix[(pivot, col)])
  refine ⟨hr.1, ?_, ?_⟩
  · intro row hprow
    have hreduce := reduceSweep_of_le ops col pivot row (List.finRange n) s2 (by omega)
    have hsign := signStep_other ops s1 col col pivot row (by omega)
    have hzero := hg.2 row (List.mem_finRange row) hprow
    exact hreduce.trans (hsign.trans hzero)
  · intro row hrowp
    exact hr.2 row (List.mem_finRange row) hrowp

/-- Clearing a later column preserves every entry of an earlier column whose
active rows are all zero. -/
theorem clearColumn_prior (ops : Accumulator α n) (s : Result α n m)
    (col j : Fin m) (pivot found : Fin n) (hfound : pivot.val ≤ found.val)
    (hz : ∀ row : Fin n, pivot.val ≤ row.val → s.matrix[(row, j)] = 0)
    (row : Fin n) :
    (clearColumn ops s col pivot found).matrix[(row, j)] = s.matrix[(row, j)] := by
  let s0 := swapStep ops s pivot found
  let s1 := (List.finRange n).foldl (gcdSweepStep ops col pivot) s0
  let s2 := signStep ops col pivot s1
  let s3 := (List.finRange n).foldl (reduceSweepStep ops col pivot) s2
  have hswap (r : Fin n) : s0.matrix[(r, j)] = s.matrix[(r, j)] :=
    swapStep_zero ops s j pivot found r (hz pivot (by omega)) (hz found hfound)
  have hz0 : ∀ r : Fin n, pivot.val ≤ r.val → s0.matrix[(r, j)] = 0 := by
    intro r hr
    exact (hswap r).trans (hz r hr)
  have hgcd (r : Fin n) : s1.matrix[(r, j)] = s0.matrix[(r, j)] :=
    gcdSweep_prior ops col j pivot (List.finRange n) s0 hz0 r
  have hp1 : s1.matrix[(pivot, j)] = 0 :=
    (hgcd pivot).trans (hz0 pivot (by omega))
  have hsign (r : Fin n) : s2.matrix[(r, j)] = s1.matrix[(r, j)] :=
    signStep_zero ops s1 col j pivot hp1 r
  have hp2 : s2.matrix[(pivot, j)] = 0 := (hsign pivot).trans hp1
  have hreduce (r : Fin n) : s3.matrix[(r, j)] = s2.matrix[(r, j)] :=
    reduceSweep_prior ops col j pivot (List.finRange n) s2 hp2 r
  exact (hreduce row).trans ((hsign row).trans ((hgcd row).trans (hswap row)))

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
  · rw [columnStep, dite_eq_left hr]
    cases hp : findPivot? s.matrix col s.pivots.length with
    | none => exact h
    | some found =>
        change ((clearColumn ops s col ⟨s.pivots.length, hr⟩ found).pivots ++ [col]).length ≤ n
        rw [clearColumn_pivots, List.length_append, List.length_singleton]
        omega
  · rw [columnStep, dite_eq_right hr]
    exact h

/-- The shared bounded Hermite sweep, parameterized by certificate state. -/
@[expose]
def run (ops : Accumulator α n) (A : Matrix Int n m) : Result α n m :=
  (List.finRange m).foldl (columnStep ops)
    { matrix := A, pivots := [], accumulator := ops.init }

/-- Fraction-free row-profile state. The elimination matrix is used only to
choose a row permutation and pivot columns; the Hermite computation itself
still consists exclusively of unimodular integer row operations. -/
structure Profile (n m : Nat) where
  matrix : Matrix Int n m
  row : Nat
  previous : Int
  swaps : List (Fin n × Fin n)
  pivots : List (Fin m)

/-- One rectangular fraction-free elimination update below a selected pivot. -/
def profileEliminate (M : Matrix Int n m) (row : Fin n) (col : Fin m)
    (previous : Int) : Matrix Int n m :=
  let pivot := M[(row, col)]
  Matrix.ofFn fun i j =>
    if row.val < i.val then
      if j = col then 0
      else if col.val < j.val then
        (pivot * M[(i, j)] - M[(i, col)] * M[(row, j)]) / previous
      else M[(i, j)]
    else M[(i, j)]

/-- Extend a fraction-free row profile by one input column. -/
def profileStep (s : Profile n m) (col : Fin m) : Profile n m :=
  if hr : s.row < n then
    match findPivot? s.matrix col s.row with
    | none => s
    | some found =>
        let row : Fin n := ⟨s.row, hr⟩
        let swapped := Matrix.rowSwap s.matrix row found
        let pivot := swapped[(row, col)]
        { matrix := profileEliminate swapped row col s.previous
          row := s.row + 1
          previous := pivot
          swaps := s.swaps ++ [(row, found)]
          pivots := s.pivots ++ [col] }
  else s

/-- A fraction-free row rank profile, represented as the row swaps needed to
place independent rows first and their increasing pivot columns. -/
def rankProfile (A : Matrix Int n m) : Profile n m :=
  (List.finRange m).foldl profileStep
    { matrix := A, row := 0, previous := 1, swaps := [], pivots := [] }

/-- Normalize one nonzero pivot and reduce every entry above it. A zero entry
is left alone, making the rank profile a checked optimization hint rather than
a partiality assumption. -/
def normalizeRow (ops : Accumulator α n) (s : Result α n m)
    (col : Fin m) (pivot : Fin n) : Result α n m :=
  if s.matrix[(pivot, col)] = 0 then s else
    let s := signStep ops col pivot s
    (List.finRange n).foldl (fun s row =>
      if row.val < pivot.val then reduceStep ops col pivot row s else s) s

/-- Clear one earlier pivot from the row currently being admitted, then
restore the canonical residues above that pivot immediately. -/
def clearPrior (ops : Accumulator α n) (pivots : List (Fin m))
    (row : Fin n) (s : Result α n m) (pivot : Fin n) : Result α n m :=
  if _hpr : pivot.val < row.val then
    if hp : pivot.val < pivots.length then
      let col := pivots.get ⟨pivot.val, hp⟩
      normalizeRow ops (gcdStep ops col pivot row s) col pivot
    else s
  else s

/-- Admit one profiled row into the growing principal Hermite block. -/
def admitRow (ops : Accumulator α n) (pivots : List (Fin m))
    (s : Result α n m) (row : Fin n) : Result α n m :=
  let s := (List.finRange n).foldl (clearPrior ops pivots row) s
  if hp : row.val < pivots.length then
    normalizeRow ops s (pivots.get ⟨row.val, hp⟩) row
  else s

/-- Rank-profiled principal-block Hermite candidate. Each prefix is restored
before another row is admitted, preventing uncontrolled suffix growth. -/
@[expose]
def principalCore (ops : Accumulator α n) (A : Matrix Int n m)
    (profile : Profile n m) : Result α n m :=
  let initial : Result α n m :=
    { matrix := A, pivots := profile.pivots, accumulator := ops.init }
  let permuted := profile.swaps.foldl (fun s swap =>
    swapStep ops s swap.1 swap.2) initial
  (List.finRange n).foldl (admitRow ops profile.pivots) permuted

/-- Compute the row profile and run the principal-block candidate. -/
@[expose]
def principalRun (ops : Accumulator α n) (A : Matrix Int n m) : Result α n m :=
  principalCore ops A (rankProfile A)

/-- Use the bounded-growth candidate when its complete HNF shape checks;
otherwise retain the proven column sweep as a total fallback. -/
@[expose]
def checkedRun (ops : Accumulator α n) (A : Matrix Int n m) : Result α n m :=
  let candidate := principalRun ops A
  if isHNFForm candidate.matrix candidate.pivots.length candidate.pivotVector then
    candidate
  else
    run ops A

/-- Shape invariant after processing the first `bound` columns. -/
private structure PrefixForm (s : Result α n m) (bound : Nat) : Prop where
  rank_le_n : s.pivots.length ≤ n
  rank_le_bound : s.pivots.length ≤ bound
  pivot_lt_bound : ∀ i : Fin s.pivots.length, (s.pivots.get i).val < bound
  pivots_sorted : ∀ i j : Fin s.pivots.length, i < j → s.pivots.get i < s.pivots.get j
  leading : ∀ (i : Fin s.pivots.length) (row : Fin n), row.val = i.val →
    ∀ j : Fin m, j < s.pivots.get i → s.matrix[(row, j)] = 0
  pivot_pos : ∀ (i : Fin s.pivots.length) (row : Fin n), row.val = i.val →
    0 < s.matrix[(row, s.pivots.get i)]
  below_zero : ∀ (i : Fin s.pivots.length) (row : Fin n), i.val < row.val →
    s.matrix[(row, s.pivots.get i)] = 0
  above_bounds : ∀ (i : Fin s.pivots.length) (row : Fin n), row.val < i.val →
    0 ≤ s.matrix[(row, s.pivots.get i)] ∧
      ∀ pivotRow : Fin n, pivotRow.val = i.val →
        s.matrix[(row, s.pivots.get i)] < s.matrix[(pivotRow, s.pivots.get i)]
  zero_prefix : ∀ row : Fin n, s.pivots.length ≤ row.val →
    ∀ j : Fin m, j.val < bound → s.matrix[(row, j)] = 0

private def prefixRun (ops : Accumulator α n) (A : Matrix Int n m) (bound : Nat) :
    Result α n m :=
  ((List.finRange m).take bound).foldl (columnStep ops)
    { matrix := A, pivots := [], accumulator := ops.init }

private theorem prefixRun_zero (ops : Accumulator α n) (A : Matrix Int n m) :
    PrefixForm (prefixRun ops A 0) 0 := by
  refine { rank_le_n := by simp [prefixRun]
           rank_le_bound := by simp [prefixRun]
           pivot_lt_bound := ?_
           pivots_sorted := ?_
           leading := ?_
           pivot_pos := ?_
           below_zero := ?_
           above_bounds := ?_
           zero_prefix := ?_ }
  all_goals simp [prefixRun]

private theorem prefixRun_succ (ops : Accumulator α n) (A : Matrix Int n m)
    {bound : Nat} (hbound : bound < m) :
    prefixRun ops A (bound + 1) =
      columnStep ops (prefixRun ops A bound) ⟨bound, hbound⟩ := by
  unfold prefixRun
  rw [List.take_succ_eq_append_getElem]
  · rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    congr 1
    apply Fin.ext
    rw [List.getElem_finRange]
    rfl
  · simpa using hbound

private theorem PrefixForm.extend {s : Result α n m} {bound : Nat}
    (h : PrefixForm s bound) (col : Fin m) (hcol : col.val = bound)
    (hz : ∀ row : Fin n, s.pivots.length ≤ row.val → s.matrix[(row, col)] = 0) :
    PrefixForm s (bound + 1) := by
  refine
    { rank_le_n := h.rank_le_n
      rank_le_bound := by
        have hr := h.rank_le_bound
        omega
      pivot_lt_bound := fun i => by have := h.pivot_lt_bound i; omega
      pivots_sorted := h.pivots_sorted
      leading := h.leading
      pivot_pos := h.pivot_pos
      below_zero := h.below_zero
      above_bounds := h.above_bounds
      zero_prefix := ?_ }
  intro row hr j hj
  by_cases hjb : j.val < bound
  · exact h.zero_prefix row hr j hjb
  · have hjc : j = col := by
      apply Fin.ext
      omega
    subst j
    exact hz row hr

private theorem get_append_old (ps : List (Fin m)) (col : Fin m)
    (i : Fin ps.length) :
    (ps ++ [col]).get ⟨i.val, by simp; omega⟩ = ps.get i := by
  simp [List.get_eq_getElem]

private theorem get_append_last (ps : List (Fin m)) (col : Fin m) :
    (ps ++ [col]).get ⟨ps.length, by simp⟩ = col := by
  simp [List.get_eq_getElem]

private theorem PrefixForm.appendClear {s : Result α n m} {bound : Nat}
    (h : PrefixForm s bound) (ops : Accumulator α n) (col : Fin m)
    (hcol : col.val = bound) (hr : s.pivots.length < n) (found : Fin n)
    (hfoundGe : s.pivots.length ≤ found.val)
    (hfound : s.matrix[(found, col)] ≠ 0) :
    let pivot : Fin n := ⟨s.pivots.length, hr⟩
    let t := clearColumn ops s col pivot found
    PrefixForm { t with pivots := s.pivots ++ [col] } (bound + 1) := by
  let pivot : Fin n := ⟨s.pivots.length, hr⟩
  let t := clearColumn ops s col pivot found
  have hcurrent := clearColumn_column ops s col pivot found hfound
  have prior (row : Fin n) (j : Fin m) (hj : j.val < bound) :
      t.matrix[(row, j)] = s.matrix[(row, j)] := by
    exact clearColumn_prior ops s col j pivot found hfoundGe
      (fun active ha => h.zero_prefix active ha j hj) row
  dsimp only [t, pivot] at prior hcurrent
  have oldGet (i : Fin s.pivots.length) :
      (s.pivots ++ [col]).get ⟨i.val, by simp; omega⟩ = s.pivots.get i :=
    get_append_old s.pivots col i
  have lastGet :
      (s.pivots ++ [col]).get ⟨s.pivots.length, by simp⟩ = col :=
    get_append_last s.pivots col
  refine
    { rank_le_n := by simp; omega
      rank_le_bound := by simp; have := h.rank_le_bound; omega
      pivot_lt_bound := ?_
      pivots_sorted := ?_
      leading := ?_
      pivot_pos := ?_
      below_zero := ?_
      above_bounds := ?_
      zero_prefix := ?_ }
  · intro i
    by_cases hi : i.val < s.pivots.length
    · let old : Fin s.pivots.length := ⟨i.val, hi⟩
      have hei : i = ⟨old.val, by simp; omega⟩ := Fin.ext rfl
      have hget : (s.pivots ++ [col]).get i = s.pivots.get old := by
        rw [hei]
        exact oldGet old
      rw [hget]
      have := h.pivot_lt_bound old
      omega
    · have hiBound : i.val < s.pivots.length + 1 := by simpa using i.isLt
      have hilast : i.val = s.pivots.length := by omega
      have hei : i = ⟨s.pivots.length, by simp⟩ := Fin.ext hilast
      have hget : (s.pivots ++ [col]).get i = col := by
        rw [hei]
        exact lastGet
      rw [hget]
      omega
  · intro i j hij
    by_cases hj : j.val < s.pivots.length
    · have hi : i.val < s.pivots.length := by omega
      let oi : Fin s.pivots.length := ⟨i.val, hi⟩
      let oj : Fin s.pivots.length := ⟨j.val, hj⟩
      have hei : i = ⟨oi.val, by simp; omega⟩ := Fin.ext rfl
      have hej : j = ⟨oj.val, by simp; omega⟩ := Fin.ext rfl
      have hgeti : (s.pivots ++ [col]).get i = s.pivots.get oi := by
        rw [hei]; exact oldGet oi
      have hgetj : (s.pivots ++ [col]).get j = s.pivots.get oj := by
        rw [hej]; exact oldGet oj
      rw [hgeti, hgetj]
      exact h.pivots_sorted oi oj (by omega)
    · have hjBound : j.val < s.pivots.length + 1 := by simpa using j.isLt
      have hjlast : j.val = s.pivots.length := by omega
      have hi : i.val < s.pivots.length := by omega
      let oi : Fin s.pivots.length := ⟨i.val, hi⟩
      have hei : i = ⟨oi.val, by simp; omega⟩ := Fin.ext rfl
      have hej : j = ⟨s.pivots.length, by simp⟩ := Fin.ext hjlast
      have hgeti : (s.pivots ++ [col]).get i = s.pivots.get oi := by
        rw [hei]; exact oldGet oi
      have hgetj : (s.pivots ++ [col]).get j = col := by
        rw [hej]; exact lastGet
      rw [hgeti, hgetj]
      have := h.pivot_lt_bound oi
      omega
  · intro i row hrow j hj
    by_cases hi : i.val < s.pivots.length
    · let old : Fin s.pivots.length := ⟨i.val, hi⟩
      have hei : i = ⟨old.val, by simp; omega⟩ := Fin.ext rfl
      have hget : (s.pivots ++ [col]).get i = s.pivots.get old := by
        rw [hei]; exact oldGet old
      rw [hget] at hj
      rw [prior row j (by have := h.pivot_lt_bound old; omega)]
      exact h.leading old row (by omega) j hj
    · have hiBound : i.val < s.pivots.length + 1 := by simpa using i.isLt
      have hilast : i.val = s.pivots.length := by omega
      have hei : i = ⟨s.pivots.length, by simp⟩ := Fin.ext hilast
      have hget : (s.pivots ++ [col]).get i = col := by
        rw [hei]; exact lastGet
      rw [hget] at hj
      rw [prior row j (by omega)]
      exact h.zero_prefix row (by omega) j (by omega)
  · intro i row hrow
    by_cases hi : i.val < s.pivots.length
    · let old : Fin s.pivots.length := ⟨i.val, hi⟩
      have hei : i = ⟨old.val, by simp; omega⟩ := Fin.ext rfl
      have hget : (s.pivots ++ [col]).get i = s.pivots.get old := by
        rw [hei]; exact oldGet old
      rw [hget]
      rw [prior row (s.pivots.get old) (h.pivot_lt_bound old)]
      exact h.pivot_pos old row (by omega)
    · have hiBound : i.val < s.pivots.length + 1 := by simpa using i.isLt
      have hilast : i.val = s.pivots.length := by omega
      have hei : i = ⟨s.pivots.length, by simp⟩ := Fin.ext hilast
      have hget : (s.pivots ++ [col]).get i = col := by
        rw [hei]; exact lastGet
      rw [hget]
      have hroweq : row = pivot := Fin.ext (by omega)
      subst row
      exact hcurrent.1
  · intro i row hbelow
    by_cases hi : i.val < s.pivots.length
    · let old : Fin s.pivots.length := ⟨i.val, hi⟩
      have hei : i = ⟨old.val, by simp; omega⟩ := Fin.ext rfl
      have hget : (s.pivots ++ [col]).get i = s.pivots.get old := by
        rw [hei]; exact oldGet old
      rw [hget]
      rw [prior row (s.pivots.get old) (h.pivot_lt_bound old)]
      exact h.below_zero old row (by omega)
    · have hiBound : i.val < s.pivots.length + 1 := by simpa using i.isLt
      have hilast : i.val = s.pivots.length := by omega
      have hei : i = ⟨s.pivots.length, by simp⟩ := Fin.ext hilast
      have hget : (s.pivots ++ [col]).get i = col := by
        rw [hei]; exact lastGet
      rw [hget]
      exact hcurrent.2.1 row (by omega)

  · intro i row habove
    by_cases hi : i.val < s.pivots.length
    · let old : Fin s.pivots.length := ⟨i.val, hi⟩
      have hei : i = ⟨old.val, by simp; omega⟩ := Fin.ext rfl
      have hget : (s.pivots ++ [col]).get i = s.pivots.get old := by
        rw [hei]; exact oldGet old
      rw [hget]
      have hold := h.above_bounds old row (by omega)
      rw [prior row (s.pivots.get old) (h.pivot_lt_bound old)]
      refine ⟨hold.1, ?_⟩
      intro pivotRow hpivotRow
      rw [prior pivotRow (s.pivots.get old) (h.pivot_lt_bound old)]
      exact hold.2 pivotRow hpivotRow
    · have hiBound : i.val < s.pivots.length + 1 := by simpa using i.isLt
      have hilast : i.val = s.pivots.length := by omega
      have hei : i = ⟨s.pivots.length, by simp⟩ := Fin.ext hilast
      have hget : (s.pivots ++ [col]).get i = col := by
        rw [hei]; exact lastGet
      rw [hget]
      have hb := hcurrent.2.2 row (by omega)
      refine ⟨hb.1, ?_⟩
      intro pivotRow hpivotRow
      have heq : pivotRow = pivot := Fin.ext (by omega)
      subst pivotRow
      exact hb.2
  · intro row hzero j hj
    simp only [List.length_append, List.length_singleton] at hzero
    by_cases hjb : j.val < bound
    · rw [prior row j hjb]
      exact h.zero_prefix row (by omega) j hjb
    · have hjc : j = col := by apply Fin.ext; omega
      subst j
      exact hcurrent.2.1 row (by omega)

private theorem columnStep_prefix (ops : Accumulator α n) {s : Result α n m}
    {bound : Nat} (h : PrefixForm s bound) (col : Fin m) (hcol : col.val = bound) :
    PrefixForm (columnStep ops s col) (bound + 1) := by
  by_cases hr : s.pivots.length < n
  · rw [columnStep, dite_eq_left hr]
    cases hp : findPivot? s.matrix col s.pivots.length with
    | none =>
        exact h.extend col hcol (fun row hrow => findPivot?_none hp row hrow)
    | some found =>
        have hf := findPivot?_some hp
        have ha := h.appendClear ops col hcol hr found hf.1 hf.2
        simp only
        have hpiv := clearColumn_pivots ops s col ⟨s.pivots.length, hr⟩ found
        simpa [hpiv] using ha
  · rw [columnStep, dite_eq_right hr]
    exact h.extend col hcol (fun row hrow => by
      have hn := h.rank_le_n
      omega)

private theorem prefixRun_form (ops : Accumulator α n) (A : Matrix Int n m)
    (bound : Nat) (hbound : bound ≤ m) : PrefixForm (prefixRun ops A bound) bound := by
  induction bound with
  | zero => exact prefixRun_zero ops A
  | succ bound ih =>
      have hlt : bound < m := by omega
      rw [prefixRun_succ ops A hlt]
      exact columnStep_prefix ops (ih (by omega)) ⟨bound, hlt⟩ rfl

private theorem run_form (ops : Accumulator α n) (A : Matrix Int n m) :
    PrefixForm (run ops A) m := by
  have h := prefixRun_form ops A m (Nat.le_refl m)
  have ht : (List.finRange m).take m = List.finRange m := by
    simpa using (@List.take_length (Fin m) (List.finRange m))
  simpa [prefixRun, run, ht] using h

private theorem PrefixForm.hnfForm {s : Result α n m}
    (h : PrefixForm s m) :
    HNFForm s.matrix s.pivots.length s.pivotVector := by
  refine ⟨h.rank_le_n, h.rank_le_bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simpa only [Result.pivotVector_get] using h.pivots_sorted i j hij
  · intro i row hrow j hj
    simpa only [Result.pivotVector_get] using h.leading i row hrow j hj
  · intro i row hrow
    simpa only [Result.pivotVector_get] using h.pivot_pos i row hrow
  · intro i row hrow
    simpa only [Result.pivotVector_get] using h.below_zero i row hrow
  · intro row hrow
    apply Vector.ext
    intro col hcol
    simp only [Vector.getElem_zero]
    change s.matrix[row][(⟨col, hcol⟩ : Fin m)] = 0
    simpa only [Matrix.getElem_pair_eq_nested] using
      h.zero_prefix row hrow ⟨col, hcol⟩ (by omega)
  · intro i row hrow
    simpa only [Result.pivotVector_get] using (h.above_bounds i row hrow).1
  · intro i row hrow pivotRow hpivotRow
    simpa only [Result.pivotVector_get] using
      (h.above_bounds i row hrow).2 pivotRow hpivotRow

private theorem checkedRun_form (ops : Accumulator α n) (A : Matrix Int n m) :
    HNFForm (checkedRun ops A).matrix (checkedRun ops A).pivots.length
      (checkedRun ops A).pivotVector := by
  by_cases h : isHNFForm (principalRun ops A).matrix
      (principalRun ops A).pivots.length (principalRun ops A).pivotVector = true
  · have hc : checkedRun ops A = principalRun ops A := by
      rw [checkedRun]
      exact ite_eq_left h
    rw [hc]
    exact (isHNFForm_iff _ _ _).mp h
  · have hc : checkedRun ops A = run ops A := by
      rw [checkedRun]
      exact ite_eq_right h
    rw [hc]
    exact (run_form ops A).hnfForm

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

private theorem normalizeRow_same (ops : Accumulator α n)
    (ops' : Accumulator β n) {s : Result α n m} {t : Result β n m}
    (h : s.Same t) (col : Fin m) (pivot : Fin n) :
    (normalizeRow ops s col pivot).Same (normalizeRow ops' t col pivot) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Same] at h
  rcases h with ⟨rfl, rfl⟩
  rw [normalizeRow, normalizeRow]
  split
  · exact ⟨rfl, rfl⟩
  · apply foldl_same
    · exact signStep_same ops ops' ⟨rfl, rfl⟩ col pivot
    · intro state state' row hstate
      split
      · exact reduceStep_same ops ops' hstate col pivot row
      · exact hstate

private theorem clearPrior_same (ops : Accumulator α n)
    (ops' : Accumulator β n) (pivots : List (Fin m)) (row : Fin n)
    {s : Result α n m} {t : Result β n m} (h : s.Same t) (pivot : Fin n) :
    (clearPrior ops pivots row s pivot).Same
      (clearPrior ops' pivots row t pivot) := by
  rw [clearPrior, clearPrior]
  split
  · split
    · exact normalizeRow_same ops ops'
        (gcdStep_same ops ops' h _ pivot row) _ pivot
    · exact h
  · exact h

private theorem admitRow_same (ops : Accumulator α n)
    (ops' : Accumulator β n) (pivots : List (Fin m))
    {s : Result α n m} {t : Result β n m} (h : s.Same t) (row : Fin n) :
    (admitRow ops pivots s row).Same (admitRow ops' pivots t row) := by
  rw [admitRow, admitRow]
  have hc := foldl_same (clearPrior ops pivots row) (clearPrior ops' pivots row)
    (List.finRange n) h (fun pivot hp => clearPrior_same ops ops' pivots row hp pivot)
  split
  · exact normalizeRow_same ops ops' hc _ row
  · exact hc

private theorem principalRun_same (ops : Accumulator α n)
    (ops' : Accumulator β n) (A : Matrix Int n m) :
    (principalRun ops A).Same (principalRun ops' A) := by
  rw [principalRun, principalRun, principalCore, principalCore]
  let profile := rankProfile A
  have hp :
      (profile.swaps.foldl (fun s swap => swapStep ops s swap.1 swap.2)
        { matrix := A, pivots := profile.pivots, accumulator := ops.init }).Same
      (profile.swaps.foldl (fun s swap => swapStep ops' s swap.1 swap.2)
        { matrix := A, pivots := profile.pivots, accumulator := ops'.init }) := by
    exact foldl_same _ _ profile.swaps ⟨rfl, rfl⟩ (by
      intro state state' swap hs
      exact swapStep_same ops ops' hs swap.1 swap.2)
  have hr := foldl_same (admitRow ops profile.pivots)
    (admitRow ops' profile.pivots) (List.finRange n) hp (by
      intro state state' row hs
      exact admitRow_same ops ops' profile.pivots hs row)
  exact hr

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
  · rw [columnStep, columnStep, dite_eq_left hr, dite_eq_left hr]
    cases hp : findPivot? matrix col pivots.length with
    | none => exact ⟨rfl, rfl⟩
    | some found =>
        simp only
        have hclear := clearColumn_same ops ops'
          (s := { matrix := matrix, pivots := pivots, accumulator := acc })
          (t := { matrix := matrix, pivots := pivots, accumulator := acc' })
          ⟨rfl, rfl⟩ col ⟨pivots.length, hr⟩ found
        exact ⟨hclear.1, congrArg (fun ps => ps ++ [col]) hclear.2⟩
  · rw [columnStep, columnStep, dite_eq_right hr, dite_eq_right hr]
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

private theorem checkedRun_same (ops : Accumulator α n)
    (ops' : Accumulator β n) (A : Matrix Int n m) :
    (checkedRun ops A).Same (checkedRun ops' A) := by
  have hp := principalRun_same ops ops' A
  have hc : isHNFForm (principalRun ops A).matrix
      (principalRun ops A).pivots.length (principalRun ops A).pivotVector =
      isHNFForm (principalRun ops' A).matrix
        (principalRun ops' A).pivots.length (principalRun ops' A).pivotVector := by
    rcases hpo : principalRun ops A with ⟨matrix, pivots, acc⟩
    rcases hpo' : principalRun ops' A with ⟨matrix', pivots', acc'⟩
    rw [hpo, hpo'] at hp
    simp only [Result.Same, Result.pivotVector] at hp ⊢
    rcases hp with ⟨rfl, rfl⟩
    rfl
  rw [checkedRun, checkedRun, hc]
  split
  · exact hp
  · exact ⟨run_matrix_agree ops ops' A, run_pivots_agree ops ops' A⟩

theorem checkedRun_matrix_agree (ops : Accumulator α n)
    (ops' : Accumulator β n) (A : Matrix Int n m) :
    (checkedRun ops A).matrix = (checkedRun ops' A).matrix :=
  (checkedRun_same ops ops' A).1

theorem checkedRun_pivots_agree (ops : Accumulator α n)
    (ops' : Accumulator β n) (A : Matrix Int n m) :
    (checkedRun ops A).pivots = (checkedRun ops' A).pivots :=
  (checkedRun_same ops ops' A).2

/-- A relation between accumulator runs that also tracks a homomorphism on
the companion state. -/
private def Result.Mapped (f : α → β) (s : Result α n m) (t : Result β n m) : Prop :=
  s.matrix = t.matrix ∧ s.pivots = t.pivots ∧ f s.accumulator = t.accumulator

private structure Accumulator.Hom (f : α → β)
    (ops : Accumulator α n) (ops' : Accumulator β n) : Prop where
  init : f ops.init = ops'.init
  swap : ∀ a i k, f (ops.swap a i k) = ops'.swap (f a) i k
  combine : ∀ a i k x y z w,
    f (ops.combine a i k x y z w) = ops'.combine (f a) i k x y z w
  negate : ∀ a i, f (ops.negate a i) = ops'.negate (f a) i
  add : ∀ a i k c, f (ops.add a i k c) = ops'.add (f a) i k c

private theorem swapStep_mapped (f : α → β) (ops : Accumulator α n)
    (ops' : Accumulator β n) (hom : ops.Hom f ops')
    {s : Result α n m} {t : Result β n m} (h : s.Mapped f t) (i k : Fin n) :
    (swapStep ops s i k).Mapped f (swapStep ops' t i k) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Mapped] at h ⊢
  rcases h with ⟨rfl, rfl, rfl⟩
  rw [swapStep, swapStep]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, hom.swap acc i k⟩

private theorem gcdStep_mapped (f : α → β) (ops : Accumulator α n)
    (ops' : Accumulator β n) (hom : ops.Hom f ops')
    {s : Result α n m} {t : Result β n m} (h : s.Mapped f t)
    (col : Fin m) (i k : Fin n) :
    (gcdStep ops col i k s).Mapped f (gcdStep ops' col i k t) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Mapped] at h ⊢
  rcases h with ⟨rfl, rfl, rfl⟩
  rw [gcdStep, gcdStep]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, hom.combine acc i k _ _ _ _⟩

private theorem signStep_mapped (f : α → β) (ops : Accumulator α n)
    (ops' : Accumulator β n) (hom : ops.Hom f ops')
    {s : Result α n m} {t : Result β n m} (h : s.Mapped f t)
    (col : Fin m) (i : Fin n) :
    (signStep ops col i s).Mapped f (signStep ops' col i t) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Mapped] at h ⊢
  rcases h with ⟨rfl, rfl, rfl⟩
  rw [signStep, signStep]
  split
  · exact ⟨rfl, rfl, hom.negate acc i⟩
  · exact ⟨rfl, rfl, rfl⟩

private theorem reduceStep_mapped (f : α → β) (ops : Accumulator α n)
    (ops' : Accumulator β n) (hom : ops.Hom f ops')
    {s : Result α n m} {t : Result β n m} (h : s.Mapped f t)
    (col : Fin m) (i k : Fin n) :
    (reduceStep ops col i k s).Mapped f (reduceStep ops' col i k t) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Mapped] at h ⊢
  rcases h with ⟨rfl, rfl, rfl⟩
  rw [reduceStep, reduceStep]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, hom.add acc i k _⟩

private theorem foldl_mapped (f : α → β) {γ : Type}
    (fstep : Result α n m → γ → Result α n m)
    (gstep : Result β n m → γ → Result β n m) (xs : List γ)
    {s : Result α n m} {t : Result β n m} (h : s.Mapped f t)
    (hstep : ∀ {s t} x, s.Mapped f t → (fstep s x).Mapped f (gstep t x)) :
    (xs.foldl fstep s).Mapped f (xs.foldl gstep t) := by
  induction xs generalizing s t with
  | nil => exact h
  | cons x xs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (hstep x h)

private theorem normalizeRow_mapped (f : α → β) (ops : Accumulator α n)
    (ops' : Accumulator β n) (hom : ops.Hom f ops')
    {s : Result α n m} {t : Result β n m} (h : s.Mapped f t)
    (col : Fin m) (pivot : Fin n) :
    (normalizeRow ops s col pivot).Mapped f (normalizeRow ops' t col pivot) := by
  rcases s with ⟨matrix, pivots, acc⟩
  rcases t with ⟨matrix', pivots', acc'⟩
  simp only [Result.Mapped] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rw [normalizeRow, normalizeRow]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · apply foldl_mapped f
    · exact signStep_mapped f ops ops' hom ⟨rfl, rfl, rfl⟩ col pivot
    · intro state state' row hs
      split
      · exact reduceStep_mapped f ops ops' hom hs col pivot row
      · exact hs

private theorem clearPrior_mapped (f : α → β) (ops : Accumulator α n)
    (ops' : Accumulator β n) (hom : ops.Hom f ops') (pivots : List (Fin m))
    (row : Fin n) {s : Result α n m} {t : Result β n m} (h : s.Mapped f t)
    (pivot : Fin n) :
    (clearPrior ops pivots row s pivot).Mapped f
      (clearPrior ops' pivots row t pivot) := by
  rw [clearPrior, clearPrior]
  split
  · split
    · exact normalizeRow_mapped f ops ops' hom
        (gcdStep_mapped f ops ops' hom h _ pivot row) _ pivot
    · exact h
  · exact h

private theorem admitRow_mapped (f : α → β) (ops : Accumulator α n)
    (ops' : Accumulator β n) (hom : ops.Hom f ops') (pivots : List (Fin m))
    {s : Result α n m} {t : Result β n m} (h : s.Mapped f t) (row : Fin n) :
    (admitRow ops pivots s row).Mapped f (admitRow ops' pivots t row) := by
  rw [admitRow, admitRow]
  have hc := foldl_mapped f (clearPrior ops pivots row) (clearPrior ops' pivots row)
    (List.finRange n) h (fun pivot hp =>
      clearPrior_mapped f ops ops' hom pivots row hp pivot)
  split
  · exact normalizeRow_mapped f ops ops' hom hc _ row
  · exact hc

private theorem principalRun_accumulator_map (f : α → β)
    (ops : Accumulator α n) (ops' : Accumulator β n) (hom : ops.Hom f ops')
    (A : Matrix Int n m) :
    f (principalRun ops A).accumulator = (principalRun ops' A).accumulator := by
  rw [principalRun, principalRun, principalCore, principalCore]
  let profile := rankProfile A
  have hp := foldl_mapped f _ _ profile.swaps
    (show ({ matrix := A, pivots := profile.pivots, accumulator := ops.init } :
        Result α n m).Mapped f
      { matrix := A, pivots := profile.pivots, accumulator := ops'.init } from
        ⟨rfl, rfl, hom.init⟩)
    (fun swap hs => swapStep_mapped f ops ops' hom hs swap.1 swap.2)
  have hr := foldl_mapped f (admitRow ops profile.pivots)
    (admitRow ops' profile.pivots) (List.finRange n) hp (fun row hs =>
      admitRow_mapped f ops ops' hom profile.pivots hs row)
  exact hr.2.2

private theorem run_accumulator_map (f : α → β)
    (ops : Accumulator α n) (ops' : Accumulator β n)
    (hinit : f ops.init = ops'.init)
    (hswap : ∀ a i k, f (ops.swap a i k) = ops'.swap (f a) i k)
    (hcombine : ∀ a i k x y z w,
      f (ops.combine a i k x y z w) = ops'.combine (f a) i k x y z w)
    (hnegate : ∀ a i, f (ops.negate a i) = ops'.negate (f a) i)
    (hadd : ∀ a i k c, f (ops.add a i k c) = ops'.add (f a) i k c)
    (A : Matrix Int n m) :
    f (run ops A).accumulator = (run ops' A).accumulator := by
  have swap_mapped {s : Result α n m} {t : Result β n m}
      (h : s.Mapped f t) (i k : Fin n) :
      (swapStep ops s i k).Mapped f (swapStep ops' t i k) := by
    rcases s with ⟨matrix, pivots, acc⟩
    rcases t with ⟨matrix', pivots', acc'⟩
    simp only [Result.Mapped] at h ⊢
    rcases h with ⟨rfl, rfl, rfl⟩
    rw [swapStep, swapStep]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, hswap acc i k⟩
  have gcd_mapped {s : Result α n m} {t : Result β n m}
      (h : s.Mapped f t) (col : Fin m) (i k : Fin n) :
      (gcdStep ops col i k s).Mapped f (gcdStep ops' col i k t) := by
    rcases s with ⟨matrix, pivots, acc⟩
    rcases t with ⟨matrix', pivots', acc'⟩
    simp only [Result.Mapped] at h ⊢
    rcases h with ⟨rfl, rfl, rfl⟩
    rw [gcdStep, gcdStep]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · dsimp only
      exact ⟨rfl, rfl, hcombine acc i k _ _ _ _⟩
  have sign_mapped {s : Result α n m} {t : Result β n m}
      (h : s.Mapped f t) (col : Fin m) (i : Fin n) :
      (signStep ops col i s).Mapped f (signStep ops' col i t) := by
    rcases s with ⟨matrix, pivots, acc⟩
    rcases t with ⟨matrix', pivots', acc'⟩
    simp only [Result.Mapped] at h ⊢
    rcases h with ⟨rfl, rfl, rfl⟩
    rw [signStep, signStep]
    split
    · exact ⟨rfl, rfl, hnegate acc i⟩
    · exact ⟨rfl, rfl, rfl⟩
  have reduce_mapped {s : Result α n m} {t : Result β n m}
      (h : s.Mapped f t) (col : Fin m) (i k : Fin n) :
      (reduceStep ops col i k s).Mapped f (reduceStep ops' col i k t) := by
    rcases s with ⟨matrix, pivots, acc⟩
    rcases t with ⟨matrix', pivots', acc'⟩
    simp only [Result.Mapped] at h ⊢
    rcases h with ⟨rfl, rfl, rfl⟩
    rw [reduceStep, reduceStep]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, hadd acc i k _⟩
  have fold_mapped {γ : Type}
      (fstep : Result α n m → γ → Result α n m)
      (gstep : Result β n m → γ → Result β n m) (xs : List γ)
      {s : Result α n m} {t : Result β n m} (h : s.Mapped f t)
      (hstep : ∀ {s t} x, s.Mapped f t → (fstep s x).Mapped f (gstep t x)) :
      (xs.foldl fstep s).Mapped f (xs.foldl gstep t) := by
    induction xs generalizing s t with
    | nil => exact h
    | cons x xs ih =>
        rw [List.foldl_cons, List.foldl_cons]
        exact ih (hstep x h)
  have clear_mapped {s : Result α n m} {t : Result β n m}
      (h : s.Mapped f t) (col : Fin m) (pivot found : Fin n) :
      (clearColumn ops s col pivot found).Mapped f
        (clearColumn ops' t col pivot found) := by
    rw [clearColumn, clearColumn]
    exact fold_mapped
      (fun state (k : Fin n) => if k.val < pivot.val then
        reduceStep ops col pivot k state else state)
      (fun state (k : Fin n) => if k.val < pivot.val then
        reduceStep ops' col pivot k state else state)
      (List.finRange n)
      (sign_mapped
        (fold_mapped
          (fun state (k : Fin n) => if pivot.val < k.val then
            gcdStep ops col pivot k state else state)
          (fun state (k : Fin n) => if pivot.val < k.val then
            gcdStep ops' col pivot k state else state)
          (List.finRange n) (swap_mapped h pivot found) (by
            intro state state' k hk
            split
            · exact gcd_mapped hk col pivot k
            · exact hk)) col pivot) (by
        intro state state' k hk
        split
        · exact reduce_mapped hk col pivot k
        · exact hk)
  have column_mapped {s : Result α n m} {t : Result β n m}
      (h : s.Mapped f t) (col : Fin m) :
      (columnStep ops s col).Mapped f (columnStep ops' t col) := by
    rcases s with ⟨matrix, pivots, acc⟩
    rcases t with ⟨matrix', pivots', acc'⟩
    simp only [Result.Mapped] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    by_cases hr : pivots.length < n
    · rw [columnStep, columnStep, dite_eq_left hr, dite_eq_left hr]
      cases hp : findPivot? matrix col pivots.length with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some found =>
          simp only
          have hc := clear_mapped (
            s := { matrix := matrix, pivots := pivots, accumulator := acc })
            (t := { matrix := matrix, pivots := pivots, accumulator := f acc })
            ⟨rfl, rfl, rfl⟩ col ⟨pivots.length, hr⟩ found
          exact ⟨hc.1, congrArg (fun ps => ps ++ [col]) hc.2.1, hc.2.2⟩
    · rw [columnStep, columnStep, dite_eq_right hr, dite_eq_right hr]
      exact ⟨rfl, rfl, rfl⟩
  have result := fold_mapped (columnStep ops) (columnStep ops')
    (List.finRange m) (s :=
      { matrix := A, pivots := [], accumulator := ops.init }) (t :=
      { matrix := A, pivots := [], accumulator := ops'.init })
    ⟨rfl, rfl, hinit⟩ (fun col h => column_mapped h col)
  exact result.2.2

private theorem checkedRun_accumulator_map (f : α → β)
    (ops : Accumulator α n) (ops' : Accumulator β n)
    (hom : ops.Hom f ops') (A : Matrix Int n m) :
    f (checkedRun ops A).accumulator = (checkedRun ops' A).accumulator := by
  have hs := principalRun_same ops ops' A
  have hc : isHNFForm (principalRun ops A).matrix
      (principalRun ops A).pivots.length (principalRun ops A).pivotVector =
      isHNFForm (principalRun ops' A).matrix
        (principalRun ops' A).pivots.length (principalRun ops' A).pivotVector := by
    rcases hpo : principalRun ops A with ⟨matrix, pivots, acc⟩
    rcases hpo' : principalRun ops' A with ⟨matrix', pivots', acc'⟩
    rw [hpo, hpo'] at hs
    simp only [Result.Same, Result.pivotVector] at hs ⊢
    rcases hs with ⟨rfl, rfl⟩
    rfl
  rw [checkedRun, checkedRun, hc]
  split
  · exact principalRun_accumulator_map f ops ops' hom A
  · exact run_accumulator_map f ops ops' hom.init hom.swap hom.combine
      hom.negate hom.add A

/-- Projecting the transform from the inverse-tracking path agrees with the
transform-only path. -/
theorem run_inverse_transform (A : Matrix Int n m) :
    (run (inverseAccumulator n) A).accumulator.transform =
      (run (transformAccumulator n) A).accumulator := by
  apply run_accumulator_map (fun p : TransformPair n => p.transform)
  · rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

private theorem checkedRun_inverse_transform (A : Matrix Int n m) :
    (checkedRun (inverseAccumulator n) A).accumulator.transform =
      (checkedRun (transformAccumulator n) A).accumulator := by
  apply checkedRun_accumulator_map (fun p : TransformPair n => p.transform)
  exact
    { init := rfl
      swap := by intros; rfl
      combine := by intros; rfl
      negate := by intros; rfl
      add := by intros; rfl }

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

theorem checkedRun_rank_le (ops : Accumulator α n) (A : Matrix Int n m) :
    (checkedRun ops A).pivots.length ≤ n :=
  (checkedRun_form ops A).1

/-- The transform accumulator always maps the original input to the current
working matrix. -/
private def Result.Transforms (A : Matrix Int n m)
    (s : Result (Matrix Int n n) n m) : Prop :=
  s.accumulator * A = s.matrix

private theorem run_transform (A : Matrix Int n m) :
    (run (transformAccumulator n) A).accumulator * A =
      (run (transformAccumulator n) A).matrix := by
  let ops := transformAccumulator n
  have swap_preserves {s : Result (Matrix Int n n) n m}
      (h : s.Transforms A) (i k : Fin n) :
      (swapStep ops s i k).Transforms A := by
    rw [swapStep]
    split
    · exact h
    · change Matrix.rowSwap s.accumulator i k * A = Matrix.rowSwap s.matrix i k
      rw [Matrix.rowSwap_mul, h]
  have gcd_preserves {s : Result (Matrix Int n n) n m}
      (h : s.Transforms A) (col : Fin m) (i k : Fin n) :
      (gcdStep ops col i k s).Transforms A := by
    rw [gcdStep]
    split
    · exact h
    · change combineRows s.accumulator i k _ _ _ _ * A =
        combineRows s.matrix i k _ _ _ _
      rw [combineRows_mul, h]
  have sign_preserves {s : Result (Matrix Int n n) n m}
      (h : s.Transforms A) (col : Fin m) (i : Fin n) :
      (signStep ops col i s).Transforms A := by
    rw [signStep]
    split
    · change Matrix.rowScale s.accumulator i (-1) * A =
        Matrix.rowScale s.matrix i (-1)
      rw [Matrix.rowScale_mul, h]
    · exact h
  have reduce_preserves {s : Result (Matrix Int n n) n m}
      (h : s.Transforms A) (col : Fin m) (i k : Fin n) :
      (reduceStep ops col i k s).Transforms A := by
    rw [reduceStep]
    split
    · exact h
    · change Matrix.rowAdd s.accumulator i k _ * A =
        Matrix.rowAdd s.matrix i k _
      rw [Matrix.rowAdd_mul, h]
  have fold_preserves {γ : Type}
      (step : Result (Matrix Int n n) n m → γ → Result (Matrix Int n n) n m)
      (xs : List γ) {s : Result (Matrix Int n n) n m} (h : s.Transforms A)
      (hstep : ∀ {s} x, s.Transforms A → (step s x).Transforms A) :
      (xs.foldl step s).Transforms A := by
    induction xs generalizing s with
    | nil => exact h
    | cons x xs ih =>
        rw [List.foldl_cons]
        exact ih (hstep x h)
  have clear_preserves {s : Result (Matrix Int n n) n m}
      (h : s.Transforms A) (col : Fin m) (pivot found : Fin n) :
      (clearColumn ops s col pivot found).Transforms A := by
    rw [clearColumn]
    exact fold_preserves
      (fun state (k : Fin n) => if k.val < pivot.val then
        reduceStep ops col pivot k state else state)
      (List.finRange n)
      (sign_preserves
        (fold_preserves
          (fun state (k : Fin n) => if pivot.val < k.val then
            gcdStep ops col pivot k state else state)
          (List.finRange n) (swap_preserves h pivot found) (by
            intro state k hk
            split
            · exact gcd_preserves hk col pivot k
            · exact hk)) col pivot) (by
        intro state k hk
        split
        · exact reduce_preserves hk col pivot k
        · exact hk)
  have column_preserves {s : Result (Matrix Int n n) n m}
      (h : s.Transforms A) (col : Fin m) :
      (columnStep ops s col).Transforms A := by
    rw [columnStep]
    split
    · split
      · exact h
      · exact clear_preserves h col _ _
    · exact h
  change (run ops A).Transforms A
  rw [run]
  exact fold_preserves (columnStep ops) (List.finRange m) (by
    change Matrix.identity (R := Int) n * A = A
    exact Matrix.identity_mul A) (by
    intro state col h
    exact column_preserves h col)

private theorem transformSwap {s : Result (Matrix Int n n) n m}
    {A : Matrix Int n m} (h : s.Transforms A) (i k : Fin n) :
    (swapStep (transformAccumulator n) s i k).Transforms A := by
  rw [swapStep]
  split
  · exact h
  · change Matrix.rowSwap s.accumulator i k * A = Matrix.rowSwap s.matrix i k
    rw [Matrix.rowSwap_mul, h]

private theorem transformGcd {s : Result (Matrix Int n n) n m}
    {A : Matrix Int n m} (h : s.Transforms A) (col : Fin m) (i k : Fin n) :
    (gcdStep (transformAccumulator n) col i k s).Transforms A := by
  rw [gcdStep]
  split
  · exact h
  · change combineRows s.accumulator i k _ _ _ _ * A =
        combineRows s.matrix i k _ _ _ _
    rw [combineRows_mul, h]

private theorem transformSign {s : Result (Matrix Int n n) n m}
    {A : Matrix Int n m} (h : s.Transforms A) (col : Fin m) (i : Fin n) :
    (signStep (transformAccumulator n) col i s).Transforms A := by
  rw [signStep]
  split
  · change Matrix.rowScale s.accumulator i (-1) * A = Matrix.rowScale s.matrix i (-1)
    rw [Matrix.rowScale_mul, h]
  · exact h

private theorem transformReduce {s : Result (Matrix Int n n) n m}
    {A : Matrix Int n m} (h : s.Transforms A) (col : Fin m) (i k : Fin n) :
    (reduceStep (transformAccumulator n) col i k s).Transforms A := by
  rw [reduceStep]
  split
  · exact h
  · change Matrix.rowAdd s.accumulator i k _ * A = Matrix.rowAdd s.matrix i k _
    rw [Matrix.rowAdd_mul, h]

private theorem transformFold {A : Matrix Int n m} {γ : Type}
    (step : Result (Matrix Int n n) n m → γ → Result (Matrix Int n n) n m)
    (xs : List γ) {s : Result (Matrix Int n n) n m} (h : s.Transforms A)
    (hstep : ∀ {s} x, s.Transforms A → (step s x).Transforms A) :
    (xs.foldl step s).Transforms A := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih (hstep x h)

private theorem transformNormalize {s : Result (Matrix Int n n) n m}
    {A : Matrix Int n m} (h : s.Transforms A) (col : Fin m) (pivot : Fin n) :
    (normalizeRow (transformAccumulator n) s col pivot).Transforms A := by
  rw [normalizeRow]
  split
  · exact h
  · exact transformFold _ (List.finRange n) (transformSign h col pivot) (by
      intro state row hs
      split
      · exact transformReduce hs col pivot row
      · exact hs)

private theorem transformClear (pivots : List (Fin m)) (row : Fin n)
    {s : Result (Matrix Int n n) n m} {A : Matrix Int n m} (h : s.Transforms A)
    (pivot : Fin n) :
    (clearPrior (transformAccumulator n) pivots row s pivot).Transforms A := by
  rw [clearPrior]
  split
  · split
    · exact transformNormalize (transformGcd h _ pivot row) _ pivot
    · exact h
  · exact h

private theorem transformAdmit (pivots : List (Fin m))
    {s : Result (Matrix Int n n) n m} {A : Matrix Int n m} (h : s.Transforms A)
    (row : Fin n) :
    (admitRow (transformAccumulator n) pivots s row).Transforms A := by
  rw [admitRow]
  have hc := transformFold (clearPrior (transformAccumulator n) pivots row)
    (List.finRange n) h (fun pivot hs => transformClear pivots row hs pivot)
  split
  · exact transformNormalize hc _ row
  · exact hc

private theorem principalCore_transform (A : Matrix Int n m) (profile : Profile n m) :
    let initial : Result (Matrix Int n n) n m :=
      { matrix := A, pivots := profile.pivots, accumulator := Matrix.identity n }
    let permuted := profile.swaps.foldl
      (fun s swap => swapStep (transformAccumulator n) s swap.1 swap.2) initial
    ((List.finRange n).foldl
      (admitRow (transformAccumulator n) profile.pivots) permuted).Transforms A := by
  dsimp only
  apply transformFold
  · apply transformFold
    · exact Matrix.identity_mul A
    · intro state swap hs
      exact transformSwap hs swap.1 swap.2
  · intro state row hs
    exact transformAdmit profile.pivots hs row

private theorem principalRun_transform (A : Matrix Int n m) :
    (principalRun (transformAccumulator n) A).Transforms A := by
  change (principalCore (transformAccumulator n) A (rankProfile A)).Transforms A
  exact principalCore_transform A (rankProfile A)

private theorem checkedRun_transform (A : Matrix Int n m) :
    (checkedRun (transformAccumulator n) A).accumulator * A =
      (checkedRun (transformAccumulator n) A).matrix := by
  rw [checkedRun]
  split
  · exact principalRun_transform A
  · exact run_transform A

set_option maxHeartbeats 800000 in
/-- The explicit inverse accumulator remains a right inverse of its transform. -/
private theorem run_inverse_mul (A : Matrix Int n m) :
    (run (inverseAccumulator n) A).accumulator.transform *
        (run (inverseAccumulator n) A).accumulator.inverse =
      Matrix.identity n := by
  let ops := inverseAccumulator n
  let Valid (s : Result (TransformPair n) n m) : Prop :=
    s.accumulator.transform * s.accumulator.inverse = Matrix.identity n
  have swap_preserves {s : Result (TransformPair n) n m}
      (h : Valid s) (i k : Fin n) : Valid (swapStep ops s i k) := by
    rw [swapStep]
    split
    · exact h
    · change Matrix.rowSwap s.accumulator.transform i k *
          Matrix.colSwap s.accumulator.inverse i k = Matrix.identity n
      rw [Matrix.rowSwap_mul, mul_colSwap, h, swap_inverse_identity]
  have gcd_preserves {s : Result (TransformPair n) n m}
      (h : Valid s) (col : Fin m) (i k : Fin n) (hik : i ≠ k) :
      Valid (gcdStep ops col i k s) := by
    rw [gcdStep]
    split
    · exact h
    · rename_i hb
      let a := s.matrix[(i, col)]
      let b := s.matrix[(k, col)]
      rcases hc : gcdCoeffs a b with ⟨x, y, z, w⟩
      have hdet := gcdCoeffs_det (a := a) (b := b) hb
      rw [hc] at hdet
      dsimp only at hdet
      dsimp [a, b] at hc
      dsimp only
      rw [hc]
      change combineRows s.accumulator.transform i k x y z w *
          combineCols s.accumulator.inverse i k w (-z) (-y) x =
        Matrix.identity n
      rw [combineRows_mul, mul_combineCols, h,
        combine_inverse_identity i k hik x y z w hdet]
  have sign_preserves {s : Result (TransformPair n) n m}
      (h : Valid s) (col : Fin m) (i : Fin n) : Valid (signStep ops col i s) := by
    rw [signStep]
    split
    · change Matrix.rowScale s.accumulator.transform i (-1) *
          Matrix.colScale s.accumulator.inverse i (-1) = Matrix.identity n
      rw [Matrix.rowScale_mul, mul_colScale, h, negate_inverse_identity]
    · exact h
  have reduce_preserves {s : Result (TransformPair n) n m}
      (h : Valid s) (col : Fin m) (i k : Fin n) (hik : i ≠ k) :
      Valid (reduceStep ops col i k s) := by
    rw [reduceStep]
    split
    · exact h
    · change Matrix.rowAdd s.accumulator.transform i k _ *
          Matrix.colAdd s.accumulator.inverse k i (-_) = Matrix.identity n
      rw [Matrix.rowAdd_mul, Matrix.mul_colAdd, h]
      exact add_inverse_identity i k hik _
  have fold_preserves {γ : Type}
      (step : Result (TransformPair n) n m → γ → Result (TransformPair n) n m)
      (xs : List γ) {s : Result (TransformPair n) n m} (h : Valid s)
      (hstep : ∀ {s} x, Valid s → Valid (step s x)) :
      Valid (xs.foldl step s) := by
    induction xs generalizing s with
    | nil => exact h
    | cons x xs ih =>
        rw [List.foldl_cons]
        exact ih (hstep x h)
  have clear_preserves {s : Result (TransformPair n) n m}
      (h : Valid s) (col : Fin m) (pivot found : Fin n) :
      Valid (clearColumn ops s col pivot found) := by
    rw [clearColumn]
    exact fold_preserves
      (fun state (k : Fin n) => if k.val < pivot.val then
        reduceStep ops col pivot k state else state)
      (List.finRange n)
      (sign_preserves
        (fold_preserves
          (fun state (k : Fin n) => if pivot.val < k.val then
            gcdStep ops col pivot k state else state)
          (List.finRange n) (swap_preserves h pivot found) (by
            intro state k hk
            split
            · exact gcd_preserves hk col pivot k (by omega)
            · exact hk)) col pivot) (by
        intro state k hk
        split
        · exact reduce_preserves hk col pivot k (by omega)
        · exact hk)
  have column_preserves {s : Result (TransformPair n) n m}
      (h : Valid s) (col : Fin m) : Valid (columnStep ops s col) := by
    rw [columnStep]
    split
    · split
      · exact h
      · exact clear_preserves h col _ _
    · exact h
  change Valid (run ops A)
  rw [run]
  exact fold_preserves (columnStep ops) (List.finRange m) (by
    change Matrix.identity (R := Int) n * Matrix.identity n = Matrix.identity n
    exact Matrix.identity_mul _) (by
    intro state col h
    exact column_preserves h col)

private def Result.Invertible (s : Result (TransformPair n) n m) : Prop :=
  s.accumulator.transform * s.accumulator.inverse = Matrix.identity n

private theorem inverseSwap {s : Result (TransformPair n) n m}
    (h : s.Invertible) (i k : Fin n) :
    (swapStep (inverseAccumulator n) s i k).Invertible := by
  rw [swapStep]
  split
  · exact h
  · change Matrix.rowSwap s.accumulator.transform i k *
        Matrix.colSwap s.accumulator.inverse i k = Matrix.identity n
    rw [Matrix.rowSwap_mul, mul_colSwap, h, swap_inverse_identity]

private theorem inverseGcd {s : Result (TransformPair n) n m}
    (h : s.Invertible) (col : Fin m) (i k : Fin n) (hik : i ≠ k) :
    (gcdStep (inverseAccumulator n) col i k s).Invertible := by
  rw [gcdStep]
  split
  · exact h
  · rename_i hb
    let a := s.matrix[(i, col)]
    let b := s.matrix[(k, col)]
    rcases hc : gcdCoeffs a b with ⟨x, y, z, w⟩
    have hdet := gcdCoeffs_det (a := a) (b := b) hb
    rw [hc] at hdet
    dsimp only at hdet
    dsimp [a, b] at hc
    dsimp only
    rw [hc]
    change combineRows s.accumulator.transform i k x y z w *
        combineCols s.accumulator.inverse i k w (-z) (-y) x = Matrix.identity n
    rw [combineRows_mul, mul_combineCols, h,
      combine_inverse_identity i k hik x y z w hdet]

private theorem inverseSign {s : Result (TransformPair n) n m}
    (h : s.Invertible) (col : Fin m) (i : Fin n) :
    (signStep (inverseAccumulator n) col i s).Invertible := by
  rw [signStep]
  split
  · change Matrix.rowScale s.accumulator.transform i (-1) *
        Matrix.colScale s.accumulator.inverse i (-1) = Matrix.identity n
    rw [Matrix.rowScale_mul, mul_colScale, h, negate_inverse_identity]
  · exact h

private theorem inverseReduce {s : Result (TransformPair n) n m}
    (h : s.Invertible) (col : Fin m) (i k : Fin n) (hik : i ≠ k) :
    (reduceStep (inverseAccumulator n) col i k s).Invertible := by
  rw [reduceStep]
  split
  · exact h
  · change Matrix.rowAdd s.accumulator.transform i k _ *
        Matrix.colAdd s.accumulator.inverse k i (-_) = Matrix.identity n
    rw [Matrix.rowAdd_mul, Matrix.mul_colAdd, h]
    exact add_inverse_identity i k hik _

private theorem inverseFold {γ : Type}
    (step : Result (TransformPair n) n m → γ → Result (TransformPair n) n m)
    (xs : List γ) {s : Result (TransformPair n) n m} (h : s.Invertible)
    (hstep : ∀ {s} x, s.Invertible → (step s x).Invertible) :
    (xs.foldl step s).Invertible := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih (hstep x h)

private theorem inverseNormalize {s : Result (TransformPair n) n m}
    (h : s.Invertible) (col : Fin m) (pivot : Fin n) :
    (normalizeRow (inverseAccumulator n) s col pivot).Invertible := by
  rw [normalizeRow]
  split
  · exact h
  · exact inverseFold _ (List.finRange n) (inverseSign h col pivot) (by
      intro state row hs
      split
      · exact inverseReduce hs col pivot row (by omega)
      · exact hs)

private theorem inverseClear (pivots : List (Fin m)) (row : Fin n)
    {s : Result (TransformPair n) n m} (h : s.Invertible) (pivot : Fin n) :
    (clearPrior (inverseAccumulator n) pivots row s pivot).Invertible := by
  rw [clearPrior]
  split
  · rename_i hpr
    split
    · exact inverseNormalize (inverseGcd h _ pivot row (by omega)) _ pivot
    · exact h
  · exact h

private theorem inverseAdmit (pivots : List (Fin m))
    {s : Result (TransformPair n) n m} (h : s.Invertible) (row : Fin n) :
    (admitRow (inverseAccumulator n) pivots s row).Invertible := by
  rw [admitRow]
  have hc := inverseFold (clearPrior (inverseAccumulator n) pivots row)
    (List.finRange n) h (fun pivot hs => inverseClear pivots row hs pivot)
  split
  · exact inverseNormalize hc _ row
  · exact hc

private theorem principalCore_inverse (A : Matrix Int n m) (profile : Profile n m) :
    let initial : Result (TransformPair n) n m :=
      { matrix := A, pivots := profile.pivots
        accumulator := ⟨Matrix.identity n, Matrix.identity n⟩ }
    let permuted := profile.swaps.foldl
      (fun s swap => swapStep (inverseAccumulator n) s swap.1 swap.2) initial
    ((List.finRange n).foldl
      (admitRow (inverseAccumulator n) profile.pivots) permuted).Invertible := by
  dsimp only
  apply inverseFold
  · apply inverseFold
    · exact Matrix.identity_mul _
    · intro state swap hs
      exact inverseSwap hs swap.1 swap.2
  · intro state row hs
    exact inverseAdmit profile.pivots hs row

private theorem principalRun_inverse_mul (A : Matrix Int n m) :
    (principalRun (inverseAccumulator n) A).Invertible := by
  change (principalCore (inverseAccumulator n) A (rankProfile A)).Invertible
  exact principalCore_inverse A (rankProfile A)

private theorem checkedRun_inverse_mul (A : Matrix Int n m) :
    (checkedRun (inverseAccumulator n) A).accumulator.transform *
        (checkedRun (inverseAccumulator n) A).accumulator.inverse =
      Matrix.identity n := by
  rw [checkedRun]
  split
  · exact principalRun_inverse_mul A
  · exact run_inverse_mul A

end Hermite

/-- Hermite data with the inverse transform accumulated on the value path. -/
structure HermiteData (n m : Nat) where
  rowData : RowEchelonData Int n m
  inverse : Matrix Int n n

/-- The Hermite normal form of `A`. Does not compute the transform. -/
@[expose]
def hnf (A : Matrix Int n m) : Matrix Int n m :=
  (Hermite.checkedRun (Hermite.formAccumulator n) A).matrix

/-- The number of nonzero rows of `hnf A`. -/
@[expose]
def hnfRank (A : Matrix Int n m) : Nat :=
  (Hermite.checkedRun (Hermite.formAccumulator n) A).pivots.length

/-- The nonzero rows of `hnf A`. -/
@[expose]
def hnfBasis (A : Matrix Int n m) : Matrix Int (hnfRank A) m :=
  let result := Hermite.checkedRun (Hermite.formAccumulator n) A
  let basis : Matrix Int result.pivots.length m := Matrix.ofFn fun i j =>
    result.matrix[(Fin.castLE
      (Hermite.checkedRun_rank_le (Hermite.formAccumulator n) A) i, j)]
  have hlen : result.pivots.length = hnfRank A := rfl
  hlen ▸ basis

/-- An entry of the HNF basis is the corresponding entry of the full form. -/
@[simp] theorem getElem_hnfBasis (A : Matrix Int n m) (i : Fin (hnfRank A))
    (j : Fin m) :
    (hnfBasis A)[i][j] =
      (hnf A)[Fin.castLE
        (Hermite.checkedRun_rank_le (Hermite.formAccumulator n) A) i][j] := by
  change Fin (Hermite.checkedRun (Hermite.formAccumulator n) A).pivots.length at i
  simp only [hnfBasis, hnfRank, hnf, Matrix.getElem_pair_eq_nested]
  rw [Matrix.getElem_ofFn]

/-- Hermite form with rank, pivot columns, and left transform. -/
@[expose]
def hnfData (A : Matrix Int n m) : RowEchelonData Int n m :=
  let result := Hermite.checkedRun (Hermite.transformAccumulator n) A
  { rank := result.pivots.length
    echelon := result.matrix
    transform := result.accumulator
    pivotCols := result.pivotVector }

/-- The accumulated left transform carries the input to the reported form. -/
theorem hnfData_transform_mul (A : Matrix Int n m) :
    (hnfData A).transform * A = (hnfData A).echelon := by
  exact Hermite.checkedRun_transform A

/-- The form-only and transform paths run the same matrix schedule. -/
theorem hnf_eq_hnfData_echelon (A : Matrix Int n m) :
    hnf A = (hnfData A).echelon := by
  exact Hermite.checkedRun_matrix_agree (Hermite.formAccumulator n)
    (Hermite.transformAccumulator n) A

/-- The form-only and transform paths report the same rank. -/
theorem hnfRank_eq (A : Matrix Int n m) :
    hnfRank A = (hnfData A).rank := by
  exact congrArg List.length (Hermite.checkedRun_pivots_agree
    (Hermite.formAccumulator n) (Hermite.transformAccumulator n) A)

/-- Hermite data with both transform and inverse accumulated in one sweep. -/
@[expose]
def hnfWithInv (A : Matrix Int n m) : HermiteData n m :=
  let result := Hermite.checkedRun (Hermite.inverseAccumulator n) A
  { rowData :=
      { rank := result.pivots.length
        echelon := result.matrix
        transform := result.accumulator.transform
        pivotCols := result.pivotVector }
    inverse := result.accumulator.inverse }

/-- The inverse-tracking path returns the same row data as `hnfData`. -/
theorem hnfWithInv_data (A : Matrix Int n m) :
    (hnfWithInv A).rowData = hnfData A := by
  let ri := Hermite.checkedRun (Hermite.inverseAccumulator n) A
  let rt := Hermite.checkedRun (Hermite.transformAccumulator n) A
  have hm : ri.matrix = rt.matrix :=
    Hermite.checkedRun_matrix_agree (Hermite.inverseAccumulator n)
      (Hermite.transformAccumulator n) A
  have hp : ri.pivots = rt.pivots :=
    Hermite.checkedRun_pivots_agree (Hermite.inverseAccumulator n)
      (Hermite.transformAccumulator n) A
  have hu : ri.accumulator.transform = rt.accumulator :=
    Hermite.checkedRun_inverse_transform A
  change
    RowEchelonData.mk ri.pivots.length ri.matrix ri.accumulator.transform
      ri.pivotVector =
    RowEchelonData.mk rt.pivots.length rt.matrix rt.accumulator rt.pivotVector
  rcases ri with ⟨mi, pi, ai⟩
  rcases rt with ⟨mt, pt, ut⟩
  simp only at hm hp hu
  subst mt
  subst pt
  subst ut
  rfl

/-- The explicitly accumulated inverse is a right inverse of the transform. -/
theorem hnfWithInv_mul_inv (A : Matrix Int n m) :
    (hnfWithInv A).rowData.transform * (hnfWithInv A).inverse =
      Matrix.identity n := by
  exact Hermite.checkedRun_inverse_mul A

/-- The explicitly accumulated inverse is also a left inverse of the transform. -/
theorem hnfWithInv_inv_mul (A : Matrix Int n m) :
    (hnfWithInv A).inverse * (hnfWithInv A).rowData.transform =
      Matrix.identity n := by
  exact mul_eq_one_comm (hnfWithInv_mul_inv A)

/-- The inverse-tracking transform carries the input to its reported form. -/
theorem hnfWithInv_transform_mul (A : Matrix Int n m) :
    (hnfWithInv A).rowData.transform * A = (hnfWithInv A).rowData.echelon := by
  rw [hnfWithInv_data A]
  exact hnfData_transform_mul A

/-- The executable Hermite sweep satisfies the complete row-HNF contract. -/
theorem hnfData_isHNF (A : Matrix Int n m) : IsHNF A (hnfData A) := by
  let s := Hermite.checkedRun (Hermite.transformAccumulator n) A
  have hs : HNFForm s.matrix s.pivots.length s.pivotVector :=
    Hermite.checkedRun_form (Hermite.transformAccumulator n) A
  rcases hs with ⟨hrn, hrm, hsorted, hleading, hpos, hbelow, hzero, hnonneg, hlt⟩
  have hleft : (hnfWithInv A).inverse * (hnfData A).transform =
      Matrix.identity n := by
    rw [← hnfWithInv_data A]
    exact hnfWithInv_inv_mul A
  have hright : (hnfData A).transform * (hnfWithInv A).inverse =
      Matrix.identity n := by
    rw [← hnfWithInv_data A]
    exact hnfWithInv_mul_inv A
  change IsHNF A
    { rank := s.pivots.length
      echelon := s.matrix
      transform := s.accumulator
      pivotCols := s.pivotVector }
  let pivotRow : Fin s.pivots.length → Fin n := fun i =>
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt hrn⟩
  refine
    { toIsEchelonForm :=
        { transform_mul := hnfData_transform_mul A
          transform_inv := ⟨(hnfWithInv A).inverse, ?_⟩
          transform_right_inv := ⟨(hnfWithInv A).inverse, ?_⟩
          rank_le_n := hrn
          rank_le_m := hrm
          pivotCols_sorted := ?_
          below_pivot_zero := ?_
          zero_row := ?_ }
      pivot_leading := ?_
      pivot_pos := ?_
      above_nonneg := ?_
      above_lt := ?_ }
  · exact hleft
  · exact hright
  · intro i j hij
    exact hsorted i j hij
  · intro i row hir
    change (s.matrix.getRow row).get (s.pivotVector.get i) = 0
    simpa only [Matrix.getElem_pair_eq_get] using hbelow i row hir
  · intro row hr
    exact hzero row hr
  · intro i j hj
    change (s.matrix.getRow (pivotRow i)).get j = 0
    simpa only [Matrix.getElem_pair_eq_get] using hleading i (pivotRow i) rfl j hj
  · intro i
    change 0 < (s.matrix.getRow (pivotRow i)).get (s.pivotVector.get i)
    simpa only [Matrix.getElem_pair_eq_get] using hpos i (pivotRow i) rfl
  · intro i row hir
    change 0 ≤ (s.matrix.getRow row).get (s.pivotVector.get i)
    simpa only [Matrix.getElem_pair_eq_get] using hnonneg i row hir
  · intro i row hir
    change (s.matrix.getRow row).get (s.pivotVector.get i) <
      (s.matrix.getRow (pivotRow i)).get (s.pivotVector.get i)
    simpa only [Matrix.getElem_pair_eq_get] using hlt i row hir (pivotRow i) rfl

end Hex.Matrix
