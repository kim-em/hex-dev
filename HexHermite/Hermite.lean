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

/-- A relation between accumulator runs that also tracks a homomorphism on
the companion state. -/
private def Result.Mapped (f : α → β) (s : Result α n m) (t : Result β n m) : Prop :=
  s.matrix = t.matrix ∧ s.pivots = t.pivots ∧ f s.accumulator = t.accumulator

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
    · rw [columnStep, columnStep, dif_pos hr, dif_pos hr]
      cases hp : findPivot? matrix col pivots.length with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some found =>
          simp only
          have hc := clear_mapped (
            s := { matrix := matrix, pivots := pivots, accumulator := acc })
            (t := { matrix := matrix, pivots := pivots, accumulator := f acc })
            ⟨rfl, rfl, rfl⟩ col ⟨pivots.length, hr⟩ found
          exact ⟨hc.1, congrArg (fun ps => ps ++ [col]) hc.2.1, hc.2.2⟩
    · rw [columnStep, columnStep, dif_neg hr, dif_neg hr]
      exact ⟨rfl, rfl, rfl⟩
  have result := fold_mapped (columnStep ops) (columnStep ops')
    (List.finRange m) (s :=
      { matrix := A, pivots := [], accumulator := ops.init }) (t :=
      { matrix := A, pivots := [], accumulator := ops'.init })
    ⟨rfl, rfl, hinit⟩ (fun col h => column_mapped h col)
  exact result.2.2

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

/-- The accumulated left transform carries the input to the reported form. -/
theorem hnfData_transform_mul (A : Matrix Int n m) :
    (hnfData A).transform * A = (hnfData A).echelon := by
  exact Hermite.run_transform A

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

/-- The inverse-tracking path returns the same row data as `hnfData`. -/
theorem hnfWithInv_data (A : Matrix Int n m) :
    (hnfWithInv A).rowData = hnfData A := by
  let ri := Hermite.run (Hermite.inverseAccumulator n) A
  let rt := Hermite.run (Hermite.transformAccumulator n) A
  have hm : ri.matrix = rt.matrix :=
    Hermite.run_matrix_agree (Hermite.inverseAccumulator n)
      (Hermite.transformAccumulator n) A
  have hp : ri.pivots = rt.pivots :=
    Hermite.run_pivots_agree (Hermite.inverseAccumulator n)
      (Hermite.transformAccumulator n) A
  have hu : ri.accumulator.transform = rt.accumulator :=
    Hermite.run_inverse_transform A
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
  exact Hermite.run_inverse_mul A

/-- The explicitly accumulated inverse is also a left inverse of the transform. -/
theorem hnfWithInv_inv_mul (A : Matrix Int n m) :
    (hnfWithInv A).inverse * (hnfWithInv A).rowData.transform =
      Matrix.identity n := by
  exact mul_eq_one_comm (hnfWithInv_mul_inv A)

end Hex.Matrix
