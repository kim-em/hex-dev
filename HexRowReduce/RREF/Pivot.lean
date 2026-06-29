/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std
public import Batteries.Data.Vector.Lemmas
public import HexRowReduce.RowEchelon

public section

/-!
Pivot search and column elimination for the `hex-matrix` RREF loop.

This module supplies the executable building blocks of Gauss-Jordan
elimination and their entrywise lemmas. It defines `rowCombination`, the
`RrefState` carrier, the pivot search `findPivot?` (with the `_some_ge`,
`_some_nonzero`, `_some_above`, `_none` characterizations) and the
column-clearing `eliminateColumn`, proving the latter zeros non-pivot rows,
fixes the pivot row, leaves other columns untouched, and preserves both the
transform equation and the transform's left/right inverses. It assembles the
`rrefLoop` driver itself together with the proof-only `RrefShapeInvariant`,
`RrefCanonicalInvariant` structures and their one-step `concat` extension
lemmas, which `RREF/Loop` then carries through the recursion.
-/

namespace Hex
universe u
namespace Matrix
variable {R : Type u} {n m : Nat}

/-- A linear combination of the rows of `M`, using coefficients `c`. -/
@[expose]
def rowCombination [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (c : Vector R n) :
    Vector R m :=
  Matrix.transpose M * c

structure RrefState (R : Type u) (n m : Nat) where
  row : Nat
  echelon : Matrix R n m
  transform : Matrix R n n
  pivots : List (Fin m)

section FieldAlgorithms

variable [Lean.Grind.Field R] [DecidableEq R]

/-- Search for a nonzero pivot in `col`, starting at row `start`. -/
private def findPivotAux (M : Matrix R n m) (col : Fin m) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[i][col] = 0 then
          findPivotAux M col (start + 1) fuel
        else
          some i
      else
        none

/-- Search for a nonzero pivot in `col`, starting at row `start`. -/
private def findPivot? (M : Matrix R n m) (col : Fin m) (start : Nat) : Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- Eliminate every non-pivot entry in a pivot column. -/
private def eliminateColumn (M : Matrix R n m) (T : Matrix R n n)
    (pivotRow : Fin n) (col : Fin m) : Matrix R n m × Matrix R n n :=
  (List.finRange n).foldl
    (fun (state : Matrix R n m × Matrix R n n) j =>
      if h : j = pivotRow then
        state
      else
        let coeff := -state.1[j][col]
        if coeff = 0 then
          state
        else
          (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
    (M, T)

/-- Successful pivot search returns an index at or above `start`. -/
private theorem findPivotAux_some_ge (M : Matrix R n m) (col : Fin m) :
    ∀ {start fuel : Nat} {i : Fin n},
      findPivotAux M col start fuel = some i → start ≤ i.val := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro i h
      simp [findPivotAux] at h
  | succ fuel ih =>
      intro i h
      unfold findPivotAux at h
      by_cases hstart : start < n
      · rw [dif_pos hstart] at h
        by_cases hzero : M[(⟨start, hstart⟩ : Fin n)][col] = 0
        · rw [if_pos hzero] at h
          exact Nat.le_of_succ_le (ih h)
        · rw [if_neg hzero] at h
          injection h with hi
          subst hi
          exact Nat.le_refl _
      · rw [dif_neg hstart] at h
        contradiction

/-- The result of a successful pivot search is a nonzero entry. -/
private theorem findPivotAux_some_nonzero (M : Matrix R n m) (col : Fin m) :
    ∀ {start fuel : Nat} {i : Fin n},
      findPivotAux M col start fuel = some i → M[i][col] ≠ 0 := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro i h
      simp [findPivotAux] at h
  | succ fuel ih =>
      intro i h
      unfold findPivotAux at h
      by_cases hstart : start < n
      · rw [dif_pos hstart] at h
        by_cases hzero : M[(⟨start, hstart⟩ : Fin n)][col] = 0
        · rw [if_pos hzero] at h
          exact ih h
        · rw [if_neg hzero] at h
          injection h with hi
          subst hi
          exact hzero
      · rw [dif_neg hstart] at h
        contradiction

/-- All rows below the pivot search start that precede the returned index are zero. -/
private theorem findPivotAux_some_above (M : Matrix R n m) (col : Fin m) :
    ∀ {start fuel : Nat} {i : Fin n},
      findPivotAux M col start fuel = some i →
      ∀ k : Fin n, start ≤ k.val → k.val < i.val → M[k][col] = 0 := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro i h
      simp [findPivotAux] at h
  | succ fuel ih =>
      intro i h k hge hlt
      unfold findPivotAux at h
      by_cases hstart : start < n
      · rw [dif_pos hstart] at h
        by_cases hzero : M[(⟨start, hstart⟩ : Fin n)][col] = 0
        · rw [if_pos hzero] at h
          rcases Nat.lt_or_ge start (k.val + 1) with hgt | hle
          · -- start < k.val + 1, so start ≤ k.val and start < k.val + 1
            -- combined with hge gives start ≤ k.val
            -- if start = k.val, k = ⟨start, hstart⟩ and goal follows from hzero
            -- else start < k.val and we apply IH
            rcases Nat.lt_or_eq_of_le hge with hgt' | heq
            · exact ih h k hgt' hlt
            · have hk_eq : k = ⟨start, hstart⟩ := Fin.ext heq.symm
              rw [hk_eq]
              exact hzero
          · -- k.val + 1 ≤ start, contradicts hge
            omega
        · rw [if_neg hzero] at h
          injection h with hi
          -- hi : ⟨start, hstart⟩ = i
          have hival : i.val = start := by
            rw [Fin.ext_iff] at hi
            exact hi.symm
          exfalso
          omega
      · rw [dif_neg hstart] at h
        contradiction

/-- Failed pivot search means every searched row is zero in this column. -/
private theorem findPivotAux_none (M : Matrix R n m) (col : Fin m) :
    ∀ {start fuel : Nat},
      findPivotAux M col start fuel = none →
      ∀ k : Fin n, start ≤ k.val → k.val < start + fuel → M[k][col] = 0 := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _h k hge hlt
      omega
  | succ fuel ih =>
      intro h k hge hlt
      unfold findPivotAux at h
      by_cases hstart : start < n
      · rw [dif_pos hstart] at h
        by_cases hzero : M[(⟨start, hstart⟩ : Fin n)][col] = 0
        · rw [if_pos hzero] at h
          rcases Nat.lt_or_eq_of_le hge with hgt | heq
          · exact ih h k hgt (by omega)
          · have hk_eq : k = ⟨start, hstart⟩ := Fin.ext heq.symm
            rw [hk_eq]
            exact hzero
        · rw [if_neg hzero] at h
          contradiction
      · exact absurd k.isLt (by omega)

/-- Successful `findPivot?` returns an index at or above `start`. -/
private theorem findPivot?_some_ge (M : Matrix R n m) (col : Fin m)
    {start : Nat} {i : Fin n} (h : findPivot? M col start = some i) :
    start ≤ i.val :=
  findPivotAux_some_ge M col h

/-- Successful `findPivot?` returns a nonzero entry. -/
private theorem findPivot?_some_nonzero (M : Matrix R n m) (col : Fin m)
    {start : Nat} {i : Fin n} (h : findPivot? M col start = some i) :
    M[i][col] ≠ 0 :=
  findPivotAux_some_nonzero M col h

/-- All rows between `start` and the index returned by `findPivot?` are zero. -/
private theorem findPivot?_some_above (M : Matrix R n m) (col : Fin m)
    {start : Nat} {i : Fin n} (h : findPivot? M col start = some i) :
    ∀ k : Fin n, start ≤ k.val → k.val < i.val → M[k][col] = 0 :=
  findPivotAux_some_above M col h

/-- Failed `findPivot?` means every row from `start` to `n` is zero in this column. -/
private theorem findPivot?_none (M : Matrix R n m) (col : Fin m) {start : Nat}
    (h : findPivot? M col start = none) :
    ∀ k : Fin n, start ≤ k.val → M[k][col] = 0 := by
  intro k hge
  apply findPivotAux_none M col h k hge
  have hk : k.val < n := k.isLt
  omega

omit [DecidableEq R] in
/-- Entry of `rowAdd M src dst c` at row `dst`. -/
private theorem rowAdd_get_dst (M : Matrix R n m) (src dst : Fin n) (c : R)
    (k : Fin m) :
    (rowAdd M src dst c)[dst][k] = M[dst][k] + c * M[src][k] := by
  simp [rowAdd]

omit [DecidableEq R] in
/-- Entry of `rowAdd M src dst c` at any row other than `dst`. -/
private theorem rowAdd_get_other (M : Matrix R n m) (src dst : Fin n) (c : R)
    {r : Fin n} (hne : r ≠ dst) (k : Fin m) :
    (rowAdd M src dst c)[r][k] = M[r][k] := by
  have hval : dst.val ≠ r.val := by
    intro hval
    exact hne (Fin.ext hval.symm)
  have hrow :
      (M.set dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]))[r] = M[r] :=
    Vector.getElem_set_ne (xs := M)
      (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k]) dst.isLt r.isLt hval
  simpa [rowAdd] using congrArg (fun row => row[k]) hrow

/-- One step of `eliminateColumn`'s fold preserves the entry at the pivot row. -/
private theorem eliminateColumn_step_pivotRow_entry
    (s : Matrix R n m × Matrix R n n) (pivotRow x : Fin n)
    (col : Fin m) (k : Fin m) :
    (if _h : x = pivotRow then s
     else
       let coeff := -s.1[x][col]
       if coeff = 0 then s
       else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff)).1[pivotRow][k]
      = s.1[pivotRow][k] := by
  by_cases hxp : x = pivotRow
  · rw [dif_pos hxp]
  · rw [dif_neg hxp]
    by_cases hcoeff : -s.1[x][col] = 0
    · rw [if_pos hcoeff]
    · rw [if_neg hcoeff]
      exact rowAdd_get_other s.1 pivotRow x _ (fun h => hxp h.symm) k

/-- One step of `eliminateColumn`'s fold preserves the entry at any row other
than `x` (the row currently being processed) at column `col`. -/
private theorem eliminateColumn_step_other_entry
    (s : Matrix R n m × Matrix R n n) (pivotRow x : Fin n)
    (col : Fin m) {r : Fin n} (hrx : r ≠ x) :
    (if _h : x = pivotRow then s
     else
       let coeff := -s.1[x][col]
       if coeff = 0 then s
       else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff)).1[r][col]
      = s.1[r][col] := by
  by_cases hxp : x = pivotRow
  · rw [dif_pos hxp]
  · rw [dif_neg hxp]
    by_cases hcoeff : -s.1[x][col] = 0
    · rw [if_pos hcoeff]
    · rw [if_neg hcoeff]
      exact rowAdd_get_other s.1 pivotRow x _ hrx col

/-- One step of `eliminateColumn`'s fold zeros the entry at row `x` (the row
currently being processed) at column `col`, provided the pivot row already
holds a `1` there. -/
private theorem eliminateColumn_step_zero_at_x
    (s : Matrix R n m × Matrix R n n) (pivotRow x : Fin n)
    (col : Fin m) (hxp : x ≠ pivotRow) (hpivot : s.1[pivotRow][col] = 1) :
    (if _h : x = pivotRow then s
     else
       let coeff := -s.1[x][col]
       if coeff = 0 then s
       else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff)).1[x][col]
      = 0 := by
  rw [dif_neg hxp]
  by_cases hcoeff : -s.1[x][col] = 0
  · rw [if_pos hcoeff]
    have : s.1[x][col] = 0 := by
      have h := hcoeff
      grind
    exact this
  · rw [if_neg hcoeff]
    show (rowAdd s.1 pivotRow x (-s.1[x][col]))[x][col] = 0
    rw [rowAdd_get_dst s.1 pivotRow x (-s.1[x][col]) col]
    rw [hpivot]
    grind

/-- The pivot-row entries at column `col` are preserved through any fold of
`eliminateColumn`'s step function. -/
private theorem eliminateColumn_foldl_pivotRow
    (pivotRow : Fin n) (col : Fin m) (k : Fin m) :
    ∀ (xs : List (Fin n)) (s : Matrix R n m × Matrix R n n),
      (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
        if _h : j = pivotRow then state
        else
          let coeff := -state.1[j][col]
          if coeff = 0 then state
          else (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
        s).1[pivotRow][k]
        = s.1[pivotRow][k] := by
  intro xs
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih =>
      intro s
      simp only [List.foldl_cons]
      rw [ih]
      exact eliminateColumn_step_pivotRow_entry s pivotRow x col k

/-- Rows outside the fold's processed list are unchanged at column `col`. -/
private theorem eliminateColumn_foldl_outside
    (pivotRow : Fin n) (col : Fin m) :
    ∀ (xs : List (Fin n)) (s : Matrix R n m × Matrix R n n) (r : Fin n),
      r ∉ xs →
      (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
        if _h : j = pivotRow then state
        else
          let coeff := -state.1[j][col]
          if coeff = 0 then state
          else (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
        s).1[r][col]
        = s.1[r][col] := by
  intro xs
  induction xs with
  | nil => intro s r _; rfl
  | cons x xs ih =>
      intro s r hnotin
      have hrx : r ≠ x := fun h => hnotin (List.mem_cons.mpr (Or.inl h))
      have hrtail : r ∉ xs := fun h => hnotin (List.mem_cons.mpr (Or.inr h))
      simp only [List.foldl_cons]
      rw [ih _ r hrtail]
      exact eliminateColumn_step_other_entry s pivotRow x col hrx

/-- The whole pivot row is unchanged by `eliminateColumn` at column `k`. -/
private theorem eliminateColumn_pivotRow (M : Matrix R n m) (T : Matrix R n n)
    (pivotRow : Fin n) (col : Fin m) (k : Fin m) :
    (eliminateColumn M T pivotRow col).1[pivotRow][k] = M[pivotRow][k] := by
  unfold eliminateColumn
  exact eliminateColumn_foldl_pivotRow pivotRow col k (List.finRange n) (M, T)

/-- After `eliminateColumn`, every non-pivot row is zero in the pivot column,
provided the pivot row already has a `1` there. -/
private theorem eliminateColumn_zero (M : Matrix R n m) (T : Matrix R n n)
    (pivotRow : Fin n) (col : Fin m) (hpivot : M[pivotRow][col] = 1)
    (r : Fin n) (hne : r ≠ pivotRow) :
    (eliminateColumn M T pivotRow col).1[r][col] = 0 := by
  unfold eliminateColumn
  -- Walk along `List.finRange n` until we reach `r`, then show the rest of the
  -- fold leaves `r`'s column entry untouched.
  suffices h : ∀ (xs : List (Fin n)) (s : Matrix R n m × Matrix R n n),
      s.1[pivotRow][col] = (1 : R) →
      r ∈ xs → xs.Nodup →
      (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
        if _h : j = pivotRow then state
        else
          let coeff := -state.1[j][col]
          if coeff = 0 then state
          else (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
        s).1[r][col] = 0 from
    h (List.finRange n) (M, T) hpivot (List.mem_finRange r) (List.nodup_finRange n)
  intro xs
  induction xs with
  | nil => intro _ _ hmem _; cases hmem
  | cons x xs ih =>
      intro s hs hmem hnodup
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with hrx | hrtail
      · -- r = x: process this step, then the remaining fold leaves r untouched
        subst hrx
        have hr_notail : r ∉ xs := (List.nodup_cons.mp hnodup).1
        rw [eliminateColumn_foldl_outside pivotRow col xs _ r hr_notail]
        exact eliminateColumn_step_zero_at_x s pivotRow r col hne hs
      · -- r ≠ x: peel one step, preserve hypothesis, recurse
        have hpivot_step :
            ((if _h : x = pivotRow then s
              else
                let coeff := -s.1[x][col]
                if coeff = 0 then s
                else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff))).1[pivotRow][col]
              = (1 : R) := by
          rw [eliminateColumn_step_pivotRow_entry s pivotRow x col col]
          exact hs
        exact ih _ hpivot_step hrtail (List.nodup_cons.mp hnodup).2

/-- Same-operation preservation of `T * M = E` through one fold step of
`eliminateColumn`'s update: applying the same `rowAdd` to both `T` (transform)
and `E` (echelon) keeps `T * M = E`. -/
private theorem eliminateColumn_step_transform_preserve
    {M : Matrix R n m} (s : Matrix R n m × Matrix R n n) (pivotRow : Fin n)
    (col : Fin m) (x : Fin n) (h : s.2 * M = s.1) :
    (if _h : x = pivotRow then s
      else
        let coeff := -s.1[x][col]
        if coeff = 0 then s
        else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff)).2 * M
      = (if _h : x = pivotRow then s
          else
            let coeff := -s.1[x][col]
            if coeff = 0 then s
            else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff)).1 := by
  by_cases hx : x = pivotRow
  · rw [dif_pos hx]; exact h
  · rw [dif_neg hx]
    by_cases hcoeff : -s.1[x][col] = 0
    · rw [if_pos hcoeff]; exact h
    · rw [if_neg hcoeff]
      exact rowAdd_transform_mul_preserve pivotRow x (-s.1[x][col]) h

/-- Folding `eliminateColumn`'s step function over any list preserves the
same-operation invariant `state.2 * M = state.1`. -/
private theorem eliminateColumn_foldl_transform_preserve
    {M : Matrix R n m} (pivotRow : Fin n) (col : Fin m) :
    ∀ (xs : List (Fin n)) (s : Matrix R n m × Matrix R n n),
      s.2 * M = s.1 →
      (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
        if _h : j = pivotRow then state
        else
          let coeff := -state.1[j][col]
          if coeff = 0 then state
          else (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
        s).2 * M
        = (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
          if _h : j = pivotRow then state
          else
            let coeff := -state.1[j][col]
            if coeff = 0 then state
            else (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
          s).1 := by
  intro xs
  induction xs with
  | nil => intro s h; exact h
  | cons x xs ih =>
      intro s h
      simp only [List.foldl_cons]
      exact ih _ (eliminateColumn_step_transform_preserve s pivotRow col x h)

/-- Same-operation preservation: when `eliminateColumn` updates both `M` (the
echelon side) and `T` (the transform side) via the same row-add operations,
the equation `T * M_orig = M_current` is preserved. -/
private theorem eliminateColumn_transform_preserve
    {M : Matrix R n m} (T : Matrix R n n) (E : Matrix R n m)
    (pivotRow : Fin n) (col : Fin m) (h : T * M = E) :
    (eliminateColumn E T pivotRow col).2 * M = (eliminateColumn E T pivotRow col).1 := by
  unfold eliminateColumn
  exact eliminateColumn_foldl_transform_preserve pivotRow col (List.finRange n) (E, T) h

/-- One fold step of `eliminateColumn` preserves existence of a left inverse
for the transform side. -/
private theorem eliminateColumn_step_left_inverse_preserve
    (s : Matrix R n m × Matrix R n n) (pivotRow : Fin n) (col : Fin m)
    (x : Fin n) (h : ∃ Tinv : Matrix R n n, Tinv * s.2 = 1) :
    ∃ Tinv' : Matrix R n n,
      Tinv' *
        (if _h : x = pivotRow then s
         else
           let coeff := -s.1[x][col]
           if coeff = 0 then s
           else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff)).2 = 1 := by
  by_cases hx : x = pivotRow
  · rw [dif_pos hx]
    exact h
  · rw [dif_neg hx]
    by_cases hcoeff : -s.1[x][col] = 0
    · rw [if_pos hcoeff]
      exact h
    · rw [if_neg hcoeff]
      exact rowAdd_left_inverse_preserve s.2 (-s.1[x][col])
        (fun hpivotx => hx hpivotx.symm) h

/-- One fold step of `eliminateColumn` preserves existence of a right inverse
for the transform side. -/
private theorem eliminateColumn_step_right_inverse_preserve
    (s : Matrix R n m × Matrix R n n) (pivotRow : Fin n) (col : Fin m)
    (x : Fin n) (h : ∃ Tinv : Matrix R n n, s.2 * Tinv = 1) :
    ∃ Tinv' : Matrix R n n,
      (if _h : x = pivotRow then s
       else
         let coeff := -s.1[x][col]
         if coeff = 0 then s
         else (rowAdd s.1 pivotRow x coeff, rowAdd s.2 pivotRow x coeff)).2 *
        Tinv' = 1 := by
  by_cases hx : x = pivotRow
  · rw [dif_pos hx]
    exact h
  · rw [dif_neg hx]
    by_cases hcoeff : -s.1[x][col] = 0
    · rw [if_pos hcoeff]
      exact h
    · rw [if_neg hcoeff]
      exact rowAdd_right_inverse_preserve s.2 (-s.1[x][col])
        (fun hpivotx => hx hpivotx.symm) h

/-- Folding `eliminateColumn` preserves existence of a left inverse for the
transform side. -/
private theorem eliminateColumn_foldl_left_inverse_preserve
    (pivotRow : Fin n) (col : Fin m) :
    ∀ (xs : List (Fin n)) (s : Matrix R n m × Matrix R n n),
      (∃ Tinv : Matrix R n n, Tinv * s.2 = 1) →
      ∃ Tinv' : Matrix R n n,
        Tinv' *
          (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
            if _h : j = pivotRow then state
            else
              let coeff := -state.1[j][col]
              if coeff = 0 then state
              else (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
            s).2 = 1 := by
  intro xs
  induction xs with
  | nil =>
      intro s h
      exact h
  | cons x xs ih =>
      intro s h
      simp only [List.foldl_cons]
      exact ih _ (eliminateColumn_step_left_inverse_preserve s pivotRow col x h)

/-- Folding `eliminateColumn` preserves existence of a right inverse for the
transform side. -/
private theorem eliminateColumn_foldl_right_inverse_preserve
    (pivotRow : Fin n) (col : Fin m) :
    ∀ (xs : List (Fin n)) (s : Matrix R n m × Matrix R n n),
      (∃ Tinv : Matrix R n n, s.2 * Tinv = 1) →
      ∃ Tinv' : Matrix R n n,
        (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
          if _h : j = pivotRow then state
          else
            let coeff := -state.1[j][col]
            if coeff = 0 then state
            else (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
          s).2 *
          Tinv' = 1 := by
  intro xs
  induction xs with
  | nil =>
      intro s h
      exact h
  | cons x xs ih =>
      intro s h
      simp only [List.foldl_cons]
      exact ih _ (eliminateColumn_step_right_inverse_preserve s pivotRow col x h)

/-- `eliminateColumn` preserves existence of a left inverse for the transform
side. -/
private theorem eliminateColumn_left_inverse_preserve
    (T : Matrix R n n) (E : Matrix R n m) (pivotRow : Fin n) (col : Fin m)
    (h : ∃ Tinv : Matrix R n n, Tinv * T = 1) :
    ∃ Tinv' : Matrix R n n,
      Tinv' * (eliminateColumn E T pivotRow col).2 = 1 := by
  unfold eliminateColumn
  exact eliminateColumn_foldl_left_inverse_preserve pivotRow col (List.finRange n) (E, T) h

/-- `eliminateColumn` preserves existence of a right inverse for the transform
side. -/
private theorem eliminateColumn_right_inverse_preserve
    (T : Matrix R n n) (E : Matrix R n m) (pivotRow : Fin n) (col : Fin m)
    (h : ∃ Tinv : Matrix R n n, T * Tinv = 1) :
    ∃ Tinv' : Matrix R n n,
      (eliminateColumn E T pivotRow col).2 * Tinv' = 1 := by
  unfold eliminateColumn
  exact eliminateColumn_foldl_right_inverse_preserve pivotRow col (List.finRange n) (E, T) h

omit [Lean.Grind.Field R] [DecidableEq R] in
/-- Swapping the current row with the discovered pivot moves the nonzero pivot
entry into the target row. -/
private theorem rowSwap_target_pivot_entry
    (E : Matrix R n m) (target pivot : Fin n) (col : Fin m) :
    (rowSwap E target pivot)[target][col] = E[pivot][col] := by
  rw [rowSwap_getElem]
  by_cases h : target = pivot
  · simp [h]
  · simp [h]

omit [DecidableEq R] in
/-- Swapping two rows that are both zero in an already-canonical pivot column
preserves that column's canonical shape. -/
private theorem rowSwap_preserve_canonical_column
    (E : Matrix R n m) (pivotRow target pivot : Fin n) (oldCol : Fin m)
    (hTarget : E[target][oldCol] = 0) (hPivot : E[pivot][oldCol] = 0)
    (hrowTarget : pivotRow ≠ target) (hrowPivot : pivotRow ≠ pivot)
    (hpivotRow : E[pivotRow][oldCol] = 1)
    (hzero : ∀ r : Fin n, r ≠ pivotRow → E[r][oldCol] = 0) :
    (rowSwap E target pivot)[pivotRow][oldCol] = 1 ∧
      ∀ r : Fin n, r ≠ pivotRow → (rowSwap E target pivot)[r][oldCol] = 0 := by
  constructor
  · rw [rowSwap_getElem]
    simpa [hrowPivot, hrowTarget] using hpivotRow
  · intro r hr
    rw [rowSwap_getElem]
    by_cases hrPivot : r = pivot
    · simpa [hrPivot] using hTarget
    · by_cases hrTarget : r = target
      · by_cases htargetPivot : target = pivot
        · simpa [hrPivot, hrTarget, htargetPivot] using hTarget
        · simpa [hrPivot, hrTarget, htargetPivot] using hPivot
      · simpa [hrPivot, hrTarget] using hzero r hr

omit [DecidableEq R] in
/-- Scaling a row that is zero in an already-canonical pivot column preserves
that column's canonical shape. -/
private theorem rowScale_preserve_canonical_column
    (E : Matrix R n m) (pivotRow target : Fin n) (oldCol : Fin m) (c : R)
    (hTarget : E[target][oldCol] = 0) (hrowTarget : pivotRow ≠ target)
    (hpivotRow : E[pivotRow][oldCol] = 1)
    (hzero : ∀ r : Fin n, r ≠ pivotRow → E[r][oldCol] = 0) :
    (rowScale E target c)[pivotRow][oldCol] = 1 ∧
      ∀ r : Fin n, r ≠ pivotRow → (rowScale E target c)[r][oldCol] = 0 := by
  constructor
  · rw [rowScale_getElem]
    simpa [hrowTarget] using hpivotRow
  · intro r hr
    rw [rowScale_getElem]
    by_cases hrTarget : r = target
    · subst r
      rw [if_pos rfl, hTarget]
      grind
    · simpa [hrTarget] using hzero r hr

omit [DecidableEq R] in
/-- Adding a multiple of a row that is zero in an already-canonical pivot
column preserves that column's canonical shape. -/
private theorem rowAdd_preserve_canonical_column
    (E : Matrix R n m) (pivotRow src dst : Fin n) (oldCol : Fin m) (c : R)
    (hSrc : E[src][oldCol] = 0)
    (hpivotRow : E[pivotRow][oldCol] = 1)
    (hzero : ∀ r : Fin n, r ≠ pivotRow → E[r][oldCol] = 0) :
    (rowAdd E src dst c)[pivotRow][oldCol] = 1 ∧
      ∀ r : Fin n, r ≠ pivotRow → (rowAdd E src dst c)[r][oldCol] = 0 := by
  constructor
  · rw [rowAdd_getElem]
    by_cases hrowDst : pivotRow = dst
    · subst dst
      rw [if_pos rfl, hpivotRow, hSrc]
      grind
    · simpa [hrowDst] using hpivotRow
  · intro r hr
    rw [rowAdd_getElem]
    by_cases hrDst : r = dst
    · subst dst
      rw [if_pos rfl, hzero r hr, hSrc]
      grind
    · simpa [hrDst] using hzero r hr

/-- Eliminating a later pivot column preserves an already-canonical pivot
column when the later pivot row is zero in the old column. -/
private theorem eliminateColumn_preserve_canonical_column
    (E : Matrix R n m) (T : Matrix R n n) (oldPivot newPivot : Fin n)
    (oldCol newCol : Fin m) (hOldNew : oldPivot ≠ newPivot)
    (hNew : E[newPivot][oldCol] = 0)
    (hOld : E[oldPivot][oldCol] = 1)
    (hzero : ∀ r : Fin n, r ≠ oldPivot → E[r][oldCol] = 0) :
    (eliminateColumn E T newPivot newCol).1[oldPivot][oldCol] = 1 ∧
      ∀ r : Fin n, r ≠ oldPivot →
        (eliminateColumn E T newPivot newCol).1[r][oldCol] = 0 := by
  unfold eliminateColumn
  suffices h : ∀ (xs : List (Fin n)) (s : Matrix R n m × Matrix R n n),
      s.1[newPivot][oldCol] = 0 →
      s.1[oldPivot][oldCol] = 1 →
      (∀ r : Fin n, r ≠ oldPivot → s.1[r][oldCol] = 0) →
      (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
        if _h : j = newPivot then state
        else
          let coeff := -state.1[j][newCol]
          if coeff = 0 then state
          else (rowAdd state.1 newPivot j coeff, rowAdd state.2 newPivot j coeff))
        s).1[oldPivot][oldCol] = 1 ∧
      ∀ r : Fin n, r ≠ oldPivot →
        (xs.foldl (fun (state : Matrix R n m × Matrix R n n) j =>
          if _h : j = newPivot then state
          else
            let coeff := -state.1[j][newCol]
            if coeff = 0 then state
            else (rowAdd state.1 newPivot j coeff, rowAdd state.2 newPivot j coeff))
          s).1[r][oldCol] = 0 from
    h (List.finRange n) (E, T) hNew hOld hzero
  intro xs
  induction xs with
  | nil =>
      intro s _ hOld hzero
      exact ⟨hOld, hzero⟩
  | cons x xs ih =>
      intro s hSrc hOld hzero
      simp only [List.foldl_cons]
      by_cases hx : x = newPivot
      · simpa [hx] using ih s hSrc hOld hzero
      · by_cases hcoeff : -s.1[x][newCol] = 0
        · simpa only [hx, hcoeff, if_false, if_true] using ih s hSrc hOld hzero
        · let next : Matrix R n m × Matrix R n n :=
            (rowAdd s.1 newPivot x (-s.1[x][newCol]), rowAdd s.2 newPivot x (-s.1[x][newCol]))
          have hcanon :
              next.1[oldPivot][oldCol] = 1 ∧
                ∀ r : Fin n, r ≠ oldPivot → next.1[r][oldCol] = 0 := by
            simpa [next] using
              rowAdd_preserve_canonical_column s.1 oldPivot newPivot x oldCol
                (-s.1[x][newCol]) hSrc hOld hzero
          have hSrcNext : next.1[newPivot][oldCol] = 0 :=
            hcanon.2 newPivot (fun h => hOldNew h.symm)
          simpa only [hx, hcoeff, if_false, next] using ih next hSrcNext hcanon.1 hcanon.2

/-- Process columns left-to-right, performing Gauss-Jordan elimination. -/
def rrefLoop (col fuel : Nat) (state : RrefState R n m) : RrefState R n m :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hRow : state.row < n then
        if hCol : col < m then
          let colFin : Fin m := ⟨col, hCol⟩
          match findPivot? state.echelon colFin state.row with
          | none =>
              rrefLoop (col + 1) fuel state
          | some pivot =>
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              let nextState : RrefState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              rrefLoop (col + 1) fuel nextState
        else
          state
      else
        state

/-- Proof-only shape invariant for `rrefLoop`: the row counter tracks the
number of pivots, discovered pivot columns are strictly increasing, and all
recorded pivots lie before the next column to inspect. -/
private structure RrefShapeInvariant (col : Nat) (state : RrefState R n m) : Prop where
  row_eq_length : state.row = state.pivots.length
  row_le_n : state.row ≤ n
  length_le_col : state.pivots.length ≤ col
  pivots_sorted :
    ∀ (i j : Nat) (hi : i < state.pivots.length) (hj : j < state.pivots.length),
      i < j → state.pivots[i] < state.pivots[j]
  pivots_lt_col : ∀ p ∈ state.pivots, p.val < col

omit [Lean.Grind.Field R] [DecidableEq R] in
/-- `RrefShapeInvariant.mono_col` relaxes the column bound: the shape invariant
at `col` still holds at any larger column bound `col' ≥ col`. -/
private theorem RrefShapeInvariant.mono_col {col col' : Nat} {state : RrefState R n m}
    (hcol : col ≤ col') (h : RrefShapeInvariant (R := R) (n := n) (m := m) col state) :
    RrefShapeInvariant (R := R) (n := n) (m := m) col' state where
  row_eq_length := h.row_eq_length
  row_le_n := h.row_le_n
  length_le_col := Nat.le_trans h.length_le_col hcol
  pivots_sorted := h.pivots_sorted
  pivots_lt_col := fun p hp => Nat.lt_of_lt_of_le (h.pivots_lt_col p hp) hcol

/-- Proof-only invariant for `rrefLoop`: every processed pivot column is
canonical — the pivot row has entry `1`, and every other row has entry `0`.
The pivot row of the `i`-th pivot is row `i` of the echelon matrix. -/
private structure RrefCanonicalInvariant (state : RrefState R n m) : Prop where
  pivot_entry_one : ∀ (i : Nat) (hi : i < state.pivots.length) (hin : i < n),
    state.echelon[(⟨i, hin⟩ : Fin n)][state.pivots[i]] = 1
  other_entry_zero : ∀ (i : Nat) (hi : i < state.pivots.length) (r : Fin n),
    r.val ≠ i → state.echelon[r][state.pivots[i]] = 0

omit [Lean.Grind.Field R] [DecidableEq R] in
/-- `list_sorted_get_concat_of_lt`: appending a column index that is strictly
greater than every element of a strictly sorted pivot list keeps the list
strictly sorted. -/
private theorem list_sorted_get_concat_of_lt {ps : List (Fin m)} {col : Nat}
    (hsorted : ∀ (i j : Nat) (hi : i < ps.length) (hj : j < ps.length),
      i < j → ps[i] < ps[j])
    (hlt : ∀ p ∈ ps, p.val < col) (hCol : col < m) :
    ∀ (i j : Nat) (hi : i < (ps.concat ⟨col, hCol⟩).length)
      (hj : j < (ps.concat ⟨col, hCol⟩).length),
      i < j → (ps.concat ⟨col, hCol⟩)[i] < (ps.concat ⟨col, hCol⟩)[j] := by
  intro i j hi hj hij
  simp at hi hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjOld | hjLast
  · have hiOld : i < ps.length := by omega
    have get_i : (ps.concat ⟨col, hCol⟩)[i] = ps[i] := by
      have hiAppend : i < (ps ++ [(⟨col, hCol⟩ : Fin m)]).length := by
        simpa [List.concat_eq_append] using hi
      simpa [List.concat_eq_append] using
        (List.getElem_append_left (as := ps) (bs := [(⟨col, hCol⟩ : Fin m)]) hiOld
          (h' := hiAppend))
    have get_j : (ps.concat ⟨col, hCol⟩)[j] = ps[j] := by
      have hjAppend : j < (ps ++ [(⟨col, hCol⟩ : Fin m)]).length := by
        simpa [List.concat_eq_append] using hj
      simpa [List.concat_eq_append] using
        (List.getElem_append_left (as := ps) (bs := [(⟨col, hCol⟩ : Fin m)]) hjOld
          (h' := hjAppend))
    rw [get_i, get_j]
    exact hsorted i j hiOld hjOld hij
  · have hiOld : i < ps.length := by omega
    have get_i : (ps.concat ⟨col, hCol⟩)[i] = ps[i] := by
      have hiAppend : i < (ps ++ [(⟨col, hCol⟩ : Fin m)]).length := by
        simpa [List.concat_eq_append] using hi
      simpa [List.concat_eq_append] using
        (List.getElem_append_left (as := ps) (bs := [(⟨col, hCol⟩ : Fin m)]) hiOld
          (h' := hiAppend))
    have get_j : (ps.concat ⟨col, hCol⟩)[j] = ⟨col, hCol⟩ := by
      have hjAppend : j < (ps ++ [(⟨col, hCol⟩ : Fin m)]).length := by
        simpa [List.concat_eq_append] using hj
      simpa [List.concat_eq_append] using
        List.getElem_concat_length (l := ps) (a := ⟨col, hCol⟩) hjLast hjAppend
    rw [get_i, get_j]
    exact hlt ps[i] (List.getElem_mem hiOld)

omit [Lean.Grind.Field R] [DecidableEq R] in
/-- `rrefShapeInvariant_concat` is the one-step extension: recording a new pivot
at `col` (advancing the row and appending the column to `pivots`) preserves the
shape invariant at the next column bound `col + 1`. -/
private theorem rrefShapeInvariant_concat {col : Nat} {state : RrefState R n m}
    (h : RrefShapeInvariant (R := R) (n := n) (m := m) col state)
    (hRow : state.row < n) (hCol : col < m)
    (echelon : Matrix R n m) (transform : Matrix R n n) :
    RrefShapeInvariant (R := R) (n := n) (m := m) (col + 1)
      { row := state.row + 1
        echelon := echelon
        transform := transform
        pivots := state.pivots.concat ⟨col, hCol⟩ } where
  row_eq_length := by
    simp [h.row_eq_length]
  row_le_n := Nat.succ_le_of_lt hRow
  length_le_col := by
    simpa using Nat.succ_le_succ h.length_le_col
  pivots_sorted := by
    exact list_sorted_get_concat_of_lt h.pivots_sorted h.pivots_lt_col hCol
  pivots_lt_col := by
    intro p hp
    rw [List.concat_eq_append] at hp
    rcases List.mem_append.mp hp with hpOld | hpLast
    · exact Nat.lt_trans (h.pivots_lt_col p hpOld) (Nat.lt_succ_self col)
    · simp at hpLast
      subst hpLast
      exact Nat.lt_succ_self col


end FieldAlgorithms
end Matrix
end Hex
