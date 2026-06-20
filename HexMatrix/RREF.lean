import Std
import Batteries.Data.Vector.Lemmas
import HexMatrix.RowEchelon

/-!
Executable RREF, row-span, and nullspace routines for `hex-matrix`.

This module implements a simple Gaussian-elimination-based `rref` routine over
decidable fields, then exposes the row-span and nullspace APIs layered on top of
the resulting echelon data. It also states the theorem surface connecting the
computed data to the `IsRREF` contract and the derived span/nullspace
characterizations.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m : Nat}

/-- A linear combination of the rows of `M`, using coefficients `c`. -/
def rowCombination [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (c : Vector R n) :
    Vector R m :=
  Matrix.transpose M * c

private structure RrefState (R : Type u) (n m : Nat) where
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
private def rrefLoop (col fuel : Nat) (state : RrefState R n m) : RrefState R n m :=
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

omit [DecidableEq R] in
/-- The empty-pivot initial state trivially satisfies the canonical-column
invariant. -/
private theorem rrefLoop_initial_canonical (M : Matrix R n m) :
    RrefCanonicalInvariant (R := R) (n := n) (m := m)
      { row := 0, echelon := M, transform := 1, pivots := [] } where
  pivot_entry_one := by intro i hi _; exact absurd hi (by simp)
  other_entry_zero := by intro i hi _ _; exact absurd hi (by simp)

/-- One pivot iteration of `rrefLoop` preserves the canonical-column
invariant: every previously processed pivot column remains canonical, and
the newly added pivot column is canonical with the just-discovered pivot
row. -/
private theorem rrefCanonicalInvariant_pivot_step
    {col : Nat} {state : RrefState R n m}
    (hshape : RrefShapeInvariant (R := R) (n := n) (m := m) col state)
    (hcanon : RrefCanonicalInvariant (R := R) (n := n) (m := m) state)
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
    RrefCanonicalInvariant (R := R) (n := n) (m := m)
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
        rowSwap_target_pivot_entry state.echelon target pivot colFin
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
          rowScale_getElem swappedEchelon target target pivotVal⁻¹ colFin
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

/-- `rrefLoop_shape`: `rrefLoop` preserves the shape invariant, advancing the
column bound from `col` to `col + fuel`. -/
private theorem rrefLoop_shape :
    ∀ (fuel col : Nat) (state : RrefState R n m),
      RrefShapeInvariant (R := R) (n := n) (m := m) col state →
      RrefShapeInvariant (R := R) (n := n) (m := m) (col + fuel)
        (rrefLoop (R := R) (n := n) (m := m) col fuel state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro col state h
      simpa [rrefLoop] using h
  | succ fuel ih =>
      intro col state h
      unfold rrefLoop
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
              let nextState : RrefState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              have hnext :
                  RrefShapeInvariant (R := R) (n := n) (m := m) (col + 1) nextState := by
                simpa [nextState, colFin] using rrefShapeInvariant_concat (R := R) (n := n) (m := m)
                  (col := col) (state := state) h hRow hCol eliminated.1 eliminated.2
              simpa [hpivot, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, nextState, colFin, target,
                swappedEchelon, swappedTransform, pivotVal, scaledEchelon, scaledTransform,
                eliminated] using ih (col + 1) nextState hnext
        · rw [dif_neg hCol]
          exact h.mono_col (by omega)
      · rw [dif_neg hRow]
        exact h.mono_col (by omega)

omit [DecidableEq R] in
/-- `rrefLoop_initial_shape`: the initial RREF state (row 0, no pivots) satisfies
the shape invariant at column bound 0. -/
private theorem rrefLoop_initial_shape (M : Matrix R n m) :
    RrefShapeInvariant (R := R) (n := n) (m := m) 0
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

/-- `rref_final_shape`: the matrix produced by the full `rrefLoop` run over all
`m` columns satisfies the shape invariant at column bound `m`. -/
private theorem rref_final_shape (M : Matrix R n m) :
    RrefShapeInvariant (R := R) (n := n) (m := m) m
      (rrefLoop 0 m
        { row := 0
          echelon := M
          transform := 1
          pivots := [] }) := by
  simpa using rrefLoop_shape (R := R) (n := n) (m := m) m 0
    { row := 0
      echelon := M
      transform := 1
      pivots := [] } (rrefLoop_initial_shape M)

/-- The canonical-column invariant is preserved through `rrefLoop`. -/
private theorem rrefLoop_canonical :
    ∀ (fuel col : Nat) (state : RrefState R n m),
      RrefShapeInvariant (R := R) (n := n) (m := m) col state →
      RrefCanonicalInvariant (R := R) (n := n) (m := m) state →
      RrefCanonicalInvariant (R := R) (n := n) (m := m)
        (rrefLoop (R := R) (n := n) (m := m) col fuel state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro col state _hshape hcanon
      simpa [rrefLoop] using hcanon
  | succ fuel ih =>
      intro col state hshape hcanon
      unfold rrefLoop
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
              let nextState : RrefState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              have hnext_shape :
                  RrefShapeInvariant (R := R) (n := n) (m := m) (col + 1) nextState := by
                simpa [nextState, colFin] using
                  rrefShapeInvariant_concat (R := R) (n := n) (m := m)
                    (col := col) (state := state) hshape hRow hCol
                    eliminated.1 eliminated.2
              have hnext_canon :
                  RrefCanonicalInvariant (R := R) (n := n) (m := m) nextState := by
                simpa [nextState, colFin, target, swappedEchelon,
                  swappedTransform, pivotVal, scaledEchelon, scaledTransform,
                  eliminated] using
                  rrefCanonicalInvariant_pivot_step (R := R) (n := n) (m := m)
                    (col := col) (state := state) hshape hcanon hRow hCol hpivot
              simpa [hpivot, nextState, colFin, target, swappedEchelon,
                swappedTransform, pivotVal, scaledEchelon, scaledTransform,
                eliminated] using
                ih (col + 1) nextState hnext_shape hnext_canon
        · rw [dif_neg hCol]
          exact hcanon
      · rw [dif_neg hRow]
        exact hcanon

/-- `rref_final_canonical`: the matrix produced by the full `rrefLoop` run over
all `m` columns satisfies the canonical-column invariant. -/
private theorem rref_final_canonical (M : Matrix R n m) :
    RrefCanonicalInvariant (R := R) (n := n) (m := m)
      (rrefLoop 0 m
        { row := 0
          echelon := M
          transform := 1
          pivots := [] }) := by
  exact rrefLoop_canonical (R := R) (n := n) (m := m) m 0
    { row := 0, echelon := M, transform := 1, pivots := [] }
    (rrefLoop_initial_shape M) (rrefLoop_initial_canonical M)

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
  rw [rowSwap_getElem]
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
  rw [rowScale_getElem]
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
        rw [eliminateColumn_step_pivotRow_entry s pivotRow x col k]
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

/-- Proof-only invariant tracking the no-pivot branch of `rrefLoop`: every
already-processed column that has not been recorded as a pivot is zero on every
row at or below `state.row`. -/
private structure RrefNoPivotZero (col : Nat) (state : RrefState R n m) : Prop where
  zero_unrecorded :
    ∀ (c : Fin m), c.val < col → c ∉ state.pivots →
      ∀ (r : Fin n), state.row ≤ r.val → state.echelon[r][c] = 0

omit [DecidableEq R] in
/-- `rrefNoPivotZero_initial`: the initial RREF state satisfies the
no-pivot-zero invariant at column bound 0, vacuously. -/
private theorem rrefNoPivotZero_initial (M : Matrix R n m) :
    RrefNoPivotZero (R := R) (n := n) (m := m) 0
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
private theorem RrefNoPivotZero.widen_col_at_m {col col' : Nat}
    {state : RrefState R n m}
    (h : RrefNoPivotZero (R := R) (n := n) (m := m) col state) (hcol : m ≤ col) :
    RrefNoPivotZero (R := R) (n := n) (m := m) col' state where
  zero_unrecorded := fun c _ hcnot r hr =>
    h.zero_unrecorded c (Nat.lt_of_lt_of_le c.isLt hcol) hcnot r hr

omit [DecidableEq R] in
/-- When the loop exits with `n ≤ state.row`, the invariant extends vacuously
to any column bound: no row index satisfies the hypothesis. -/
private theorem RrefNoPivotZero.widen_col_at_n {col col' : Nat}
    {state : RrefState R n m}
    (_h : RrefNoPivotZero (R := R) (n := n) (m := m) col state) (hrow : n ≤ state.row) :
    RrefNoPivotZero (R := R) (n := n) (m := m) col' state where
  zero_unrecorded := fun _ _ _ r hr => by
    have hge : n ≤ r.val := Nat.le_trans hrow hr
    exact absurd r.isLt (Nat.not_lt_of_ge hge)

/-- `rrefLoop_no_pivot_zero`: `rrefLoop` preserves the no-pivot-zero invariant,
advancing the column bound from `col` to `col + fuel`. -/
private theorem rrefLoop_no_pivot_zero :
    ∀ (fuel col : Nat) (state : RrefState R n m),
      RrefNoPivotZero col state →
      RrefNoPivotZero (col + fuel)
        (rrefLoop (R := R) (n := n) (m := m) col fuel state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro col state h
      simpa [rrefLoop] using h
  | succ fuel ih =>
      intro col state h
      unfold rrefLoop
      by_cases hRow : state.row < n
      · rw [dif_pos hRow]
        by_cases hCol : col < m
        · rw [dif_pos hCol]
          cases hpivot : findPivot? state.echelon ⟨col, hCol⟩ state.row with
          | none =>
              have hnext : RrefNoPivotZero (R := R) (n := n) (m := m) (col + 1) state := by
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
              let nextState : RrefState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              have hpivot_ge : state.row ≤ pivot.val :=
                findPivot?_some_ge state.echelon colFin hpivot
              have htarget_val : (target : Fin n).val = state.row := rfl
              have hnext :
                  RrefNoPivotZero (R := R) (n := n) (m := m) (col + 1) nextState := by
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

/-- `rref_final_no_pivot_zero`: the matrix produced by the full `rrefLoop` run
over all `m` columns satisfies the no-pivot-zero invariant at column bound `m`. -/
private theorem rref_final_no_pivot_zero (M : Matrix R n m) :
    RrefNoPivotZero (R := R) (n := n) (m := m) m
      (rrefLoop 0 m
        { row := 0
          echelon := M
          transform := 1
          pivots := [] }) := by
  simpa using rrefLoop_no_pivot_zero (R := R) (n := n) (m := m) m 0
    { row := 0
      echelon := M
      transform := 1
      pivots := [] } (rrefNoPivotZero_initial M)

/-- `rrefLoop` preserves existence of a left inverse for the transform. -/
private theorem rrefLoop_left_inverse_preserve (col fuel : Nat)
    (state : RrefState R n m)
    (h : ∃ Tinv : Matrix R n n, Tinv * state.transform = 1) :
    ∃ Tinv' : Matrix R n n,
      Tinv' * (rrefLoop col fuel state).transform = 1 := by
  induction fuel generalizing col state with
  | zero =>
      simpa [rrefLoop] using h
  | succ fuel ih =>
      by_cases hRow : state.row < n
      · by_cases hCol : col < m
        ·
          let colFin : Fin m := ⟨col, hCol⟩
          cases hpivot : findPivot? state.echelon colFin state.row with
          | none =>
              simpa [rrefLoop, hRow, hCol, colFin, hpivot] using ih (col + 1) state h
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
              have hswap :
                  ∃ Tinv : Matrix R n n, Tinv * swappedTransform = 1 :=
                rowSwap_left_inverse_preserve state.transform target pivot h
              have hpivotVal : pivotVal ≠ 0 := by
                have hpivotNonzero := findPivot?_some_nonzero state.echelon colFin hpivot
                have hentry : pivotVal = state.echelon[pivot][colFin] := by
                  simpa [pivotVal, swappedEchelon] using
                    (rowSwap_target_pivot_entry state.echelon target pivot colFin)
                simpa [hentry] using hpivotNonzero
              have hscale :
                  ∃ Tinv : Matrix R n n, Tinv * scaledTransform = 1 :=
                rowScale_left_inverse_preserve swappedTransform target
                  (show pivotVal⁻¹ ≠ 0 by grind) hswap
              have helim :
                  ∃ Tinv : Matrix R n n, Tinv * eliminated.2 = 1 :=
                eliminateColumn_left_inverse_preserve scaledTransform scaledEchelon target colFin hscale
              simpa [rrefLoop, hRow, hCol, colFin, hpivot, target, swappedEchelon,
                swappedTransform, pivotVal, scaledEchelon, scaledTransform, eliminated,
                nextState] using ih (col + 1) nextState helim
        · simpa [rrefLoop, hRow, hCol] using h
      · simpa [rrefLoop, hRow] using h

/-- `rrefLoop` preserves existence of a right inverse for the transform. -/
private theorem rrefLoop_right_inverse_preserve (col fuel : Nat)
    (state : RrefState R n m)
    (h : ∃ Tinv : Matrix R n n, state.transform * Tinv = 1) :
    ∃ Tinv' : Matrix R n n,
      (rrefLoop col fuel state).transform * Tinv' = 1 := by
  induction fuel generalizing col state with
  | zero =>
      simpa [rrefLoop] using h
  | succ fuel ih =>
      by_cases hRow : state.row < n
      · by_cases hCol : col < m
        ·
          let colFin : Fin m := ⟨col, hCol⟩
          cases hpivot : findPivot? state.echelon colFin state.row with
          | none =>
              simpa [rrefLoop, hRow, hCol, colFin, hpivot] using ih (col + 1) state h
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
              have hswap :
                  ∃ Tinv : Matrix R n n, swappedTransform * Tinv = 1 :=
                rowSwap_right_inverse_preserve state.transform target pivot h
              have hpivotVal : pivotVal ≠ 0 := by
                have hpivotNonzero := findPivot?_some_nonzero state.echelon colFin hpivot
                have hentry : pivotVal = state.echelon[pivot][colFin] := by
                  simpa [pivotVal, swappedEchelon] using
                    (rowSwap_target_pivot_entry state.echelon target pivot colFin)
                simpa [hentry] using hpivotNonzero
              have hscale :
                  ∃ Tinv : Matrix R n n, scaledTransform * Tinv = 1 :=
                rowScale_right_inverse_preserve swappedTransform target
                  (show pivotVal⁻¹ ≠ 0 by grind) hswap
              have helim :
                  ∃ Tinv : Matrix R n n, eliminated.2 * Tinv = 1 :=
                eliminateColumn_right_inverse_preserve scaledTransform scaledEchelon target colFin hscale
              simpa [rrefLoop, hRow, hCol, colFin, hpivot, target, swappedEchelon,
                swappedTransform, pivotVal, scaledEchelon, scaledTransform, eliminated,
                nextState] using ih (col + 1) nextState helim
        · simpa [rrefLoop, hRow, hCol] using h
      · simpa [rrefLoop, hRow] using h

/-- The Gauss-Jordan loop preserves the same-operation transform invariant:
the recorded transform applied to the original matrix is the current echelon
matrix. -/
private theorem rrefLoop_transform_preserve (M : Matrix R n m) :
    ∀ (col fuel : Nat) (state : RrefState R n m),
      state.transform * M = state.echelon →
      (rrefLoop col fuel state).transform * M = (rrefLoop col fuel state).echelon := by
  intro col fuel
  induction fuel generalizing col with
  | zero =>
      intro state h
      simp [rrefLoop, h]
  | succ fuel ih =>
      intro state h
      unfold rrefLoop
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
def rref (M : Matrix R n m) : RowEchelonData R n m :=
  let final := rrefLoop 0 m
    { row := 0
      echelon := M
      transform := 1
      pivots := [] }
  { rank := final.pivots.length
    echelon := final.echelon
    transform := final.transform
    pivotCols := ⟨final.pivots.toArray, by simp⟩ }

/-- Wrapper-level projection of the rank row bound from `rref_isRREF M`. -/
theorem rref_rank_le_n (M : Matrix R n m) : (rref M).rank ≤ n := by
  unfold rref
  change (rrefLoop 0 m { row := 0, echelon := M, transform := 1, pivots := [] }).pivots.length ≤ n
  rw [← (rref_final_shape M).row_eq_length]
  exact (rref_final_shape M).row_le_n

/-- Wrapper-level projection of the rank column bound from `rref_isRREF M`. -/
theorem rref_rank_le_m (M : Matrix R n m) : (rref M).rank ≤ m := by
  unfold rref
  exact (rref_final_shape M).length_le_col

/-- Wrapper-level projection of pivot-column sortedness from `rref_isRREF M`. -/
theorem rref_pivotCols_sorted (M : Matrix R n m) :
    ∀ i j, i < j → (rref M).pivotCols.get i < (rref M).pivotCols.get j := by
  intro i j hij
  unfold rref
  let final := rrefLoop 0 m
    { row := 0
      echelon := M
      transform := 1
      pivots := [] }
  have hshape : RrefShapeInvariant (R := R) (n := n) (m := m) m final := by
    simpa [final] using rref_final_shape M
  change (⟨final.pivots.toArray, by simp⟩ : Vector (Fin m) final.pivots.length).get i <
    (⟨final.pivots.toArray, by simp⟩ : Vector (Fin m) final.pivots.length).get j
  simpa [Vector.get, List.getElem_toArray] using
    hshape.pivots_sorted i.val j.val i.isLt j.isLt hij

/-- Final `rref` row transform has a left inverse. -/
private theorem rref_transform_left_inverse (M : Matrix R n m) :
    ∃ Tinv : Matrix R n n, Tinv * (rref M).transform = 1 := by
  unfold rref
  exact rrefLoop_left_inverse_preserve 0 m
    { row := 0, echelon := M, transform := 1, pivots := [] }
    ⟨1, by rw [one_mul]⟩

/-- Final `rref` row transform has a right inverse. -/
private theorem rref_transform_right_inverse (M : Matrix R n m) :
    ∃ Tinv : Matrix R n n, (rref M).transform * Tinv = 1 := by
  unfold rref
  exact rrefLoop_right_inverse_preserve 0 m
    { row := 0, echelon := M, transform := 1, pivots := [] }
    ⟨1, by rw [one_mul]⟩

/-- Wrapper-level projection of the transform equation from `rref_isRREF M`. -/
theorem rref_transform_mul (M : Matrix R n m) :
    (rref M).transform * M = (rref M).echelon := by
  unfold rref
  exact rrefLoop_transform_preserve M 0 m
    { row := 0
      echelon := M
      transform := 1
      pivots := [] }
    (by rw [Matrix.one_mul])

/-- The computed `rref` data satisfies the `IsRREF` contract. -/
theorem rref_isRREF (M : Matrix R n m) : IsRREF M (rref M) := by
  let final := rrefLoop 0 m
    { row := 0, echelon := M, transform := 1, pivots := [] }
  have hcanon : RrefCanonicalInvariant (R := R) (n := n) (m := m) final := by
    simpa [final] using rref_final_canonical M
  have hshape : RrefShapeInvariant (R := R) (n := n) (m := m) m final := by
    simpa [final] using rref_final_shape M
  have hrank_eq : (rref M).rank = final.pivots.length := by simp [rref, final]
  have hechelon_eq : (rref M).echelon = final.echelon := by simp [rref, final]
  have hpivotCol_get : ∀ (i : Fin (rref M).rank)
      (hi : i.val < final.pivots.length),
      ((rref M).pivotCols.get i).val = (final.pivots[i.val]'hi).val := by
    intro i _hi
    simp [rref, final, Vector.get, List.getElem_toArray]
  refine
    { toIsEchelonForm :=
        { transform_mul := rref_transform_mul M
          transform_inv := rref_transform_left_inverse M
          transform_right_inv := rref_transform_right_inverse M
          rank_le_n := rref_rank_le_n M
          rank_le_m := rref_rank_le_m M
          pivotCols_sorted := rref_pivotCols_sorted M
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
    have hcol_eq : (rref M).pivotCols.get i = final.pivots[i.val] :=
      Fin.ext (hpivotCol_get i hi_lt_len)
    have hech : (rref M).echelon[i][(rref M).pivotCols.get i] =
        final.echelon[(⟨i.val, hin⟩ : Fin n)][final.pivots[i.val]] := by
      simp only [hechelon_eq, hcol_eq]
      rfl
    rw [hech]
    exact hentry
  case apz =>
    intro i j hji
    have hi_lt_len : i.val < final.pivots.length := hrank_eq ▸ i.isLt
    have hentry := hcanon.other_entry_zero i.val hi_lt_len j (Nat.ne_of_lt hji)
    have hcol_eq : (rref M).pivotCols.get i = final.pivots[i.val] :=
      Fin.ext (hpivotCol_get i hi_lt_len)
    have hech : (rref M).echelon[j][(rref M).pivotCols.get i] =
        final.echelon[j][final.pivots[i.val]] := by
      simp only [hcol_eq, hechelon_eq]
    rw [hech]
    exact hentry
  case bpz =>
    intro i j hij
    have hi_lt_len : i.val < final.pivots.length := hrank_eq ▸ i.isLt
    have hentry := hcanon.other_entry_zero i.val hi_lt_len j (Nat.ne_of_gt hij)
    have hcol_eq : (rref M).pivotCols.get i = final.pivots[i.val] :=
      Fin.ext (hpivotCol_get i hi_lt_len)
    have hech : (rref M).echelon[j][(rref M).pivotCols.get i] =
        final.echelon[j][final.pivots[i.val]] := by
      simp only [hcol_eq, hechelon_eq]
    rw [hech]
    exact hentry
  case zr =>
    intro i hi
    have hno_pivot : RrefNoPivotZero (R := R) (n := n) (m := m) m final := by
      simpa [final] using rref_final_no_pivot_zero M
    have hi_ge : final.pivots.length ≤ i.val := hrank_eq ▸ hi
    have hrow_le_i : final.row ≤ i.val := hshape.row_eq_length ▸ hi_ge
    rw [hechelon_eq]
    apply Vector.ext
    intro c hc
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

namespace IsEchelonForm

/-- Row combinations transport forward along the echelon transform. -/
theorem rowCombination_transform_transpose [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) (e : Vector R n) :
    rowCombination M (Matrix.transpose D.transform * e) =
      rowCombination D.echelon e := by
  unfold rowCombination
  calc
    Matrix.transpose M * (Matrix.transpose D.transform * e) =
        (Matrix.transpose M * Matrix.transpose D.transform) * e := by
          exact (Matrix.mul_assoc_vec (A := Matrix.transpose M)
            (B := Matrix.transpose D.transform) (v := e)).symm
    _ = Matrix.transpose (D.transform * M) * e := by
          rw [← Matrix.transpose_mul_of_mul_comm Lean.Grind.CommSemiring.mul_comm]
    _ = Matrix.transpose D.echelon * e := by
          rw [E.transform_mul]

/-- Converse row-combination transport: an `M`-row-combination witness `c`
yields a `D.echelon`-row-combination witness `Matrix.transpose Tinv * c`,
where `Tinv` is any left inverse of `D.transform`. The proof reuses the
forward transport at the candidate witness. -/
theorem rowCombination_transformInv_transpose [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) {Tinv : Matrix R n n}
    (hTinv : Tinv * D.transform = 1) (c : Vector R n) :
    rowCombination D.echelon (Matrix.transpose Tinv * c) = rowCombination M c := by
  have hcompose :
      Matrix.transpose D.transform * (Matrix.transpose Tinv * c) = c := by
    calc
      Matrix.transpose D.transform * (Matrix.transpose Tinv * c) =
          (Matrix.transpose D.transform * Matrix.transpose Tinv) * c := by
            exact (Matrix.mul_assoc_vec (A := Matrix.transpose D.transform)
              (B := Matrix.transpose Tinv) (v := c)).symm
      _ = Matrix.transpose (Tinv * D.transform) * c := by
            rw [← Matrix.transpose_mul_of_mul_comm Lean.Grind.CommSemiring.mul_comm]
      _ = Matrix.transpose (1 : Matrix R n n) * c := by
            rw [hTinv]
      _ = (1 : Matrix R n n) * c := by
            rw [Matrix.transpose_one]
      _ = c := Matrix.one_mulVec c
  have hforward := E.rowCombination_transform_transpose (e := Matrix.transpose Tinv * c)
  rw [hcompose] at hforward
  exact hforward.symm

/-- Existential converse transport: any `v` in the row span of `M` is also in
the row span of `D.echelon`, with an explicit witness produced from a left
inverse of `D.transform`. -/
theorem exists_rowCombination_echelon_of_M [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) {v : Vector R m}
    (h : ∃ c : Vector R n, rowCombination M c = v) :
    ∃ d : Vector R n, rowCombination D.echelon d = v := by
  rcases h with ⟨c, hc⟩
  rcases E.transform_inv with ⟨Tinv, hTinv⟩
  refine ⟨Matrix.transpose Tinv * c, ?_⟩
  rw [E.rowCombination_transformInv_transpose hTinv c, hc]

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}

/-- The echelon-side coefficients selected by pivot coordinates. -/
private def echelonCoeffs [Lean.Grind.Field R] (E : IsEchelonForm M D)
    (v : Vector R m) : Vector R n :=
  Vector.ofFn fun i =>
    if h : i.val < D.rank then
      let pi : Fin D.rank := ⟨i.val, h⟩
      v[D.pivotCols.get pi] /
        D.echelon[(IsEchelonForm.pivotRow E pi)][D.pivotCols.get pi]
    else
      0

/-- Coefficients for expressing `v` in the row span, if the echelon rows solve it. -/
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Option (Vector R n) :=
  let coeffs := Matrix.transpose D.transform * E.echelonCoeffs v
  if rowCombination M coeffs = v then
    some coeffs
  else
    none

/-- Decidable row-span membership test derived from `spanCoeffs`. -/
def spanContains [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Bool :=
  (E.spanCoeffs v).isSome

/-- `spanContains` is the Boolean `isSome` view of `spanCoeffs`. -/
@[simp, grind =] theorem spanContains_eq_isSome [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (v : Vector R m) :
    E.spanContains v = (E.spanCoeffs v).isSome := rfl

/-- `spanCoeffs` returns coefficients whose row combination equals `v`. -/
theorem spanCoeffs_sound [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (v : Vector R m) (c : Vector R n) :
    E.spanCoeffs v = some c → rowCombination M c = v := by
  intro h
  unfold spanCoeffs at h
  dsimp only at h
  split at h
  · rename_i hspan
    injection h with hc
    subst c
    exact hspan
  · contradiction

/-- If `spanContains` succeeds, the vector is in the row span. -/
theorem spanContains_sound [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (v : Vector R m) :
    E.spanContains v = true → ∃ c : Vector R n, rowCombination M c = v := by
  intro h
  unfold spanContains at h
  cases hCoeffs : E.spanCoeffs v with
  | none =>
      simp [hCoeffs] at h
  | some c =>
      exact ⟨c, E.spanCoeffs_sound v c hCoeffs⟩

end IsEchelonForm

namespace IsRREF

/-- RREF data has nonzero pivots because every pivot is normalized to one. -/
theorem hasNonzeroPivots [Lean.Grind.Field R]
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D) :
    E.toIsEchelonForm.HasNonzeroPivots := by
  intro i
  have hpivot :
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] = 1 := by
    simpa [IsEchelonForm.pivotRow] using E.pivot_one i
  intro hzero
  exact (show (0 : R) ≠ 1 from Lean.Grind.Field.zero_ne_one) (hzero.symm.trans hpivot)

variable {M : Matrix R n m} {D : RowEchelonData R n m}

private theorem foldl_add_eq_acc_ring {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hac : acc + (0 : R) = acc := by grind
      rw [hac]
      exact ih acc hxs

private theorem foldl_sum_congr {R : Type u} [Add R]
    {α : Type v} (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs

private theorem foldl_indicator_mul_unique {R : Type u} [Lean.Grind.Ring R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (f : Fin n → R)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0) * f l) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · subst i
        have hxs_zero :
            ∀ y ∈ xs, (if x = y then (1 : R) else 0) * f y = 0 := by
          intro y hy
          have hxy : x ≠ y := fun heq => (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hxy]
          grind
        rw [if_pos rfl]
        rw [foldl_add_eq_acc_ring xs _ _ hxs_zero]
        grind
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : (0 : R) * f x = 0 := by grind
        rw [hzero]
        have hacc : acc + (0 : R) = acc := by grind
        rw [hacc]
        rw [ih hitail (List.nodup_cons.mp hnodup).2 acc]

/-- A row-combination vector with a single coefficient `1` at row `i`
and zero elsewhere selects exactly row `i` of the matrix. This packages
the singleton-row case used by span and RREF arguments. -/
theorem rowCombination_single {R : Type u} [Lean.Grind.CommRing R]
    {n m : Nat} (M : Matrix R n m) (i : Fin n) :
    rowCombination M (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0) =
      row M i := by
  apply Vector.ext
  intro j hj
  let jf : Fin m := ⟨j, hj⟩
  change
    (rowCombination M (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0))[jf] =
      (row M i)[jf]
  unfold rowCombination
  change (Matrix.mulVec (Matrix.transpose M)
      (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0))[jf] =
    (row M i)[jf]
  unfold Matrix.mulVec Matrix.dot Matrix.row Hex.Vector.dotProduct Matrix.transpose
    Matrix.col
  change (Vector.ofFn fun j : Fin m =>
      (List.finRange n).foldl
        (fun acc l => acc + (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[j][l] *
          (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]) 0).get jf =
    M[i][jf]
  rw [Vector.get_ofFn]
  change
    (List.finRange n).foldl
        (fun acc l => acc +
          (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[jf][l] *
          (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]) 0 =
      M[i][jf]
  have hbody :
      (List.finRange n).foldl
          (fun acc l => acc +
            (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[jf][l] *
            (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]) 0 =
        (List.finRange n).foldl
          (fun acc l => acc + (if i = l then (1 : R) else 0) * M[l][jf]) 0 := by
    apply foldl_sum_congr
    intro l _hl
    by_cases hil : i = l
    · simp [hil, Lean.Grind.CommSemiring.mul_comm]
    · rw [if_neg hil]
      grind
  rw [hbody]
  have hpick := foldl_indicator_mul_unique (R := R) (List.finRange n) i
    (fun l : Fin n => M[l][jf]) (List.mem_finRange i) (List.nodup_finRange n) 0
  have hzero : (0 : R) + M[i][jf] = M[i][jf] := by grind
  exact hpick.trans hzero

/-- In an RREF, a pivot column is a standard basis vector: its entry in row `i`
is `1` when `i` is the pivot row of `p` and `0` otherwise. -/
private theorem pivot_column_entry [Lean.Grind.Field R] (E : IsRREF M D)
    (p : Fin D.rank) (i : Fin n) :
    D.echelon[i][D.pivotCols.get p] =
      if E.toIsEchelonForm.pivotRow p = i then 1 else 0 := by
  by_cases hi : i.val < D.rank
  · let q : Fin D.rank := ⟨i.val, hi⟩
    by_cases hpq : p = q
    · subst q
      have hip : E.toIsEchelonForm.pivotRow p = i := by
        apply Fin.ext
        simpa [IsEchelonForm.pivotRow] using congrArg Fin.val hpq
      rw [if_pos hip]
      subst p
      simpa [IsEchelonForm.pivotRow] using E.pivot_one ⟨i.val, hi⟩
    · have hrow_ne : E.toIsEchelonForm.pivotRow p ≠ i := by
        intro hrow
        apply hpq
        apply Fin.ext
        simpa [IsEchelonForm.pivotRow] using congrArg Fin.val hrow
      rw [if_neg hrow_ne]
      have hne : i.val ≠ p.val := by
        intro hval
        apply hpq
        apply Fin.ext
        exact hval.symm
      cases Nat.lt_or_gt_of_ne hne with
      | inl hip =>
          exact E.above_pivot_zero p i hip
      | inr hpi =>
          exact E.toIsEchelonForm.below_pivot_zero p i hpi
  · have hrow_ne : E.toIsEchelonForm.pivotRow p ≠ i := by
      intro hrow
      apply hi
      rw [← Fin.ext_iff.mp hrow]
      exact p.isLt
    rw [if_neg hrow_ne]
    have hzero := E.toIsEchelonForm.zero_row i (by omega)
    simpa using congrArg (fun row => row[D.pivotCols.get p]) hzero

/-- Reading a row combination of the echelon rows off at pivot column `p` recovers
exactly the coefficient applied to the pivot row of `p`, since that column is a
standard basis vector. -/
private theorem rowCombination_pivotCoeff [Lean.Grind.Field R] (E : IsRREF M D)
    (c : Vector R n) (p : Fin D.rank) :
    (rowCombination D.echelon c)[D.pivotCols.get p] =
      c[E.toIsEchelonForm.pivotRow p] := by
  unfold rowCombination
  simp [HMul.hMul, Matrix.mulVec, Matrix.dot, Matrix.row, Hex.Vector.dotProduct,
    Matrix.transpose, Matrix.col]
  change (List.finRange n).foldl
      (fun acc i => acc + D.echelon[i][D.pivotCols.get p] * c[i]) 0 =
    c[E.toIsEchelonForm.pivotRow p]
  calc
    (List.finRange n).foldl
        (fun acc i => acc + D.echelon[i][D.pivotCols.get p] * c[i]) 0 =
        (List.finRange n).foldl
          (fun acc i =>
            acc + (if E.toIsEchelonForm.pivotRow p = i then (1 : R) else 0) * c[i]) 0 := by
          apply foldl_sum_congr
          intro i _hi
          rw [pivot_column_entry E p i]
    _ = c[E.toIsEchelonForm.pivotRow p] := by
          have h :=
            foldl_indicator_mul_unique (List.finRange n) (E.toIsEchelonForm.pivotRow p)
              (fun i => c[i]) (List.mem_finRange _) (List.nodup_finRange n) 0
          have hzero : (0 : R) + c[E.toIsEchelonForm.pivotRow p] =
              c[E.toIsEchelonForm.pivotRow p] := by
            grind
          exact h.trans hzero

/-- Two coefficient vectors that agree on every pivot row yield the same row
combination of the echelon rows, because the non-pivot rows are zero rows and
contribute nothing. -/
private theorem rowCombination_eq_of_coeffs_eq_on_rank [Lean.Grind.Field R]
    (E : IsRREF M D) {c d : Vector R n}
    (hcoeff : ∀ i : Fin D.rank,
      c[E.toIsEchelonForm.pivotRow i] = d[E.toIsEchelonForm.pivotRow i]) :
    rowCombination D.echelon c = rowCombination D.echelon d := by
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  unfold rowCombination
  simp [HMul.hMul, Matrix.mulVec, Matrix.dot, Matrix.row, Hex.Vector.dotProduct,
    Matrix.transpose, Matrix.col]
  change (List.finRange n).foldl
      (fun acc i => acc + D.echelon[i][jj] * c[i]) 0 =
    (List.finRange n).foldl
      (fun acc i => acc + D.echelon[i][jj] * d[i]) 0
  apply foldl_sum_congr
  intro i _hi
  by_cases hirank : i.val < D.rank
  · let r : Fin D.rank := ⟨i.val, hirank⟩
    have hirow : E.toIsEchelonForm.pivotRow r = i := by
      apply Fin.ext
      rfl
    have hci : c[i] = d[i] := by
      simpa [hirow] using hcoeff r
    rw [hci]
  · have hrow := E.toIsEchelonForm.zero_row i (by omega)
    have hentry : D.echelon[i][jj] = 0 := by
      simpa using congrArg (fun row => row[jj]) hrow
    rw [hentry]
    have hleft : (0 : R) * c[i] = 0 := by grind
    have hright : (0 : R) * d[i] = 0 := by grind
    rw [hleft, hright]

/-- For any vector in the row span of the echelon matrix, the coefficients recovered
by `echelonCoeffs` reproduce it, so `echelonCoeffs` is a right inverse to row
combination on the span. -/
private theorem rowCombination_echelonCoeffs_of_rowCombination [Lean.Grind.Field R]
    (E : IsRREF M D) {v : Vector R m}
    (h : ∃ c : Vector R n, rowCombination D.echelon c = v) :
    rowCombination D.echelon (E.toIsEchelonForm.echelonCoeffs v) = v := by
  rcases h with ⟨c, hc⟩
  rw [← hc]
  apply rowCombination_eq_of_coeffs_eq_on_rank E
  intro i
  have hi : (E.toIsEchelonForm.pivotRow i).val < D.rank := i.isLt
  have hpi : (⟨(E.toIsEchelonForm.pivotRow i).val, hi⟩ : Fin D.rank) = i := by
    apply Fin.ext
    simp [IsEchelonForm.pivotRow]
  simp [IsEchelonForm.echelonCoeffs, hi, hpi]
  change (rowCombination D.echelon c)[D.pivotCols.get i] /
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] =
    c[E.toIsEchelonForm.pivotRow i]
  have hpivot := rowCombination_pivotCoeff E c i
  rw [hpivot]
  have hpivotOne :
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] = 1 := by
    simpa [IsEchelonForm.pivotRow] using E.pivot_one i
  rw [hpivotOne]
  grind

/-- Any vector in the row span produces coefficients via the RREF-backed
`spanCoeffs` API. -/
theorem spanCoeffs_complete [Lean.Grind.Field R] [DecidableEq R]
    (E : IsRREF M D) (v : Vector R m) :
    (∃ c : Vector R n, rowCombination M c = v) →
      (E.toIsEchelonForm.spanCoeffs v).isSome := by
  intro h
  unfold IsEchelonForm.spanCoeffs
  dsimp only
  have hechelon :
      ∃ d : Vector R n, rowCombination D.echelon d = v :=
    E.toIsEchelonForm.exists_rowCombination_echelon_of_M h
  have hreconstruct :
      rowCombination D.echelon (E.toIsEchelonForm.echelonCoeffs v) = v :=
    rowCombination_echelonCoeffs_of_rowCombination E hechelon
  have htransport :
      rowCombination M
          (Matrix.transpose D.transform * E.toIsEchelonForm.echelonCoeffs v) = v := by
    rw [E.toIsEchelonForm.rowCombination_transform_transpose]
    exact hreconstruct
  simp [htransport]

/-- For RREF data, `spanContains` is exactly row-span membership. -/
theorem spanContains_iff [Lean.Grind.Field R] [DecidableEq R]
    (E : IsRREF M D) (v : Vector R m) :
    E.toIsEchelonForm.spanContains v = true ↔
      ∃ c : Vector R n, rowCombination M c = v := by
  constructor
  · exact E.toIsEchelonForm.spanContains_sound v
  · intro h
    unfold IsEchelonForm.spanContains
    simpa using E.spanCoeffs_complete v h

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]

/-- Find the pivot-row index for column `j`, if `j` is a pivot column. -/
private def pivotIndexAux (D : RowEchelonData R n m) (j : Fin m) (start fuel : Nat) :
    Option (Fin D.rank) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < D.rank then
        let i : Fin D.rank := ⟨start, h⟩
        if D.pivotCols.get i = j then
          some i
        else
          pivotIndexAux D j (start + 1) fuel
      else
        none

/-- Find the pivot-row index for column `j`, if `j` is a pivot column. -/
private def pivotIndex? (D : RowEchelonData R n m) (j : Fin m) : Option (Fin D.rank) :=
  pivotIndexAux D j 0 D.rank

private theorem pivotIndexAux_pivot (E : IsEchelonForm M D) (i : Fin D.rank) :
    ∀ start fuel,
      start ≤ i.val →
      i.val < start + fuel →
      pivotIndexAux D (D.pivotCols.get i) start fuel = some i := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _ hlt
      omega
  | succ fuel ih =>
      intro hstart hlt
      unfold pivotIndexAux
      have hstartRank : start < D.rank := by omega
      simp [hstartRank]
      let s : Fin D.rank := ⟨start, hstartRank⟩
      by_cases hsi : s = i
      · have hcols : D.pivotCols.get s = D.pivotCols.get i := by rw [hsi]
        rw [if_pos hcols]
        change some s = some i
        exact congrArg some hsi
      · have hcols : D.pivotCols.get s ≠ D.pivotCols.get i := by
          intro hcols
          exact hsi (E.pivotCols_injective hcols)
        rw [if_neg hcols]
        apply ih (start := start + 1)
        · have hslt : start < i.val := by
            have hsne : start ≠ i.val := by
              intro hval
              exact hsi (Fin.ext hval)
            omega
          omega
        · omega

private theorem pivotIndex?_pivot (E : IsEchelonForm M D) (i : Fin D.rank) :
    pivotIndex? D (D.pivotCols.get i) = some i := by
  unfold pivotIndex?
  apply pivotIndexAux_pivot E i
  · omega
  · omega

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem pivotIndexAux_none_of_not_pivot {j : Fin m}
    (hnot : ∀ i : Fin D.rank, D.pivotCols.get i ≠ j) :
    ∀ start fuel, pivotIndexAux D j start fuel = none := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold pivotIndexAux
      by_cases hstart : start < D.rank
      · simp [hstart, hnot ⟨start, hstart⟩]
        exact ih (start + 1)
      · simp [hstart]

private theorem pivotIndex?_free_none (E : IsEchelonForm M D) (k : Fin (m - D.rank)) :
    pivotIndex? D (E.freeCols.get k) = none := by
  unfold pivotIndex?
  apply pivotIndexAux_none_of_not_pivot
  intro i
  exact E.pivotCols_disjoint_freeCols i k

/-- Nullspace basis vectors assembled as columns indexed by the free variables. -/
def nullspaceMatrix [Lean.Grind.Ring R] (E : IsRREF M D) :
    Matrix R m (m - D.rank) :=
  let freeCols := E.toIsEchelonForm.freeCols
  Matrix.ofFn fun j k =>
    if hFree : j = freeCols.get k then
      1
    else
      match pivotIndex? D j with
      | some i =>
          -D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][freeCols.get k]
      | none => 0

/-- In the `k`th nullspace-matrix column, the row for its own free column is `1`. -/
@[grind =] theorem nullspaceMatrix_free [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get k][k] = 1 := by
  unfold nullspaceMatrix Matrix.ofFn
  simp

/-- In the `k`th nullspace-matrix column, every other free-column row is `0`. -/
@[grind =] theorem nullspaceMatrix_free_ne [Lean.Grind.Ring R] (E : IsRREF M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get l][k] = 0 := by
  unfold nullspaceMatrix Matrix.ofFn
  have hne : E.toIsEchelonForm.freeCols.get l ≠ E.toIsEchelonForm.freeCols.get k := by
    intro h
    exact hkl ((E.toIsEchelonForm.freeCols_injective h).symm)
  simp [hne, pivotIndex?_free_none E.toIsEchelonForm l]

/-- In a pivot-column row, a nullspace-matrix entry is the negative RREF entry in
the matching pivot row and free column. -/
@[grind =] theorem nullspaceMatrix_pivot [Lean.Grind.Ring R] (E : IsRREF M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[D.pivotCols.get i][k] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  unfold nullspaceMatrix Matrix.ofFn
  simp [E.toIsEchelonForm.pivotCols_disjoint_freeCols i k,
    pivotIndex?_pivot E.toIsEchelonForm i]

/-- The individual nullspace basis vectors. -/
def nullspace [Lean.Grind.Ring R] (E : IsRREF M D) :
    Vector (Vector R m) (m - D.rank) :=
  Vector.ofFn fun k => Matrix.col (E.nullspaceMatrix) k

private theorem nullspace_get [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    E.nullspace.get k = Matrix.col E.nullspaceMatrix k := by
  unfold nullspace
  rw [Vector.get_ofFn]

/-- On its own free column, a nullspace basis vector has entry `1`. -/
@[grind =] theorem nullspace_get_free [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get k] = 1 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free E k

/-- On every other free column, a nullspace basis vector has entry `0`. -/
@[grind =] theorem nullspace_get_free_ne [Lean.Grind.Ring R] (E : IsRREF M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get l] = 0 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free_ne E hkl

/-- On a pivot column, a nullspace basis vector is the negative RREF entry in
the matching pivot row and free column. -/
@[grind =] theorem nullspace_get_pivot [Lean.Grind.Ring R] (E : IsRREF M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[D.pivotCols.get i] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_pivot E i k

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_add_eq_acc_ring_echelon {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hac : acc + (0 : R) = acc := by grind
      rw [hac]
      exact ih acc hxs

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_sum_start {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R) :
    xs.foldl (fun acc x => acc + f x) acc =
      acc + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      rw [ih (acc := (0 : R) + f x)]
      grind

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_one_nonzero {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} [DecidableEq α] (xs : List α) (a : α) (f : α → R) (x : R)
    (haMem : a ∈ xs) (hnodup : xs.Nodup)
    (ha : f a = x) (hz : ∀ z ∈ xs, z ≠ a → f z = 0) :
    xs.foldl (fun acc z => acc + f z) 0 = x := by
  induction xs with
  | nil =>
      cases haMem
  | cons z zs ih =>
      simp only [List.foldl_cons]
      by_cases hza : z = a
      · subst z
        rw [ha]
        have hzero : ∀ y ∈ zs, f y = 0 := by
          intro y hy
          have hya : y ≠ a := by
            intro h
            subst y
            exact (List.nodup_cons.mp hnodup).1 hy
          exact hz y (List.mem_cons_of_mem _ hy) hya
        have h0x : (0 : R) + x = x := by grind
        rw [h0x]
        rw [foldl_add_eq_acc_ring_echelon zs f x hzero]
      · have hz0 : f z = 0 := hz z (by simp) hza
        rw [hz0]
        have haTail : a ∈ zs := by
          rcases List.mem_cons.mp haMem with hhead | htail
          · exact False.elim (hza hhead.symm)
          · exact htail
        have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
        have hzTail : ∀ y ∈ zs, y ≠ a → f y = 0 := by
          intro y hy hya
          exact hz y (List.mem_cons_of_mem _ hy) hya
        have hzeroAdd : (0 : R) + 0 = 0 := by grind
        rw [hzeroAdd]
        exact ih haTail hnodupTail hzTail

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_two_nonzero {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} [DecidableEq α] (xs : List α) (a b : α) (f : α → R) (x y : R)
    (hab : a ≠ b) (haMem : a ∈ xs) (hbMem : b ∈ xs) (hnodup : xs.Nodup)
    (ha : f a = x) (hb : f b = y)
    (hz : ∀ z ∈ xs, z ≠ a → z ≠ b → f z = 0) :
    xs.foldl (fun acc z => acc + f z) 0 = x + y := by
  induction xs with
  | nil =>
      cases haMem
  | cons z zs ih =>
      simp only [List.foldl_cons]
      by_cases hza : z = a
      · subst z
        rw [ha]
        have hbTail : b ∈ zs := by
          rcases List.mem_cons.mp hbMem with hhead | htail
          · exact False.elim (hab hhead.symm)
          · exact htail
        have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
        have hbOnly : ∀ t ∈ zs, t ≠ b → f t = 0 := by
          intro t ht htb
          have hta : t ≠ a := by
            intro h
            subst t
            exact (List.nodup_cons.mp hnodup).1 ht
          exact hz t (List.mem_cons_of_mem _ ht) hta htb
        have h0x : (0 : R) + x = x := by grind
        rw [h0x]
        rw [foldl_sum_start zs f x]
        rw [foldl_one_nonzero zs b f y hbTail hnodupTail hb hbOnly]
      · by_cases hzb : z = b
        · subst z
          rw [hb]
          have haTail : a ∈ zs := by
            rcases List.mem_cons.mp haMem with hhead | htail
            · exact False.elim (hza hhead.symm)
            · exact htail
          have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
          have haOnly : ∀ t ∈ zs, t ≠ a → f t = 0 := by
            intro t ht hta
            have htb : t ≠ b := by
              intro h
              subst t
              exact (List.nodup_cons.mp hnodup).1 ht
            exact hz t (List.mem_cons_of_mem _ ht) hta htb
          have h0y : (0 : R) + y = y := by grind
          rw [h0y]
          rw [foldl_sum_start zs f y]
          rw [foldl_one_nonzero zs a f x haTail hnodupTail ha haOnly]
          grind
        · have hz0 : f z = 0 := hz z (by simp) hza hzb
          rw [hz0]
          have haTail : a ∈ zs := by
            rcases List.mem_cons.mp haMem with hhead | htail
            · exact False.elim (hza hhead.symm)
            · exact htail
          have hbTail : b ∈ zs := by
            rcases List.mem_cons.mp hbMem with hhead | htail
            · exact False.elim (hzb hhead.symm)
            · exact htail
          have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
          have hzTail : ∀ t ∈ zs, t ≠ a → t ≠ b → f t = 0 := by
            intro t ht hta htb
            exact hz t (List.mem_cons_of_mem _ ht) hta htb
          have hzeroAdd : (0 : R) + 0 = 0 := by grind
          rw [hzeroAdd]
          exact ih haTail hbTail hnodupTail hzTail

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem nullspace_echelon_sound {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    D.echelon * E.nullspace.get k = 0 := by
  apply Vector.ext
  intro r hr
  let row : Fin n := ⟨r, hr⟩
  by_cases hrow : r < D.rank
  · let ri : Fin D.rank := ⟨r, hrow⟩
    let free := E.toIsEchelonForm.freeCols.get k
    let pivot := D.pivotCols.get ri
    let coeff := D.echelon[row][free]
    have hrowEq : row = E.toIsEchelonForm.pivotRow ri := by
      apply Fin.ext
      rfl
    have hpivotFree : pivot ≠ free := by
      exact E.toIsEchelonForm.pivotCols_disjoint_freeCols ri k
    change (Matrix.mulVec D.echelon (E.nullspace.get k))[r] = (0 : Vector R n)[r]
    unfold Matrix.mulVec Matrix.dot Matrix.row Hex.Vector.dotProduct
    rw [Vector.getElem_ofFn hr]
    rw [Vector.getElem_zero r hr]
    change (List.finRange m).foldl
        (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 = 0
    have hpivotTerm :
        D.echelon[row][pivot] * (E.nullspace.get k)[pivot] = -coeff := by
      have hpone : D.echelon[row][pivot] = 1 := by
        simpa [row, ri, pivot, IsEchelonForm.pivotRow] using E.pivot_one ri
      have hnp := nullspace_get_pivot E ri k
      rw [hpone, hnp]
      have hcoeff :
          D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm ri)][free] = coeff := by
        simp [free, coeff, row, ri, IsEchelonForm.pivotRow]
      change (1 : R) *
          (-D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm ri)][free]) = -coeff
      rw [hcoeff]
      grind
    have hfreeTerm :
        D.echelon[row][free] * (E.nullspace.get k)[free] = coeff := by
      have hnf := nullspace_get_free E k
      rw [hnf]
      grind
    have hzero :
        ∀ j ∈ List.finRange m, j ≠ pivot → j ≠ free →
          D.echelon[row][j] * (E.nullspace.get k)[j] = 0 := by
      intro j _ hjp hjf
      rcases E.toIsEchelonForm.colPartition j with ⟨i, hi⟩ | ⟨l, hl⟩
      · have hij : i ≠ ri := by
          intro hir
          subst i
          exact hjp hi.symm
        have hpivotZero : D.echelon[row][D.pivotCols.get i] = 0 := by
          have hval : i.val ≠ ri.val := by
            intro h
            exact hij (Fin.ext h)
          cases Nat.lt_or_gt_of_ne hval with
          | inl hlt =>
              have hbelow := E.toIsEchelonForm.below_pivot_zero i row (by
                change i.val < r
                simpa [ri] using hlt)
              simpa using hbelow
          | inr hgt =>
              have habove := E.above_pivot_zero i row (by
                change r < i.val
                simpa [ri] using hgt)
              simpa using habove
        rw [← hi, hpivotZero]
        grind
      · have hlk : k ≠ l := by
          intro hkl
          subst l
          exact hjf hl.symm
        have hfreeZero := nullspace_get_free_ne E hlk
        rw [← hl, hfreeZero]
        grind
    have hsum := foldl_two_nonzero (R := R) (xs := List.finRange m) pivot free
      (fun j => D.echelon[row][j] * (E.nullspace.get k)[j]) (-coeff) coeff
      hpivotFree (List.mem_finRange pivot) (List.mem_finRange free)
      (List.nodup_finRange m) hpivotTerm hfreeTerm hzero
    calc
      (List.finRange m).foldl
          (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 =
          -coeff + coeff := by
            simpa only using hsum
      _ = 0 := by grind
  · have hzeroRow := E.toIsEchelonForm.zero_row row (by
      exact Nat.le_of_not_gt hrow)
    change (Matrix.mulVec D.echelon (E.nullspace.get k))[r] = (0 : Vector R n)[r]
    unfold Matrix.mulVec Matrix.dot Matrix.row Hex.Vector.dotProduct
    rw [Vector.getElem_ofFn hr]
    rw [Vector.getElem_zero r hr]
    change (List.finRange m).foldl
        (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 = 0
    have hzero :
        ∀ j ∈ List.finRange m, D.echelon[row][j] * (E.nullspace.get k)[j] = 0 := by
      intro j _
      have hentry : D.echelon[row][j] = 0 := by
        have hrowGet := congrArg (fun v => v[j]) hzeroRow
        simpa using hrowGet
      rw [hentry]
      grind
    simpa only using foldl_add_eq_acc_ring_echelon (List.finRange m)
      (fun j => D.echelon[row][j] * (E.nullspace.get k)[j]) 0 hzero

/-- Every basis vector returned by `nullspace` lies in the nullspace of `M`. -/
theorem nullspace_sound {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D) (k : Fin (m - D.rank)) :
    M * E.nullspace.get k = 0 := by
  let b := E.nullspace.get k
  have hbEchelon : D.echelon * b = 0 := by
    exact nullspace_echelon_sound (M := M) (D := D) E k
  have hbTransform : D.transform * (M * b) = 0 := by
    calc
      D.transform * (M * b) = (D.transform * M) * b := by
        exact (Matrix.mul_assoc_vec D.transform M b).symm
      _ = D.echelon * b := by
        rw [E.toIsEchelonForm.transform_mul]
      _ = 0 := hbEchelon
  rcases E.toIsEchelonForm.transform_inv with ⟨Tinv, hTinv⟩
  calc
    M * b = (1 : Matrix R n n) * (M * b) := by
      rw [Matrix.one_mulVec]
    _ = (Tinv * D.transform) * (M * b) := by
      rw [hTinv]
    _ = Tinv * (D.transform * (M * b)) := by
      exact Matrix.mul_assoc_vec Tinv D.transform (M * b)
    _ = Tinv * (0 : Vector R n) := by
      rw [hbTransform]
    _ = 0 := by
      rw [Matrix.mulVec_zero]

private theorem vector_toList_eq_finRange_map_get {α : Type u} {n : Nat}
    (v : Vector α n) :
    v.toList = (List.finRange n).map fun i => v[i] := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k _ _
    simp

private theorem foldl_sum_mul_left_local {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (c acc : R) :
    c * xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + c * f x) (c * acc) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      have hdist : c * (acc + f x) = c * acc + c * f x := by grind
      rw [hdist]

private theorem foldl_sum_perm_local {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (f : β → R) {xs ys : List β} (hperm : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc + f x) z =
      ys.foldl (fun acc x => acc + f x) z := by
  induction hperm generalizing z with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.foldl_cons]
      exact ih (z + _)
  | swap x y xs =>
      simp only [List.foldl_cons]
      congr 1
      grind
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ z).trans (ih₂ z)

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem pivotCols_toList_nodup
    [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) :
    D.pivotCols.toList.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < D.rank := by simpa [Vector.length_toList] using hi
  have hj' : j < D.rank := by simpa [Vector.length_toList] using hj
  have h := E.pivotCols_sorted ⟨i, hi'⟩ ⟨j, hj'⟩ hij
  intro heq
  have heqGet :
      D.pivotCols.toList[i]'hi = D.pivotCols.toList[j]'hj := heq
  rw [Vector.getElem_toList, Vector.getElem_toList] at heqGet
  have : D.pivotCols.get ⟨i, hi'⟩ = D.pivotCols.get ⟨j, hj'⟩ := heqGet
  rw [this] at h
  omega

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem finRange_perm_pivot_free
    [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) :
    (List.finRange m).Perm
      (D.pivotCols.toList ++ E.freeColsList) := by
  let p : Fin m → Bool := fun j => decide (j ∈ D.pivotCols.toList)
  have hpivot_pair : List.Pairwise (fun a b : Fin m => a < b)
      ((List.finRange m).filter p) :=
    List.Pairwise.filter p (List.pairwise_lt_finRange m)
  have hpivot_nodup : ((List.finRange m).filter p).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hpivot_pair.imp (fun hlt heq => by subst heq; omega)
  have hpivot_perm : D.pivotCols.toList.Perm ((List.finRange m).filter p) := by
    rw [List.perm_ext_iff_of_nodup (pivotCols_toList_nodup E) hpivot_nodup]
    intro a
    constructor
    · intro ha
      rw [List.mem_filter]
      refine ⟨List.mem_finRange a, ?_⟩
      exact decide_eq_true ha
    · intro ha
      rw [List.mem_filter] at ha
      exact of_decide_eq_true ha.2
  have hfree_eq :
      E.freeColsList = (List.finRange m).filter (fun j => !p j) := by
    unfold IsEchelonForm.freeColsList
    apply List.filter_congr
    intro j _hj
    show decide (j ∉ D.pivotCols.toList) = !decide (j ∈ D.pivotCols.toList)
    by_cases hjp : j ∈ D.pivotCols.toList
    · simp [hjp]
    · simp [hjp]
  have hgoal : (D.pivotCols.toList ++ E.freeColsList).Perm (List.finRange m) := by
    rw [hfree_eq]
    exact (hpivot_perm.append_right _).trans
      (List.filter_append_perm p (List.finRange m))
  exact hgoal.symm

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- The pivot-column entry in row `pivotRow i` is `1` exactly when the pivot
indices match. This is the indicator characterization used to extract
`v[D.pivotCols.get i]` from the row sum. -/
private theorem pivot_column_entry_pivotRow {R : Type u} [Lean.Grind.Field R]
    {n m : Nat} {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D)
    (i i' : Fin D.rank) :
    D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i'] =
      if i' = i then (1 : R) else 0 := by
  have h := pivot_column_entry E i' (E.toIsEchelonForm.pivotRow i)
  by_cases hii : i' = i
  · subst i'
    rw [if_pos rfl]
    rw [h]
    rw [if_pos rfl]
  · rw [if_neg hii]
    rw [h]
    have hrow_ne : E.toIsEchelonForm.pivotRow i' ≠ E.toIsEchelonForm.pivotRow i := by
      intro heq
      apply hii
      apply Fin.ext
      simpa [IsEchelonForm.pivotRow] using congrArg Fin.val heq
    rw [if_neg hrow_ne]

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- The row of `D.echelon * v` at `pivotRow i`, expanded as a foldl, is the
sum of the pivot-column contribution `v[D.pivotCols.get i]` plus the
free-column contributions. When `D.echelon * v = 0`, this gives a relation
between `v[D.pivotCols.get i]` and the free-column entries. -/
private theorem freeSum_eq_neg_pivot {R : Type u} [Lean.Grind.Field R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsRREF M D) {v : Vector R m}
    (hEchelon : D.echelon * v = 0) (i : Fin D.rank) :
    v[D.pivotCols.get i] +
      (List.finRange (m - D.rank)).foldl
        (fun acc k =>
          acc +
            D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
              v[E.toIsEchelonForm.freeCols.get k]) 0 = 0 := by
  -- Expand `(D.echelon * v)[pivotRow i] = 0` into a foldl over `Fin m`.
  have hZero : (List.finRange m).foldl
      (fun acc l =>
        acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 = 0 := by
    have hentry := congrArg (fun w => w[(E.toIsEchelonForm.pivotRow i).val]'
      (E.toIsEchelonForm.pivotRow i).isLt) hEchelon
    -- `hentry : (D.echelon * v)[pivotRow i] = (0 : Vector R n)[pivotRow i]`
    change
      (Matrix.mulVec D.echelon v)[(E.toIsEchelonForm.pivotRow i).val]'
        (E.toIsEchelonForm.pivotRow i).isLt =
      (0 : Vector R n)[(E.toIsEchelonForm.pivotRow i).val]'
        (E.toIsEchelonForm.pivotRow i).isLt at hentry
    unfold Matrix.mulVec Matrix.dot Matrix.row Hex.Vector.dotProduct at hentry
    rw [Vector.getElem_ofFn (E.toIsEchelonForm.pivotRow i).isLt] at hentry
    rw [Vector.getElem_zero (E.toIsEchelonForm.pivotRow i).val
      (E.toIsEchelonForm.pivotRow i).isLt] at hentry
    exact hentry
  -- Split the foldl using the perm `finRange m ~ pivotCols.toList ++ freeColsList`.
  have hperm := finRange_perm_pivot_free (M := M) (D := D) E.toIsEchelonForm
  have hSplit :
      (List.finRange m).foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        D.pivotCols.toList.foldl
            (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 +
        E.toIsEchelonForm.freeColsList.foldl
            (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 := by
    rw [foldl_sum_perm_local
      (f := fun l => D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) hperm]
    rw [List.foldl_append]
    rw [foldl_sum_start (R := R)
      (xs := E.toIsEchelonForm.freeColsList)
      (f := fun l => D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l])
      (acc := D.pivotCols.toList.foldl
        (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0)]
  -- Pivot half: convert to fold over Fin D.rank, use indicator structure.
  have hPivotPart :
      D.pivotCols.toList.foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        v[D.pivotCols.get i] := by
    have hList : D.pivotCols.toList =
        (List.finRange D.rank).map fun i' => D.pivotCols.get i' := by
      have h := vector_toList_eq_finRange_map_get D.pivotCols
      simpa [Vector.get] using h
    rw [hList, List.foldl_map]
    have hrewrite :
        (List.finRange D.rank).foldl
            (fun acc i' =>
              acc + D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i'] *
                v[D.pivotCols.get i']) 0 =
          (List.finRange D.rank).foldl
            (fun acc i' =>
              acc + (if i = i' then (1 : R) else 0) * v[D.pivotCols.get i']) 0 := by
      apply foldl_sum_congr
      intro i' _hi'
      have h := pivot_column_entry_pivotRow E i i'
      rw [h]
      by_cases hii : i' = i
      · subst i'
        rfl
      · have hii' : i ≠ i' := fun h => hii h.symm
        rw [if_neg hii, if_neg hii']
    rw [hrewrite]
    rw [foldl_indicator_mul_unique (List.finRange D.rank) i
      (fun i' => v[D.pivotCols.get i'])
      (List.mem_finRange i) (List.nodup_finRange D.rank) 0]
    grind
  -- Free half: convert to fold over Fin (m - D.rank).
  have hFreePart :
      E.toIsEchelonForm.freeColsList.foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        (List.finRange (m - D.rank)).foldl
          (fun acc k =>
            acc +
              D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
                v[E.toIsEchelonForm.freeCols.get k]) 0 := by
    have hList : E.toIsEchelonForm.freeColsList =
        (List.finRange (m - D.rank)).map fun k => E.toIsEchelonForm.freeCols.get k := by
      apply List.ext_getElem
      · simp [E.toIsEchelonForm.freeColsList_length]
      · intro k hk₁ _
        have hk : k < m - D.rank := by
          rw [E.toIsEchelonForm.freeColsList_length] at hk₁
          exact hk₁
        rw [List.getElem_map, List.getElem_finRange]
        change E.toIsEchelonForm.freeColsList[k]'_ = E.toIsEchelonForm.freeCols.get ⟨k, hk⟩
        unfold IsEchelonForm.freeCols
        simp [Vector.get, List.getElem_toArray]
    rw [hList, List.foldl_map]
  rw [hSplit, hPivotPart, hFreePart] at hZero
  exact hZero

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- Every nullspace vector is generated by the computed nullspace basis. -/
theorem nullspace_complete {R : Type u} [Lean.Grind.Field R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsRREF M D) (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - D.rank), E.nullspaceMatrix * c = v := by
  intro hMv
  have hEchelon : D.echelon * v = 0 := by
    calc
      D.echelon * v = (D.transform * M) * v := by rw [E.toIsEchelonForm.transform_mul]
      _ = D.transform * (M * v) := Matrix.mul_assoc_vec _ _ _
      _ = D.transform * (0 : Vector R n) := by rw [hMv]
      _ = 0 := Matrix.mulVec_zero _
  refine ⟨Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]), ?_⟩
  -- Prove the entry-wise equality for an arbitrary `Fin m` index, then convert
  -- to the `Vector.ext` form. Working with `Fin` lets us use `subst` on the
  -- `colPartition` hypothesis without dependent-type rewriting issues.
  have hcEntry : ∀ k : Fin (m - D.rank),
      (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
          Vector R (m - D.rank))[k] =
        v[E.toIsEchelonForm.freeCols.get k] := by
    intro k
    simp [Vector.getElem_ofFn]
  have key : ∀ jj : Fin m,
      (E.nullspaceMatrix *
          (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
            Vector R (m - D.rank)))[jj.val]'jj.isLt = v[jj.val]'jj.isLt := by
    intro jj
    -- Expand the matrix-vector product to a foldl.
    change
      (Matrix.mulVec E.nullspaceMatrix
        (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
          Vector R (m - D.rank)))[jj.val]'jj.isLt = v[jj.val]'jj.isLt
    unfold Matrix.mulVec Matrix.dot Matrix.row Hex.Vector.dotProduct
    rw [Vector.getElem_ofFn jj.isLt]
    change
      (List.finRange (m - D.rank)).foldl
          (fun acc k =>
            acc + E.nullspaceMatrix[jj][k] *
              (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                Vector R (m - D.rank))[k]) 0 = v[jj]
    rcases E.toIsEchelonForm.colPartition jj with ⟨i, hi⟩ | ⟨l, hl⟩
    · -- Pivot case: substitute jj := D.pivotCols.get i
      subst hi
      -- Replace v[D.pivotCols.get i] using the freeSum identity.
      have hRowEq :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + E.nullspaceMatrix[D.pivotCols.get i][k] *
                  (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                    Vector R (m - D.rank))[k]) 0 =
            (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  -(D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k])) 0 := by
        apply foldl_sum_congr
        intro k _hk
        rw [nullspaceMatrix_pivot E i k, hcEntry k]
        grind
      rw [hRowEq]
      have hFree := freeSum_eq_neg_pivot E hEchelon i
      have hNeg :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  -(D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k])) 0 =
            -((List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                      v[E.toIsEchelonForm.freeCols.get k]) 0) := by
        have hmul := foldl_sum_mul_left_local
          (xs := List.finRange (m - D.rank))
          (f := fun k =>
            D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
              v[E.toIsEchelonForm.freeCols.get k])
          (c := (-1 : R)) (acc := 0)
        have hzero : ((-1 : R)) * 0 = 0 := by grind
        rw [hzero] at hmul
        have h1 :
            (List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    -(D.echelon[E.toIsEchelonForm.pivotRow i][
                        E.toIsEchelonForm.freeCols.get k] *
                      v[E.toIsEchelonForm.freeCols.get k])) 0 =
              (List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    ((-1 : R) *
                      (D.echelon[E.toIsEchelonForm.pivotRow i][
                          E.toIsEchelonForm.freeCols.get k] *
                        v[E.toIsEchelonForm.freeCols.get k]))) 0 := by
          apply foldl_sum_congr
          intro k _hk
          grind
        rw [h1, ← hmul]
        grind
      rw [hNeg]
      have hsum :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  D.echelon[E.toIsEchelonForm.pivotRow i][
                    E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k]) 0 =
            -v[D.pivotCols.get i] := by
        have h := hFree
        grind
      rw [hsum]
      grind
    · -- Free case: substitute jj := freeCols.get l
      subst hl
      have hcongr :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get l][k] *
                  (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                    Vector R (m - D.rank))[k]) 0 =
            (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + (if l = k then (1 : R) else 0) *
                  v[E.toIsEchelonForm.freeCols.get k]) 0 := by
        apply foldl_sum_congr
        intro k _hk
        rw [hcEntry k]
        by_cases hkl : k = l
        · subst k
          rw [nullspaceMatrix_free E l, if_pos rfl]
        · have hlk : l ≠ k := fun heq => hkl heq.symm
          rw [nullspaceMatrix_free_ne E (k := k) (l := l) hkl, if_neg hlk]
      rw [hcongr]
      rw [foldl_indicator_mul_unique (List.finRange (m - D.rank)) l
        (fun k => v[E.toIsEchelonForm.freeCols.get k])
        (List.mem_finRange l) (List.nodup_finRange (m - D.rank)) 0]
      grind
  apply Vector.ext
  intro j hj
  exact key ⟨j, hj⟩

end IsRREF

/-- Convenience wrapper: compute row-span coefficients using `rref` internally. -/
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Option (Vector R n) :=
  let E := (rref_isRREF M).toIsEchelonForm
  E.spanCoeffs v

/-- Wrapper-layer soundness contract for `Matrix.spanCoeffs`. -/
@[grind =>]
theorem spanCoeffs_sound [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) (c : Vector R n) :
    spanCoeffs M v = some c → rowCombination M c = v := by
  intro h
  exact (rref_isRREF M).toIsEchelonForm.spanCoeffs_sound v c h

/-- Convenience wrapper: decide row-span membership using `rref` internally. -/
def spanContains [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Bool :=
  let E := (rref_isRREF M).toIsEchelonForm
  E.spanContains v

/-- The public `spanContains` wrapper is the Boolean `isSome` view of
`spanCoeffs`. -/
@[simp, grind =] theorem spanContains_eq_isSome [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) :
    spanContains M v = (spanCoeffs M v).isSome := by
  rfl

/-- The public `spanContains` wrapper is exactly row-span membership. -/
@[grind =]
theorem spanContains_iff [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) :
    spanContains M v = true ↔ ∃ c : Vector R n, rowCombination M c = v := by
  unfold spanContains
  simpa using (rref_isRREF M).spanContains_iff v

/-- The rank returned by `rref`. -/
def rref_rank [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) : Nat :=
  (rref M).rank

/-- The public nullspace basis assembled as a matrix of basis columns. -/
def nullspaceBasisMatrix [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) :
    Matrix R m (m - rref_rank M) :=
  let E := rref_isRREF M
  E.nullspaceMatrix

/-- Convenience wrapper: compute the nullspace basis using `rref` internally. -/
def nullspace [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) :
    Vector (Vector R m) (m - rref_rank M) :=
  let E := rref_isRREF M
  E.nullspace

/-- Public column bridge between the matrix and vector nullspace wrappers:
the `k`-th column of `nullspaceBasisMatrix M` is the `k`-th vector in
`nullspace M`. -/
@[grind =>]
theorem nullspaceBasisMatrix_col [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (k : Fin (m - rref_rank M)) :
    Matrix.col (nullspaceBasisMatrix M) k = (nullspace M).get k := by
  unfold nullspaceBasisMatrix nullspace
  exact ((rref_isRREF M).nullspace_get k).symm

/-- Every vector returned by the public `nullspace` wrapper is annihilated by `M`. -/
@[grind =>]
theorem nullspace_sound [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (k : Fin (m - rref_rank M)) :
    M * (nullspace M).get k = 0 := by
  unfold nullspace rref_rank
  exact (rref_isRREF M).nullspace_sound k

/-- Every vector annihilated by `M` is generated by the public nullspace basis matrix. -/
@[grind =>]
theorem nullspace_complete [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - rref_rank M), nullspaceBasisMatrix M * c = v := by
  intro hv
  unfold nullspaceBasisMatrix rref_rank
  exact (rref_isRREF M).nullspace_complete v hv

end Matrix
end Hex
