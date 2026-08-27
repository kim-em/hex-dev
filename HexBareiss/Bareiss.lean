/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant
public import HexBasic.ExactDiv
public import HexArith.ExactDiv
public import HexBareiss.BorderedMinor

public section

/-!
Executable Bareiss determinant algorithm for `hex-matrix`.

This module implements fraction-free Bareiss elimination over `Int` in two
layers: a no-pivot recurrence that follows the standard exact-division update,
and a public row-pivoting wrapper that swaps in a nonzero pivot when needed and
tracks the resulting determinant sign. The Mathlib-free layer exposes the
executable data and state needed by later bridge proofs; it does not expose a
theorem identifying the executable Bareiss determinant with the generic
Leibniz determinant.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n : Nat}

/-- Output of an executable Bareiss elimination pass. -/
structure BareissData (R : Type u) (n : Nat) where
  /-- Terminal matrix produced by the Bareiss pass. When `singularStep = none`,
  `BareissData.det` reads the last diagonal entry of this matrix, with the
  row-swap sign applied; for `n = 0`, the empty diagonal contributes `1`. -/
  matrix : Matrix R n n
  /-- Number of row swaps performed by pivoting. Even parity contributes sign
  `1`; odd parity contributes sign `-1`. -/
  rowSwaps : Nat
  /-- The first elimination step that found a zero pivot and no replacement
  row. A value `some k` records that singular step and makes
  `BareissData.det` return `0`; `none` means the run reached the terminal
  diagonal encoding. -/
  singularStep : Option Nat

namespace BareissData

/-- The determinant sign contributed by the recorded row swaps. -/
@[expose]
def sign [One R] [Neg R] (data : BareissData R n) : R :=
  if data.rowSwaps % 2 = 0 then 1 else -1

@[expose]
def lastDiag? (M : Matrix R n n) : Option R :=
  match n with
  | 0 => none
  | k + 1 =>
      let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      some M[(i, i)]

/-- The determinant encoded by a Bareiss elimination result. -/
@[expose]
def det [Zero R] [One R] [Neg R] [Mul R] (data : BareissData R n) : R :=
  match data.singularStep with
  | some _ => 0
  | none =>
      match lastDiag? data.matrix with
      | some d => data.sign * d
      | none => data.sign

/-- A recorded singular step encodes determinant zero. -/
@[grind →]
theorem det_eq_zero_of_singularStep [Zero R] [One R] [Neg R] [Mul R]
    {data : BareissData R n} {k : Nat}
    (h : data.singularStep = some k) :
    data.det = 0 := by
  unfold det
  rw [h]

/-- For a non-singular Bareiss elimination of a positive-size matrix, the
encoded determinant is `sign * (last diagonal entry)`. -/
@[grind =]
theorem det_succ_eq [Zero R] [One R] [Neg R] [Mul R]
    {k : Nat} (data : BareissData R (k + 1))
    (h : data.singularStep = none) :
    data.det = data.sign *
      data.matrix[(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] := by
  unfold det
  rw [h, ← Matrix.getElem_pair_eq_nested]
  rfl

/-- For a non-singular Bareiss elimination of an empty matrix, the encoded
determinant is the sign. -/
@[grind =]
theorem det_zero_eq [Zero R] [One R] [Neg R] [Mul R] (data : BareissData R 0)
    (h : data.singularStep = none) :
    data.det = data.sign := by
  unfold det
  rw [h]
  rfl

end BareissData

/-- Internal state of the no-pivot Bareiss recurrence, exposed read-only for
the Mathlib-side determinant proof. -/
structure BareissState (R : Type u) (n : Nat) where
  /-- Current elimination step. The next update, if any, uses this row and
  column as the pivot position. -/
  step : Nat
  /-- Current matrix carried by the Bareiss recurrence. Its terminal value is
  copied into `BareissData.matrix` by `finish`. -/
  matrix : Matrix R n n
  /-- Previous nonzero pivot used as the exact-division denominator; initially
  `1`. -/
  prevPivot : R
  /-- Number of row swaps already performed by the pivoting wrapper. Even
  parity contributes determinant sign `1`; odd parity contributes sign `-1`. -/
  rowSwaps : Nat
  /-- First step at which the recurrence found a zero pivot and could not
  continue. A value `some k` is terminal evidence for the determinant-zero
  encoding; `none` means no singular step has been recorded. -/
  singularStep : Option Nat

/-- Compatibility alias for the exact-division primitive now owned by
`hex-arith`. New code should use `HexArith.Int.exactDiv`. -/
@[expose]
abbrev exactDiv (num denom : @& Int) : Int := HexArith.Int.exactDiv num denom

/-- When divisibility is known, `exactDiv` is the GMP-backed exact quotient. -/
-- @[grind]-excluded: RHS `Int.divExact num denom h` mentions the divisibility
-- proof term `h`, which `grind =` cannot instantiate from the LHS pattern.
theorem exactDiv_eq_divExact {num denom : Int} (h : denom ∣ num) :
    exactDiv num denom = Int.divExact num denom h := by
  exact HexArith.Int.exactDiv_eq_divExact h

/-- Search column `col` for a nonzero pivot at or below `start`. -/
@[expose]
def findPivotAux [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[(i, col)] = 0 then
          findPivotAux M col (start + 1) fuel
        else
          some i
      else
        none

/-- Search column `col` for a nonzero pivot at or below `start`. -/
@[expose]
def findPivot? [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n) (start : Nat) :
    Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- A pivot returned by `findPivotAux` is always at or below its starting row. -/
-- @[grind]-excluded: subsumed by `findPivot?_ge_start`; tagging the fuelled
-- helper too would duplicate grind's rule for the same fact.
theorem findPivotAux_ge_start [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start fuel : Nat) {pivot : Fin n}
    (hfind : findPivotAux M col start fuel = some pivot) :
    start ≤ pivot.val := by
  induction fuel generalizing start with
  | zero =>
      simp [findPivotAux] at hfind
  | succ fuel ih =>
      by_cases hstart : start < n
      · simp [findPivotAux, hstart] at hfind
        split at hfind
        · exact Nat.le_trans (Nat.le_succ start) (ih (start + 1) hfind)
        · cases hfind
          exact Nat.le_refl _
      · simp [findPivotAux, hstart] at hfind

/-- A pivot returned by `findPivot?` is always at or below its starting row. -/
@[grind →]
theorem findPivot?_ge_start [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start : Nat) {pivot : Fin n}
    (hfind : findPivot? M col start = some pivot) :
    start ≤ pivot.val :=
  findPivotAux_ge_start M col start (n - start) hfind

/-- If bounded pivot search fails, every checked entry in the pivot column is
zero. -/
-- @[grind]-excluded: subsumed by `findPivot?_eq_zero_of_none`.
theorem findPivotAux_eq_zero_of_none [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start fuel : Nat) (hfind : findPivotAux M col start fuel = none)
    (i : Fin n) (hstart : start ≤ i.val) (hfuel : i.val < start + fuel) :
    M[i][col] = 0 := by
  induction fuel generalizing start with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases hlt : start < n
      · by_cases hi : i.val = start
        · have hentry : M[(⟨start, hlt⟩ : Fin n)][col] = 0 := by
            by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
            · exact hzero
            · have hzeroNat : ¬ M[start][col.val] = 0 := by
                simpa using hzero
              simp only [findPivotAux, hlt, dif_pos] at hfind
              rw [if_neg (by simpa [getRow, Fin.getElem_fin] using hzero)] at hfind
              simp at hfind
          have hiFin : i = (⟨start, hlt⟩ : Fin n) := Fin.ext hi
          rw [hiFin]
          exact hentry
        · have hentry : M[(⟨start, hlt⟩ : Fin n)][col] = 0 := by
            by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
            · exact hzero
            · have hzeroNat : ¬ M[start][col.val] = 0 := by
                simpa using hzero
              simp only [findPivotAux, hlt, dif_pos] at hfind
              rw [if_neg (by simpa [getRow, Fin.getElem_fin] using hzero)] at hfind
              simp at hfind
          have hnext : findPivotAux M col (start + 1) fuel = none := by
            have hentryNat : M[start][col.val] = 0 := by
              simpa using hentry
            simp only [findPivotAux, hlt, dif_pos] at hfind
            rw [if_pos (by simpa [getRow, Fin.getElem_fin] using hentry)] at hfind
            exact hfind
          have hstart' : start + 1 ≤ i.val := by omega
          have hfuel' : i.val < start + 1 + fuel := by omega
          exact ih (start + 1) hnext hstart' hfuel'
      · omega

/-- If pivot search fails, every entry in the searched suffix of the pivot
column is zero. -/
@[grind]
theorem findPivot?_eq_zero_of_none [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start : Nat) (hfind : findPivot? M col start = none)
    (i : Fin n) (hstart : start ≤ i.val) :
    M[i][col] = 0 := by
  apply findPivotAux_eq_zero_of_none M col start (n - start) hfind i hstart
  omega

/-- If every entry in the bounded suffix searched by `findPivotAux` is zero,
the search fails. -/
-- @[grind]-excluded: ∀-quantified `hzero` premise grind cannot discharge (same
-- reason its `findPivot?` wrapper is left untagged).
theorem findPivotAux_eq_none_of_zero [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start fuel : Nat)
    (hzero : ∀ i : Fin n, start ≤ i.val → i.val < start + fuel → M[i][col] = 0) :
    findPivotAux M col start fuel = none := by
  induction fuel generalizing start with
  | zero =>
      simp [findPivotAux]
  | succ fuel ih =>
      by_cases hstart : start < n
      · have hentry : M[(⟨start, hstart⟩ : Fin n)][col] = 0 :=
          hzero ⟨start, hstart⟩ (Nat.le_refl _)
            (show (⟨start, hstart⟩ : Fin n).val < start + (fuel + 1) by
              simp)
        simp only [findPivotAux, hstart, dif_pos]
        rw [if_pos (by simpa [getRow, Fin.getElem_fin] using hentry)]
        apply ih
        intro i hle hlt
        exact hzero i (by omega) (by omega)
      · simp [findPivotAux, hstart]

/-- If every entry in the suffix searched by `findPivot?` is zero, pivot
search fails. This is the converse of `findPivot?_eq_zero_of_none` and lets
callers turn a column-zero invariant into the executable no-replacement-pivot
condition used by `pivotLoopWith`. -/
-- @[grind]-excluded: its conclusion `findPivot? … = none` makes grind E-match on
-- every `findPivot?` term and inject an existential case-split from the ∀-premise
-- (`hzero`), derailing unrelated goals — confirmed to break `findPivot?_ge_start`
-- closes under `grind`. Use the lemma explicitly when the column-zero converse is
-- needed.
theorem findPivot?_eq_none_of_zero [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start : Nat)
    (hzero : ∀ i : Fin n, start ≤ i.val → M[i][col] = 0) :
    findPivot? M col start = none := by
  apply findPivotAux_eq_none_of_zero M col start (n - start)
  intro i hle _hlt
  exact hzero i hle

/-- A pivot returned by `findPivotAux` indexes a nonzero entry in the pivot
column. -/
-- @[grind]-excluded: subsumed by `findPivot?_some_ne_zero`.
theorem findPivotAux_some_ne_zero [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start fuel : Nat) {pivot : Fin n}
    (hfind : findPivotAux M col start fuel = some pivot) :
    M[pivot][col] ≠ 0 := by
  induction fuel generalizing start with
  | zero =>
      simp [findPivotAux] at hfind
  | succ fuel ih =>
      by_cases hlt : start < n
      · by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
        · simp only [findPivotAux, hlt, dif_pos] at hfind
          rw [if_pos (by simpa [getRow, Fin.getElem_fin] using hzero)] at hfind
          exact ih (start + 1) hfind
        · simp only [findPivotAux, hlt, dif_pos] at hfind
          rw [if_neg (by simpa [getRow, Fin.getElem_fin] using hzero)] at hfind
          simp only [Option.some.injEq] at hfind
          subst hfind
          exact hzero
      · simp [findPivotAux, hlt] at hfind

/-- A pivot returned by `findPivot?` indexes a nonzero entry in the pivot
column. Lets row-pivoted Bareiss callers read off the nonzero post-swap pivot
without unfolding the `findPivotAux` recursion. -/
@[grind →]
theorem findPivot?_some_ne_zero [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start : Nat) {pivot : Fin n}
    (hfind : findPivot? M col start = some pivot) :
    M[pivot][col] ≠ 0 :=
  findPivotAux_some_ne_zero M col start (n - start) hfind

/-- Apply one Bareiss update step to the trailing submatrix strictly below and
to the right of the current pivot.

Rows at or above the pivot (`i ≤ k`) are left untouched, and only the rows below
the pivot are rebuilt. The pivot row is read once into `pivotRow` before the
scatter (it is never mutated, since only rows `i > k` change). This
`mapRowsIdx` form is the reference the entry lemmas reduce through; compiled
code runs the per-entry in-place `stepMatrixWithImpl` via the `@[csimp]` below. -/
@[expose, specialize quot]
def stepMatrixWith [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    Matrix R n n :=
  if hk : k < n then
    let pivotRow := Matrix.getRow M ⟨k, hk⟩
    M.mapRowsIdx fun i row =>
      if k < i.val then
        let mik := row[k]'hk
        Fin.foldl n (fun r j =>
          r.modify j.val fun x =>
            if k < j.val then
              quot (pivot * x - mik * pivotRow[j]) prevPivot
            else if j.val = k then
              0
            else
              x) row
      else
        row
  else
    M

/-- Fast in-place implementation of `stepMatrixWith`: each updated row is written
through per-entry `Matrix.modifyEntries` updates of the flat backing buffer,
with no per-row materialization or write-back. Swapped in for compiled code by
the `@[csimp]` lemma below; `stepMatrixWith` stays the reference form for proofs. -/
@[expose, specialize quot]
def stepMatrixWithImpl [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    Matrix R n n :=
  if hk : k < n then
    let pivotRow := Matrix.getRow M ⟨k, hk⟩
    Fin.foldl n (fun A i =>
      if k < i.val then
        let mik := A[(i, (⟨k, hk⟩ : Fin n))]
        A.modifyEntries i.val fun j x =>
          if k < j.val then
            quot (pivot * x - mik * pivotRow[j]) prevPivot
          else if j.val = k then
            0
          else
            x
      else
        A) M
  else
    M

/-- The `stepMatrixWithImpl` fold leaves row `r` untouched when `r` is not among the
folded indices. -/
private theorem stepImplFold_ne [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (k : Nat) (hk : k < n) (pivot prevPivot : R)
    (pivotRow : Vector R n) (r c : Fin n) :
    ∀ (xs : List (Fin n)) (A : Matrix R n n), (∀ t ∈ xs, t ≠ r) →
      (xs.foldl (fun A (i : Fin n) =>
        if k < i.val then
          A.modifyEntries i.val fun j x =>
            if k < j.val then
              quot (pivot * x - A[(i, (⟨k, hk⟩ : Fin n))] * pivotRow[j]) prevPivot
            else if j.val = k then 0
            else x
        else A) A)[r][c] = A[r][c] := by
  intro xs
  induction xs with
  | nil => intro A _; rfl
  | cons x xs ih =>
    intro A hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht))]
    by_cases hx : k < x.val
    · rw [if_pos hx, Matrix.getElem_modifyEntries,
        if_neg (fun hv => hne x List.mem_cons_self ((Fin.ext hv).symm))]
    · rw [if_neg hx]

/-- The `stepMatrixWithImpl` fold updates every member row from its original
entries. -/
private theorem stepImplFold_mem [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (k : Nat) (hk : k < n) (pivot prevPivot : R)
    (pivotRow : Vector R n) (c : Fin n) :
    ∀ (xs : List (Fin n)), xs.Nodup → ∀ (A : Matrix R n n) (r : Fin n), r ∈ xs →
      (xs.foldl (fun A (i : Fin n) =>
        if k < i.val then
          A.modifyEntries i.val fun j x =>
            if k < j.val then
              quot (pivot * x - A[(i, (⟨k, hk⟩ : Fin n))] * pivotRow[j]) prevPivot
            else if j.val = k then 0
            else x
        else A) A)[r][c] =
      if k < r.val then
        (if k < c.val then
          quot (pivot * A[r][c] - A[(r, (⟨k, hk⟩ : Fin n))] * pivotRow[c]) prevPivot
        else if c.val = k then 0
        else A[r][c])
      else A[r][c] := by
  intro xs
  induction xs with
  | nil => intro _ A r hr; simp at hr
  | cons x xs ih =>
    intro hnd A r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [stepImplFold_ne quot k hk pivot prevPivot pivotRow r c xs _
        (fun t ht heq => (List.nodup_cons.mp hnd).1 (heq ▸ ht))]
      by_cases hx : k < r.val
      · rw [if_pos hx, if_pos hx, Matrix.getElem_modifyEntries, if_pos rfl]
      · rw [if_neg hx, if_neg hx]
    · have hxr : x ≠ r := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hr')
      have hrowr : ∀ cc : Fin n,
          (if k < x.val then
            A.modifyEntries x.val fun j y =>
              if k < j.val then
                quot (pivot * y - A[(x, (⟨k, hk⟩ : Fin n))] * pivotRow[j]) prevPivot
              else if j.val = k then 0
              else y
          else A)[r][cc] = A[r][cc] := by
        intro cc
        by_cases hx : k < x.val
        · rw [if_pos hx, Matrix.getElem_modifyEntries,
            if_neg (fun hv => hxr (Fin.ext hv.symm))]
        · rw [if_neg hx]
      rw [ih (List.nodup_cons.mp hnd).2 _ r hr']
      rw [show (if k < x.val then
            A.modifyEntries x.val fun j y =>
              if k < j.val then
                quot (pivot * y - A[(x, (⟨k, hk⟩ : Fin n))] * pivotRow[j]) prevPivot
              else if j.val = k then 0
              else y
          else A)[(r, (⟨k, hk⟩ : Fin n))] = A[(r, (⟨k, hk⟩ : Fin n))] from by
        rw [Matrix.getElem_pair_eq_nested (i := r) (j := (⟨k, hk⟩ : Fin n)),
          Matrix.getElem_pair_eq_nested (i := r) (j := (⟨k, hk⟩ : Fin n))]
        exact hrowr ⟨k, hk⟩]
      rw [hrowr c]

/-- `stepMatrixWithImpl` agrees entrywise with the same `ofFn` form as
`stepMatrixWith` (`stepMatrixWith_eq_ofFn`); the `@[csimp]` equality chains the two. -/
private theorem stepMatrixImpl_eq_ofFn [Zero R] [Sub R] [Mul R]
    (quot : R → R → R) (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    stepMatrixWithImpl quot M k pivot prevPivot =
      Matrix.ofFn fun i j =>
        if hkij : k < i.val ∧ k < j.val then
          let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
          let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
          quot (pivot * M[(i, j)] - M[(i, colK)] * M[(rowK, j)]) prevPivot
        else if k < i.val ∧ j.val = k then
          0
        else
          M[(i, j)] := by
  apply Matrix.ext_getElem
  intro i j
  rw [Matrix.getElem_ofFn]
  unfold stepMatrixWithImpl
  by_cases hk : k < n
  · rw [dif_pos hk]
    show (Fin.foldl n _ M)[i][j] = _
    rw [Fin.foldl_eq_finRange_foldl,
      stepImplFold_mem quot k hk pivot prevPivot (Matrix.getRow M ⟨k, hk⟩) j
        (List.finRange n) (List.nodup_finRange n) M i (List.mem_finRange _)]
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_eq_getRow]
    rw [show (Matrix.getRow M ⟨k, hk⟩)[j] = (Matrix.getRow M ⟨k, hk⟩)[j.val] from rfl]
    grind
  · rw [dif_neg hk]
    have hik : ¬ k < i.val := fun h => hk (Nat.lt_trans h i.isLt)
    simp only [Matrix.getElem_pair_eq_nested]
    grind

/-- The in-place `stepMatrixWith` agrees entrywise with the `ofFn` form it replaces;
lets the existing entry lemmas reduce through the same body. -/
theorem stepMatrixWith_eq_ofFn [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    stepMatrixWith quot M k pivot prevPivot =
      Matrix.ofFn fun i j =>
        if hkij : k < i.val ∧ k < j.val then
          let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
          let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
          quot (pivot * M[(i, j)] - M[(i, colK)] * M[(rowK, j)]) prevPivot
        else if k < i.val ∧ j.val = k then
          0
        else
          M[(i, j)] := by
  apply Matrix.ext_getElem
  intro i j
  rw [Matrix.getElem_ofFn]
  unfold stepMatrixWith
  by_cases hk : k < n
  · rw [dif_pos hk, Matrix.getElem_mapRowsIdx]
    by_cases hi : k < i.val
    · simp only [hi, if_pos, Vector.getElem_finFoldl_modify, Matrix.getElem_pair_eq_nested,
        Matrix.getElem_eq_getRow, Matrix.getRow, Fin.getElem_fin]
      grind
    · simp only [hi, Matrix.getElem_pair_eq_nested, Matrix.getElem_eq_getRow,
        Matrix.getRow, Fin.getElem_fin]
      grind
  · rw [dif_neg hk]
    have hik : ¬ k < i.val := fun h => hk (Nat.lt_trans h i.isLt)
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_eq_getRow, Matrix.getRow,
      Fin.getElem_fin]
    grind

@[csimp] theorem stepMatrixWith_eq_stepMatrixWithImpl : @stepMatrixWith = @stepMatrixWithImpl := by
  funext R _ _ _ quot n M k pivot prevPivot
  rw [stepMatrixWith_eq_ofFn, stepMatrixImpl_eq_ofFn]

/-- Outside the trailing update region and pivot column below the pivot,
`stepMatrixWith` leaves entries unchanged. -/
@[grind =]
theorem stepMatrixWith_eq_of_not_update
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i j : Fin n)
    (htrail : ¬ (k < i.val ∧ k < j.val))
    (hcol : ¬ (k < i.val ∧ j.val = k)) :
    (stepMatrixWith quot M k pivot prevPivot)[i][j] = M[i][j] := by
  rw [stepMatrixWith_eq_ofFn, Matrix.getElem_ofFn]; simp [htrail, hcol]

/-- `stepMatrixWith` preserves diagonal entries whose index is at or before the
current pivot step. -/
@[grind =]
theorem stepMatrixWith_diag_of_le
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i : Fin n)
    (hi : i.val ≤ k) :
    (stepMatrixWith quot M k pivot prevPivot)[i][i] = M[i][i] := by
  apply stepMatrixWith_eq_of_not_update
  · intro htrail
    exact Nat.not_lt_of_ge hi htrail.1
  · intro hcol
    exact Nat.not_lt_of_ge hi hcol.1

/-- `stepMatrixWith` clears the pivot column below the current pivot. -/
@[grind =]
theorem stepMatrixWith_pivot_col_below
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i colK : Fin n)
    (hi : k < i.val) (hcolK : colK.val = k) :
    (stepMatrixWith quot M k pivot prevPivot)[i][colK] = 0 := by
  rw [stepMatrixWith_eq_ofFn, Matrix.getElem_ofFn]; simp [hi, hcolK]

/-- Entry formula for the trailing block updated by one Bareiss step. -/
-- @[grind]-excluded: `let`-wrapped RHS (`let colK := …; let rowK := …`) is
-- rejected by `grind =`; left untagged like the analogous Hensel step lemmas.
theorem stepMatrixWith_update_eq
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i j : Fin n)
    (hi : k < i.val) (hj : k < j.val) :
    (stepMatrixWith quot M k pivot prevPivot)[i][j] =
      (let colK : Fin n := ⟨k, Nat.lt_trans hi i.isLt⟩
       let rowK : Fin n := ⟨k, Nat.lt_trans hj j.isLt⟩
       quot (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot) := by
  rw [stepMatrixWith_eq_ofFn, Matrix.getElem_ofFn]; simp [hi, hj]

/-- If the current matrix entries already match bordered minors and exact
division evaluates to the next bordered minor, then one `stepMatrixWith` update
preserves the bordered-minor invariant at the updated entry. -/
-- @[grind]-excluded: one-shot bordered-minor invariant-preservation lemma whose
-- bespoke premises (`hpivot`/`hentry`/`hexact`) are not a characterising rewrite.
theorem stepMatrixWith_borderedMinor_update
    [Lean.Grind.CommRing R] (quot : R → R → R)
    (source current : Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (pivot prevPivot : R)
    (hpivot :
      pivot =
        det (borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
          (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (hentry :
      current[i][j] = det (borderedMinor source k hk i j))
    (hleft :
      current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] =
        det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (htop :
      current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j] =
        det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
    (hexact :
      quot
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
          det (borderedMinor source (k + 1) hnext i j)) :
    (stepMatrixWith quot current k pivot prevPivot)[i][j] =
      det (borderedMinor source (k + 1) hnext i j) := by
  rw [stepMatrixWith_update_eq quot current k pivot prevPivot i j hi hj]
  change
    quot
      (pivot * current[i][j] -
        current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] *
        current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j])
      prevPivot =
        det (borderedMinor source (k + 1) hnext i j)
  rw [hpivot, hentry, hleft, htop]
  exact hexact

/-- Exact-division equation for one Bareiss bordered-minor update.

Once a determinant identity supplies the numerator as `nextMinor * prevPivot`,
this lemma packages it as the `quot` premise expected by
`stepMatrixWith_borderedMinor_update`. -/
-- @[grind]-excluded: proof-composition lemma gated on a determinant identity
-- premise (`hdesnanot`); not a local rewrite.
theorem exactQuot_borderedMinor_of_mul_eq [Lean.Grind.CommRing R]
    (quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (prevPivot : R)
    (hprev_ne : prevPivot ≠ 0)
    (hdesnanot :
      det (borderedMinor source (k + 1) hnext i j) * prevPivot =
        det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)) :
    quot
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
      det (borderedMinor source (k + 1) hnext i j) := by
  let nextMinor := det (borderedMinor source (k + 1) hnext i j)
  let numerator :=
    det (borderedMinor source k hk
        (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
        (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
      det (borderedMinor source k hk i j) -
      det (borderedMinor source k hk
        i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
      det (borderedMinor source k hk
        (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)
  have hnum : numerator = prevPivot * nextMinor := by
    dsimp [numerator, nextMinor]
    rw [← hdesnanot, Lean.Grind.CommRing.mul_comm]
  change quot numerator prevPivot = nextMinor
  rw [hnum, Lean.Grind.CommRing.mul_comm]
  exact hquot nextMinor prevPivot hprev_ne

/-- Integer specialization of `exactQuot_borderedMinor_of_mul_eq`. -/
theorem bareissExactDiv_borderedMinor_of_mul_eq
    (source : Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (prevPivot : Int)
    (hprev_ne : prevPivot ≠ 0)
    (hdesnanot :
      det (borderedMinor source (k + 1) hnext i j) * prevPivot =
        det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)) :
    exactDiv
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
      det (borderedMinor source (k + 1) hnext i j) :=
  exactQuot_borderedMinor_of_mul_eq exactDiv Int.mul_ediv_cancel source k hk hnext
    i j hi hj prevPivot hprev_ne hdesnanot

/-- Array-backed state used by the executable row-pivoted Bareiss loop. -/
structure BareissArrayState (R : Type u) where
  step : Nat
  matrix : Array (Array R)
  prevPivot : R
  rowSwaps : Nat
  singularStep : Option Nat

/-- Read an entry from an `Array (Array R)` row-storage representation.

Exposed so downstream Mathlib-free clients (notably the shared scaled
Gram-Schmidt loop in `HexGramSchmidt.Int`) can speak about array storage
without re-deriving the conversion lemmas. -/
@[expose, inline] def getEntry [Zero R]
    (rows : Array (Array R)) (row col : Nat) : R :=
  (rows.getD row #[]).getD col 0

/-- Pack a `Matrix R n n` as an `Array (Array R)` of size `n × n`. The
representation used by the executable Bareiss array pass. -/
@[expose]
def matrixToRows [Zero R] (M : Matrix R n n) : Array (Array R) :=
  (Array.range n).map fun row =>
    (Array.range n).map fun col =>
      if hrow : row < n then
        if hcol : col < n then
          let i : Fin n := ⟨row, hrow⟩
          let j : Fin n := ⟨col, hcol⟩
          M[(i, j)]
        else
          0
      else
        0

/-- Unpack an `Array (Array R)` row-storage representation back into a
`Matrix R n n`. Inverse-on-the-left of `matrixToRows`. -/
@[expose]
def rowsToMatrix [Zero R] (rows : Array (Array R)) (n : Nat) : Matrix R n n :=
  Matrix.ofFn fun i j => getEntry rows i.val j.val

/-- Pointwise round-trip: `getEntry (matrixToRows M)` reads back the matrix
entry at the same index. -/
@[grind =]
theorem getEntry_matrixToRows [Zero R] (M : Matrix R n n) (i j : Fin n) :
    getEntry (matrixToRows M) i.val j.val = M[i][j] := by
  simp [getEntry, matrixToRows]

/-- Reading back the array storage produced by `matrixToRows` recovers the
original matrix. -/
@[grind =]
theorem rowsToMatrix_matrixToRows [Zero R] (M : Matrix R n n) :
    rowsToMatrix (matrixToRows M) n = M := by
  apply Matrix.ext_getElem
  intro i j
  unfold rowsToMatrix
  rw [Matrix.getElem_ofFn]
  exact getEntry_matrixToRows M i j

/-- `set!`-ing index `i` to `v` makes `(xs.set! i v)[i]!` return `v` when `i` is
in bounds, the base case for tracking entries through the array row swap. -/
-- @[grind]-excluded: generic `Array.set!` bookkeeping; tagging would enlarge
-- grind's global search with no Bareiss-specific gain.
private theorem array_getElem!_set!_same {α : Type u} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.set!_eq_setIfInBounds, hi]

/-- `set!`-ing index `i` leaves every other entry untouched: `(xs.set! i v)[j]!`
equals `xs[j]!` whenever `j ≠ i`, the non-target case of the array row swap. -/
-- @[grind]-excluded: generic `Array.set!` bookkeeping (see `_set!_same`).
private theorem array_getElem!_set!_ne {α : Type u} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.set! i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.set!
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]

/-- The `setIfInBounds` analogue of `array_getElem!_set!_same`:
`(xs.setIfInBounds i v)[i]!` returns `v` when `i` is in bounds. -/
-- @[grind]-excluded: generic `Array.setIfInBounds` bookkeeping (see `_set!_same`).
private theorem array_getElem!_setIfInBounds_same {α : Type u} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.setIfInBounds i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  simp [Array.setIfInBounds, hi]

/-- The `setIfInBounds` analogue of `array_getElem!_set!_ne`:
`(xs.setIfInBounds i v)[j]!` equals `xs[j]!` whenever `j ≠ i`. -/
-- @[grind]-excluded: generic `Array.setIfInBounds` bookkeeping (see `_set!_same`).
private theorem array_getElem!_setIfInBounds_ne {α : Type u} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.setIfInBounds i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]

/-- Reading the updated index through `getD` returns the new value. -/
private theorem array_getD_setIfInBounds_same {α : Type u}
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v d : α) :
    (xs.setIfInBounds i v).getD i d = v := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-- Reading another index through `getD` is unchanged by `setIfInBounds`. -/
private theorem array_getD_setIfInBounds_ne {α : Type u}
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v d : α) :
    (xs.setIfInBounds i v).getD j d = xs.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split <;> simp_all

/-- `swapRowsArray` exchanges rows `rowA` and `rowB` of an `Array (Array R)`
via two `set!`s, returning `rows` unchanged when the indices coincide. -/
private def swapRowsArray (rows : Array (Array R)) (rowA rowB : Nat) :
    Array (Array R) :=
  if rowA = rowB then
    rows
  else
    (rows.set! rowA (rows.getD rowB #[])).set! rowB (rows.getD rowA #[])

/-- Entry-wise value of the abstract `rowSwap M rowA rowB` at `[i][j]`: the
swapped rows read from the opposite source, every other row is unchanged. -/
@[grind =]
private theorem rowSwap_get (M : Matrix R n n) (rowA rowB i j : Fin n) :
    (rowSwap M rowA rowB)[i][j] =
      if i = rowB then M[rowA][j] else if i = rowA then M[rowB][j] else M[i][j] :=
  getElem_rowSwap M rowA rowB i j

/-- `swapRowsArray` applied to `matrixToRows M` matches the abstract
`rowSwap M rowA rowB` entry by entry. -/
@[grind =]
private theorem getEntry_swapRowsArray_matrixToRows [Zero R] (M : Matrix R n n)
    (rowA rowB i j : Fin n) :
    getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) i.val j.val =
      (rowSwap M rowA rowB)[i][j] := by
  by_cases hsame : rowA.val = rowB.val
  · have hrows : rowA = rowB := Fin.ext hsame
    subst rowB
    rw [rowSwap_get]
    by_cases hir : i = rowA <;>
      simp [swapRowsArray, getEntry_matrixToRows, hir]
  · have hrows_size : (matrixToRows M).size = n := by
      simp [matrixToRows]
    have hrowA : rowA.val < (matrixToRows M).size := by
      simp [hrows_size, rowA.isLt]
    have hrowB : rowB.val < (matrixToRows M).size := by
      simp [hrows_size, rowB.isLt]
    by_cases hiB : i = rowB
    · subst i
      have hBA : rowB.val ≠ rowA.val := by
        intro h
        exact hsame h.symm
      have hrowB_after :
          rowB.val <
            ((matrixToRows M).setIfInBounds rowA.val
              ((matrixToRows M).getD rowB.val #[])).size := by
        simpa [Array.size_setIfInBounds] using hrowB
      calc
        getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) rowB.val j.val =
            getEntry (matrixToRows M) rowA.val j.val := by
              simp only [swapRowsArray, hsame, if_false, getEntry,
                Array.set!_eq_setIfInBounds]
              exact congrArg (fun row : Array R => row.getD j.val 0)
                (array_getD_setIfInBounds_same
                  ((matrixToRows M).setIfInBounds rowA.val
                    ((matrixToRows M).getD rowB.val #[]))
                  hrowB_after ((matrixToRows M).getD rowA.val #[]) (#[] : Array R))
        _ = M[rowA][j] := getEntry_matrixToRows M rowA j
        _ = (rowSwap M rowA rowB)[rowB][j] := by
              rw [rowSwap_get]
              simp
    · by_cases hiA : i = rowA
      · subst i
        have hAB : rowA.val ≠ rowB.val := by
          intro h
          exact hsame h
        calc
          getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) rowA.val j.val =
              getEntry (matrixToRows M) rowB.val j.val := by
                simp only [swapRowsArray, hsame, if_false, getEntry,
                  Array.set!_eq_setIfInBounds]
                exact congrArg (fun row : Array R => row.getD j.val 0)
                  ((array_getD_setIfInBounds_ne
                    ((matrixToRows M).setIfInBounds rowA.val
                      ((matrixToRows M).getD rowB.val #[]))
                    hAB ((matrixToRows M).getD rowA.val #[]) (#[] : Array R)).trans
                  (array_getD_setIfInBounds_same
                    (matrixToRows M) hrowA ((matrixToRows M).getD rowB.val #[])
                    (#[] : Array R)))
          _ = M[rowB][j] := getEntry_matrixToRows M rowB j
          _ = (rowSwap M rowA rowB)[rowA][j] := by
                rw [rowSwap_get]
                simp [hiB]
      · have hiA_val : i.val ≠ rowA.val := by
          intro h
          exact hiA (Fin.ext h)
        have hiB_val : i.val ≠ rowB.val := by
          intro h
          exact hiB (Fin.ext h)
        calc
          getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) i.val j.val =
              getEntry (matrixToRows M) i.val j.val := by
                simp only [swapRowsArray, hsame, if_false, getEntry,
                  Array.set!_eq_setIfInBounds]
                exact congrArg (fun row : Array R => row.getD j.val 0)
                  ((array_getD_setIfInBounds_ne
                    ((matrixToRows M).setIfInBounds rowA.val
                      ((matrixToRows M).getD rowB.val #[]))
                    hiB_val ((matrixToRows M).getD rowA.val #[]) (#[] : Array R)).trans
                  (array_getD_setIfInBounds_ne
                    (matrixToRows M) hiA_val ((matrixToRows M).getD rowB.val #[])
                    (#[] : Array R)))
          _ = M[i][j] := getEntry_matrixToRows M i j
          _ = (rowSwap M rowA rowB)[i][j] := by
                rw [rowSwap_get]
                simp [hiA, hiB]

/-- Round-tripping `swapRowsArray (matrixToRows M)` back through `rowsToMatrix`
reproduces the abstract `rowSwap M rowA rowB`. -/
@[grind =]
private theorem rowsToMatrix_swapRowsArray_matrixToRows [Zero R] (M : Matrix R n n)
    (rowA rowB : Fin n) :
    rowsToMatrix (swapRowsArray (matrixToRows M) rowA.val rowB.val) n =
      rowSwap M rowA rowB := by
  apply Matrix.ext_getElem
  intro i j
  unfold rowsToMatrix
  rw [Matrix.getElem_ofFn]
  exact getEntry_swapRowsArray_matrixToRows M rowA rowB i j

section GenericBareiss

variable [Zero R] [One R] [Neg R] [Sub R] [Mul R] [DecidableEq R]
variable {quot : R → R → R}

/-- Bareiss elimination with row pivoting. If a column has no nonzero pivot,
the elimination aborts and the determinant is zero. -/
@[expose, specialize quot]
def pivotLoopWith (quot : R → R → R) (fuel : Nat)
    (state : BareissState R n) : BareissState R n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let (M, swaps) :=
          if state.matrix[(k, k)] = 0 then
            match findPivot? state.matrix k (state.step + 1) with
            | some pivot => (rowSwap state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := M[(k, k)]
        if hp : pivot = 0 then
          { state with matrix := M, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissState R n :=
            { step := state.step + 1
              matrix := stepMatrixWith quot M state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotLoopWith quot fuel next
      else
        state

/-- With zero fuel, the row-pivoted Bareiss loop returns its input state. -/
@[grind]
theorem pivotLoopWith_zero_fuel (state : BareissState R n) :
    pivotLoopWith quot 0 state = state := by
  rfl

/-- If the current step is already past the last update step, the row-pivoted
Bareiss loop returns its input state. -/
@[grind]
theorem pivotLoopWith_done (fuel : Nat) (state : BareissState R n)
    (hDone : ¬ state.step + 1 < n) :
    pivotLoopWith quot (fuel + 1) state = state := by
  simp [pivotLoopWith, hDone]

/-- If the current row-pivoted Bareiss pivot is already nonzero, one loop
iteration applies `stepMatrixWith quot`, advances the step, and recurses without
changing the row-swap counter. -/
@[grind]
theorem pivotLoopWith_of_regular_no_swap (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    pivotLoopWith quot (fuel + 1) state =
      pivotLoopWith quot fuel
        { step := state.step + 1
          matrix := stepMatrixWith quot state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp_all [pivotLoopWith, getRow, Fin.getElem_fin]

/-- If the current pivot is zero and pivot search finds no replacement row,
the row-pivoted Bareiss loop records a singular step. -/
@[grind]
theorem pivotLoopWith_of_singular_no_pivot (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    pivotLoopWith quot (fuel + 1) state =
      { state with singularStep := some state.step } := by
  simp_all [pivotLoopWith]

/-- If the current pivot is zero, pivot search finds a replacement row, and
the swapped pivot is nonzero, one loop iteration swaps rows, applies
`stepMatrixWith quot`, advances the step, increments the row-swap counter, and recurses. -/
@[grind]
theorem pivotLoopWith_of_regular_swap (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0) {pivot : Fin n}
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot)
    (hp :
      (rowSwap state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        pivot)[state.step][state.step] ≠ 0) :
    pivotLoopWith quot (fuel + 1) state =
      pivotLoopWith quot fuel
        { step := state.step + 1
          matrix := stepMatrixWith quot
            (rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)
            state.step
            ((rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)[state.step][state.step])
            state.prevPivot
          prevPivot :=
            (rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)[state.step][state.step]
          rowSwaps := state.rowSwaps + 1
          singularStep := none } := by
  simp_all [pivotLoopWith]

/-- `bareissArrayStateWith` runs the matrix-level Bareiss elimination via `pivotLoopWith quot`
and repackages the reduced result as a `BareissArrayState R`, storing the matrix
row-by-row via `matrixToRows`. -/
@[expose, specialize quot]
def bareissArrayStateWith (quot : R → R → R) (M : Matrix R n n) : BareissArrayState R :=
  let state := pivotLoopWith quot n
    { step := 0
      matrix := M
      prevPivot := 1
      rowSwaps := 0
      singularStep := none }
  { step := state.step
    matrix := matrixToRows state.matrix
    prevPivot := state.prevPivot
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- `arraySign` is the determinant sign contributed by `rowSwaps` recorded row
swaps, `1` for an even count and `-1` for an odd count. -/
@[expose]
def arraySign (rowSwaps : Nat) : R :=
  if rowSwaps % 2 = 0 then 1 else -1

/-- `arrayLastDiag?` reads the last diagonal entry `(n-1, n-1)` of the reduced
rows, returning `none` when `n = 0`. -/
@[expose]
def arrayLastDiag? (rows : Array (Array R)) (n : Nat) : Option R :=
  match n with
  | 0 => none
  | k + 1 => some (getEntry rows k k)

/-- `bareissArrayDet` assembles the determinant value from the final array
state, returning `0` when elimination recorded a singular column and the signed
last diagonal entry otherwise. -/
@[expose]
def bareissArrayDet (state : BareissArrayState R) (n : Nat) : R :=
  match state.singularStep with
  | some _ => 0
  | none =>
      match arrayLastDiag? state.matrix n with
      | some d => arraySign state.rowSwaps * d
      | none => arraySign state.rowSwaps

/-- Package a Bareiss state as public elimination data. -/
@[expose]
def finish (state : BareissState R n) : BareissData R n :=
  { matrix := state.matrix
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- Bareiss elimination without pivoting. A zero pivot aborts and records the
singular step. -/
@[expose, specialize quot]
def noPivotLoopWith (quot : R → R → R) (fuel : Nat)
    (state : BareissState R n) : BareissState R n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let pivot := state.matrix[(k, k)]
        if hp : pivot = 0 then
          { state with singularStep := some state.step }
        else
          let next : BareissState R n :=
            { step := state.step + 1
              matrix := stepMatrixWith quot state.matrix state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := state.rowSwaps
              singularStep := none }
          noPivotLoopWith quot fuel next
      else
        state

/-- With zero fuel, the no-pivot Bareiss loop returns its input state. -/
@[grind]
theorem noPivotLoopWith_zero_fuel (state : BareissState R n) :
    noPivotLoopWith quot 0 state = state := by
  rfl

/-- If the current step is already past the last update step, the no-pivot loop
returns its input state. -/
@[grind]
theorem noPivotLoopWith_done (fuel : Nat) (state : BareissState R n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoopWith quot (fuel + 1) state = state := by
  simp [noPivotLoopWith, hDone]

/-- If the no-pivot loop sees a zero pivot before completion, it records the
current step as singular. -/
@[grind]
theorem noPivotLoopWith_of_singular (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] = 0) :
    noPivotLoopWith quot (fuel + 1) state = { state with singularStep := some state.step } := by
  simp_all [noPivotLoopWith]

/-- If the current no-pivot Bareiss pivot is nonzero, one loop iteration applies
`stepMatrixWith quot`, advances the step, and recurses on the remaining fuel. -/
@[grind]
theorem noPivotLoopWith_of_regular (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    noPivotLoopWith quot (fuel + 1) state =
      noPivotLoopWith quot fuel
        { step := state.step + 1
          matrix := stepMatrixWith quot state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp_all [noPivotLoopWith]

/-- Entries in rows already processed, or in columns strictly before the current
step, are unchanged by subsequent no-pivot loop iterations. -/
@[grind]
theorem noPivotLoopWith_matrix_entry_of_row_le_or_col_lt (fuel : Nat)
    (state : BareissState R n) (i j : Fin n)
    (hfixed : i.val ≤ state.step ∨ j.val < state.step) :
    (noPivotLoopWith quot fuel state).matrix[i][j] = state.matrix[i][j] := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoopWith]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoopWith_of_singular (quot := quot) fuel state hDone hp]
        · rw [noPivotLoopWith_of_regular (quot := quot) fuel state hDone]
          · let next : BareissState R n :=
              { step := state.step + 1
                matrix := stepMatrixWith quot state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoopWith quot fuel next).matrix[i][j] = state.matrix[i][j]
            have hnext : i.val ≤ next.step ∨ j.val < next.step := by
              cases hfixed with
              | inl hi =>
                  exact Or.inl (Nat.le_trans hi (Nat.le_succ state.step))
              | inr hj =>
                  exact Or.inr (Nat.lt_trans hj (Nat.lt_succ_self state.step))
            rw [ih next hnext]
            dsimp [next]
            apply stepMatrixWith_eq_of_not_update
            · intro htrail
              cases hfixed with
              | inl hi =>
                  exact Nat.not_lt_of_ge hi htrail.1
              | inr hj =>
                  exact Nat.not_lt_of_ge (Nat.le_of_lt hj) htrail.2
            · intro hcol
              cases hfixed with
              | inl hi =>
                  exact Nat.not_lt_of_ge hi hcol.1
              | inr hj =>
                  exact Nat.ne_of_lt hj hcol.2
          · simpa [k] using hp
      · simp [noPivotLoopWith_done (quot := quot) fuel state hDone]

/-- Diagonal entries at or before the current step are unchanged by subsequent
no-pivot loop iterations. -/
@[grind =]
theorem noPivotLoopWith_diag_of_le_step (fuel : Nat) (state : BareissState R n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoopWith quot fuel state).matrix[i][i] = state.matrix[i][i] :=
  noPivotLoopWith_matrix_entry_of_row_le_or_col_lt (quot := quot) fuel state i i (Or.inl hi)

/-- The no-pivot loop never changes the row-swap counter. -/
@[grind =]
theorem noPivotLoopWith_rowSwaps (fuel : Nat) (state : BareissState R n) :
    (noPivotLoopWith quot fuel state).rowSwaps = state.rowSwaps := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoopWith]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoopWith_of_singular (quot := quot) fuel state hDone hp]
        · rw [noPivotLoopWith_of_regular (quot := quot) fuel state hDone]
          · let next : BareissState R n :=
              { step := state.step + 1
                matrix := stepMatrixWith quot state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoopWith quot fuel next).rowSwaps = state.rowSwaps
            rw [ih next]
          · simpa [k] using hp
      · simp [noPivotLoopWith_done (quot := quot) fuel state hDone]

/-- Once a no-pivot Bareiss state is already at the terminal step boundary,
additional fuel leaves it unchanged. -/
-- @[grind]-excluded: structural fixed-point lemma overlapping `noPivotLoopWith_done (quot := quot)`;
-- kept for manual fuel reasoning.
theorem noPivotLoopWith_id_at_done
    {n : Nat} (fuel : Nat) (state : BareissState R n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoopWith quot fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih => exact noPivotLoopWith_done (quot := quot) f state hDone

/-- Once a no-pivot Bareiss state has recorded a zero pivot at the current
step, additional fuel leaves that singular fixed point unchanged. -/
-- @[grind]-excluded: structural fixed-point lemma with bespoke singular-state
-- premises; used once inside `noPivotLoopWith_add (quot := quot)`.
theorem noPivotLoopWith_id_at_singular_fixedpoint
    {n : Nat} (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0)
    (hsing : state.singularStep = some state.step) :
    noPivotLoopWith quot fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih =>
      rw [noPivotLoopWith_of_singular (quot := quot) f state hDone hp]
      cases state
      simp at hsing ⊢
      exact hsing.symm

/-- Fuel composition for the no-pivot Bareiss loop: running `a + b` units of
fuel from `state` equals running `b` more units after `a` initial units. -/
-- @[grind]-excluded: fuel-composition (associativity) lemma; as a rewrite it
-- splits one loop into two and risks non-termination of grind's saturation.
theorem noPivotLoopWith_add
    {n : Nat} (a b : Nat) (state : BareissState R n) :
    noPivotLoopWith quot (a + b) state = noPivotLoopWith quot b (noPivotLoopWith quot a state) := by
  induction a generalizing state with
  | zero =>
      show noPivotLoopWith quot (0 + b) state = noPivotLoopWith quot b state
      simp
  | succ a' ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · have h_lhs :
              noPivotLoopWith quot (a' + 1 + b) state =
                {state with singularStep := some state.step} := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact noPivotLoopWith_of_singular (quot := quot) (a' + b) state hDone hp
          have h_rhs_inner :
              noPivotLoopWith quot (a' + 1) state =
                {state with singularStep := some state.step} :=
            noPivotLoopWith_of_singular (quot := quot) a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          symm
          let s' : BareissState R n := {state with singularStep := some state.step}
          have hDone_s' : s'.step + 1 < n := hDone
          have hp_s' : s'.matrix[(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)][
              (⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)] = 0 := hp
          have hsing_s' : s'.singularStep = some s'.step := rfl
          exact noPivotLoopWith_id_at_singular_fixedpoint (quot := quot) b s' hDone_s' hp_s' hsing_s'
        · have h_lhs :
              noPivotLoopWith quot (a' + 1 + b) state =
                noPivotLoopWith quot (a' + b)
                  { step := state.step + 1
                    matrix := stepMatrixWith quot state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact noPivotLoopWith_of_regular (quot := quot) (a' + b) state hDone hp
          have h_rhs_inner :
              noPivotLoopWith quot (a' + 1) state =
                noPivotLoopWith quot a'
                  { step := state.step + 1
                    matrix := stepMatrixWith quot state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } :=
            noPivotLoopWith_of_regular (quot := quot) a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          exact ih _
      · rw [noPivotLoopWith_id_at_done (quot := quot) (a' + 1 + b) state hDone]
        rw [noPivotLoopWith_id_at_done (quot := quot) (a' + 1) state hDone]
        exact (noPivotLoopWith_id_at_done (quot := quot) b state hDone).symm

/-- When a no-pivot Bareiss run records no singular step and has enough room,
the `step` field advances by exactly the amount of consumed fuel. -/
-- @[grind]-excluded: step-count accounting lemma with arithmetic-room and
-- no-singular premises; proof-internal, not a characterising rewrite.
theorem noPivotLoopWith_step_eq_add_of_singularStep_none
    {n : Nat} (fuel : Nat) (state : BareissState R n)
    (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (noPivotLoopWith quot fuel state).singularStep = none) :
    (noPivotLoopWith quot fuel state).step = state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step = state.step + 0
      omega
  | succ f ih =>
      have hDone : state.step + 1 < n := by omega
      by_cases hp : state.matrix[state.step][state.step] = 0
      · rw [noPivotLoopWith_of_singular (quot := quot) f state hDone hp] at h_no_sing
        simp at h_no_sing
      · rw [noPivotLoopWith_of_regular (quot := quot) f state hDone hp] at h_no_sing
        rw [noPivotLoopWith_of_regular (quot := quot) f state hDone hp]
        have h_next_room : state.step + 1 + f + 1 ≤ n := by omega
        have h_next_step := ih
          { step := state.step + 1
            matrix := stepMatrixWith quot state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          rfl h_next_room h_no_sing
        rw [h_next_step]
        show state.step + 1 + f = state.step + (f + 1)
        omega

/-- When the no-pivot Bareiss loop completes `fuel` iterations without
recording a singular step, the row-pivoted Bareiss loop produces an
identical state: every diagonal pivot is nonzero, so the row search and
swap branches of `pivotLoopWith quot` are never entered and both loops apply the
same `stepMatrixWith quot` updates. -/
-- @[grind]-excluded: one-shot equivalence-of-two-algorithms bridge gated on a
-- no-singular premise.
theorem pivotLoopWith_eq_noPivotLoopWith_of_no_singular {n : Nat}
    (fuel : Nat) (state : BareissState R n)
    (h_no_sing : (noPivotLoopWith quot fuel state).singularStep = none) :
    pivotLoopWith quot fuel state = noPivotLoopWith quot fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- `noPivotLoopWith quot` records `singularStep = some state.step`, contradicting
          -- `h_no_sing`.
          rw [noPivotLoopWith_of_singular (quot := quot) f state hDone hp] at h_no_sing
          simp at h_no_sing
        · -- Regular branch in both loops; recurse on the same updated state.
          let next : BareissState R n :=
            { step := state.step + 1
              matrix := stepMatrixWith quot state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          rw [noPivotLoopWith_of_regular (quot := quot) f state hDone hp,
            pivotLoopWith_of_regular_no_swap (quot := quot) f state hDone hp]
          show pivotLoopWith quot f next = noPivotLoopWith quot f next
          apply ih
          show (noPivotLoopWith quot f next).singularStep = none
          rw [← noPivotLoopWith_of_regular (quot := quot) f state hDone hp]
          exact h_no_sing
      · rw [pivotLoopWith_done (quot := quot) f state hDone]
        rw [noPivotLoopWith_done (quot := quot) f state hDone]

/-- Initial state used by the no-pivot Bareiss recurrence. -/
@[expose]
def noPivotInitialState (M : Matrix R n n) : BareissState R n :=
  { step := 0
    matrix := M
    prevPivot := 1
    rowSwaps := 0
    singularStep := none }

/-- Run the no-pivot Bareiss recurrence and return the final elimination data. -/
@[expose]
def bareissNoPivotDataWith (quot : R → R → R) (M : Matrix R n n) : BareissData R n :=
  finish <| noPivotLoopWith quot n (noPivotInitialState M)

/-- Determinant computed by the no-pivot Bareiss recurrence. -/
@[expose]
def bareissNoPivotWith (quot : R → R → R) (M : Matrix R n n) : R :=
  (bareissNoPivotDataWith quot M).det

/-- Run the row-pivoted Bareiss elimination and return the final elimination
data together with the swap/sign bookkeeping. -/
@[expose]
def bareissDataWith (quot : R → R → R) (M : Matrix R n n) : BareissData R n :=
  let state := bareissArrayStateWith quot M
  { matrix := rowsToMatrix state.matrix n
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- The packaged row-pivoted Bareiss data is exactly the structured pivot loop
state finished into public determinant data. This is the equality consumed by the
Mathlib determinant proof; array storage is erased by `rowsToMatrix`. -/
-- @[grind]-excluded: array-erasure bridge consumed by the Mathlib determinant
-- proof; not a local rewrite.
theorem bareissDataWith_eq_finish_pivotLoopWith (M : Matrix R n n) :
    bareissDataWith quot M = finish (pivotLoopWith quot n (noPivotInitialState M)) := by
  simp [bareissDataWith, bareissArrayStateWith, noPivotInitialState, finish,
    rowsToMatrix_matrixToRows]

/-- Determinant computed by the row-pivoted Bareiss algorithm. -/
@[expose, specialize quot]
def bareissWith (quot : R → R → R) (M : Matrix R n n) : R :=
  let state := bareissArrayStateWith quot M
  bareissArrayDet state n

/-- The public row-pivoted determinant agrees with the determinant encoded by
`bareissDataWith`. This separates executable array evaluation from the packaged
elimination data used by correctness proofs. -/
-- @[grind]-excluded: one-shot executable-vs-packaged determinant bridge.
theorem bareissWith_eq_bareissDataWith_det (M : Matrix R n n) :
    bareissWith quot M = (bareissDataWith quot M).det := by
  cases n with
  | zero =>
      simp [bareissWith, bareissDataWith, bareissArrayDet, BareissData.det,
        arrayLastDiag?, BareissData.lastDiag?, arraySign, BareissData.sign]
      rfl
  | succ k =>
      simp [bareissWith, bareissDataWith, bareissArrayDet, BareissData.det,
        arrayLastDiag?, BareissData.lastDiag?, rowsToMatrix,
        arraySign, BareissData.sign]
      cases (bareissArrayStateWith quot M).singularStep with
      | some s => rfl
      | none =>
          exact congrArg
            (fun x =>
              (if (bareissArrayStateWith quot M).rowSwaps % 2 = 0 then (1 : R) else -1) * x)
            (Matrix.getElem_ofFn
              (fun i j => getEntry (bareissArrayStateWith quot M).matrix i.val j.val)
              ⟨k, Nat.lt_succ_self k⟩ ⟨k, Nat.lt_succ_self k⟩).symm

/-- If the no-pivot Bareiss pass reaches the final pivot without recording a
singular step, then the public row-pivoted `bareissWith` determinant is exactly
the no-pivot final diagonal entry. -/
-- @[grind]-excluded: premise-heavy final-diagonal identity; one-shot.
theorem bareissWith_eq_noPivotLoopWith_last_of_no_singular {k : Nat}
    (M : Matrix R (k + 1) (k + 1))
    (h_no_sing :
      (noPivotLoopWith quot k (noPivotInitialState M)).singularStep = none)
    (hone : ∀ x : R, 1 * x = x) :
    bareissWith quot M =
      (noPivotLoopWith quot k (noPivotInitialState M)).matrix[Fin.last k][Fin.last k] := by
  let init := noPivotInitialState M
  let stateK := noPivotLoopWith quot k init
  have h_step : stateK.step = k := by
    have h := noPivotLoopWith_step_eq_add_of_singularStep_none (quot := quot) k init rfl
      (by simp [init, noPivotInitialState]) h_no_sing
    simpa [stateK, init, noPivotInitialState] using h
  have hDone_stateK : ¬ stateK.step + 1 < k + 1 := by omega
  have h_full_nopivot : noPivotLoopWith quot (k + 1) init = stateK := by
    rw [noPivotLoopWith_add (quot := quot) k 1 init]
    exact noPivotLoopWith_id_at_done (quot := quot) 1 stateK hDone_stateK
  have h_full_sing : (noPivotLoopWith quot (k + 1) init).singularStep = none := by
    rw [h_full_nopivot]
    exact h_no_sing
  have hpivot := pivotLoopWith_eq_noPivotLoopWith_of_no_singular (quot := quot) (k + 1) init h_full_sing
  rw [bareissWith_eq_bareissDataWith_det (quot := quot), bareissDataWith_eq_finish_pivotLoopWith (quot := quot), hpivot, h_full_nopivot]
  have hdet := BareissData.det_succ_eq (finish stateK) h_no_sing
  rw [hdet]
  simp [finish, BareissData.sign, stateK, init, noPivotInitialState,
    noPivotLoopWith_rowSwaps (quot := quot), hone,
    getRow, Fin.getElem_fin]

end GenericBareiss

/-- Integer specialization of the generic Bareiss matrix update. -/
abbrev stepMatrix (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) :
    Matrix Int n n :=
  stepMatrixWith exactDiv M k pivot prevPivot

/-- Integer specialization of the generic row-pivoted Bareiss loop. -/
abbrev pivotLoop (fuel : Nat) (state : BareissState Int n) : BareissState Int n :=
  pivotLoopWith exactDiv fuel state

/-- Integer specialization of the generic no-pivot Bareiss loop. -/
abbrev noPivotLoop (fuel : Nat) (state : BareissState Int n) : BareissState Int n :=
  noPivotLoopWith exactDiv fuel state

/-- Integer specialization returning the executable array-backed state. -/
abbrev bareissArrayState (M : Matrix Int n n) : BareissArrayState Int :=
  bareissArrayStateWith exactDiv M

/-- Integer specialization returning no-pivot elimination data. -/
abbrev bareissNoPivotData (M : Matrix Int n n) : BareissData Int n :=
  bareissNoPivotDataWith exactDiv M

/-- Integer specialization of the no-pivot Bareiss determinant. -/
abbrev bareissNoPivot (M : Matrix Int n n) : Int :=
  bareissNoPivotWith exactDiv M

/-- Integer specialization returning row-pivoted elimination data. -/
abbrev bareissData (M : Matrix Int n n) : BareissData Int n :=
  bareissDataWith exactDiv M

/-- Integer specialization of the row-pivoted Bareiss determinant. -/
abbrev bareiss (M : Matrix Int n n) : Int :=
  bareissWith exactDiv M

/-! Integer proof-interface compatibility.  These theorems state their
conclusions through the traditional entry points while delegating every proof
to the generic `With` theorem. -/

theorem stepMatrix_eq_ofFn (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) :
    stepMatrix M k pivot prevPivot =
      Matrix.ofFn fun i j =>
        if hkij : k < i.val ∧ k < j.val then
          let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
          let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
          exactDiv (pivot * M[(i, j)] - M[(i, colK)] * M[(rowK, j)]) prevPivot
        else if k < i.val ∧ j.val = k then
          0
        else
          M[(i, j)] :=
  stepMatrixWith_eq_ofFn exactDiv M k pivot prevPivot

@[grind =]
theorem stepMatrix_eq_of_not_update (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i j : Fin n)
    (htrail : ¬ (k < i.val ∧ k < j.val))
    (hcol : ¬ (k < i.val ∧ j.val = k)) :
    (stepMatrix M k pivot prevPivot)[i][j] = M[i][j] :=
  stepMatrixWith_eq_of_not_update exactDiv M k pivot prevPivot i j htrail hcol

@[grind =]
theorem stepMatrix_diag_of_le (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i : Fin n) (hi : i.val ≤ k) :
    (stepMatrix M k pivot prevPivot)[i][i] = M[i][i] :=
  stepMatrixWith_diag_of_le exactDiv M k pivot prevPivot i hi

@[grind =]
theorem stepMatrix_pivot_col_below (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i colK : Fin n)
    (hi : k < i.val) (hcolK : colK.val = k) :
    (stepMatrix M k pivot prevPivot)[i][colK] = 0 :=
  stepMatrixWith_pivot_col_below exactDiv M k pivot prevPivot i colK hi hcolK

theorem stepMatrix_update_eq (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i j : Fin n) (hi : k < i.val) (hj : k < j.val) :
    (stepMatrix M k pivot prevPivot)[i][j] =
      (let colK : Fin n := ⟨k, Nat.lt_trans hi i.isLt⟩
       let rowK : Fin n := ⟨k, Nat.lt_trans hj j.isLt⟩
       exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot) :=
  stepMatrixWith_update_eq exactDiv M k pivot prevPivot i j hi hj

theorem stepMatrix_borderedMinor_update
    (source current : Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (pivot prevPivot : Int)
    (hpivot :
      pivot =
        det (borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
          (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (hentry : current[i][j] = det (borderedMinor source k hk i j))
    (hleft :
      current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] =
        det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (htop :
      current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j] =
        det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
    (hexact :
      exactDiv
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot = det (borderedMinor source (k + 1) hnext i j)) :
    (stepMatrix current k pivot prevPivot)[i][j] =
      det (borderedMinor source (k + 1) hnext i j) :=
  stepMatrixWith_borderedMinor_update exactDiv source current k hk hnext i j hi hj
    pivot prevPivot hpivot hentry hleft htop hexact

@[grind]
theorem pivotLoop_zero_fuel (state : BareissState Int n) :
    pivotLoop 0 state = state :=
  pivotLoopWith_zero_fuel (quot := exactDiv) state

@[grind]
theorem pivotLoop_done (fuel : Nat) (state : BareissState Int n)
    (hDone : ¬ state.step + 1 < n) :
    pivotLoop (fuel + 1) state = state :=
  pivotLoopWith_done (quot := exactDiv) fuel state hDone

@[grind]
theorem pivotLoop_of_regular_no_swap (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    pivotLoop (fuel + 1) state =
      pivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } :=
  pivotLoopWith_of_regular_no_swap (quot := exactDiv) fuel state hDone hp

@[grind]
theorem pivotLoop_of_singular_no_pivot (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    pivotLoop (fuel + 1) state =
      { state with singularStep := some state.step } :=
  pivotLoopWith_of_singular_no_pivot (quot := exactDiv) fuel state hDone hp0 hfind

@[grind]
theorem pivotLoop_of_regular_swap (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0) {pivot : Fin n}
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot)
    (hp :
      (rowSwap state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        pivot)[state.step][state.step] ≠ 0) :
    pivotLoop (fuel + 1) state =
      pivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix
            (rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)
            state.step
            ((rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)[state.step][state.step])
            state.prevPivot
          prevPivot :=
            (rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)[state.step][state.step]
          rowSwaps := state.rowSwaps + 1
          singularStep := none } :=
  pivotLoopWith_of_regular_swap (quot := exactDiv) fuel state hDone hp0 hfind hp

@[grind]
theorem noPivotLoop_zero_fuel (state : BareissState Int n) :
    noPivotLoop 0 state = state :=
  noPivotLoopWith_zero_fuel (quot := exactDiv) state

@[grind]
theorem noPivotLoop_done (fuel : Nat) (state : BareissState Int n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoop (fuel + 1) state = state :=
  noPivotLoopWith_done (quot := exactDiv) fuel state hDone

@[grind]
theorem noPivotLoop_of_singular (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] = 0) :
    noPivotLoop (fuel + 1) state = { state with singularStep := some state.step } :=
  noPivotLoopWith_of_singular (quot := exactDiv) fuel state hDone hp

@[grind]
theorem noPivotLoop_of_regular (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    noPivotLoop (fuel + 1) state =
      noPivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } :=
  noPivotLoopWith_of_regular (quot := exactDiv) fuel state hDone hp

@[grind]
theorem noPivotLoop_matrix_entry_of_row_le_or_col_lt (fuel : Nat)
    (state : BareissState Int n) (i j : Fin n)
    (hfixed : i.val ≤ state.step ∨ j.val < state.step) :
    (noPivotLoop fuel state).matrix[i][j] = state.matrix[i][j] :=
  noPivotLoopWith_matrix_entry_of_row_le_or_col_lt
    (quot := exactDiv) fuel state i j hfixed

@[grind =]
theorem noPivotLoop_diag_of_le_step (fuel : Nat) (state : BareissState Int n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoop fuel state).matrix[i][i] = state.matrix[i][i] :=
  noPivotLoopWith_diag_of_le_step (quot := exactDiv) fuel state i hi

@[grind =]
theorem noPivotLoop_rowSwaps (fuel : Nat) (state : BareissState Int n) :
    (noPivotLoop fuel state).rowSwaps = state.rowSwaps :=
  noPivotLoopWith_rowSwaps (quot := exactDiv) fuel state

theorem noPivotLoop_id_at_done (fuel : Nat) (state : BareissState Int n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoop fuel state = state :=
  noPivotLoopWith_id_at_done (quot := exactDiv) fuel state hDone

theorem noPivotLoop_id_at_singular_fixedpoint (fuel : Nat)
    (state : BareissState Int n) (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0)
    (hsing : state.singularStep = some state.step) :
    noPivotLoop fuel state = state :=
  noPivotLoopWith_id_at_singular_fixedpoint
    (quot := exactDiv) fuel state hDone hp hsing

theorem noPivotLoop_add (a b : Nat) (state : BareissState Int n) :
    noPivotLoop (a + b) state = noPivotLoop b (noPivotLoop a state) :=
  noPivotLoopWith_add (quot := exactDiv) a b state

theorem noPivotLoop_step_eq_add_of_singularStep_none (fuel : Nat)
    (state : BareissState Int n) (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (noPivotLoop fuel state).singularStep = none) :
    (noPivotLoop fuel state).step = state.step + fuel :=
  noPivotLoopWith_step_eq_add_of_singularStep_none
    (quot := exactDiv) fuel state h_init h_room h_no_sing

theorem pivotLoop_eq_noPivotLoop_of_no_singular (fuel : Nat)
    (state : BareissState Int n)
    (h_no_sing : (noPivotLoop fuel state).singularStep = none) :
    pivotLoop fuel state = noPivotLoop fuel state :=
  pivotLoopWith_eq_noPivotLoopWith_of_no_singular
    (quot := exactDiv) fuel state h_no_sing

theorem bareissData_eq_finish_pivotLoop (M : Matrix Int n n) :
    bareissData M = finish (pivotLoop n (noPivotInitialState M)) :=
  bareissDataWith_eq_finish_pivotLoopWith (quot := exactDiv) M

theorem bareiss_eq_bareissData_det (M : Matrix Int n n) :
    bareiss M = (bareissData M).det :=
  bareissWith_eq_bareissDataWith_det (quot := exactDiv) M

theorem bareiss_eq_noPivotLoop_last_of_no_singular {k : Nat}
    (M : Matrix Int (k + 1) (k + 1))
    (h_no_sing :
      (noPivotLoop k (noPivotInitialState M)).singularStep = none) :
    bareiss M =
      (noPivotLoop k (noPivotInitialState M)).matrix[Fin.last k][Fin.last k] :=
  bareissWith_eq_noPivotLoopWith_last_of_no_singular
    (quot := exactDiv) M h_no_sing Int.one_mul

end Matrix
end Hex
