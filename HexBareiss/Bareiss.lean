/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant
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

variable {n : Nat}

/-- Output of an executable Bareiss elimination pass. -/
structure BareissData (n : Nat) where
  /-- Terminal matrix produced by the Bareiss pass. When `singularStep = none`,
  `BareissData.det` reads the last diagonal entry of this matrix, with the
  row-swap sign applied; for `n = 0`, the empty diagonal contributes `1`. -/
  matrix : Matrix Int n n
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
def sign (data : BareissData n) : Int :=
  if data.rowSwaps % 2 = 0 then 1 else -1

@[expose]
def lastDiag? (M : Matrix Int n n) : Option Int :=
  match n with
  | 0 => none
  | k + 1 =>
      let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      some M[i][i]

/-- The determinant encoded by a Bareiss elimination result. -/
@[expose]
def det (data : BareissData n) : Int :=
  match data.singularStep with
  | some _ => 0
  | none =>
      match lastDiag? data.matrix with
      | some d => data.sign * d
      | none => data.sign

/-- A recorded singular step encodes determinant zero. -/
@[grind →]
theorem det_eq_zero_of_singularStep {data : BareissData n} {k : Nat}
    (h : data.singularStep = some k) :
    data.det = 0 := by
  unfold det
  rw [h]

/-- For a non-singular Bareiss elimination of a positive-size matrix, the
encoded determinant is `sign * (last diagonal entry)`. -/
@[grind =]
theorem det_succ_eq {k : Nat} (data : BareissData (k + 1))
    (h : data.singularStep = none) :
    data.det = data.sign *
      data.matrix[(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] := by
  unfold det
  rw [h]
  rfl

/-- For a non-singular Bareiss elimination of an empty matrix, the encoded
determinant is the sign. -/
@[grind =]
theorem det_zero_eq (data : BareissData 0)
    (h : data.singularStep = none) :
    data.det = data.sign := by
  unfold det
  rw [h]
  rfl

end BareissData

/-- Internal state of the no-pivot Bareiss recurrence, exposed read-only for
the Mathlib-side determinant proof. -/
structure BareissState (n : Nat) where
  /-- Current elimination step. The next update, if any, uses this row and
  column as the pivot position. -/
  step : Nat
  /-- Current matrix carried by the Bareiss recurrence. Its terminal value is
  copied into `BareissData.matrix` by `finish`. -/
  matrix : Matrix Int n n
  /-- Previous nonzero pivot used as the exact-division denominator; initially
  `1`. -/
  prevPivot : Int
  /-- Number of row swaps already performed by the pivoting wrapper. Even
  parity contributes determinant sign `1`; odd parity contributes sign `-1`. -/
  rowSwaps : Nat
  /-- First step at which the recurrence found a zero pivot and could not
  continue. A value `some k` is terminal evidence for the determinant-zero
  encoding; `none` means no singular step has been recorded. -/
  singularStep : Option Nat

/-- Exact division used by the Bareiss recurrence.

Divisibility holds at every call site by the algorithmic invariant, so
this function performs no runtime divisibility check: the `@[extern]`
binding compiles the call directly to `lean_int_div_exact`, matching
`Int.divExact`. The Lean-level reduction is the same `num / denom` that
`Int.divExact` uses as its logical model. -/
@[expose, extern "lean_int_div_exact"]
def exactDiv (num denom : @& Int) : Int := num / denom

/-- When divisibility is known, `exactDiv` is the GMP-backed exact quotient. -/
-- @[grind]-excluded: RHS `Int.divExact num denom h` mentions the divisibility
-- proof term `h`, which `grind =` cannot instantiate from the LHS pattern.
theorem exactDiv_eq_divExact {num denom : Int} (h : denom ∣ num) :
    exactDiv num denom = Int.divExact num denom h := by
  simp [exactDiv, Int.divExact_eq_ediv]

/-- Search column `col` for a nonzero pivot at or below `start`. -/
@[expose]
def findPivotAux (M : Matrix Int n n) (col : Fin n) (start fuel : Nat) :
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

/-- Search column `col` for a nonzero pivot at or below `start`. -/
@[expose]
def findPivot? (M : Matrix Int n n) (col : Fin n) (start : Nat) :
    Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- A pivot returned by `findPivotAux` is always at or below its starting row. -/
-- @[grind]-excluded: subsumed by `findPivot?_ge_start`; tagging the fuelled
-- helper too would duplicate grind's rule for the same fact.
theorem findPivotAux_ge_start (M : Matrix Int n n) (col : Fin n)
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
theorem findPivot?_ge_start (M : Matrix Int n n) (col : Fin n)
    (start : Nat) {pivot : Fin n}
    (hfind : findPivot? M col start = some pivot) :
    start ≤ pivot.val :=
  findPivotAux_ge_start M col start (n - start) hfind

/-- If bounded pivot search fails, every checked entry in the pivot column is
zero. -/
-- @[grind]-excluded: subsumed by `findPivot?_eq_zero_of_none`.
theorem findPivotAux_eq_zero_of_none (M : Matrix Int n n) (col : Fin n)
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
              simp [findPivotAux, hlt, hzeroNat] at hfind
          have hiFin : i = (⟨start, hlt⟩ : Fin n) := Fin.ext hi
          rw [hiFin]
          exact hentry
        · have hentry : M[(⟨start, hlt⟩ : Fin n)][col] = 0 := by
            by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
            · exact hzero
            · have hzeroNat : ¬ M[start][col.val] = 0 := by
                simpa using hzero
              simp [findPivotAux, hlt, hzeroNat] at hfind
          have hnext : findPivotAux M col (start + 1) fuel = none := by
            have hentryNat : M[start][col.val] = 0 := by
              simpa using hentry
            simp [findPivotAux, hlt, hentryNat] at hfind
            exact hfind
          have hstart' : start + 1 ≤ i.val := by omega
          have hfuel' : i.val < start + 1 + fuel := by omega
          exact ih (start + 1) hnext hstart' hfuel'
      · omega

/-- If pivot search fails, every entry in the searched suffix of the pivot
column is zero. -/
@[grind]
theorem findPivot?_eq_zero_of_none (M : Matrix Int n n) (col : Fin n)
    (start : Nat) (hfind : findPivot? M col start = none)
    (i : Fin n) (hstart : start ≤ i.val) :
    M[i][col] = 0 := by
  apply findPivotAux_eq_zero_of_none M col start (n - start) hfind i hstart
  omega

/-- If every entry in the bounded suffix searched by `findPivotAux` is zero,
the search fails. -/
-- @[grind]-excluded: ∀-quantified `hzero` premise grind cannot discharge (same
-- reason its `findPivot?` wrapper is left untagged).
theorem findPivotAux_eq_none_of_zero (M : Matrix Int n n) (col : Fin n)
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
        have hentryNat : M[start][col.val] = 0 := by
          simpa using hentry
        simp [findPivotAux, hstart, hentryNat]
        apply ih
        intro i hle hlt
        exact hzero i (by omega) (by omega)
      · simp [findPivotAux, hstart]

/-- If every entry in the suffix searched by `findPivot?` is zero, pivot
search fails. This is the converse of `findPivot?_eq_zero_of_none` and lets
callers turn a column-zero invariant into the executable no-replacement-pivot
condition used by `pivotLoop`. -/
-- @[grind]-excluded: its conclusion `findPivot? … = none` makes grind E-match on
-- every `findPivot?` term and inject an existential case-split from the ∀-premise
-- (`hzero`), derailing unrelated goals — confirmed to break `findPivot?_ge_start`
-- closes under `grind`. Use the lemma explicitly when the column-zero converse is
-- needed.
theorem findPivot?_eq_none_of_zero (M : Matrix Int n n) (col : Fin n)
    (start : Nat)
    (hzero : ∀ i : Fin n, start ≤ i.val → M[i][col] = 0) :
    findPivot? M col start = none := by
  apply findPivotAux_eq_none_of_zero M col start (n - start)
  intro i hle _hlt
  exact hzero i hle

/-- A pivot returned by `findPivotAux` indexes a nonzero entry in the pivot
column. -/
-- @[grind]-excluded: subsumed by `findPivot?_some_ne_zero`.
theorem findPivotAux_some_ne_zero (M : Matrix Int n n) (col : Fin n)
    (start fuel : Nat) {pivot : Fin n}
    (hfind : findPivotAux M col start fuel = some pivot) :
    M[pivot][col] ≠ 0 := by
  induction fuel generalizing start with
  | zero =>
      simp [findPivotAux] at hfind
  | succ fuel ih =>
      by_cases hlt : start < n
      · by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
        · have hzeroNat : M[start][col.val] = 0 := by
            simpa using hzero
          simp [findPivotAux, hlt, hzeroNat] at hfind
          exact ih (start + 1) hfind
        · have hzeroNat : ¬ M[start][col.val] = 0 := by
            simpa using hzero
          simp [findPivotAux, hlt, hzeroNat] at hfind
          subst hfind
          exact hzero
      · simp [findPivotAux, hlt] at hfind

/-- A pivot returned by `findPivot?` indexes a nonzero entry in the pivot
column. Lets row-pivoted Bareiss callers read off the nonzero post-swap pivot
without unfolding the `findPivotAux` recursion. -/
@[grind →]
theorem findPivot?_some_ne_zero (M : Matrix Int n n) (col : Fin n)
    (start : Nat) {pivot : Fin n}
    (hfind : findPivot? M col start = some pivot) :
    M[pivot][col] ≠ 0 :=
  findPivotAux_some_ne_zero M col start (n - start) hfind

/-- Apply one Bareiss update step to the trailing submatrix strictly below and
to the right of the current pivot. -/
@[expose]
def stepMatrix (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) :
    Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if hkij : k < i.val ∧ k < j.val then
      let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
      let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
      exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot
    else if hBelow : k < i.val ∧ j.val = k then
      0
    else
      M[i][j]

/-- Outside the trailing update region and pivot column below the pivot,
`stepMatrix` leaves entries unchanged. -/
@[grind =]
theorem stepMatrix_eq_of_not_update
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i j : Fin n)
    (htrail : ¬ (k < i.val ∧ k < j.val))
    (hcol : ¬ (k < i.val ∧ j.val = k)) :
    (stepMatrix M k pivot prevPivot)[i][j] = M[i][j] := by
  simp [stepMatrix, Matrix.ofFn, htrail, hcol]

/-- `stepMatrix` preserves diagonal entries whose index is at or before the
current pivot step. -/
@[grind =]
theorem stepMatrix_diag_of_le
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i : Fin n)
    (hi : i.val ≤ k) :
    (stepMatrix M k pivot prevPivot)[i][i] = M[i][i] := by
  apply stepMatrix_eq_of_not_update
  · intro htrail
    exact Nat.not_lt_of_ge hi htrail.1
  · intro hcol
    exact Nat.not_lt_of_ge hi hcol.1

/-- `stepMatrix` clears the pivot column below the current pivot. -/
@[grind =]
theorem stepMatrix_pivot_col_below
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i colK : Fin n)
    (hi : k < i.val) (hcolK : colK.val = k) :
    (stepMatrix M k pivot prevPivot)[i][colK] = 0 := by
  simp [stepMatrix, Matrix.ofFn, hi, hcolK]

/-- Entry formula for the trailing block updated by one Bareiss step. -/
-- @[grind]-excluded: `let`-wrapped RHS (`let colK := …; let rowK := …`) is
-- rejected by `grind =`; left untagged like the analogous Hensel step lemmas.
theorem stepMatrix_update_eq
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i j : Fin n)
    (hi : k < i.val) (hj : k < j.val) :
    (stepMatrix M k pivot prevPivot)[i][j] =
      (let colK : Fin n := ⟨k, Nat.lt_trans hi i.isLt⟩
       let rowK : Fin n := ⟨k, Nat.lt_trans hj j.isLt⟩
       exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot) := by
  simp [stepMatrix, Matrix.ofFn, hi, hj]

/-- If the current matrix entries already match bordered minors and exact
division evaluates to the next bordered minor, then one `stepMatrix` update
preserves the bordered-minor invariant at the updated entry. -/
-- @[grind]-excluded: one-shot bordered-minor invariant-preservation lemma whose
-- bespoke premises (`hpivot`/`hentry`/`hexact`) are not a characterising rewrite.
theorem stepMatrix_borderedMinor_update
    (source current : Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (pivot prevPivot : Int)
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
      exactDiv
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
          det (borderedMinor source (k + 1) hnext i j)) :
    (stepMatrix current k pivot prevPivot)[i][j] =
      det (borderedMinor source (k + 1) hnext i j) := by
  rw [stepMatrix_update_eq current k pivot prevPivot i j hi hj]
  change
    exactDiv
      (pivot * current[i][j] -
        current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] *
        current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j])
      prevPivot =
        det (borderedMinor source (k + 1) hnext i j)
  rw [hpivot, hentry, hleft, htop]
  exact hexact

/-- Exact-division equation for one Bareiss bordered-minor update.

Once a determinant identity supplies the numerator as `nextMinor * prevPivot`,
this lemma packages it as the `exactDiv` premise expected by
`stepMatrix_borderedMinor_update`. -/
-- @[grind]-excluded: proof-composition lemma gated on a determinant identity
-- premise (`hdesnanot`); not a local rewrite.
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
  have hdvd : prevPivot ∣ numerator := ⟨nextMinor, hnum⟩
  rw [exactDiv_eq_divExact hdvd]
  change numerator / prevPivot = nextMinor
  exact Int.ediv_eq_of_eq_mul_right hprev_ne hnum

structure BareissArrayState where
  step : Nat
  matrix : Array (Array Int)
  prevPivot : Int
  rowSwaps : Nat
  singularStep : Option Nat

/-- Read an entry from an `Array (Array Int)` row-storage representation.

Exposed so downstream Mathlib-free clients (notably the shared scaled
Gram-Schmidt loop in `HexGramSchmidt.Int`) can speak about array storage
without re-deriving the conversion lemmas. -/
@[expose, inline] def getEntry (rows : Array (Array Int)) (row col : Nat) : Int :=
  rows[row]![col]!

/-- Pack a `Matrix Int n n` as an `Array (Array Int)` of size `n × n`. The
representation used by the executable Bareiss array pass. -/
@[expose]
def matrixToRows (M : Matrix Int n n) : Array (Array Int) :=
  (Array.range n).map fun row =>
    (Array.range n).map fun col =>
      if hrow : row < n then
        if hcol : col < n then
          let i : Fin n := ⟨row, hrow⟩
          let j : Fin n := ⟨col, hcol⟩
          M[i][j]
        else
          0
      else
        0

/-- Unpack an `Array (Array Int)` row-storage representation back into a
`Matrix Int n n`. Inverse-on-the-left of `matrixToRows`. -/
@[expose]
def rowsToMatrix (rows : Array (Array Int)) (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j => getEntry rows i.val j.val

/-- Pointwise round-trip: `getEntry (matrixToRows M)` reads back the matrix
entry at the same index. -/
@[grind =]
theorem getEntry_matrixToRows (M : Matrix Int n n) (i j : Fin n) :
    getEntry (matrixToRows M) i.val j.val = M[i][j] := by
  simp [getEntry, matrixToRows]

/-- Reading back the array storage produced by `matrixToRows` recovers the
original matrix. -/
@[grind =]
theorem rowsToMatrix_matrixToRows (M : Matrix Int n n) :
    rowsToMatrix (matrixToRows M) n = M := by
  ext i hi j hj
  simpa [rowsToMatrix, Matrix.ofFn] using getEntry_matrixToRows M ⟨i, hi⟩ ⟨j, hj⟩

/-- `set!`-ing index `i` to `v` makes `(xs.set! i v)[i]!` return `v` when `i` is
in bounds, the base case for tracking entries through the array row swap. -/
-- @[grind]-excluded: generic `Array.set!` bookkeeping; tagging would enlarge
-- grind's global search with no Bareiss-specific gain.
private theorem array_getElem!_set!_same {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.set!_eq_setIfInBounds, hi]

/-- `set!`-ing index `i` leaves every other entry untouched: `(xs.set! i v)[j]!`
equals `xs[j]!` whenever `j ≠ i`, the non-target case of the array row swap. -/
-- @[grind]-excluded: generic `Array.set!` bookkeeping (see `_set!_same`).
private theorem array_getElem!_set!_ne {α : Type} [Inhabited α]
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
private theorem array_getElem!_setIfInBounds_same {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.setIfInBounds i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  simp [Array.setIfInBounds, hi]

/-- The `setIfInBounds` analogue of `array_getElem!_set!_ne`:
`(xs.setIfInBounds i v)[j]!` equals `xs[j]!` whenever `j ≠ i`. -/
-- @[grind]-excluded: generic `Array.setIfInBounds` bookkeeping (see `_set!_same`).
private theorem array_getElem!_setIfInBounds_ne {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.setIfInBounds i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]

/-- `swapRowsArray` exchanges rows `rowA` and `rowB` of an `Array (Array Int)`
via two `set!`s, returning `rows` unchanged when the indices coincide. -/
private def swapRowsArray (rows : Array (Array Int)) (rowA rowB : Nat) :
    Array (Array Int) :=
  if rowA = rowB then
    rows
  else
    (rows.set! rowA rows[rowB]!).set! rowB rows[rowA]!

/-- Entry-wise value of the abstract `rowSwap M rowA rowB` at `[i][j]`: the
swapped rows read from the opposite source, every other row is unchanged. -/
@[grind =]
private theorem rowSwap_get (M : Matrix Int n n) (rowA rowB i j : Fin n) :
    (rowSwap M rowA rowB)[i][j] =
      if i = rowB then M[rowA][j] else if i = rowA then M[rowB][j] else M[i][j] :=
  getElem_rowSwap M rowA rowB i j

/-- `swapRowsArray` applied to `matrixToRows M` matches the abstract
`rowSwap M rowA rowB` entry by entry. -/
@[grind =]
private theorem getEntry_swapRowsArray_matrixToRows (M : Matrix Int n n)
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
            ((matrixToRows M).setIfInBounds rowA.val (matrixToRows M)[rowB.val]!).size := by
        simpa [Array.size_setIfInBounds] using hrowB
      calc
        getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) rowB.val j.val =
            getEntry (matrixToRows M) rowA.val j.val := by
              simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
              rw [array_getElem!_setIfInBounds_same
                (xs := (matrixToRows M).setIfInBounds rowA.val (matrixToRows M)[rowB.val]!)
                hrowB_after]
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
                simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
                rw [array_getElem!_setIfInBounds_ne
                  (xs := (matrixToRows M).setIfInBounds rowA.val
                    (matrixToRows M)[rowB.val]!) hAB]
                exact congrArg (fun row => row[j.val]!)
                  (array_getElem!_setIfInBounds_same
                    (xs := matrixToRows M) hrowA (matrixToRows M)[rowB.val]!)
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
                simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
                rw [array_getElem!_setIfInBounds_ne
                  (xs := (matrixToRows M).setIfInBounds rowA.val
                    (matrixToRows M)[rowB.val]!) hiB_val]
                exact congrArg (fun row => row[j.val]!)
                  (array_getElem!_setIfInBounds_ne
                    (xs := matrixToRows M) hiA_val (matrixToRows M)[rowB.val]!)
          _ = M[i][j] := getEntry_matrixToRows M i j
          _ = (rowSwap M rowA rowB)[i][j] := by
                rw [rowSwap_get]
                simp [hiA, hiB]

/-- Round-tripping `swapRowsArray (matrixToRows M)` back through `rowsToMatrix`
reproduces the abstract `rowSwap M rowA rowB`. -/
@[grind =]
private theorem rowsToMatrix_swapRowsArray_matrixToRows (M : Matrix Int n n)
    (rowA rowB : Fin n) :
    rowsToMatrix (swapRowsArray (matrixToRows M) rowA.val rowB.val) n =
      rowSwap M rowA rowB := by
  ext i hi j hj
  simpa [rowsToMatrix, Matrix.ofFn] using
    getEntry_swapRowsArray_matrixToRows M rowA rowB ⟨i, hi⟩ ⟨j, hj⟩

/-- `findPivotArrayAux` searches the array-backed column `col` from `start` for
a nonzero Bareiss pivot, using `fuel` to bound the scan. -/
private def findPivotArrayAux
    (rows : Array (Array Int)) (n col start fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if start < n then
        if getEntry rows start col = 0 then
          findPivotArrayAux rows n col (start + 1) fuel
        else
          some start
      else
        none

/-- `findPivotArray?` runs array-backed pivot search on the suffix at or below
`start`, mirroring the matrix-level `findPivot?` search range. -/
private def findPivotArray? (rows : Array (Array Int)) (n col start : Nat) :
    Option Nat :=
  findPivotArrayAux rows n col start (n - start)

/-- `findPivotArrayAux_matrixToRows` identifies bounded array pivot search on
`matrixToRows M` with the matrix-level `findPivotAux` result. -/
-- @[grind]-excluded: subsumed by `findPivotArray?_matrixToRows`.
private theorem findPivotArrayAux_matrixToRows (M : Matrix Int n n)
    (col : Fin n) (start fuel : Nat) :
    findPivotArrayAux (matrixToRows M) n col.val start fuel =
      (findPivotAux M col start fuel).map Fin.val := by
  induction fuel generalizing start with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [findPivotArrayAux, findPivotAux]
      by_cases hstart : start < n
      · simp [hstart]
        have hentry :
            getEntry (matrixToRows M) start col.val =
              M[(⟨start, hstart⟩ : Fin n)][col] := by
          simpa [getEntry] using
            getEntry_matrixToRows M (⟨start, hstart⟩ : Fin n) col
        rw [hentry]
        by_cases hpivotNat : M[start][col.val] = 0
        · have hpivot : M[(⟨start, hstart⟩ : Fin n)][col] = 0 := by
            simpa using hpivotNat
          simp [hpivotNat, ih]
        · have hpivot : M[(⟨start, hstart⟩ : Fin n)][col] ≠ 0 := by
            simpa using hpivotNat
          simp [hpivotNat]
      · simp [hstart]

/-- `findPivotArray?_matrixToRows` identifies full array pivot search on
`matrixToRows M` with the matrix-level `findPivot?` result. -/
@[grind =]
private theorem findPivotArray?_matrixToRows (M : Matrix Int n n)
    (col : Fin n) (start : Nat) :
    findPivotArray? (matrixToRows M) n col.val start =
      (findPivot? M col start).map Fin.val := by
  simp [findPivotArray?, findPivot?, findPivotArrayAux_matrixToRows]

/-- `findPivotArrayAux_matches` shows bounded array pivot search agrees with
`findPivotAux` whenever the searched array column matches the matrix column. -/
-- @[grind]-excluded: ∀-quantified `hentry` premise that grind cannot discharge.
private theorem findPivotArrayAux_matches (rows : Array (Array Int))
    (M : Matrix Int n n) (col : Fin n) (start fuel : Nat)
    (hentry : ∀ i : Fin n, getEntry rows i.val col.val = M[i][col]) :
    findPivotArrayAux rows n col.val start fuel =
      (findPivotAux M col start fuel).map Fin.val := by
  induction fuel generalizing start with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [findPivotArrayAux, findPivotAux]
      by_cases hstart : start < n
      · simp [hstart]
        have hentry_start :
            getEntry rows start col.val =
              M[(⟨start, hstart⟩ : Fin n)][col] :=
          hentry ⟨start, hstart⟩
        rw [hentry_start]
        by_cases hpivotNat : M[start][col.val] = 0
        · have hpivot : M[(⟨start, hstart⟩ : Fin n)][col] = 0 := by
            simpa using hpivotNat
          simp [hpivotNat, ih]
        · simp [hpivotNat]
      · simp [hstart]

/-- `findPivotArray?_matches` shows full array pivot search agrees with
`findPivot?` whenever the searched array column matches the matrix column. -/
-- @[grind]-excluded: ∀-quantified `hentry` premise that grind cannot discharge.
private theorem findPivotArray?_matches (rows : Array (Array Int))
    (M : Matrix Int n n) (col : Fin n) (start : Nat)
    (hentry : ∀ i : Fin n, getEntry rows i.val col.val = M[i][col]) :
    findPivotArray? rows n col.val start =
      (findPivot? M col start).map Fin.val := by
  simp [findPivotArray?, findPivot?, findPivotArrayAux_matches rows M col start (n - start)
    hentry]

/-- Array-storage form of `stepMatrix`: rebuild the whole `n × n` array,
applying the Bareiss trailing update for entries strictly below and to the
right of the pivot, clearing the pivot column below the pivot, and leaving
all other entries unchanged. -/
@[expose]
def stepArray (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int) :
    Array (Array Int) :=
  (Array.range n).map fun i =>
    if k < i then
      (Array.range n).map fun j =>
        if k < j then
          exactDiv (pivot * getEntry rows i j - getEntry rows i k * getEntry rows k j)
            prevPivot
        else if j = k then
          0
        else
          getEntry rows i j
    else
      rows[i]!

/-- `getEntry_rangeMap₂` proves that reading entry `(i, j)` from the matrix
materialised by the doubly-ranged `Array.range` map of `f` recovers `f i j`. -/
-- @[grind]-excluded: the function parameter `f` lives only inside the inner
-- `Array.map`, unreachable from the LHS pattern, so `grind =` cannot instantiate it.
private theorem getEntry_rangeMap₂ (f : Nat → Nat → Int) (i j : Fin n) :
    getEntry ((Array.range n).map fun row => (Array.range n).map fun col => f row col)
      i.val j.val = f i.val j.val := by
  simp [getEntry]

/-- Pointwise correspondence: if the array storage `rows` matches a matrix `M`
at every entry, then `stepArray` on `rows` matches `stepMatrix` on `M` at
every entry. -/
-- @[grind]-excluded: ∀-quantified `hentry` premise that grind cannot discharge.
theorem getEntry_stepArray_matches
    (rows : Array (Array Int)) (M : Matrix Int n n)
    (hentry : ∀ i j : Fin n, getEntry rows i.val j.val = M[i][j])
    (k : Nat) (pivot prevPivot : Int) (i j : Fin n) :
    getEntry (stepArray rows n k pivot prevPivot) i.val j.val =
      (stepMatrix M k pivot prevPivot)[i][j] := by
  unfold stepArray
  by_cases hi : k < i.val
  · by_cases hj : k < j.val
    · have hcol₁ :
          getEntry rows i.val k =
            M[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] := by
        simpa using hentry i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)
      have hrow₁ :
          getEntry rows k j.val =
            M[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j] := by
        simpa using hentry (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j
      have hij := hentry i j
      simp [getEntry, hi, hj]
      change exactDiv (pivot * getEntry rows i.val j.val - getEntry rows i.val k *
          getEntry rows k j.val) prevPivot = (stepMatrix M k pivot prevPivot)[i][j]
      rw [stepMatrix_update_eq M k pivot prevPivot i j hi hj, hij, hcol₁, hrow₁]
    · by_cases hjeq : j.val = k
      · have hjFin : j = (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n) := Fin.ext hjeq
        subst j
        have hkn : k < n := Nat.lt_trans hi i.isLt
        simp [getEntry, hi, hkn]
        exact (stepMatrix_pivot_col_below M k pivot prevPivot i
          (⟨k, hkn⟩ : Fin n) hi rfl).symm
      · have htrail : ¬ (k < i.val ∧ k < j.val) := fun h => hj h.2
        have hcol : ¬ (k < i.val ∧ j.val = k) := fun h => hjeq h.2
        have hij := hentry i j
        simp [getEntry, hi, hj, hjeq]
        change getEntry rows i.val j.val = (stepMatrix M k pivot prevPivot)[i][j]
        rw [stepMatrix_eq_of_not_update M k pivot prevPivot i j htrail hcol]
        exact hij
  · have htrail : ¬ (k < i.val ∧ k < j.val) := fun h => hi h.1
    have hcol : ¬ (k < i.val ∧ j.val = k) := fun h => hi h.1
    have hij := hentry i j
    simp [getEntry, hi]
    change getEntry rows i.val j.val = (stepMatrix M k pivot prevPivot)[i][j]
    rw [stepMatrix_eq_of_not_update M k pivot prevPivot i j htrail hcol]
    exact hij

/-- `stepArray` rebuilds the storage as an `n`-sized array of rows. -/
@[grind =]
theorem stepArray_size (rows : Array (Array Int)) (n k : Nat)
    (pivot prevPivot : Int) :
    (stepArray rows n k pivot prevPivot).size = n := by
  simp [stepArray]

/-- Matrix-level correspondence: applying `stepArray` to a row-storage representation
and reading it back as a matrix agrees with applying `stepMatrix` to the
matrix view of the same row storage. The one-step companion to
`getEntry_stepArray_matches` packaged at the `rowsToMatrix` level. -/
@[grind =]
theorem rowsToMatrix_stepArray {n : Nat} (rows : Array (Array Int)) (k : Nat)
    (pivot prevPivot : Int) :
    rowsToMatrix (stepArray rows n k pivot prevPivot) n =
      stepMatrix (rowsToMatrix rows n) k pivot prevPivot := by
  ext i hi j hj
  have hentry : ∀ a b : Fin n,
      getEntry rows a.val b.val = (rowsToMatrix rows n)[a][b] := by
    intro a b
    simp [rowsToMatrix, Matrix.ofFn]
  simpa [rowsToMatrix, Matrix.ofFn] using
    getEntry_stepArray_matches rows (rowsToMatrix rows n) hentry k pivot prevPivot
      ⟨i, hi⟩ ⟨j, hj⟩

/-- `pivotArrayLoop` runs the fuelled main elimination loop over the
array-backed state, pivoting at each step, recording a singular column when no
nonzero pivot exists, and otherwise applying `stepArray` before recursing. -/
private def pivotArrayLoop (n fuel : Nat) (state : BareissArrayState) :
    BareissArrayState :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if state.step + 1 < n then
        let k := state.step
        let (rows, swaps) :=
          if getEntry state.matrix k k = 0 then
            match findPivotArray? state.matrix n k (state.step + 1) with
            | some pivot => (swapRowsArray state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := getEntry rows k k
        if pivot = 0 then
          { state with matrix := rows, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissArrayState :=
            { step := state.step + 1
              matrix := stepArray rows n state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotArrayLoop n fuel next
      else
        state

/-- Bareiss elimination with row pivoting. If a column has no nonzero pivot,
the elimination aborts and the determinant is zero. -/
@[expose]
def pivotLoop (fuel : Nat) (state : BareissState n) : BareissState n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let (M, swaps) :=
          if state.matrix[k][k] = 0 then
            match findPivot? state.matrix k (state.step + 1) with
            | some pivot => (rowSwap state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := M[k][k]
        if hp : pivot = 0 then
          { state with matrix := M, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix M state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotLoop fuel next
      else
        state

/-- With zero fuel, the row-pivoted Bareiss loop returns its input state. -/
@[grind]
theorem pivotLoop_zero_fuel (state : BareissState n) :
    pivotLoop 0 state = state := by
  rfl

/-- If the current step is already past the last update step, the row-pivoted
Bareiss loop returns its input state. -/
@[grind]
theorem pivotLoop_done (fuel : Nat) (state : BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    pivotLoop (fuel + 1) state = state := by
  simp [pivotLoop, hDone]

/-- If the current row-pivoted Bareiss pivot is already nonzero, one loop
iteration applies `stepMatrix`, advances the step, and recurses without
changing the row-swap counter. -/
@[grind]
theorem pivotLoop_regular_branch_no_swap (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    pivotLoop (fuel + 1) state =
      pivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp [pivotLoop, hDone, hp]

/-- If the current pivot is zero and pivot search finds no replacement row,
the row-pivoted Bareiss loop records a singular step. -/
@[grind]
theorem pivotLoop_singular_branch_no_pivot (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    pivotLoop (fuel + 1) state =
      { state with singularStep := some state.step } := by
  simp [pivotLoop, hDone, hp0, hfind]

/-- If the current pivot is zero, pivot search finds a replacement row, and
the swapped pivot is nonzero, one loop iteration swaps rows, applies
`stepMatrix`, advances the step, increments the row-swap counter, and recurses. -/
@[grind]
theorem pivotLoop_regular_branch_swap (fuel : Nat) (state : BareissState n)
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
          singularStep := none } := by
  simp [pivotLoop, hDone, hp0, hfind, hp]

/-- `bareissArrayState` runs the matrix-level Bareiss elimination via `pivotLoop`
and repackages the reduced result as a `BareissArrayState`, storing the matrix
row-by-row via `matrixToRows`. -/
@[expose]
def bareissArrayState (M : Matrix Int n n) : BareissArrayState :=
  let state := pivotLoop n
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
def arraySign (rowSwaps : Nat) : Int :=
  if rowSwaps % 2 = 0 then 1 else -1

/-- `arrayLastDiag?` reads the last diagonal entry `(n-1, n-1)` of the reduced
rows, returning `none` when `n = 0`. -/
@[expose]
def arrayLastDiag? (rows : Array (Array Int)) (n : Nat) : Option Int :=
  match n with
  | 0 => none
  | k + 1 => some (getEntry rows k k)

/-- `bareissArrayDet` assembles the determinant value from the final array
state, returning `0` when elimination recorded a singular column and the signed
last diagonal entry otherwise. -/
@[expose]
def bareissArrayDet (state : BareissArrayState) (n : Nat) : Int :=
  match state.singularStep with
  | some _ => 0
  | none =>
      match arrayLastDiag? state.matrix n with
      | some d => arraySign state.rowSwaps * d
      | none => arraySign state.rowSwaps

/-- Package a Bareiss state as public elimination data. -/
@[expose]
def finish (state : BareissState n) : BareissData n :=
  { matrix := state.matrix
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- Bareiss elimination without pivoting. A zero pivot aborts and records the
singular step. -/
@[expose]
def noPivotLoop (fuel : Nat) (state : BareissState n) : BareissState n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let pivot := state.matrix[k][k]
        if hp : pivot = 0 then
          { state with singularStep := some state.step }
        else
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix state.matrix state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := state.rowSwaps
              singularStep := none }
          noPivotLoop fuel next
      else
        state

/-- With zero fuel, the no-pivot Bareiss loop returns its input state. -/
@[grind]
theorem noPivotLoop_zero_fuel (state : BareissState n) :
    noPivotLoop 0 state = state := by
  rfl

/-- If the current step is already past the last update step, the no-pivot loop
returns its input state. -/
@[grind]
theorem noPivotLoop_done (fuel : Nat) (state : BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoop (fuel + 1) state = state := by
  simp [noPivotLoop, hDone]

/-- If the no-pivot loop sees a zero pivot before completion, it records the
current step as singular. -/
@[grind]
theorem noPivotLoop_singular_branch (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] = 0) :
    noPivotLoop (fuel + 1) state = { state with singularStep := some state.step } := by
  simp [noPivotLoop, hDone, hp]

/-- If the current no-pivot Bareiss pivot is nonzero, one loop iteration applies
`stepMatrix`, advances the step, and recurses on the remaining fuel. -/
@[grind]
theorem noPivotLoop_regular_branch (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    noPivotLoop (fuel + 1) state =
      noPivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp [noPivotLoop, hDone, hp]

/-- Entries in rows already processed, or in columns strictly before the current
step, are unchanged by subsequent no-pivot loop iterations. -/
@[grind]
theorem noPivotLoop_matrix_entry_of_row_le_or_col_lt (fuel : Nat)
    (state : BareissState n) (i j : Fin n)
    (hfixed : i.val ≤ state.step ∨ j.val < state.step) :
    (noPivotLoop fuel state).matrix[i][j] = state.matrix[i][j] := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoop]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoop_singular_branch fuel state hDone hp]
        · rw [noPivotLoop_regular_branch fuel state hDone]
          · let next : BareissState n :=
              { step := state.step + 1
                matrix := stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoop fuel next).matrix[i][j] = state.matrix[i][j]
            have hnext : i.val ≤ next.step ∨ j.val < next.step := by
              cases hfixed with
              | inl hi =>
                  exact Or.inl (Nat.le_trans hi (Nat.le_succ state.step))
              | inr hj =>
                  exact Or.inr (Nat.lt_trans hj (Nat.lt_succ_self state.step))
            rw [ih next hnext]
            dsimp [next]
            apply stepMatrix_eq_of_not_update
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
      · simp [noPivotLoop_done fuel state hDone]

/-- Diagonal entries at or before the current step are unchanged by subsequent
no-pivot loop iterations. -/
@[grind =]
theorem noPivotLoop_diag_of_le_step (fuel : Nat) (state : BareissState n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoop fuel state).matrix[i][i] = state.matrix[i][i] :=
  noPivotLoop_matrix_entry_of_row_le_or_col_lt fuel state i i (Or.inl hi)

/-- The no-pivot loop never changes the row-swap counter. -/
@[grind =]
theorem noPivotLoop_rowSwaps (fuel : Nat) (state : BareissState n) :
    (noPivotLoop fuel state).rowSwaps = state.rowSwaps := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoop]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoop_singular_branch fuel state hDone hp]
        · rw [noPivotLoop_regular_branch fuel state hDone]
          · let next : BareissState n :=
              { step := state.step + 1
                matrix := stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoop fuel next).rowSwaps = state.rowSwaps
            rw [ih next]
          · simpa [k] using hp
      · simp [noPivotLoop_done fuel state hDone]

/-- Once a no-pivot Bareiss state is already at the terminal step boundary,
additional fuel leaves it unchanged. -/
-- @[grind]-excluded: structural fixed-point lemma overlapping `noPivotLoop_done`;
-- kept for manual fuel reasoning.
theorem noPivotLoop_id_at_done
    {n : Nat} (fuel : Nat) (state : BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoop fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih => exact noPivotLoop_done f state hDone

/-- Once a no-pivot Bareiss state has recorded a zero pivot at the current
step, additional fuel leaves that singular fixed point unchanged. -/
-- @[grind]-excluded: structural fixed-point lemma with bespoke singular-state
-- premises; used once inside `noPivotLoop_add`.
theorem noPivotLoop_id_at_singular_fixedpoint
    {n : Nat} (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0)
    (hsing : state.singularStep = some state.step) :
    noPivotLoop fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih =>
      rw [noPivotLoop_singular_branch f state hDone hp]
      cases state
      simp at hsing ⊢
      exact hsing.symm

/-- Fuel composition for the no-pivot Bareiss loop: running `a + b` units of
fuel from `state` equals running `b` more units after `a` initial units. -/
-- @[grind]-excluded: fuel-composition (associativity) lemma; as a rewrite it
-- splits one loop into two and risks non-termination of grind's saturation.
theorem noPivotLoop_add
    {n : Nat} (a b : Nat) (state : BareissState n) :
    noPivotLoop (a + b) state = noPivotLoop b (noPivotLoop a state) := by
  induction a generalizing state with
  | zero =>
      show noPivotLoop (0 + b) state = noPivotLoop b state
      simp
  | succ a' ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · have h_lhs :
              noPivotLoop (a' + 1 + b) state =
                {state with singularStep := some state.step} := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact noPivotLoop_singular_branch (a' + b) state hDone hp
          have h_rhs_inner :
              noPivotLoop (a' + 1) state =
                {state with singularStep := some state.step} :=
            noPivotLoop_singular_branch a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          symm
          let s' : BareissState n := {state with singularStep := some state.step}
          have hDone_s' : s'.step + 1 < n := hDone
          have hp_s' : s'.matrix[(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)][
              (⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)] = 0 := hp
          have hsing_s' : s'.singularStep = some s'.step := rfl
          exact noPivotLoop_id_at_singular_fixedpoint b s' hDone_s' hp_s' hsing_s'
        · have h_lhs :
              noPivotLoop (a' + 1 + b) state =
                noPivotLoop (a' + b)
                  { step := state.step + 1
                    matrix := stepMatrix state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact noPivotLoop_regular_branch (a' + b) state hDone hp
          have h_rhs_inner :
              noPivotLoop (a' + 1) state =
                noPivotLoop a'
                  { step := state.step + 1
                    matrix := stepMatrix state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } :=
            noPivotLoop_regular_branch a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          exact ih _
      · rw [noPivotLoop_id_at_done (a' + 1 + b) state hDone]
        rw [noPivotLoop_id_at_done (a' + 1) state hDone]
        exact (noPivotLoop_id_at_done b state hDone).symm

/-- When a no-pivot Bareiss run records no singular step and has enough room,
the `step` field advances by exactly the amount of consumed fuel. -/
-- @[grind]-excluded: step-count accounting lemma with arithmetic-room and
-- no-singular premises; proof-internal, not a characterising rewrite.
theorem noPivotLoop_step_eq_add_of_singularStep_none
    {n : Nat} (fuel : Nat) (state : BareissState n)
    (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (noPivotLoop fuel state).singularStep = none) :
    (noPivotLoop fuel state).step = state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step = state.step + 0
      omega
  | succ f ih =>
      have hDone : state.step + 1 < n := by omega
      by_cases hp : state.matrix[state.step][state.step] = 0
      · rw [noPivotLoop_singular_branch f state hDone hp] at h_no_sing
        simp at h_no_sing
      · rw [noPivotLoop_regular_branch f state hDone hp] at h_no_sing
        rw [noPivotLoop_regular_branch f state hDone hp]
        have h_next_room : state.step + 1 + f + 1 ≤ n := by omega
        have h_next_step := ih
          { step := state.step + 1
            matrix := stepMatrix state.matrix state.step
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
swap branches of `pivotLoop` are never entered and both loops apply the
same `stepMatrix` updates. -/
-- @[grind]-excluded: one-shot equivalence-of-two-algorithms bridge gated on a
-- no-singular premise.
theorem pivotLoop_eq_noPivotLoop_of_no_singular {n : Nat}
    (fuel : Nat) (state : BareissState n)
    (h_no_sing : (noPivotLoop fuel state).singularStep = none) :
    pivotLoop fuel state = noPivotLoop fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- `noPivotLoop` records `singularStep = some state.step`, contradicting
          -- `h_no_sing`.
          rw [noPivotLoop_singular_branch f state hDone hp] at h_no_sing
          simp at h_no_sing
        · -- Regular branch in both loops; recurse on the same updated state.
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          rw [noPivotLoop_regular_branch f state hDone hp,
            pivotLoop_regular_branch_no_swap f state hDone hp]
          show pivotLoop f next = noPivotLoop f next
          apply ih
          show (noPivotLoop f next).singularStep = none
          rw [← noPivotLoop_regular_branch f state hDone hp]
          exact h_no_sing
      · rw [pivotLoop_done f state hDone]
        rw [noPivotLoop_done f state hDone]

/-- Initial state used by the no-pivot Bareiss recurrence. -/
@[expose]
def noPivotInitialState (M : Matrix Int n n) : BareissState n :=
  { step := 0
    matrix := M
    prevPivot := 1
    rowSwaps := 0
    singularStep := none }

/-- Run the no-pivot Bareiss recurrence and return the final elimination data. -/
@[expose]
def bareissNoPivotData (M : Matrix Int n n) : BareissData n :=
  finish <| noPivotLoop n (noPivotInitialState M)

/-- Determinant computed by the no-pivot Bareiss recurrence. -/
@[expose]
def bareissNoPivot (M : Matrix Int n n) : Int :=
  (bareissNoPivotData M).det

/-- Run the row-pivoted Bareiss elimination and return the final elimination
data together with the swap/sign bookkeeping. -/
@[expose]
def bareissData (M : Matrix Int n n) : BareissData n :=
  let state := bareissArrayState M
  { matrix := rowsToMatrix state.matrix n
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- The packaged row-pivoted Bareiss data is exactly the structured pivot loop
state finished into public determinant data. This is the equality consumed by the
Mathlib determinant proof; array storage is erased by `rowsToMatrix`. -/
-- @[grind]-excluded: array-erasure bridge consumed by the Mathlib determinant
-- proof; not a local rewrite.
theorem bareissData_eq_finish_pivotLoop (M : Matrix Int n n) :
    bareissData M = finish (pivotLoop n (noPivotInitialState M)) := by
  simp [bareissData, bareissArrayState, noPivotInitialState, finish,
    rowsToMatrix_matrixToRows]

/-- Determinant computed by the row-pivoted Bareiss algorithm. -/
@[expose]
def bareiss (M : Matrix Int n n) : Int :=
  let state := bareissArrayState M
  bareissArrayDet state n

/-- The public row-pivoted determinant agrees with the determinant encoded by
`bareissData`. This separates executable array evaluation from the packaged
elimination data used by correctness proofs. -/
-- @[grind]-excluded: one-shot executable-vs-packaged determinant bridge.
theorem bareiss_eq_bareissData_det (M : Matrix Int n n) :
    bareiss M = (bareissData M).det := by
  cases n with
  | zero =>
      simp [bareiss, bareissData, bareissArrayDet, BareissData.det,
        arrayLastDiag?, BareissData.lastDiag?, arraySign, BareissData.sign]
      rfl
  | succ k =>
      simp [bareiss, bareissData, bareissArrayDet, BareissData.det,
        arrayLastDiag?, BareissData.lastDiag?, rowsToMatrix, Matrix.ofFn,
        arraySign, BareissData.sign]
      rfl

/-- If the no-pivot Bareiss pass reaches the final pivot without recording a
singular step, then the public row-pivoted `bareiss` determinant is exactly
the no-pivot final diagonal entry. -/
-- @[grind]-excluded: premise-heavy final-diagonal identity; one-shot.
theorem bareiss_eq_noPivotLoop_last_of_no_singular {k : Nat}
    (M : Matrix Int (k + 1) (k + 1))
    (h_no_sing :
      (noPivotLoop k (noPivotInitialState M)).singularStep = none) :
    bareiss M =
      (noPivotLoop k (noPivotInitialState M)).matrix[Fin.last k][Fin.last k] := by
  let init := noPivotInitialState M
  let stateK := noPivotLoop k init
  have h_step : stateK.step = k := by
    have h := noPivotLoop_step_eq_add_of_singularStep_none k init rfl
      (by simp [init, noPivotInitialState]) h_no_sing
    simpa [stateK, init, noPivotInitialState] using h
  have hDone_stateK : ¬ stateK.step + 1 < k + 1 := by omega
  have h_full_nopivot : noPivotLoop (k + 1) init = stateK := by
    rw [noPivotLoop_add k 1 init]
    exact noPivotLoop_id_at_done 1 stateK hDone_stateK
  have h_full_sing : (noPivotLoop (k + 1) init).singularStep = none := by
    rw [h_full_nopivot]
    exact h_no_sing
  have hpivot := pivotLoop_eq_noPivotLoop_of_no_singular (k + 1) init h_full_sing
  rw [bareiss_eq_bareissData_det, bareissData_eq_finish_pivotLoop, hpivot, h_full_nopivot]
  have hdet := BareissData.det_succ_eq (finish stateK) h_no_sing
  rw [hdet]
  simp [finish, BareissData.sign, stateK, init, noPivotInitialState, noPivotLoop_rowSwaps]

end Matrix
end Hex
