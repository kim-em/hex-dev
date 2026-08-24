/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith
public import HexRowReduce.RowEchelon.Elementary

public section

/-!
Elementary two-row Hermite updates and accumulator operations.

The working matrix and every requested certificate follow the same schedule.
The form-only accumulator is `Unit`, so that path allocates no transform.
-/

namespace Hex.Matrix.Hermite

/-- Replace rows `i` and `k` by two simultaneous linear combinations. -/
@[expose]
def combineRows (M : Matrix Int n m) (i k : Fin n)
    (a b c d : Int) : Matrix Int n m :=
  Matrix.ofFn fun r j =>
    if r = i then a * M[(i, j)] + b * M[(k, j)]
    else if r = k then c * M[(i, j)] + d * M[(k, j)]
    else M[(r, j)]

/-- Replace columns `i` and `k` by two simultaneous linear combinations. -/
@[expose]
def combineCols (M : Matrix Int n n) (i k : Fin n)
    (a b c d : Int) : Matrix Int n n :=
  Matrix.ofFn fun r j =>
    if j = i then a * M[(r, i)] + b * M[(r, k)]
    else if j = k then c * M[(r, i)] + d * M[(r, k)]
    else M[(r, j)]

/-- Simultaneous two-row replacement commutes with multiplication on the
right. -/
theorem combineRows_mul (A : Matrix Int n p) (B : Matrix Int p m)
    (i k : Fin n) (a b c d : Int) :
    combineRows A i k a b c d * B = combineRows (A * B) i k a b c d := by
  apply Matrix.ext_getElem
  intro r j
  rw [Matrix.getElem_mul]
  by_cases hri : r = i
  · subst r
    rw [show Matrix.row (combineRows A i k a b c d) i =
        a • Matrix.row A i + b • Matrix.row A k by
      ext q hq
      let qq : Fin p := ⟨q, hq⟩
      change (combineRows A i k a b c d)[i][qq] =
        (a • Matrix.row A i + b • Matrix.row A k)[qq]
      unfold combineRows
      rw [Matrix.getElem_ofFn]
      simp only [if_pos]
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested]
      simp only [Fin.getElem_fin, Vector.getElem_add, Vector.getElem_smul,
        Matrix.getElem_row]
      rfl
      ]
    rw [Vector.dotProduct_add_left, Vector.dotProduct_smul_left,
      Vector.dotProduct_smul_left]
    unfold combineRows
    rw [Matrix.getElem_ofFn]
    simp only [if_pos, Matrix.getElem_pair_eq_nested]
    rw [Matrix.getElem_mul, Matrix.getElem_mul]
  · by_cases hrk : r = k
    · subst r
      rw [show Matrix.row (combineRows A i k a b c d) k =
          c • Matrix.row A i + d • Matrix.row A k by
        ext q hq
        let qq : Fin p := ⟨q, hq⟩
        change (combineRows A i k a b c d)[k][qq] =
          (c • Matrix.row A i + d • Matrix.row A k)[qq]
        unfold combineRows
        rw [Matrix.getElem_ofFn]
        simp only [if_neg hri, if_pos]
        rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested]
        simp only [Fin.getElem_fin, Vector.getElem_add, Vector.getElem_smul,
          Matrix.getElem_row]
        rfl]
      rw [Vector.dotProduct_add_left, Vector.dotProduct_smul_left,
        Vector.dotProduct_smul_left]
      unfold combineRows
      rw [Matrix.getElem_ofFn]
      simp only [if_neg hri, if_pos, Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_mul, Matrix.getElem_mul]
    · rw [show Matrix.row (combineRows A i k a b c d) r = Matrix.row A r by
        ext q hq
        let qq : Fin p := ⟨q, hq⟩
        change (combineRows A i k a b c d)[r][qq] = A[r][qq]
        unfold combineRows
        rw [Matrix.getElem_ofFn]
        simp [hri, hrk, Matrix.getElem_pair_eq_nested]]
      unfold combineRows
      rw [Matrix.getElem_ofFn]
      simp only [if_neg hri, if_neg hrk, Matrix.getElem_pair_eq_nested]
      exact (Matrix.getElem_mul A B r j).symm

/-- Operations performed on a companion accumulator by the Hermite sweep. -/
structure Accumulator (α : Type) (n : Nat) where
  init : α
  swap : α → Fin n → Fin n → α
  combine : α → Fin n → Fin n → Int → Int → Int → Int → α
  negate : α → Fin n → α
  add : α → Fin n → Fin n → Int → α

/-- The form-only accumulator. -/
@[expose]
def formAccumulator (n : Nat) : Accumulator Unit n where
  init := ()
  swap acc _ _ := acc
  combine acc _ _ _ _ _ _ := acc
  negate acc _ := acc
  add acc _ _ _ := acc

/-- Accumulator for the left transform `U`. -/
@[expose]
def transformAccumulator (n : Nat) : Accumulator (Matrix Int n n) n where
  init := Matrix.identity n
  swap U i k := Matrix.rowSwap U i k
  combine U i k a b c d := combineRows U i k a b c d
  negate U i := Matrix.rowScale U i (-1)
  add U src dst c := Matrix.rowAdd U src dst c

/-- Transform and explicitly accumulated inverse transform. -/
structure TransformPair (n : Nat) where
  transform : Matrix Int n n
  inverse : Matrix Int n n

/-- Accumulator for `(U, W)` with `W = U⁻¹`. -/
@[expose]
def inverseAccumulator (n : Nat) : Accumulator (TransformPair n) n where
  init := ⟨Matrix.identity n, Matrix.identity n⟩
  swap acc i k :=
    ⟨Matrix.rowSwap acc.transform i k, Matrix.colSwap acc.inverse i k⟩
  combine acc i k a b c d :=
    -- The caller supplies `[[a,b],[c,d]]` with determinant one. Its inverse is
    -- `[[d,-b],[-c,a]]`, and right multiplication updates columns.
    ⟨combineRows acc.transform i k a b c d,
      combineCols acc.inverse i k d (-c) (-b) a⟩
  negate acc i :=
    ⟨Matrix.rowScale acc.transform i (-1), Matrix.colScale acc.inverse i (-1)⟩
  add acc src dst c :=
    ⟨Matrix.rowAdd acc.transform src dst c,
      Matrix.colAdd acc.inverse dst src (-c)⟩

/-- Extended-GCD elimination of the entry in row `k`, using pivot row `i`.
The four returned coefficients form a determinant-one two-row update. -/
@[expose]
def gcdCoeffs (a b : Int) : Int × Int × Int × Int :=
  let (g, s, t) := HexArith.Int.extGcd a b
  let g' : Int := Int.ofNat g
  let qa := HexArith.Int.exactDiv a g'
  let qb := HexArith.Int.exactDiv b g'
  (s, t, -qb, qa)

end Hex.Matrix.Hermite
