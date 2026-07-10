/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Principal submatrices and row prefixes.
-/

namespace Hex

universe u

namespace Matrix

/-- Leading principal `k × k` submatrix of a square matrix: the top-left block
indexed by `{0, …, k-1}` along both axes. Includes the empty submatrix
(`k = 0`) and is convenient for Bareiss pivot/minor statements. -/
@[expose]
def principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n) : Matrix R k k :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[(ii, jj)]

/-- The first `k` rows of a matrix, retaining all source columns. -/
@[expose]
def takeRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n) : Matrix R k m :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    M[(ii, j)]

/-- Entry formula for the `k × k` principal submatrix. -/
@[grind =] theorem getElem_principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (principalSubmatrix M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]) := by
  unfold principalSubmatrix
  rw [getElem_ofFn, getElem_pair_eq_nested]

/-- Row `i` of the `k × k` principal submatrix is row `i` of `M`, restricted to
the first `k` columns. -/
@[simp, grind =] theorem row_principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i : Fin k) :
    row (principalSubmatrix M k hk) i =
      Vector.ofFn fun j : Fin k =>
        (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
         let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
         M[ii][jj]) := by
  ext j hj
  show (row (principalSubmatrix M k hk) i)[(⟨j, hj⟩ : Fin k)] =
    (Vector.ofFn fun j : Fin k =>
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]))[(⟨j, hj⟩ : Fin k)]
  rw [getElem_row, getElem_principalSubmatrix]
  simp

/-- Column `j` of the `k × k` principal submatrix is column `j` of `M`,
restricted to the first `k` rows. -/
@[simp, grind =] theorem col_principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (j : Fin k) :
    col (principalSubmatrix M k hk) j =
      Vector.ofFn fun i : Fin k =>
        (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
         let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
         M[ii][jj]) := by
  ext i hi
  show (col (principalSubmatrix M k hk) j)[(⟨i, hi⟩ : Fin k)] =
    (Vector.ofFn fun i : Fin k =>
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]))[(⟨i, hi⟩ : Fin k)]
  rw [getElem_col, getElem_principalSubmatrix]
  simp

/-- The first `k` columns of a matrix, retaining all source rows. -/
@[expose]
def takeCols (M : Matrix R n m) (k : Nat) (hk : k ≤ m) : Matrix R n k :=
  ofFn fun i j =>
    let jj : Fin m := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[(i, jj)]

/-- Entry formula for the first-`k`-rows slice. -/
@[grind =] theorem getElem_takeRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (j : Fin m) :
    (takeRows M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       M[ii][j]) := by
  unfold takeRows
  rw [getElem_ofFn, getElem_pair_eq_nested]

/-- Entry formula for the first-`k`-columns slice. -/
@[grind =] theorem getElem_takeCols (M : Matrix R n m) (k : Nat) (hk : k ≤ m)
    (i : Fin n) (j : Fin k) :
    (takeCols M k hk)[i][j] =
      (let jj : Fin m := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[i][jj]) := by
  unfold takeCols
  rw [getElem_ofFn, getElem_pair_eq_nested]

/-- The leading principal `k × k` submatrix of the identity is the identity. -/
@[simp, grind =] theorem principalSubmatrix_identity {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (k : Nat) (hk : k ≤ n) :
    principalSubmatrix (Matrix.identity (R := R) n) k hk = (Matrix.identity (R := R) k) := by
  apply ext_getElem
  intro i j
  rw [getElem_principalSubmatrix,
    getElem_identity (i := (⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ : Fin n)),
    getElem_identity (i := i)]
  by_cases hij : i = j
  · simp [hij]
  · have hijn :
        (⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ : Fin n) ≠ ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ := by
      intro heq
      exact hij (Fin.ext (by simpa using congrArg Fin.val heq))
    simp [hij, hijn]

end Matrix

end Hex
