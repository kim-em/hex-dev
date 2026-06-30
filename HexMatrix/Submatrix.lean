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
    M[ii][jj]

/-- The first `k` rows of a matrix, retaining all source columns. -/
@[expose]
def takeRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n) : Matrix R k m :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    M[ii][j]

/-- Entry formula for the `k × k` principal submatrix. -/
@[grind =] theorem getElem_principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (principalSubmatrix M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]) := by
  simp [principalSubmatrix, ofFn]

/-- Entry formula for the first-`k`-rows slice. -/
@[grind =] theorem getElem_takeRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (j : Fin m) :
    (takeRows M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       M[ii][j]) := by
  simp [takeRows, ofFn]

/-- The leading principal `k × k` submatrix of the identity is the identity. -/
@[simp, grind =] theorem principalSubmatrix_identity {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (k : Nat) (hk : k ≤ n) :
    principalSubmatrix (Matrix.identity (R := R) n) k hk = (Matrix.identity (R := R) k) := by
  ext i hi j hj
  show (principalSubmatrix (Matrix.identity (R := R) n) k hk)[(⟨i, hi⟩ : Fin k)][(⟨j, hj⟩ : Fin k)] =
    (Matrix.identity (R := R) k)[(⟨i, hi⟩ : Fin k)][(⟨j, hj⟩ : Fin k)]
  rw [getElem_principalSubmatrix, getElem_identity (i := (⟨i, Nat.lt_of_lt_of_le hi hk⟩ : Fin n)),
    getElem_identity (i := (⟨i, hi⟩ : Fin k))]
  by_cases hij : (⟨i, hi⟩ : Fin k) = ⟨j, hj⟩
  · have hval : i = j := Fin.val_eq_of_eq hij
    have hijn :
        (⟨i, Nat.lt_of_lt_of_le hi hk⟩ : Fin n) = ⟨j, Nat.lt_of_lt_of_le hj hk⟩ := by
      apply Fin.eq_of_val_eq; exact hval
    simp [hij, hijn]
  · have hval : i ≠ j := fun heq => hij (by apply Fin.eq_of_val_eq; exact heq)
    have hijn :
        (⟨i, Nat.lt_of_lt_of_le hi hk⟩ : Fin n) ≠ ⟨j, Nat.lt_of_lt_of_le hj hk⟩ := fun heq =>
      hval (Fin.val_eq_of_eq heq)
    simp [hij, hijn]

end Matrix

end Hex
