/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Leading submatrices and row prefixes.
-/

namespace Hex

universe u

namespace Matrix

/-- Leading principal `(k + 1) × (k + 1)` submatrix of a square matrix. -/
@[expose]
def leadingSubmatrix (M : Matrix R n n) (k : Fin n) : Matrix R (k.val + 1) (k.val + 1) :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
    M[ii][jj]

/-- Leading principal `k × k` prefix of a square matrix. This variant includes
the empty prefix and is convenient for Bareiss pivot/minor statements. -/
@[expose]
def leadingPrefix (M : Matrix R n n) (k : Nat) (hk : k ≤ n) : Matrix R k k :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[ii][jj]

/-- The first `k` rows of a matrix, retaining all source columns. -/
@[expose]
def leadingRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n) : Matrix R k m :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    M[ii][j]

/-- Entry formula for the `k × k` leading prefix. -/
@[grind =] theorem leadingPrefix_entry (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (leadingPrefix M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]) := by
  simp [leadingPrefix, ofFn]

/-- Entry formula for the first-`k`-rows slice. -/
@[grind =] theorem leadingRows_entry (M : Matrix R n m) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (j : Fin m) :
    (leadingRows M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       M[ii][j]) := by
  simp [leadingRows, ofFn]

/-- Entry formula for the `(k + 1)` leading submatrix. -/
@[grind =] theorem leadingSubmatrix_entry (M : Matrix R n n) (k : Fin n)
    (i j : Fin (k.val + 1)) :
    (leadingSubmatrix M k)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
       M[ii][jj]) := by
  simp [leadingSubmatrix, ofFn]

/-- The `leadingSubmatrix` API is the `(k + 1)` leading-prefix API at the
same boundary. -/
theorem leadingSubmatrix_eq_leadingPrefix (M : Matrix R n n) (k : Fin n) :
    leadingSubmatrix M k = leadingPrefix M (k.val + 1) (Nat.succ_le_of_lt k.isLt) := by
  ext i hi j hj
  simp [leadingSubmatrix, leadingPrefix, ofFn]

/-- The leading principal `(k + 1) × (k + 1)` submatrix of the identity is the
identity. -/
@[simp, grind =] theorem leadingSubmatrix_one {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (k : Fin n) :
    leadingSubmatrix (1 : Matrix R n n) k = (1 : Matrix R (k.val + 1) (k.val + 1)) := by
  ext i hi j hj
  show (leadingSubmatrix (1 : Matrix R n n) k)[(⟨i, hi⟩ : Fin (k.val + 1))][
      (⟨j, hj⟩ : Fin (k.val + 1))] =
    (1 : Matrix R (k.val + 1) (k.val + 1))[(⟨i, hi⟩ : Fin (k.val + 1))][
      (⟨j, hj⟩ : Fin (k.val + 1))]
  rw [leadingSubmatrix_entry]
  rw [getElem_one (i := (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n))]
  rw [getElem_one (i := (⟨i, hi⟩ : Fin (k.val + 1)))]
  by_cases hij : (⟨i, hi⟩ : Fin (k.val + 1)) = ⟨j, hj⟩
  · have hval : i = j := Fin.val_eq_of_eq hij
    have hijn :
        (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n) =
          ⟨j, Nat.lt_of_lt_of_le hj (Nat.succ_le_of_lt k.isLt)⟩ := by
      apply Fin.eq_of_val_eq; exact hval
    simp [hij, hijn]
  · have hval : i ≠ j := fun heq => hij (by apply Fin.eq_of_val_eq; exact heq)
    have hijn :
        (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n) ≠
          ⟨j, Nat.lt_of_lt_of_le hj (Nat.succ_le_of_lt k.isLt)⟩ := fun heq =>
      hval (Fin.val_eq_of_eq heq)
    simp [hij, hijn]

end Matrix

end Hex
