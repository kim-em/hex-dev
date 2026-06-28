module

public import HexMatrix.Determinant.Leibniz

public section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Embed `Fin n` into `Fin (n + 1)` while skipping one deleted index. -/
@[expose]
def skipIndex {n : Nat} (skip : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if h : i.val < skip.val then
    ⟨i.val, by omega⟩
  else
    ⟨i.val + 1, by omega⟩

/-- The skipped-index embedding leaves entries below the deleted index unchanged.
This is the low-side `simp` branch for row and column deletion. -/
@[simp, grind =] theorem skipIndex_val_of_lt {n : Nat} (skip : Fin (n + 1)) (i : Fin n)
    (h : i.val < skip.val) :
    (skipIndex skip i).val = i.val := by
  simp [skipIndex, h]

/-- The skipped-index embedding shifts entries at or above the deleted index by
one. This is the high-side `simp` branch for row and column deletion. -/
@[simp, grind =] theorem skipIndex_val_of_not_lt {n : Nat} (skip : Fin (n + 1)) (i : Fin n)
    (h : ¬ i.val < skip.val) :
    (skipIndex skip i).val = i.val + 1 := by
  simp [skipIndex, h]

/-- The index produced by `skipIndex skip` is never the deleted index `skip`.
This is the basic side condition for minors that remove a row or column. -/
theorem skipIndex_ne {n : Nat} (skip : Fin (n + 1)) (i : Fin n) :
    skipIndex skip i ≠ skip := by
  intro hsame
  have hval : (skipIndex skip i).val = skip.val := congrArg Fin.val hsame
  by_cases hlt : i.val < skip.val
  · rw [skipIndex_val_of_lt skip i hlt] at hval
    omega
  · rw [skipIndex_val_of_not_lt skip i hlt] at hval
    omega

/-- The deleted-index embedding `skipIndex skip` is injective. -/
private theorem skipIndex_injective {n : Nat} (skip : Fin (n + 1)) :
    Function.Injective (skipIndex skip) := by
  intro i j h
  apply Fin.ext
  have hval : (skipIndex skip i).val = (skipIndex skip j).val := congrArg Fin.val h
  by_cases hi : i.val < skip.val
  · rw [skipIndex_val_of_lt skip i hi] at hval
    by_cases hj : j.val < skip.val
    · rw [skipIndex_val_of_lt skip j hj] at hval
      exact hval
    · rw [skipIndex_val_of_not_lt skip j hj] at hval
      omega
  · rw [skipIndex_val_of_not_lt skip i hi] at hval
    by_cases hj : j.val < skip.val
    · rw [skipIndex_val_of_lt skip j hj] at hval
      omega
    · rw [skipIndex_val_of_not_lt skip j hj] at hval
      omega

/-- Skipping the final index embeds `Fin n` by `castSucc`.
This normalizes bottom-right minors to leading prefixes. -/
@[simp, grind =] theorem skipIndex_last {n : Nat} (i : Fin n) :
    skipIndex (Fin.last n) i = i.castSucc := by
  apply Fin.ext
  simp [skipIndex, Fin.last, i.isLt]

/-- Delete one row and one column from an `(n + 1) × (n + 1)` matrix. -/
@[expose]
def deleteRowCol {R : Type u} {n : Nat} (M : Matrix R (n + 1) (n + 1))
    (row col : Fin (n + 1)) : Matrix R n n :=
  ofFn fun i j => M[skipIndex row i][skipIndex col j]

/-- Entries of a deleted-row/deleted-column minor are the corresponding source
entries at the skipped row and column indices. -/
@[grind =] theorem deleteRowCol_entry {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) (i j : Fin n) :
    (deleteRowCol M row col)[i][j] = M[skipIndex row i][skipIndex col j] := by
  simp [deleteRowCol, ofFn]

/-- Deleting the final row and final column gives the leading prefix.
This is the minor normalization used by bottom-right cofactor expansion. -/
@[simp, grind =] theorem deleteRowCol_last_last {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    deleteRowCol M (Fin.last n) (Fin.last n) =
      leadingPrefix M n (Nat.le_succ n) := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol M (Fin.last n) (Fin.last n))[ii][jj] =
    (leadingPrefix M n (Nat.le_succ n))[ii][jj]
  rw [deleteRowCol_entry]
  simp [leadingPrefix, ofFn]

/-- Deleting row `row` and column `col` after transposing is the transpose of
the minor obtained by deleting row `col` and column `row` before transposing. -/
theorem deleteRowCol_transpose {R : Type u} {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) :
    deleteRowCol M.transpose row col = (deleteRowCol M col row).transpose := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (deleteRowCol M.transpose row col)[ii][jj] =
    (deleteRowCol M col row).transpose[ii][jj]
  simp [deleteRowCol, ofFn, Matrix.transpose, Matrix.col]

/-- The alternating sign used in signed cofactors. -/
@[expose]
def cofactorSign {R : Type u} [OfNat R 1] [Neg R] {n : Nat}
    (row col : Fin (n + 1)) : R :=
  if (row.val + col.val) % 2 = 0 then 1 else -1

/-- An even row-plus-column parity gives cofactor sign `1`.
This is the positive `simp` branch for signed cofactors. -/
@[simp, grind =] theorem cofactorSign_of_even {R : Type u} [OfNat R 1] [Neg R] {n : Nat}
    (row col : Fin (n + 1)) (h : (row.val + col.val) % 2 = 0) :
    cofactorSign (R := R) row col = 1 := by
  simp [cofactorSign, h]

/-- An odd row-plus-column parity gives cofactor sign `-1`.
This is the negative `simp` branch for signed cofactors. -/
@[simp, grind =] theorem cofactorSign_of_odd {R : Type u} [OfNat R 1] [Neg R] {n : Nat}
    (row col : Fin (n + 1)) (h : (row.val + col.val) % 2 ≠ 0) :
    cofactorSign (R := R) row col = -1 := by
  simp [cofactorSign, h]

/-- The signed cofactor for the local Leibniz determinant. -/
@[expose]
def cofactor {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1)) : R :=
  cofactorSign row col * det (deleteRowCol M row col)

/-- At even parity, a signed cofactor is just the determinant of its minor.
This removes the sign in cofactor-expansion normalization. -/
@[simp, grind =] theorem cofactor_of_even {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1))
    (h : (row.val + col.val) % 2 = 0) :
    cofactor M row col = det (deleteRowCol M row col) := by
  simp [cofactor, h]
  grind

/-- At odd parity, a signed cofactor is the negated determinant of its minor.
This supplies the alternating sign in cofactor-expansion normalization. -/
@[simp, grind =] theorem cofactor_of_odd {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row col : Fin (n + 1))
    (h : (row.val + col.val) % 2 ≠ 0) :
    cofactor M row col = -det (deleteRowCol M row col) := by
  simp [cofactor, h]
  grind

/-- The bottom-right cofactor reduces to the determinant of the leading prefix.
This combines the final-index minor with its even sign. -/
@[simp, grind =] theorem cofactor_last_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    cofactor M (Fin.last n) (Fin.last n) =
      det (leadingPrefix M n (Nat.le_succ n)) := by
  rw [cofactor_of_even]
  · simp
  · omega

end Matrix
end Hex
