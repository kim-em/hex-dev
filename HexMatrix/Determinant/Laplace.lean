/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Determinant.ColumnLinear
import all HexMatrix.Determinant.ColumnLinear

public section

/-!
Laplace (cofactor) expansion of the determinant.

This module proves that `det` expands as a signed sum of `M[·][·] * cofactor`
along any fixed row or column. `det_eq_foldl_laplace_last` and
`det_eq_foldl_laplace_last_row` handle the final column and final row, and
`det_eq_foldl_laplace_col` / `det_eq_foldl_laplace_row` generalize to an
arbitrary column or row. The general case is reduced to the last-column case by
the column-move permutation `moveColumnToLastValues`, whose sign
`(-1) ^ (n - col.val)` is computed via the inversion-count machinery and
cancelled against the cofactor sign through `cofactorSign_col_eq`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Inner sum-over-permutations collapse: for any row `i`, the Leibniz terms whose
permutation sends row `i` to the last column collapse to `M[i][last] * cofactor M i last`. -/
private theorem foldl_detTerm_insertions_eq
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (i : Fin (n + 1)) :
    (permutationVectors n).foldl
        (fun acc v => acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) 0 =
      M[i][Fin.last n] * cofactor M i (Fin.last n) := by
  have hsumands : (permutationVectors n).foldl
        (fun acc v => acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) 0 =
      (permutationVectors n).foldl
        (fun acc v => acc + cofactorSign (R := R) i (Fin.last n) *
          (M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v)) 0 := by
    apply foldl_det_sum_congr
    intro v _hmem
    exact detTerm_insertAt_general M v i
  rw [hsumands]
  rw [foldl_det_sum_mul_left_zero (permutationVectors n)
    (cofactorSign (R := R) i (Fin.last n))
    (fun v => M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v)]
  rw [foldl_det_sum_mul_left_zero (permutationVectors n) M[i][Fin.last n]
    (fun v => detTerm (deleteRowCol M i (Fin.last n)) v)]
  show cofactorSign (R := R) i (Fin.last n) *
       (M[i][Fin.last n] * det (deleteRowCol M i (Fin.last n))) = _
  unfold cofactor
  grind

/-- Laplace expansion of the determinant along the final column. -/
theorem det_eq_foldl_laplace_last
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][Fin.last n] * cofactor M row (Fin.last n)) 0 := by
  unfold det
  rw [show permutationVectors (n + 1) =
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n) from rfl]
  rw [foldl_det_sum_flatMap]
  have hmap :
      (permutationVectors n).foldl
        (fun acc v =>
          ((List.finRange (n + 1)).map
            (fun i => insertAt (Fin.last n) (v.map Fin.castSucc) i)).foldl
            (fun acc perm => acc + detTerm M perm) acc) 0 =
      (permutationVectors n).foldl
        (fun acc v =>
          (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) acc) 0 := by
    apply foldl_acc_congr
    intro acc v _hmem
    simp only [List.foldl_map]
  rw [hmap]
  rw [foldl_det_sum_nested_zero (permutationVectors n) (List.finRange (n + 1))
    (fun v i => detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i))]
  rw [foldl_det_sum_swap (permutationVectors n) (List.finRange (n + 1))
    (fun v i => detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i))]
  apply foldl_acc_congr
  intro acc i _hmem
  congr 1
  exact foldl_detTerm_insertions_eq M i

/-- Laplace expansion of the determinant along the final row. -/
theorem det_eq_foldl_laplace_last_row
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[Fin.last n][col] * cofactor M (Fin.last n) col) 0 := by
  calc
    det M = det M.transpose := (det_transpose M).symm
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M.transpose[col][Fin.last n] *
          cofactor M.transpose col (Fin.last n)) 0 := det_eq_foldl_laplace_last M.transpose
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[Fin.last n][col] * cofactor M (Fin.last n) col) 0 := by
        apply foldl_acc_congr
        intro acc col _hmem
        rw [cofactor_transpose]
        simp [Matrix.transpose, Matrix.col]

/-- Column permutation that preserves the relative order of every column except
`col`, which is moved to the final position. -/
private def moveColumnToLastValues {n : Nat} (col : Fin (n + 1)) :
    Vector (Fin (n + 1)) (n + 1) :=
  insertAt col (Vector.ofFn fun i : Fin n => skipIndex col i) (Fin.last n)

/-- `moveColumnToLastValues_last` states that the moved column `col` lands in the
final position of the permutation, the defining property that sends the cofactor
column to the last column. -/
private theorem moveColumnToLastValues_last {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col)[Fin.last n] = col := by
  exact insertAt_get_self col (Vector.ofFn fun i : Fin n => skipIndex col i) (Fin.last n)

/-- `moveColumnToLastValues_castSucc` states that every non-final position
`i.castSucc` of the permutation holds the original columns with `col` skipped over,
preserving the relative order of the surviving columns. -/
private theorem moveColumnToLastValues_castSucc {n : Nat} (col : Fin (n + 1)) (i : Fin n) :
    (moveColumnToLastValues col)[i.castSucc] = skipIndex col i := by
  rw [moveColumnToLastValues]
  simpa using
    insertAt_last_get_castSucc col (Vector.ofFn fun i : Fin n => skipIndex col i) i

/-- `moveColumnToLastValues_nodup` states that the permutation's values are
pairwise distinct, the no-repeat condition needed to certify it as a genuine
permutation of the columns. -/
private theorem moveColumnToLastValues_nodup {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col).toList.Nodup := by
  rw [moveColumnToLastValues, insertAt_last_toList]
  rw [vector_toList_eq]
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply list_nodup_map_of_injective
    · intro i j h
      exact skipIndex_injective col (by simpa using h)
    · exact List.nodup_finRange n
  · simp
  · intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    have hxcol : x = col := hxy.trans hy
    rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
    exact skipIndex_ne col i (by simpa using hxcol)

/-- `moveColumnToLastValues_mem_permutationVectors` states that the column move is
a member of `permutationVectors (n + 1)`, packaging the nodup proof so the move can
be fed to the determinant column-permutation machinery. -/
private theorem moveColumnToLastValues_mem_permutationVectors {n : Nat}
    (col : Fin (n + 1)) :
    moveColumnToLastValues col ∈ permutationVectors (n + 1) :=
  permutationVectors_complete (moveColumnToLastValues_nodup col)

/-- `skipIndex_eq_raiseFinAbove` states that the two index-shifting functions agree,
letting the column-move list be rewritten in the `raiseFinAbove` form used by the
inversion-count sign computation. -/
private theorem skipIndex_eq_raiseFinAbove {n : Nat} (col : Fin (n + 1)) (i : Fin n) :
    skipIndex col i = raiseFinAbove col i := by
  unfold skipIndex raiseFinAbove
  split <;> rfl

/-- `moveColumnToLastValues_toList` gives the explicit list form of the column move:
the `n` surviving columns in order (via `raiseFinAbove col`) followed by `col`, the
shape consumed by the inversion-count sign lemma. -/
private theorem moveColumnToLastValues_toList {n : Nat} (col : Fin (n + 1)) :
    (moveColumnToLastValues col).toList =
      ((List.finRange n).map (raiseFinAbove col)) ++ [col] := by
  rw [moveColumnToLastValues, insertAt_last_toList]
  rw [vector_toList_eq]
  apply congrArg (fun xs => xs ++ [col])
  apply List.map_congr_left
  intro i _hi
  simpa using skipIndex_eq_raiseFinAbove col i

/-- `detSign_moveColumnToLastValues` evaluates the sign of the column move to
`(-1) ^ (n - col.val)`, the parity contributed by sliding `col` past the `n - col.val`
columns to its right. -/
private theorem detSign_moveColumnToLastValues
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (col : Fin (n + 1)) :
    detSign (R := R) (moveColumnToLastValues col) =
      (-1 : R) ^ (n - col.val) := by
  have hidList :
      (Vector.ofFn fun i : Fin n => i).toList = List.finRange n := by
    rw [vector_toList_eq]
    simp
  calc
    detSign (R := R) (moveColumnToLastValues col) =
        (-1 : R) ^ (n - col.val) *
          detSign (R := R) (Vector.ofFn fun i : Fin n => i) := by
      apply detSign_of_inversionCount_add
      rw [moveColumnToLastValues_toList, hidList]
      rw [inversionCount_map_raiseFinAbove_append_self]
      rw [foldCount_finRange_ge]
    _ = (-1 : R) ^ (n - col.val) := by
      rw [detSign_identity]
      grind

/-- `neg_one_pow_mul_self` states that a sign `(-1) ^ k` squares to one, the
cancellation used to undo the column-move sign factor when transporting the Laplace
expansion back to the original column. -/
private theorem neg_one_pow_mul_self {R : Type u} [Lean.Grind.CommRing R] (k : Nat) :
    (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
  induction k with
  | zero =>
      grind
  | succ k ih =>
      grind

/-- `cofactorSign_col_eq` relates the cofactor sign at column `col` to
the sign at the last column through the `(-1) ^ (n - col.val)` column-move factor, the
parity bookkeeping that turns last-column Laplace expansion into expansion along `col`. -/
private theorem cofactorSign_col_eq
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (row col : Fin (n + 1)) :
    cofactorSign (R := R) row col =
      (-1 : R) ^ (n - col.val) * cofactorSign (R := R) row (Fin.last n) := by
  unfold cofactorSign
  simp only [Fin.val_last]
  have hle : col.val ≤ n := Nat.le_of_lt_succ col.isLt
  have h := detSignParity_add (R := R) (row.val + col.val) (n - col.val)
  have hsum : row.val + col.val + (n - col.val) = row.val + n := by omega
  rw [hsum] at h
  let s : R := (-1 : R) ^ (n - col.val)
  let a : R := if (row.val + col.val) % 2 = 0 then 1 else -1
  let b : R := if (row.val + n) % 2 = 0 then 1 else -1
  have hs : s * s = 1 := neg_one_pow_mul_self (R := R) (n - col.val)
  have hb : b = s * a := by simpa [a, b, s] using h
  calc
    (if (row.val + col.val) % 2 = 0 then (1 : R) else -1) = a := rfl
    _ = s * (s * a) := by
      have hss : s * (s * a) = a := by
        calc
          s * (s * a) = (s * s) * a := by grind
          _ = 1 * a := by rw [hs]
          _ = a := by grind
      exact hss.symm
    _ = s * b := by rw [hb]
    _ = s * (if (row.val + n) % 2 = 0 then (1 : R) else -1) := rfl

/-- Laplace expansion of the determinant along an arbitrary fixed column. -/
theorem det_eq_foldl_laplace_col
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (col : Fin (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][col] * cofactor M row col) 0 := by
  let sigma := moveColumnToLastValues col
  let C : Matrix R (n + 1) (n + 1) := ofFn fun r c => M[r][sigma[c]]
  have hsigma : sigma ∈ permutationVectors (n + 1) :=
    moveColumnToLastValues_mem_permutationVectors col
  have hdetC : det C = (-1 : R) ^ (n - col.val) * det M := by
    calc
      det C = detSign (R := R) sigma * det M := by
        exact det_colPermute_vector M sigma hsigma
      _ = (-1 : R) ^ (n - col.val) * det M := by
        rw [detSign_moveColumnToLastValues col]
  have hsign_sq : (-1 : R) ^ (n - col.val) * ((-1 : R) ^ (n - col.val)) = 1 := by
    exact neg_one_pow_mul_self (R := R) (n - col.val)
  calc
    det M = (-1 : R) ^ (n - col.val) * det C := by
      rw [hdetC]
      grind
    _ =
      (-1 : R) ^ (n - col.val) *
        (List.finRange (n + 1)).foldl
          (fun acc row => acc + C[row][Fin.last n] * cofactor C row (Fin.last n)) 0 := by
        rw [det_eq_foldl_laplace_last C]
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc row =>
          acc + (-1 : R) ^ (n - col.val) *
            (C[row][Fin.last n] * cofactor C row (Fin.last n))) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc row => acc + M[row][col] * cofactor M row col) 0 := by
        apply foldl_acc_congr
        intro acc row _hmem
        congr 1
        unfold cofactor
        have hClast : C[row][Fin.last n] = M[row][col] := by
          rw [show C[row][Fin.last n] = M[row][sigma[Fin.last n]] by
            simp [C, ofFn]]
          exact congrArg (fun c => M[row][c]) (moveColumnToLastValues_last col)
        have hminor : deleteRowCol C row (Fin.last n) = deleteRowCol M row col := by
          ext i hi j hj
          let ii : Fin n := ⟨i, hi⟩
          let jj : Fin n := ⟨j, hj⟩
          change (deleteRowCol C row (Fin.last n))[ii][jj] =
            (deleteRowCol M row col)[ii][jj]
          rw [deleteRowCol_entry, deleteRowCol_entry]
          rw [show C[skipIndex row ii][skipIndex (Fin.last n) jj] =
              C[skipIndex row ii][jj.castSucc] by
            exact congrArg (fun c => C[skipIndex row ii][c]) (skipIndex_last jj)]
          rw [show C[skipIndex row ii][jj.castSucc] =
              M[skipIndex row ii][sigma[jj.castSucc]] by
            simp [C, ofFn]]
          exact congrArg (fun c => M[skipIndex row ii][c])
            (moveColumnToLastValues_castSucc col jj)
        rw [hClast, hminor]
        rw [cofactorSign_col_eq (R := R) row col]
        grind

/-- Laplace expansion of the determinant along an arbitrary fixed row. -/
theorem det_eq_foldl_laplace_row
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[row][col] * cofactor M row col) 0 := by
  calc
    det M = det M.transpose := (det_transpose M).symm
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M.transpose[col][row] *
          cofactor M.transpose col row) 0 := det_eq_foldl_laplace_col M.transpose row
    _ =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[row][col] * cofactor M row col) 0 := by
        apply foldl_acc_congr
        intro acc col _hmem
        rw [cofactor_transpose]
        rw [transpose_getElem]

end Matrix
end Hex
