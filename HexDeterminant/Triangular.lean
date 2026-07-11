/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant.RowOps
import all HexDeterminant.RowOps

public section

/-!
Determinant of triangular matrices.

The determinant of an upper- or lower-triangular square matrix is the product of
its diagonal entries. The upper-triangular case recurses on the last row via the
factorisation in `HexDeterminant.LastRow`; the lower-triangular case is derived
from it through `det_transpose`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- An integer upper-triangular matrix with strictly positive diagonal has
strictly positive determinant. -/
theorem det_upperTriangular_pos_diag
    {n : Nat} (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i]) :
    0 < det M := by
  induction n with
  | zero =>
      simp [det, permutationVectors, detTerm, detSign, detProduct, inversionCount]
  | succ n ih =>
      have hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0 := by
        intro j hj
        exact hzero (Fin.last n) j hj
      rw [det_eq_principalSubmatrix_mul_last M hrow]
      have hprefixZero :
          ∀ i j : Fin n, j.val < i.val →
            (principalSubmatrix M n (Nat.le_succ n))[i][j] = 0 := by
        intro i j hij
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        let jj : Fin (n + 1) := ⟨j.val, by omega⟩
        have hentry : (principalSubmatrix M n (Nat.le_succ n))[i][j] = M[ii][jj] :=
          getElem_principalSubmatrix M n (Nat.le_succ n) i j
        rw [hentry]
        exact hzero ii jj hij
      have hprefixDiag :
          ∀ i : Fin n, 0 < (principalSubmatrix M n (Nat.le_succ n))[i][i] := by
        intro i
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        have hentry : (principalSubmatrix M n (Nat.le_succ n))[i][i] = M[ii][ii] :=
          getElem_principalSubmatrix M n (Nat.le_succ n) i i
        rw [hentry]
        exact hdiag ii
      exact Int.mul_pos (ih (principalSubmatrix M n (Nat.le_succ n)) hprefixZero hprefixDiag)
        (hdiag (Fin.last n))

/-- The determinant of an upper-triangular square matrix (entries below the
diagonal are zero) over a commutative ring is the product of its diagonal
entries, expressed via a `Fin.foldl` over the diagonal indices. -/
theorem det_upperTriangular_eq_finFoldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0) :
    det M = Fin.foldl n (fun acc i => acc * M[i][i]) 1 := by
  induction n with
  | zero =>
      simp only [Fin.foldl_zero]
      simp [det, permutationVectors, detTerm, detSign, detProduct,
        inversionCount]
      grind
  | succ n ih =>
      have hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0 := by
        intro j hj
        exact hzero (Fin.last n) j hj
      rw [det_eq_principalSubmatrix_mul_last M hrow]
      have hprefixZero :
          ∀ i j : Fin n, j.val < i.val →
            (principalSubmatrix M n (Nat.le_succ n))[i][j] = 0 := by
        intro i j hij
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        let jj : Fin (n + 1) := ⟨j.val, by omega⟩
        have hentry : (principalSubmatrix M n (Nat.le_succ n))[i][j] = M[ii][jj] :=
          getElem_principalSubmatrix M n (Nat.le_succ n) i j
        rw [hentry]
        exact hzero ii jj hij
      rw [ih (principalSubmatrix M n (Nat.le_succ n)) hprefixZero]
      -- The (n+1)-length Fin.foldl over diagonals splits as the n-length foldl
      -- times the last diagonal entry.
      rw [Fin.foldl_succ_last]
      -- Rewrite the leading prefix diagonal entries as M[i.castSucc][i.castSucc].
      have hcongr :
          Fin.foldl n
              (fun acc i => acc * (principalSubmatrix M n (Nat.le_succ n))[i][i]) 1 =
            Fin.foldl n (fun acc i => acc * M[i.castSucc][i.castSucc]) 1 := by
        rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
        apply List.foldl_congr
        intro acc i _hmem
        have hentry : (principalSubmatrix M n (Nat.le_succ n))[i][i] = M[i.castSucc][i.castSucc] :=
          getElem_principalSubmatrix M n (Nat.le_succ n) i i
        rw [hentry]
      rw [hcongr]

/-- The determinant of an upper-triangular square matrix as a `List.foldl`
product over the diagonal indices in `Fin.finRange`. -/
theorem det_upperTriangular_eq_foldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0) :
    det M = (List.finRange n).foldl (fun acc i => acc * M[i][i]) 1 := by
  rw [det_upperTriangular_eq_finFoldl_diag M hzero, Fin.foldl_eq_finRange_foldl]

/-- Diagonal-product formula for the determinant of a lower-triangular matrix
(entries above the diagonal are zero). Derived from the upper-triangular form
via `det_transpose`. -/
theorem det_lowerTriangular_eq_finFoldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, i.val < j.val → M[i][j] = 0) :
    det M = Fin.foldl n (fun acc i => acc * M[i][i]) 1 := by
  rw [← det_transpose M]
  have htransposeZero :
      ∀ i j : Fin n, j.val < i.val → M.transpose[i][j] = 0 := by
    intro i j hij
    have hentry : M.transpose[i][j] = M[j][i] := getElem_transpose M i j
    rw [hentry]
    exact hzero j i hij
  rw [det_upperTriangular_eq_finFoldl_diag M.transpose htransposeZero]
  have hdiag : ∀ i : Fin n, M.transpose[i][i] = M[i][i] := by
    intro i
    exact getElem_transpose M i i
  -- Rewrite the foldl over `M.transpose[i][i]` to `M[i][i]`.
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  apply List.foldl_congr
  intro acc i _hmem
  rw [hdiag]

/-- The determinant of a lower-triangular square matrix as a `List.foldl`
product over the diagonal indices in `Fin.finRange`. -/
theorem det_lowerTriangular_eq_foldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, i.val < j.val → M[i][j] = 0) :
    det M = (List.finRange n).foldl (fun acc i => acc * M[i][i]) 1 := by
  rw [det_lowerTriangular_eq_finFoldl_diag M hzero, Fin.foldl_eq_finRange_foldl]
end Matrix
end Hex
