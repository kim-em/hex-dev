/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import HexMatrix

public section

/-!
Identification lemmas between `Hex.Matrix` and Mathlib's `Matrix`.

This module exposes a concrete equivalence between the dense executable
`Vector`-based matrix representation used by `HexMatrix` and Mathlib's
function-based `Matrix`, together with the first row-operation correspondence
lemmas needed by downstream determinant and rank lemmas.
-/

open Matrix

namespace HexMatrixMathlib

universe u

/-- The bijection between a `Hex.Matrix` and the Mathlib `Matrix` with the
same entries. -/
@[expose]
def matrixEquiv : Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R where
  toFun M := fun i j => M[(i, j)]
  invFun M := Hex.Matrix.ofFn fun i j => M i j
  left_inv M := by
    ext i j
    simp [Hex.Matrix.ofFn, Hex.Matrix.getRow, Fin.getElem_fin]
  right_inv M := by
    ext i j
    simp [Hex.Matrix.ofFn, Hex.Matrix.getRow, Fin.getElem_fin]

/-- `matrixEquiv M` has entry `M[i][j]` at `(i, j)`, so a caller can rewrite
`matrixEquiv M i j` to `M[i][j]` without unfolding the equivalence. -/
@[simp, grind =]
theorem matrixEquiv_apply (M : Hex.Matrix R n m) (i : Fin n) (j : Fin m) :
    matrixEquiv M i j = M[i][j] :=
  rfl

/-- The inverse direction of `matrixEquiv` materialises a Mathlib matrix as an
executable one entrywise: `(matrixEquiv.symm M)[i][j]` is just `M i j`. -/
@[simp, grind =]
theorem matrixEquiv_symm_apply (M : Matrix (Fin n) (Fin m) R) (i : Fin n) (j : Fin m) :
    (matrixEquiv.symm M)[(i : Nat)][(j : Nat)] = M i j :=
  by simp [matrixEquiv, Hex.Matrix.ofFn]

/-- `matrixEquiv` is a left inverse of `Hex.Matrix.ofFn`: building an executable
matrix from `f` and transporting it to Mathlib recovers `f` itself. -/
@[simp, grind =]
theorem matrixEquiv_ofFn (f : Fin n → Fin m → R) :
    matrixEquiv (Hex.Matrix.ofFn f) = f := by
  ext i j
  simp [Hex.Matrix.ofFn]

section RowOps

variable [Semiring R]

/-- The executable elementary row swap corresponds to left multiplication by
Mathlib's permutation matrix `Matrix.swap`, so downstream determinant and rank
lemmas can reason about `rowSwap` through Mathlib's swap algebra. -/
theorem matrixEquiv_rowSwap (M : Hex.Matrix R n m) (i j : Fin n) :
    matrixEquiv (Hex.Matrix.rowSwap M i j) = Matrix.swap R i j * matrixEquiv M := by
  ext r k
  change (Hex.Matrix.rowSwap M i j)[r][k] = (Matrix.swap R i j * matrixEquiv M) r k
  rw [Hex.Matrix.getElem_rowSwap]
  by_cases hrj : r = j
  · subst r
    simp
  · by_cases hri : r = i
    · subst r
      simp [hrj]
    · simp [hrj, hri, Matrix.swap_mul_of_ne]

/-- The executable elementary row scaling corresponds to left multiplication by
the diagonal matrix that carries `c` in row `i` and `1` elsewhere, exposing
`rowScale` to Mathlib's diagonal-matrix algebra. -/
theorem matrixEquiv_rowScale (M : Hex.Matrix R n m) (i : Fin n) (c : R) :
    matrixEquiv (Hex.Matrix.rowScale M i c) =
      Matrix.diagonal (Function.update (fun _ : Fin n => (1 : R)) i c) * matrixEquiv M := by
  ext r k
  change (Hex.Matrix.rowScale M i c)[r][k] =
    (Matrix.diagonal (Function.update (fun _ : Fin n => (1 : R)) i c) * matrixEquiv M) r k
  rw [Hex.Matrix.getElem_rowScale]
  by_cases hri : r = i
  · subst r
    simp
  · simp [hri]

end RowOps

section RowAdd

variable [CommRing R]

/-- The executable elementary row addition (add `c` times row `src` to row
`dst`) corresponds to left multiplication by Mathlib's transvection matrix,
completing the row-operation dictionary used by the determinant correspondence. -/
theorem matrixEquiv_rowAdd (M : Hex.Matrix R n m) (src dst : Fin n) (c : R) :
    matrixEquiv (Hex.Matrix.rowAdd M src dst c) =
      Matrix.transvection dst src c * matrixEquiv M := by
  ext r k
  change (Hex.Matrix.rowAdd M src dst c)[r][k] =
    (Matrix.transvection dst src c * matrixEquiv M) r k
  by_cases hrd : r = dst
  · subst r
    have hrhs :
        (Matrix.transvection dst src c * matrixEquiv M) dst k =
          M[(dst, k)] + c * M[(src, k)] := by
      have hone :
          ((1 : Matrix (Fin n) (Fin n) R) * matrixEquiv M) dst k =
            M[(dst, k)] := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_mul, one_mul]
        rfl
      have hsingle :
          (Matrix.single dst src c * matrixEquiv M) dst k =
            c * M[(src, k)] := by
        simp
      rw [Matrix.transvection, Matrix.add_mul]
      change ((1 : Matrix (Fin n) (Fin n) R) * matrixEquiv M) dst k +
          (Matrix.single dst src c * matrixEquiv M) dst k =
        M[(dst, k)] + c * M[(src, k)]
      rw [hone, hsingle]
    rw [hrhs, Hex.Matrix.getElem_rowAdd]
    simp
  · have hval : dst.val ≠ r.val := by
      intro h
      exact hrd (Fin.ext h).symm
    have hrhs :
        (Matrix.transvection dst src c * matrixEquiv M) r k = M[(r, k)] := by
      have hone :
          ((1 : Matrix (Fin n) (Fin n) R) * matrixEquiv M) r k =
            M[(r, k)] := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_mul, one_mul]
        rfl
      have hsingle :
          (Matrix.single dst src c * matrixEquiv M) r k = 0 := by
        simpa using Matrix.single_mul_apply_of_ne c dst src r k hrd (matrixEquiv M)
      rw [Matrix.transvection, Matrix.add_mul]
      change ((1 : Matrix (Fin n) (Fin n) R) * matrixEquiv M) r k +
          (Matrix.single dst src c * matrixEquiv M) r k =
        M[(r, k)]
      rw [hone, hsingle, add_zero]
    rw [hrhs, Hex.Matrix.getElem_rowAdd]
    simp [hrd]

end RowAdd

end HexMatrixMathlib
