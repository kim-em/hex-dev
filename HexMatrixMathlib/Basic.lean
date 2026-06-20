import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection
import HexMatrix.RowEchelon

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

/-- Interpret a `Hex.Matrix` as a Mathlib `Matrix`. -/
def matrixEquiv : Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R where
  toFun M := fun i j => M[i][j]
  invFun M := Hex.Matrix.ofFn fun i j => M i j
  left_inv M := by
    ext i j
    simp [Hex.Matrix.ofFn]
  right_inv M := by
    ext i j
    simp [Hex.Matrix.ofFn]

/-- The Mathlib matrix produced by `matrixEquiv` reads off the executable
matrix entrywise, so a caller can rewrite `matrixEquiv M i j` to the underlying
`M[i][j]` without unfolding the equivalence. -/
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
  rw [Hex.Matrix.rowSwap_getElem]
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
  by_cases hri : r = i
  · subst r
    simp [Hex.Matrix.rowScale]
  · have hval : i.val ≠ r.val := by
      intro h
      exact hri (Fin.ext h).symm
    have hentry :
        ((Vector.set M i.val (Vector.ofFn fun k => c * M[i][k]) i.isLt)[r.val])[k.val] =
          M[r][k] := by
      exact congrArg (fun row => row[k])
        (Vector.getElem_set_ne (xs := M) (x := Vector.ofFn fun k => c * M[i][k])
          (hi := i.isLt) (hj := r.isLt) hval)
    simpa [Hex.Matrix.rowScale, hri] using hentry

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
    have hentry :
        ((Vector.set M dst.val (Vector.ofFn fun k => M[dst][k] + c * M[src][k])
            dst.isLt)[dst.val])[k.val] =
          M[dst][k] + c * M[src][k] := by
      simp
    have hrhs :
        (Matrix.transvection dst src c * matrixEquiv M) dst k =
          M[dst][k] + c * M[src][k] := by
      have hone :
          ((1 : Matrix (Fin n) (Fin n) R) * matrixEquiv M) dst k =
            M[dst][k] := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_mul]
        rw [one_mul]
        rfl
      have hsingle :
          (Matrix.single dst src c * matrixEquiv M) dst k =
            c * M[src][k] := by
        simp
      rw [Matrix.transvection, Matrix.add_mul]
      change ((1 : Matrix (Fin n) (Fin n) R) * matrixEquiv M) dst k +
          (Matrix.single dst src c * matrixEquiv M) dst k =
        M[dst][k] + c * M[src][k]
      rw [hone, hsingle]
    rw [hrhs]
    exact hentry
  · have hval : dst.val ≠ r.val := by
      intro h
      exact hrd (Fin.ext h).symm
    have hentry :
        ((Vector.set M dst.val (Vector.ofFn fun k => M[dst][k] + c * M[src][k])
            dst.isLt)[r.val])[k.val] =
          M[r][k] := by
      exact congrArg (fun row => row[k])
        (Vector.getElem_set_ne (xs := M)
          (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
          (hi := dst.isLt) (hj := r.isLt) hval)
    have hrhs :
        (Matrix.transvection dst src c * matrixEquiv M) r k = M[r][k] := by
      have hone :
          ((1 : Matrix (Fin n) (Fin n) R) * matrixEquiv M) r k =
            M[r][k] := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_mul]
        rw [one_mul]
        rfl
      have hsingle :
          (Matrix.single dst src c * matrixEquiv M) r k = 0 := by
        simpa using Matrix.single_mul_apply_of_ne c dst src r k hrd (matrixEquiv M)
      rw [Matrix.transvection, Matrix.add_mul]
      change ((1 : Matrix (Fin n) (Fin n) R) * matrixEquiv M) r k +
          (Matrix.single dst src c * matrixEquiv M) r k =
        M[r][k]
      rw [hone, hsingle, add_zero]
    rw [hrhs]
    exact hentry

end RowAdd

end HexMatrixMathlib
