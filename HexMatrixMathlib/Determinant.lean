import HexMatrixMathlib.Basic
import HexMatrixMathlib.Determinant.DesnanotJacobi
import HexMatrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Determinant bridge theorems for `hex-matrix-mathlib`.

This module relates the executable Leibniz-formula determinant on `Hex.Matrix`
to Mathlib's determinant on function-based matrices. The supporting lemmas keep
the permutation-indexed product surface in a form that downstream proofs can
rewrite through `matrixEquiv` directly.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n : Nat}

@[simp]
theorem detProduct_eq_matrixEquiv
    [Lean.Grind.Ring R] (M : Hex.Matrix R n n) (perm : Vector (Fin n) n) :
    Hex.Matrix.detProduct M perm =
      (List.finRange n).foldl (fun acc i => acc * matrixEquiv M i (perm[i])) 1 := by
  rfl

@[simp]
theorem detTerm_eq_matrixEquiv
    [Lean.Grind.Ring R] (M : Hex.Matrix R n n) (perm : Vector (Fin n) n) :
    Hex.Matrix.detTerm M perm =
      Hex.Matrix.detSign perm *
        (List.finRange n).foldl (fun acc i => acc * matrixEquiv M i (perm[i])) 1 := by
  rfl

theorem det_eq [CommRing R] (M : Hex.Matrix R n n) :
    Hex.Matrix.det M = Matrix.det (matrixEquiv M) := by
  sorry

end HexMatrixMathlib
