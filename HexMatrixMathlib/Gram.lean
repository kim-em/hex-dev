/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Algebra
public import HexMatrix.Gram

public section

/-!
The executable Gram matrix corresponds to `M * Mᵀ` under `matrixEquiv`.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n m : Nat}

/-- The Gram matrix of the rows of `M` is `matrixEquiv M * (matrixEquiv M)ᵀ`. -/
@[simp, grind =] theorem matrixEquiv_gramMatrix [Semiring R] (M : Hex.Matrix R n m) :
    matrixEquiv (Hex.Matrix.gramMatrix M) = matrixEquiv M * (matrixEquiv M)ᵀ := by
  ext i j
  rw [matrixEquiv_apply, Hex.Matrix.getElem_gramMatrix, Matrix.mul_apply, dotProduct_eq]
  unfold dotProduct
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_apply]
  grind

end HexMatrixMathlib
