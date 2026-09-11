/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Vector
public import HexMatrix.Submatrix

public section

/-!
The executable principal-submatrix and row-prefix operations correspond to
Mathlib's `Matrix.submatrix` reindexed along `Fin.castLE`.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n m : Nat}

/-- The `k × k` principal submatrix is the `Fin.castLE`-reindexed submatrix. -/
@[simp, grind =] theorem matrixEquiv_principalSubmatrix (M : Hex.Matrix R n n) (k : Nat)
    (hk : k ≤ n) :
    matrixEquiv (Hex.Matrix.principalSubmatrix M k hk) =
      (matrixEquiv M).submatrix (Fin.castLE hk) (Fin.castLE hk) := by
  ext i j
  simp only [matrixEquiv_apply, Hex.Matrix.getElem_principalSubmatrix, Matrix.submatrix_apply,
    Fin.castLE]

/-- The first-`k`-rows slice is the submatrix reindexing rows by `Fin.castLE`. -/
@[simp, grind =] theorem matrixEquiv_takeRows (M : Hex.Matrix R n m) (k : Nat)
    (hk : k ≤ n) :
    matrixEquiv (Hex.Matrix.takeRows M k hk) =
      (matrixEquiv M).submatrix (Fin.castLE hk) id := by
  ext i j
  simp only [matrixEquiv_apply, Hex.Matrix.getElem_takeRows, Matrix.submatrix_apply,
    Fin.castLE, id_eq]

/-- Selecting rows is the submatrix reindexing rows by the index vector. -/
@[simp, grind =] theorem matrixEquiv_selectRows {k : Nat} (M : Hex.Matrix R n m)
    (rows : Vector (Fin n) k) :
    matrixEquiv (Hex.Matrix.selectRows M rows) = (matrixEquiv M).submatrix rows.get id := by
  ext i j
  simp only [matrixEquiv_apply, Hex.Matrix.getElem_selectRows, Matrix.submatrix_apply, id_eq]
  rfl

/-- Selecting columns is the submatrix reindexing columns by the index vector. -/
@[simp, grind =] theorem matrixEquiv_selectCols {k : Nat} (M : Hex.Matrix R n m)
    (cols : Vector (Fin m) k) :
    matrixEquiv (Hex.Matrix.selectCols M cols) = (matrixEquiv M).submatrix id cols.get := by
  ext i j
  simp only [matrixEquiv_apply, Hex.Matrix.getElem_selectCols, Matrix.submatrix_apply, id_eq]
  rfl

end HexMatrixMathlib
