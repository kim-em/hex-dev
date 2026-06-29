/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Vector

public section

/-!
Correspondence lemmas carrying the executable container API of `Hex.Matrix`
(transpose, row/column updates) across `matrixEquiv` to the matching Mathlib
`Matrix` operations.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n m : Nat}

/-- Transpose commutes with `matrixEquiv`: the executable transpose becomes
Mathlib's `ᵀ`. -/
@[simp, grind =] theorem matrixEquiv_transpose (M : Hex.Matrix R n m) :
    matrixEquiv (Hex.Matrix.transpose M) = (matrixEquiv M)ᵀ := by
  ext i j
  rw [matrixEquiv_apply, Hex.Matrix.transpose_getElem, Matrix.transpose_apply,
    matrixEquiv_apply]

/-- Replacing a row carries `matrixEquiv` to Mathlib's `updateRow`. -/
@[simp, grind =] theorem matrixEquiv_setRow (M : Hex.Matrix R n m) (dst : Fin n)
    (v : Vector R m) :
    matrixEquiv (Hex.Matrix.setRow M dst v) =
      (matrixEquiv M).updateRow dst (vectorEquiv v) := by
  ext i j
  rw [matrixEquiv_apply, Matrix.updateRow_apply]
  by_cases h : i = dst
  · subst h
    rw [if_pos rfl, vectorEquiv_apply]
    exact congrArg (·[j.val]) (Hex.Matrix.setRow_get_self M i v)
  · rw [if_neg h]
    rw [matrixEquiv_apply]
    exact congrArg (·[j.val]) (Hex.Matrix.setRow_row_ne M dst i v h)

/-- Replacing a column carries `matrixEquiv` to Mathlib's `updateCol`. -/
@[simp, grind =] theorem matrixEquiv_setCol (M : Hex.Matrix R n m) (dst : Fin m)
    (v : Fin n → R) :
    matrixEquiv (Hex.Matrix.setCol M dst v) = (matrixEquiv M).updateCol dst v := by
  ext i j
  rw [matrixEquiv_apply, Hex.Matrix.setCol_getElem, Matrix.updateCol_apply,
    matrixEquiv_apply]

end HexMatrixMathlib
