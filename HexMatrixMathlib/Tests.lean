/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexMatrixMathlib

/-! Build-only examples for the literal layer: the identification of each
literal syntax with its row list, by `rfl` for the vector chains and by the
kernel's `entriesEq` for the other shapes, and the empty shapes. -/

open HexMatrixMathlib

example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ) = ofLists 2 2 [[1, 2], [3, 4]] := rfl
example : Matrix.of ![![(1 : ℤ), 2], ![3, 4]] = ofLists 2 2 [[1, 2], [3, 4]] := rfl
example : (!![] : Matrix (Fin 0) (Fin 0) ℤ) = ofLists 0 0 [] := rfl
example : (!![,,,] : Matrix (Fin 0) (Fin 3) ℤ) = ofLists 0 3 [] := rfl
example : (!![;;;] : Matrix (Fin 3) (Fin 0) ℤ) = ofLists 3 0 [[], [], []] := rfl
example : (!![1 / 2, 3; -1, 5 / 3] : Matrix (Fin 2) (Fin 2) ℚ) = ofLists 2 2 [[1 / 2, 3], [-1, 5 / 3]] :=
  rfl

/-- A `fun i j => …` literal. -/
def fromFn : Matrix (Fin 2) (Fin 2) ℤ := fun i j => (i : ℤ) + 2 * j

example : fromFn = ofLists 2 2 [[0, 2], [1, 3]] :=
  eq_ofLists_of_entriesEq 2 2 fromFn _ (by decide +kernel)

/-- A row-major array literal. -/
def ofArr : Matrix (Fin 2) (Fin 2) ℤ := Matrix.ofArray #[1, 2, 3, 4] rfl

example : ofArr = ofLists 2 2 [[1, 2], [3, 4]] :=
  eq_ofLists_of_entriesEq 2 2 ofArr _ (by decide +kernel)

example (i : Fin 2) (j : Fin 3) : ofLists 2 3 [[1, 2, 3], [4, 5, 6]] i j = ([[1, 2, 3], [4, 5, 6]].getD i []).getD j (0 : ℤ) :=
  ofLists_apply 2 3 _ i j
