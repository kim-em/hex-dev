/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantMathlib

public section

/-!
# Closing a `Matrix.det` goal by running the executable determinant

`Matrix.det` is noncomputable, so `decide` cannot see it. `HexDeterminantMathlib.det_eq`
identifies it with the executable Leibniz determinant `Hex.Matrix.det`, which the
kernel evaluates directly. Rewriting a Mathlib determinant goal backwards through
`det_eq` therefore turns it into a closed computation that `decide +kernel`
finishes.

The rewrite needs the goal's matrix to be in the image of
`HexMatrixMathlib.matrixEquiv`. For a matrix literal that is
`matrixEquiv.apply_symm_apply`: replace `A` by `matrixEquiv (matrixEquiv.symm A)`,
then `det_eq` applies.

`decide +kernel`, not `decide`, and never `native_decide`: the proofs below run
in Lean's kernel and depend on nothing beyond `propext`, `Classical.choice`, and
`Quot.sound`. This is the determinant counterpart of the rank recipe in
`HexManual/Chapters/HexRowReduce.lean`.
-/

namespace Examples.DeterminantKernelProof

open Hex Hex.Matrix HexMatrixMathlib

/-- A Mathlib matrix literal whose determinant is `3`. -/
def A : _root_.Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, 0, 1; 1, 3, 2; 0, 1, 1]

/-- The Mathlib determinant of `A`, proved by running the executable Leibniz
determinant in the kernel. -/
theorem det_eq_three : A.det = 3 := by
  rw [← matrixEquiv.apply_symm_apply A, ← det_eq]
  decide +kernel

/-- The same recipe settles a singular matrix: dependent rows give determinant
zero. -/
def S : _root_.Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 2; 2, 4]

theorem det_S_eq_zero : S.det = 0 := by
  rw [← matrixEquiv.apply_symm_apply S, ← det_eq]
  decide +kernel

/-- Once the value is known, Mathlib's determinant theory takes over: `A`
is not invertible over `ℤ`, because `3` is not a unit there. -/
theorem not_isUnit_det : ¬ IsUnit A.det := by
  rw [det_eq_three]
  decide

/-- Mathlib theory also transfers in the other direction: the transpose has the
same determinant, so its value follows without a second kernel run. -/
theorem det_transpose_eq_three : A.transpose.det = 3 := by
  rw [_root_.Matrix.det_transpose, det_eq_three]

end Examples.DeterminantKernelProof
