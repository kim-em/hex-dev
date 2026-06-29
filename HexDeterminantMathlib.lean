/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantMathlib.Core

public section

/-!
The `HexDeterminantMathlib` library is the Mathlib bridge for `hex-determinant`.
It connects the executable Leibniz determinant `Hex.Matrix.det` to Mathlib's
`Matrix.det` (`det_eq`), together with the permutation-sign transport and the
four-row / double-row Plücker and Desnanot-Jacobi assembly used by the Bareiss
correctness proof. This module re-exports the determinant correspondence core.
-/
