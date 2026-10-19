/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantTheory.Core

public section

/-!
The `HexDeterminantTheory` library is the theory companion of `hex-determinant`.
It connects the executable Leibniz determinant `Hex.Matrix.det` to Mathlib's
`Matrix.det` (`det_eq`), together with the permutation-sign transport, the
Desnanot-Jacobi bordered-minor identity used by the Bareiss correctness proof,
and the four-row / double-row Grassmann-Plücker assembly. This module
re-exports the determinant correspondence core.
-/
