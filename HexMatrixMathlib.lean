/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Basic

public section

/-!
The `HexMatrixMathlib` library is the base Mathlib bridge for the matrix family.
It exposes the concrete equivalence `matrixEquiv` between the executable
`HexMatrix` dense representation and Mathlib's function-based `Matrix`, together
with the row-operation correspondence lemmas relating our executable `rowSwap`,
`rowScale`, and `rowAdd` helpers to Mathlib's elementary matrix operations.

The determinant correspondence lives in `HexDeterminantMathlib`, the row-pivoted
Bareiss correctness theorems in `HexBareissMathlib`, and the rank/span/nullspace
correspondence in `HexRowReduceMathlib`.
-/
