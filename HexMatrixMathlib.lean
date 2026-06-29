/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Basic
public import HexMatrixMathlib.Vector
public import HexMatrixMathlib.Algebra
public import HexMatrixMathlib.Lemmas
public import HexMatrixMathlib.Gram
public import HexMatrixMathlib.Submatrix

public section

/-!
The `HexMatrixMathlib` library is the base Mathlib bridge for the matrix family.
It exposes the concrete equivalence `matrixEquiv` between the executable
`HexMatrix` dense representation and Mathlib's function-based `Matrix`, together
with the row-operation correspondence lemmas relating our executable `rowSwap`,
`rowScale`, and `rowAdd` helpers to Mathlib's elementary matrix operations.

On top of this, `HexMatrixMathlib` equips `Hex.Matrix` with the Mathlib
algebraic tower whose operations are the executable ones — `AddCommMonoid`,
`AddCommGroup`, `Module`, `Semiring`, `Ring`, and `Algebra` — and upgrades
`matrixEquiv` to additive (`matrixAddEquiv`), linear (`matrixLinearEquiv`), ring
(`matrixRingEquiv`), and algebra (`matrixAlgEquiv`) equivalences. The companion
modules carry the vector equivalence and matrix-vector product (`Vector`), the
container API such as transpose and row/column updates (`Lemmas`), the Gram
matrix (`Gram`), and the leading-submatrix family (`Submatrix`) across the
equivalence.

The determinant correspondence lives in `HexDeterminantMathlib`, the row-pivoted
Bareiss correctness theorems in `HexBareissMathlib`, and the rank/span/nullspace
correspondence in `HexRowReduceMathlib`.
-/
