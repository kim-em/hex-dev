/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixTheory.Basic
public import HexMatrixTheory.Vector
public import HexMatrixTheory.Algebra
public import HexMatrixTheory.Lemmas
public import HexMatrixTheory.Gram
public import HexMatrixTheory.Submatrix
public import HexMatrixTheory.Literal
public import HexMatrixTheory.Hadamard
public import HexMatrixTheory.Packed
public import HexMatrixTheory.ListProducts
public import HexMatrixTheory.Rational

public section

/-!
The `HexMatrixTheory` library is the base theory companion for the matrix family.
It exposes the concrete equivalence `matrixEquiv` between the executable
`HexMatrix` dense representation and Mathlib's function-based `Matrix`, together
with the row-operation correspondence lemmas relating our executable `rowSwap`,
`rowScale`, and `rowAdd` helpers to Mathlib's elementary matrix operations.

On top of this, `HexMatrixTheory` equips `Hex.Matrix` with the Mathlib
algebraic tower whose operations are the executable ones — `AddCommMonoid`,
`AddCommGroup`, `Module`, `Semiring`, `Ring`, and `Algebra` — and upgrades
`matrixEquiv` to additive (`matrixAddEquiv`), linear (`matrixLinearEquiv`), ring
(`matrixRingEquiv`), and algebra (`matrixAlgEquiv`) equivalences. The companion
modules carry the vector equivalence and matrix-vector product (`Vector`), the
container API such as transpose and row/column updates (`Lemmas`), the Gram
matrix (`Gram`), and the leading-submatrix family (`Submatrix`) across the
equivalence.

The determinant correspondence lives in `HexDeterminantTheory`, the row-pivoted
Bareiss correctness theorems in `HexBareissTheory`, and the rank/span/nullspace
correspondence in `HexRowReduceTheory`.
-/
