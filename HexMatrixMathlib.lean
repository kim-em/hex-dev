/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Basic
public import HexMatrixMathlib.Determinant
public import HexMatrixMathlib.Determinant.Bareiss
public import HexMatrixMathlib.RankSpanNullspace

public section

/-!
The `HexMatrixMathlib` library connects the executable `HexMatrix` core to
Mathlib's matrix API and linear-algebra definitions.

This library exposes the concrete equivalence between the two matrix
representations and the row-operation lemmas relating our executable
`rowSwap`, `rowScale`, and `rowAdd` helpers to Mathlib's standard elementary
matrix operations, the determinant comparison theorem, and the
rank/span/nullspace correspondence theorems for row reduction.
-/
