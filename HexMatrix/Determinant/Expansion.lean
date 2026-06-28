/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Determinant.ColumnLinear
public import HexMatrix.Determinant.Laplace
public import HexMatrix.Determinant.CauchyBinet
import all HexMatrix.Determinant.ColumnLinear
import all HexMatrix.Determinant.Laplace
import all HexMatrix.Determinant.CauchyBinet

public section

/-!
Compatibility barrel for determinant expansion theorems.

The implementation is split into column linearity, Laplace expansion, and
Cauchy-Binet support modules.
-/
