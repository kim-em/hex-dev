/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant.ColumnLinear
public import HexDeterminant.Laplace
public import HexDeterminant.CauchyBinet
import all HexDeterminant.ColumnLinear
import all HexDeterminant.Laplace
import all HexDeterminant.CauchyBinet

public section

/-!
Compatibility barrel for determinant expansion theorems.

The implementation is split into column linearity, Laplace expansion, and
Cauchy-Binet support modules.
-/
