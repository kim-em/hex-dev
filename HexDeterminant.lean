/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant.Leibniz
public import HexDeterminant.Enumeration
public import HexDeterminant.Minor
public import HexDeterminant.Index
public import HexDeterminant.Permutation
public import HexDeterminant.ColumnLinear
public import HexDeterminant.Laplace
public import HexDeterminant.CauchyBinet
public import HexDeterminant.Expansion
public import HexDeterminant.Selection
public import HexDeterminant.Adjugate
public import HexDeterminant.Plucker

public section

/-!
Determinant routines for `hex-determinant`: the generic Leibniz-formula
determinant for dense square matrices, the determinant behaviour of elementary
row/column operations, cofactor/adjugate theory, column-tuple (Cauchy-Binet)
expansion, and the two-row Plücker / Desnanot-Jacobi identities. The development
is split by subject across `HexDeterminant/*`; this module re-exports them.
-/
