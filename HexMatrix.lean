/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic
public import HexMatrix.Vector.Insert
public import HexMatrix.DotProduct
public import HexMatrix.MatrixAlgebra
public import HexMatrix.Elementary
public import HexMatrix.Submatrix
public import HexMatrix.Gram

public section

/-!
The `HexMatrix` library exposes the dense matrix core: the `Vector`-based
matrix representation, basic vector helpers, the dot product, dense matrix
algebra, elementary row/column operations, and submatrix/Gram helpers. The
row-echelon transforms, determinant APIs, and the executable Bareiss algorithm
live in the `HexRowReduce`, `HexDeterminant`, and `HexBareiss` libraries.
-/
