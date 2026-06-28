module

public import HexMatrix.Basic
public import HexMatrix.Vector.Insert
public import HexMatrix.Vector.Modify
public import HexMatrix.DotProduct
public import HexMatrix.MatrixAlgebra
public import HexMatrix.Elementary
public import HexMatrix.Submatrix
public import HexMatrix.BorderedMinor
public import HexMatrix.Gram
public import HexMatrix.Determinant
public import HexMatrix.RowEchelon
public import HexMatrix.RREF
public import HexMatrix.Bareiss

public section

/-!
The `HexMatrix` library exposes the dense matrix core used throughout the
project's linear-algebra stack, including dense matrix operations,
row-echelon transforms, determinant APIs, and the executable Bareiss
determinant algorithm over `Int`.
-/
