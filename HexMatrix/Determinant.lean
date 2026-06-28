module

public import HexMatrix.Determinant.Leibniz
public import HexMatrix.Determinant.Enumeration
public import HexMatrix.Determinant.Minor
public import HexMatrix.Determinant.Index
public import HexMatrix.Determinant.Permutation
public import HexMatrix.Determinant.ColumnLinear
public import HexMatrix.Determinant.Laplace
public import HexMatrix.Determinant.CauchyBinet
public import HexMatrix.Determinant.Expansion
public import HexMatrix.Determinant.Selection
public import HexMatrix.Determinant.Adjugate
public import HexMatrix.Determinant.Plucker

public section

/-!
Determinant routines for `hex-matrix`: the generic Leibniz-formula determinant
for dense square matrices, the determinant behaviour of elementary row/column
operations, cofactor/adjugate theory, column-tuple (Cauchy-Binet) expansion,
and the two-row Plücker / Desnanot-Jacobi identities. The development is split
by subject across `HexMatrix/Determinant/*`; this module re-exports them.
-/
