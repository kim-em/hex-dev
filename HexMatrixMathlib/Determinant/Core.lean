module

public import HexMatrixMathlib.Determinant.CoreTransport
public import HexMatrixMathlib.Determinant.CorePlucker

public section

/-!
Mathlib-side determinant bridge for `hex-matrix-mathlib`, split by subject:
the permutation-sign bridge and ordered `nMatrix`/four-row transport helpers
(`CoreTransport`), and the four-row / double-row Plücker and Desnanot-Jacobi
assembly (`CorePlucker`). This module re-exports both.
-/
