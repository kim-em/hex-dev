import HexMatrixMathlib.Basic
import HexMatrixMathlib.Determinant
import HexMatrixMathlib.Determinant.Bareiss
import HexMatrixMathlib.RankSpanNullspace

/-!
The `HexMatrixMathlib` library connects the executable `HexMatrix` core to
Mathlib's matrix API and linear-algebra definitions.

This library exposes the concrete equivalence between the two matrix
representations and the row-operation lemmas relating our executable
`rowSwap`, `rowScale`, and `rowAdd` helpers to Mathlib's standard elementary
matrix operations, the determinant comparison theorem, and the
rank/span/nullspace correspondence theorems for row reduction.
-/
