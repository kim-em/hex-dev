import HexMatrixMathlib.Determinant.Core
import HexMatrixMathlib.Determinant.Bareiss

/-!
Determinant bridge theorems for `hex-matrix-mathlib`.

This module re-exports the generic determinant bridge core and exposes the
row-pivoted Bareiss correctness theorem against Mathlib's determinant.
-/

namespace HexMatrixMathlib

universe u

variable {n : Nat}

/-- Row-pivoted Bareiss determinant soundness, exposed against Mathlib's
determinant for downstream bridge users. -/
theorem bareissDet_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M) :=
  bareiss_eq_mathlib_det M

end HexMatrixMathlib
