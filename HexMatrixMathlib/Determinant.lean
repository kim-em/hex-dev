import HexMatrixMathlib.Determinant.Core
import HexMatrixMathlib.Determinant.Bareiss

/-!
Determinant correspondence theorems for `hex-matrix-mathlib`.

This module re-exports the generic determinant correspondence core and exposes
the row-pivoted Bareiss correctness theorem against Mathlib's determinant.
-/

namespace HexMatrixMathlib

universe u

variable {n : Nat}

/-- Row-pivoted Bareiss determinant soundness, exposed against Mathlib's
determinant for downstream Mathlib-side callers. -/
theorem bareissDet_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M) :=
  bareiss_eq_mathlib_det M

/-- Mathlib-side companion to the Mathlib-free orphan
`Hex.Matrix.bareiss_eq_det` (sorry-bound in `HexMatrix/Bareiss.lean`): the
row-pivoted Bareiss determinant equals the executable Leibniz determinant
on integer square matrices. Proven by composing `bareiss_eq_mathlib_det`
with `det_eq`, so it carries no dependency on the Mathlib-free orphan and
is the preferred surface for downstream Mathlib-side callers. -/
theorem bareiss_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Hex.Matrix.det M :=
  (bareiss_eq_mathlib_det M).trans (det_eq M).symm

end HexMatrixMathlib
