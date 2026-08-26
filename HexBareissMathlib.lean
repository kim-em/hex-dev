/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareissMathlib.Bareiss

public section

/-!
The `HexBareissMathlib` library is the Mathlib bridge for `hex-bareiss`. It
exposes the row-pivoted Bareiss determinant correctness theorems against both
Mathlib's determinant and the executable Leibniz determinant, building on the
no-pivot bordered-minor invariant in `HexBareissMathlib.Bareiss` and the
determinant correspondence in `HexDeterminantMathlib`.
-/

namespace HexMatrixMathlib

universe u

variable {n : Nat}

/-- Row-pivoted Bareiss determinant soundness, exposed against Mathlib's
determinant for downstream Mathlib-side callers. -/
theorem bareissDet_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M) :=
  bareiss_eq_mathlib_det M

/-- The row-pivoted Bareiss determinant equals the executable Leibniz
determinant on integer square matrices. Proven Mathlib-side by composing
`bareiss_eq_mathlib_det` with `det_eq`, so it holds unconditionally (with no
side hypothesis) and is the preferred surface for downstream Mathlib-side callers. -/
theorem bareiss_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Hex.Matrix.det M :=
  (bareiss_eq_mathlib_det M).trans (det_eq M).symm

end HexMatrixMathlib
