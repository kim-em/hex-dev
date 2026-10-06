/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib

open Matrix

namespace HexPolyDetMathlib.Diagnostics

/-- Named input exercises frontend unfolding rather than a matrix literal. -/
def tridiagonal (x : Int) : Matrix (Fin 4) (Fin 4) Int :=
  !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x]

theorem tridiagonalDet (x : Int) : Matrix.det (tridiagonal x) = x^4-3*x^2+1 := by
  det

/-- info: 'HexPolyDetMathlib.Diagnostics.tridiagonalDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tridiagonalDet

end HexPolyDetMathlib.Diagnostics
