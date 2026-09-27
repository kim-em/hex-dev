/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import HexPolyDetMathlib.ProofProbe.GeneralSupport

open Matrix

private theorem result (x : Int) : Matrix.det (HexPolyDetMathlib.ProofProbe.quadratic x) = x^4-3*x^2+1 := by
  det

#print axioms result
