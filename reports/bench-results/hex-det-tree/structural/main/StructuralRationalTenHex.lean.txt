/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
import Mathlib.Tactic.NormDet
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option trace.HexMatrix.certificate false
set_option profiler false

namespace HexPolyDetMathlib.ProofProbe.StructuralRationalTenHex
theorem result (x0 x1 x2 : Rat) : Matrix.det (R := Rat) (!![((-2) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x2) + 2 * (x0 * x1 * x2) + 3 * (x0 * x1 ^ 3) + 1 * (x0 * x2) + 2 * (x1 ^ 3) + 3 * (x1 * x2) + 1 * (x2 ^ 2) + 2 * (x0 * x2 ^ 3) + 3 * (x0 ^ 2 * x2 ^ 2))) / 2, ((3) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x2) + 2 * (x0 * x1 * x2) + 3 * (x0 * x1 ^ 3) + 1 * (x0 * x2) + 2 * (x1 ^ 3) + 3 * (x1 * x2) + 1 * (x2 ^ 2) + 2 * (x0 * x2 ^ 3) + 3 * (x0 ^ 2 * x2 ^ 2))) / 2, ((-2) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x2) + 2 * (x0 * x1 * x2) + 3 * (x0 * x1 ^ 3) + 1 * (x0 * x2) + 2 * (x1 ^ 3) + 3 * (x1 * x2) + 1 * (x2 ^ 2) + 2 * (x0 * x2 ^ 3) + 3 * (x0 ^ 2 * x2 ^ 2))) / 2; ((-3) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x2) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 * x2 ^ 2) + 2 * (x0 ^ 2 * x1) + 3 * (x1 ^ 3) + 1 * (x0 * x1 * x2) + 2 * (x0 * x2) + 3 * (1) + 1 * (x0 ^ 2 * x1 ^ 2))) / 3, ((1) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x2) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 * x2 ^ 2) + 2 * (x0 ^ 2 * x1) + 3 * (x1 ^ 3) + 1 * (x0 * x1 * x2) + 2 * (x0 * x2) + 3 * (1) + 1 * (x0 ^ 2 * x1 ^ 2))) / 3, ((3) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x2) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 * x2 ^ 2) + 2 * (x0 ^ 2 * x1) + 3 * (x1 ^ 3) + 1 * (x0 * x1 * x2) + 2 * (x0 * x2) + 3 * (1) + 1 * (x0 ^ 2 * x1 ^ 2))) / 3; ((-1) * (3 * (x2 ^ 4) + 1 * (x2) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1) + 2 * (x1 ^ 4) + 3 * (x2 ^ 3) + 1 * (x1 * x2) + 2 * (x2 ^ 2) + 3 * (x0 * x1 ^ 3) + 1 * (x0 ^ 2 * x1 ^ 2) + 2 * (x0 ^ 3))) / 4, ((-3) * (3 * (x2 ^ 4) + 1 * (x2) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1) + 2 * (x1 ^ 4) + 3 * (x2 ^ 3) + 1 * (x1 * x2) + 2 * (x2 ^ 2) + 3 * (x0 * x1 ^ 3) + 1 * (x0 ^ 2 * x1 ^ 2) + 2 * (x0 ^ 3))) / 4, ((1) * (3 * (x2 ^ 4) + 1 * (x2) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1) + 2 * (x1 ^ 4) + 3 * (x2 ^ 3) + 1 * (x1 * x2) + 2 * (x2 ^ 2) + 3 * (x0 * x1 ^ 3) + 1 * (x0 ^ 2 * x1 ^ 2) + 2 * (x0 ^ 3))) / 4]) = ((-40) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x2) + 2 * (x0 * x1 * x2) + 3 * (x0 * x1 ^ 3) + 1 * (x0 * x2) + 2 * (x1 ^ 3) + 3 * (x1 * x2) + 1 * (x2 ^ 2) + 2 * (x0 * x2 ^ 3) + 3 * (x0 ^ 2 * x2 ^ 2)) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x2) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 * x2 ^ 2) + 2 * (x0 ^ 2 * x1) + 3 * (x1 ^ 3) + 1 * (x0 * x1 * x2) + 2 * (x0 * x2) + 3 * (1) + 1 * (x0 ^ 2 * x1 ^ 2)) * (3 * (x2 ^ 4) + 1 * (x2) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1) + 2 * (x1 ^ 4) + 3 * (x2 ^ 3) + 1 * (x1 * x2) + 2 * (x2 ^ 2) + 3 * (x0 * x1 ^ 3) + 1 * (x0 ^ 2 * x1 ^ 2) + 2 * (x0 ^ 3))) / 24 := by
  det
end HexPolyDetMathlib.ProofProbe.StructuralRationalTenHex
