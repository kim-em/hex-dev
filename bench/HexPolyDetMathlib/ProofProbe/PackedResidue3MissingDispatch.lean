/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
import Mathlib.Algebra.Field.ZMod
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option trace.HexMatrix.certificate true
set_option hex.det.checker 0
set_option hex.det.quotients false
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x0 x1 : ZMod 3) : Matrix.det (R := ZMod 3) (!![x0, 1, 0, 0; 1, x0, 0, 0; 0, 0, x1, 1; 0, 0, 1, x1]) = (x0^2-1)*(x1^2-1) := by
  det

#print axioms result
