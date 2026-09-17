/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option trace.HexMatrix.certificate true
set_option hex.det.checker 2
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Int) : Matrix.det (R := Int) (!![x0, x1, x2, x3, 0; x4, x5, x6, x7, 0; x8, x9, x10, x11, 0; x12, x13, x14, x15, 0; 0, 0, 0, 0, x16]) = (-x0*x10*x13*x7 + x0*x10*x15*x5 + x0*x11*x13*x6 - x0*x11*x14*x5 + x0*x14*x7*x9 - x0*x15*x6*x9 + x1*x10*x12*x7 - x1*x10*x15*x4 - x1*x11*x12*x6 + x1*x11*x14*x4 - x1*x14*x7*x8 + x1*x15*x6*x8 - x10*x12*x3*x5 + x10*x13*x3*x4 + x11*x12*x2*x5 - x11*x13*x2*x4 - x12*x2*x7*x9 + x12*x3*x6*x9 + x13*x2*x7*x8 - x13*x3*x6*x8 - x14*x3*x4*x9 + x14*x3*x5*x8 + x15*x2*x4*x9 - x15*x2*x5*x8 ) * x16 := by
  det

#print axioms result
