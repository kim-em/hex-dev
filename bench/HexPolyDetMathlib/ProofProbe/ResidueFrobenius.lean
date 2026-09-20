/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
set_option trace.HexMatrix.certificate true
set_option hex.det.checker 1

set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000000

open MvPolynomial in
theorem result : Matrix.det
    (!![X 0 ^ 3 - X 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 1) (ZMod 3))) = X 0 ^ 3 - X 0 := by det

#print axioms result
