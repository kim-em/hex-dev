/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic

set_option trace.HexMatrix.certificate true
set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
theorem result (x0 : Int) : Matrix.det (R := Int) (fun i j : Fin 4 => x0 + if i = j then 1 else 0) = 4 * x0 + 1 := by
  det

#print axioms result
