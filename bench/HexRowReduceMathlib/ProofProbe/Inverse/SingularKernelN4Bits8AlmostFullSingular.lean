/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : (!![23, 23, 23, 23; -23, 5, -51, -51; 23, -5, 79, 23; 23, 51, 23, -33] : Matrix (Fin 4) (Fin 4) ℚ)⁻¹ = 0 := by inverse

#print axioms result
