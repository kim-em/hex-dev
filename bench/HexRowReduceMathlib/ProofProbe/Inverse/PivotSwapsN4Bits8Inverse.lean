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

theorem result : (!![0, 0, 0, 8; 0, 0, 31, 0; 0, 4, 0, 0; 31, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℚ)⁻¹ = !![0, 0, 0, (1 / 31); 0, 0, (1 / 4), 0; 0, (1 / 31), 0, 0; (1 / 8), 0, 0, 0] := by inverse

#print axioms result
