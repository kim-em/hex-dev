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

theorem result : (!![0, 0, 0, 0, 0, 0, 0, 59; 0, 0, 0, 0, 0, 0, 91, 0; 0, 0, 0, 0, 0, 118, 0, 0; 0, 0, 0, 0, 47, 0, 0, 0; 0, 0, 0, 29, 0, 0, 0, 0; 0, 0, 107, 0, 0, 0, 0, 0; 0, 116, 0, 0, 0, 0, 0, 0; 73, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℚ)⁻¹ = !![0, 0, 0, 0, 0, 0, 0, (1 / 73); 0, 0, 0, 0, 0, 0, (1 / 116), 0; 0, 0, 0, 0, 0, (1 / 107), 0, 0; 0, 0, 0, 0, (1 / 29), 0, 0, 0; 0, 0, 0, (1 / 47), 0, 0, 0, 0; 0, 0, (1 / 118), 0, 0, 0, 0, 0; 0, (1 / 91), 0, 0, 0, 0, 0, 0; (1 / 59), 0, 0, 0, 0, 0, 0, 0] := by inverse

#print axioms result
