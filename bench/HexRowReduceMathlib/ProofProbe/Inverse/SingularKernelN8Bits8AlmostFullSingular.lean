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

theorem result : (!![8, 8, 8, -8, -8, -8, 8, -8; 8, 19, 19, -19, 3, 3, 19, -19; -8, 3, 15, -15, 31, 7, -9, 9; 8, -3, 9, -1, -15, -23, -7, 7; 8, 19, 31, -23, 20, 12, 2, -28; -8, 3, 15, -23, 26, -4, -14, 20; -8, -19, -31, 23, 6, 4, -9, 21; -8, -19, -7, 15, -12, -30, 9, 55] : Matrix (Fin 8) (Fin 8) ℚ)⁻¹ = 0 := by inverse

#print axioms result
