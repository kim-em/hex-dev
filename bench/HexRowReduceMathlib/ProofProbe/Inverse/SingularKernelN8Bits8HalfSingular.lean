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

theorem result : (!![12, 12, 12, -12, 12, -12, 12, -12; -12, 0, 0, 0, 0, 24, -24, 24; -12, -24, -15, 15, -33, -9, -9, -9; -12, -24, -15, 30, -18, 6, -24, 6; -12, 0, -9, -6, -6, 18, 0, 18; 12, 0, 9, 6, 6, -18, 0, -18; 12, 0, -9, 24, 24, 0, 18, 0; -12, 0, -9, 24, 24, 48, -30, 48] : Matrix (Fin 8) (Fin 8) ℚ)⁻¹ = 0 := by inverse

#print axioms result
