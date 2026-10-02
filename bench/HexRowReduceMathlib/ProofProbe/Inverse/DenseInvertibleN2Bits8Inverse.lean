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

theorem result : (!![18, 18; 18, 38] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = !![(19 / 180), (-1 / 20); (-1 / 20), (1 / 20)] := by inverse

#print axioms result
