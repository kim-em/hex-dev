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

theorem result : (!![0, 721814692; 1697282277, 0] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = !![0, (1 / 1697282277); (1 / 721814692), 0] := by inverse

#print axioms result
