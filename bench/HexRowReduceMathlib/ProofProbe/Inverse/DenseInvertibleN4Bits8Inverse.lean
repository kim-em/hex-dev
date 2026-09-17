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

theorem result : (!![12, -12, 12, -12; 12, 3, 27, -27; -12, -3, -18, 18; -12, 27, -6, 19] : Matrix (Fin 4) (Fin 4) ℚ)⁻¹ = !![(1 / 60), (-7 / 45), (-2 / 9), 0; (-1 / 15), (-2 / 45), (-1 / 9), 0; (2 / 13), (1 / 9), (22 / 117), (1 / 13); (2 / 13), 0, (1 / 13), (1 / 13)] := by inverse

#print axioms result
