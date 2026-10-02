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

theorem result : (!![(11 / 17), (11 / 17), (11 / 17), (-11 / 17); (-11 / 17), (1 / 17), (1 / 17), (-1 / 17); (-11 / 17), (-23 / 17), (-15 / 17), (31 / 17); (11 / 17), (-1 / 17), (-9 / 17), (6 / 17)] : Matrix (Fin 4) (Fin 4) ℚ)⁻¹ = !![(17 / 132), (-17 / 12), 0, 0; (187 / 78), (1411 / 312), (51 / 104), (34 / 13); (85 / 52), (-51 / 104), (85 / 104), (-17 / 13); (34 / 13), (34 / 13), (17 / 13), (17 / 13)] := by inverse

#print axioms result
