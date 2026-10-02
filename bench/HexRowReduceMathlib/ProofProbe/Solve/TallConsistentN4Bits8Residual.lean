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

theorem result : (!![(15 / 17), (15 / 17), (15 / 17), (-15 / 17); (15 / 17), (29 / 17), (29 / 17), (-29 / 17); (15 / 17), (1 / 17), (10 / 17), (-10 / 17); (15 / 17), (29 / 17), (38 / 17), (-28 / 17); (-15 / 17), (-1 / 17), (8 / 17), (2 / 17); (15 / 17), (29 / 17), (38 / 17), (-28 / 17); (-15 / 17), (-29 / 17), (-20 / 17), (10 / 17); (15 / 17), (1 / 17), (10 / 17), (-20 / 17)] : Matrix (Fin 8) (Fin 4) ℚ).mulVec ![(-1 / 3), (2 / 3), (2 / 3), (-1 / 3)] = ![(20 / 17), (130 / 51), (1 / 3), (49 / 17), (9 / 17), (49 / 17), (-31 / 17), (9 / 17)] := by solve

#print axioms result
