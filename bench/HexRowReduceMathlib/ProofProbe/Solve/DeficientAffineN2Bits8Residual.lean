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

theorem result : (!![(41 / 65), (-41 / 65); (41 / 65), (-41 / 65)] : Matrix (Fin 2) (Fin 2) ℚ).mulVec ![(1 / 3), (-1 / 3)] = ![(82 / 195), (82 / 195)] := by solve

#print axioms result
