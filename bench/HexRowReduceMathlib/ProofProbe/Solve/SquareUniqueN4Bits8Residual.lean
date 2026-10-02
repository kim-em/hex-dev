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

theorem result : (!![(13 / 17), (-13 / 17), (13 / 17), (13 / 17); (-13 / 17), (23 / 17), (-23 / 17), (-23 / 17); (-13 / 17), (3 / 17), (9 / 17), (9 / 17); (-13 / 17), (3 / 17), (-15 / 17), (-6 / 17)] : Matrix (Fin 4) (Fin 4) ℚ).mulVec ![(2 / 3), (2 / 3), (-2 / 3), (2 / 3)] = ![0, (20 / 51), (-20 / 51), (-2 / 51)] := by solve

#print axioms result
