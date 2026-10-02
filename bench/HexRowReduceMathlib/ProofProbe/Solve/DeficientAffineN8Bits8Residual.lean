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

theorem result : (!![(12 / 17), (12 / 17), (-12 / 17), (-12 / 17), (-12 / 17), (-12 / 17), (-12 / 17), (12 / 17); (-12 / 17), (-2 / 17), (2 / 17), (2 / 17), (2 / 17), (22 / 17), (2 / 17), (-22 / 17); (-12 / 17), (-22 / 17), (31 / 17), (13 / 17), (31 / 17), (-7 / 17), (13 / 17), (7 / 17); (12 / 17), (2 / 17), (-11 / 17), (21 / 17), (-25 / 17), (1 / 17), (-7 / 17), (-1 / 17); (12 / 17), (2 / 17), (7 / 17), (-25 / 17), (21 / 17), (-45 / 17), (3 / 17), (45 / 17); (12 / 17), (22 / 17), (-13 / 17), (-45 / 17), (1 / 17), (-25 / 17), -1, (25 / 17); (12 / 17), (22 / 17), (-13 / 17), -1, (-27 / 17), (3 / 17), (-45 / 17), (-3 / 17); (-12 / 17), (-2 / 17), (11 / 17), (-21 / 17), (25 / 17), (-1 / 17), (7 / 17), (1 / 17)] : Matrix (Fin 8) (Fin 8) ℚ).mulVec ![(-1 / 3), (-2 / 3), (1 / 3), (-1 / 3), (-1 / 3), (-2 / 3), (1 / 3), (-2 / 3)] = ![(-12 / 17), (16 / 51), (56 / 51), (-10 / 17), (-2 / 51), (-14 / 17), (-70 / 51), (10 / 17)] := by solve

#print axioms result
