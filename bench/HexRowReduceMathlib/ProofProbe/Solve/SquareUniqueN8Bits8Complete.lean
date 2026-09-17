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

noncomputable def result := solve% (!![(5 / 9), (5 / 9), (-5 / 9), (-5 / 9), (5 / 9), (5 / 9), (-5 / 9), (5 / 9); (-5 / 9), (1 / 9), (11 / 9), (11 / 9), (-11 / 9), (-11 / 9), (-1 / 9), (-11 / 9); (-5 / 9), (1 / 9), 2, 2, -2, -2, (-8 / 9), (-4 / 9); (5 / 9), (-1 / 9), -2, (-13 / 9), (23 / 9), (23 / 9), (1 / 3), 1; (5 / 9), (11 / 9), (-2 / 3), (-1 / 9), (17 / 9), (17 / 9), (-5 / 3), -1; (-5 / 9), (-11 / 9), (-8 / 9), (-1 / 3), (7 / 9), (11 / 9), (23 / 9), 1; (-5 / 9), (1 / 9), (4 / 9), 1, (-5 / 9), (-1 / 9), 2, (4 / 9); (5 / 9), (11 / 9), (8 / 9), (13 / 9), (1 / 3), (-1 / 9), (-26 / 9), (4 / 3)] : Matrix (Fin 8) (Fin 8) ℚ) ![(-10 / 27), (58 / 27), (86 / 27), (-91 / 27), (5 / 27), (-91 / 27), (-16 / 27), (56 / 27)]

#print axioms result
