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

noncomputable def result := solve% (!![(2 / 3), (2 / 3), (-2 / 3), (-2 / 3); (2 / 3), (4 / 3), (-4 / 3), (-4 / 3)] : Matrix (Fin 2) (Fin 4) ℚ) ![(8 / 9), (14 / 9)]

#print axioms result
