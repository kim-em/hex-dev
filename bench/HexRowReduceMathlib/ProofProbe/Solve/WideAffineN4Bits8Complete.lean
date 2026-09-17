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

noncomputable def result := solve% (!![(12 / 17), (12 / 17), (12 / 17), (-12 / 17), (12 / 17), (-12 / 17), (12 / 17), (12 / 17); (-12 / 17), (-1 / 17), (-23 / 17), (1 / 17), (-1 / 17), (23 / 17), (-23 / 17), (-1 / 17); (12 / 17), (1 / 17), (31 / 17), (7 / 17), (-7 / 17), (-31 / 17), (31 / 17), (-7 / 17); (-12 / 17), (-1 / 17), (-31 / 17), (6 / 17), (-6 / 17), (44 / 17), (-18 / 17), (-6 / 17)] : Matrix (Fin 4) (Fin 8) ℚ) ![(-12 / 17), (-10 / 17), (70 / 51), (-6 / 17)]

#print axioms result
