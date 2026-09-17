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

theorem result : ¬ ∃ x, (!![(6 / 11), (6 / 11), (-6 / 11), (-6 / 11); (-6 / 11), (10 / 33), (-10 / 33), (46 / 33); (-6 / 11), (-46 / 33), (46 / 33), (-10 / 33); (-6 / 11), (-46 / 33), (46 / 33), (-10 / 33)] : Matrix (Fin 4) (Fin 4) ℚ).mulVec x = ![(-6 / 11), (10 / 9), (97 / 99), (-101 / 99)] := by solve

#print axioms result
