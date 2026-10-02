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

theorem result : (!![(854181327 / 1073741825), (-854181327 / 1073741825); (854181327 / 1073741825), (-854181327 / 1073741825)] : Matrix (Fin 2) (Fin 2) ℚ).mulVec ![(-2 / 3), (-1 / 3)] = ![(-284727109 / 1073741825), (-284727109 / 1073741825)] := by solve

#print axioms result
