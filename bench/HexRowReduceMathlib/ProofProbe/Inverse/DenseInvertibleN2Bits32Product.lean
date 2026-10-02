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

theorem result : (!![518600345, 518600345; -518600345, -157341746] : Matrix (Fin 2) (Fin 2) ℚ) * !![(-157341746 / 187348834075616655), (-1 / 361258599); (1 / 361258599), (1 / 361258599)] = 1 := by inverse

#print axioms result
