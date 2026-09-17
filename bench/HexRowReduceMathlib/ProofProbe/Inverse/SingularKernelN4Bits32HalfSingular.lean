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

theorem result : (!![472242224, -472242224, 472242224, -472242224; 472242224, -184567671, 759916777, -184567671; 472242224, -184567671, 759916777, -184567671; -472242224, 759916777, -184567671, 759916777] : Matrix (Fin 4) (Fin 4) ℚ)⁻¹ = 0 := by inverse

#print axioms result
