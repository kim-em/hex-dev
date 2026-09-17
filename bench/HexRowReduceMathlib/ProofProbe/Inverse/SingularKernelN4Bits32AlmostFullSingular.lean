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

theorem result : (!![422709228, 422709228, 422709228, -422709228; 422709228, 863934129, 863934129, 18515673; 422709228, 863934129, 1323619122, -441169320; 422709228, 863934129, 404249136, 478200666] : Matrix (Fin 4) (Fin 4) ℚ)⁻¹ = 0 := by inverse

#print axioms result
