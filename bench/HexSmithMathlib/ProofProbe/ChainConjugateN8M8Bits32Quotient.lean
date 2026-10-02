/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSmithMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, -1, 1, -1, -1, 1, 1, 1; -1, 17, -17, 17, 17, -17, -17, 15; -1, 17, 239, -239, 273, 239, -273, -241; -1, 17, 239, 3857, -3823, -3857, 3823, 3855; -1, 17, -273, -3823, 69393, -61713, 61679, 61711; -1, 17, -273, -3823, -61679, 1117935, 979183, -1117937; 1, -17, -239, 4335, 61167, -1118447, 15798545, 17895665; -1, -15, 271, -4367, 69873, -1109745, 15789839, 286322415] 8 ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456]) := by smith

#print axioms result
