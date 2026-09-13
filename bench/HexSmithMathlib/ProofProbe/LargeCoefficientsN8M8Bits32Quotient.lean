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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, 1, -1, 1, -1, 1, -1, -1; -1, 15, 17, 15, 17, 15, -15, -15; -1, -17, 241, -273, -271, 239, -239, -239; -1, 15, -239, 4367, 4369, -4337, -3855, 4337; 1, -15, 239, -4367, 61167, -61199, -61681, -69873; 1, -15, 239, -4367, 61167, 987377, -1110257, -1118449; -1, 15, 273, -4337, -69871, 1118479, 15798001, -17764623; 1, 17, 271, 3857, 69391, -1117935, 17755887, 252645103] 8 ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456]) := by smith

#print axioms result
