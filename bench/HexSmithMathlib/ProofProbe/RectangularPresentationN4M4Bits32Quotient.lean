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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, 1, 1, 1; 1, 513, -511, 513; 1, -511, 524801, -524799; 1, -511, -523775, 537394689; -1, 511, -524801, 537395711; -1, -513, -523777, -536347137; -1, 511, 523775, -537394689; 1, -511, -523775, -536347135] 4 ![1, 512, 524288, 536870912]) := by smith

#print axioms result
