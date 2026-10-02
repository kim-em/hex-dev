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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, 1, -1, -1, -1, 1, -1, -1; 1, 513, -513, 511, 511, 513, 511, -513; -1, 511, 523777, -523775, 524801, -523777, -523775, -524799; 1, -511, -523777, 537394687, 536346111, -536347135, 537394687, -536346113] 4 ![1, 512, 524288, 536870912]) := by smith

#print axioms result
