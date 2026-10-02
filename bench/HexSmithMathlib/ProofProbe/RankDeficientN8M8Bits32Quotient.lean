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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, -1, -1, -1, 1, 1, 1, -1; 1, 511, -513, -513, -511, -511, 513, -513; 1, -513, 524799, -523777, -523775, 524801, -524799, -523777; -1, -511, 524801, 536347137, -537394689, -536346113, 536346111, -537394687; -1, -511, -523775, -536346111, 537395711, 536347135, -536347137, 537395713; 1, -513, -523777, 537395711, -536346111, -537394687, 537394689, -536346113; -1, 513, -524799, -536347135, 537394687, 536346111, -536346113, 537394689; -1, -511, 524801, -537394687, 536347135, 537395711, -537395713, 536347137] 4 ![1, 512, 524288, 536870912]) := by smith

#print axioms result
