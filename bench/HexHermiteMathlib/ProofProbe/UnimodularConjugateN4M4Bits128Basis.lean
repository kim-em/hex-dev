/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexHermiteMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, -2, -2, -2; 2, 4398046511102, 4398046511102, 4398046511102; -2, 4398046511106, 9671406556921431444160514, 9671406556921431444160514; -2, 4398046511106, -9671406556912635351138302, 42535295865107636526364913293619888130] 4) := by hermite

#print axioms result
