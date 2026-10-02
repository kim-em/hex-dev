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

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![-2, 4, 4, 4, -4, -4, 4, -4, -6, 6, -6, 6, -6, 6, 6, -10; -4, 6, 4, 4, -4, -4, 4, -4, -6, 6, -6, 6, -6, 6, 6, -10; 4, -4, -2, -4, 4, 4, -4, 4, 6, -6, 6, -6, 6, -6, -6, 10; -4, 4, 4, 6, -4, -4, 4, -4, -6, 6, -6, 6, -6, 6, 6, -10; 4, -4, -4, -4, 6, 4, -4, 4, 6, -6, 6, -6, 6, -6, -6, 10; -4, 4, 4, 4, -4, -2, 4, -4, -6, 6, -6, 6, -6, 6, 6, -10; -4, 4, 4, 4, -4, -4, 6, -4, -6, 6, -6, 6, -6, 6, 6, -10; -4, 4, 4, 4, -4, -4, 4, -2, -6, 6, -6, 6, -6, 6, 6, -10; -2, 2, 2, 2, -2, -2, 2, -2, 0, 4, -4, 4, -4, 4, 4, -8; -2, 2, 2, 2, -2, -2, 2, -2, -4, 8, -4, 4, -4, 4, 4, -8; -2, 2, 2, 2, -2, -2, 2, -2, -4, 4, 0, 4, -4, 4, 4, -8; -2, 2, 2, 2, -2, -2, 2, -2, -4, 4, -4, 8, -4, 4, 4, -8; 2, -2, -2, -2, 2, 2, -2, 2, 4, -4, 4, -4, 8, -4, -4, 8; 2, -2, -2, -2, 2, 2, -2, 2, 4, -4, 4, -4, 4, 0, -4, 8; -2, 2, 2, 2, -2, -2, 2, -2, -4, 4, -4, 4, -4, 4, 8, -8; 2, -2, -2, -2, 2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 4] 16) := by hermite

#print axioms result
