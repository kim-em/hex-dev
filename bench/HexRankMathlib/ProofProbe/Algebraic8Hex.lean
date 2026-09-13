/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRankMathlib.ProofProbe.NumberFieldSupport

open RankProbe
open scoped Hex.PolyQuot.QAdjoinField
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem result : Matrix.rank (R := K) !![α, 1, 0, 0, 0, 0, 0, 0;
  1, α, 0, 0, 0, 0, 0, 0;
  0, 0, α, 1, 0, 0, 0, 0;
  0, 0, 1, α, 0, 0, 0, 0;
  0, 0, 0, 0, α, 1, 0, 0;
  0, 0, 0, 0, 1, α, 0, 0;
  0, 0, 0, 0, 0, 0, α, 1;
  0, 0, 0, 0, 0, 0, 1, α] = 8 := by rank

#print axioms result
