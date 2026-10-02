/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminantalIdealMathlib

set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.Hex.rankLocus true

-- symbolic full.n4.k1.d1.s1, threshold 3.
noncomputable def result (x0 : ℚ) :=
  rank_locus% !![x0, 2*x0, 3*x0, 4*x0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1] 3

#print axioms result
