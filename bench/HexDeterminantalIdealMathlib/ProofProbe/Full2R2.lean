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

-- symbolic full.n2.k2.d2.s4, threshold 2.
noncomputable def result (x0 x1 : ℚ) :=
  rank_locus% !![x0^2 + 2*x0*x1 + 3*x0 + 4*x1^2, 2*x0^2 + 3*x0*x1 + 4*x0 + 5*x1^2;
    0, 1] 2

#print axioms result
