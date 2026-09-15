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

-- symbolic low.n8.k1.d1.s1, threshold 3.
noncomputable def result (x0 : ℚ) :=
  rank_locus% !![x0, 0, 0, 0, 5*x0^2, x0^2, 2*x0^2, 3*x0^2;
    0, 1, 0, 0, x0, 2*x0, 3*x0, 4*x0;
    0, 0, 1, 0, 2*x0, 3*x0, 4*x0, 5*x0;
    0, 0, 0, 1, 3*x0, 4*x0, 5*x0, x0;
    x0, 0, 0, 0, 5*x0^2, x0^2, 2*x0^2, 3*x0^2;
    2*x0, 0, 0, 0, 10*x0^2, 2*x0^2, 4*x0^2, 6*x0^2;
    3*x0, 0, 0, 0, 15*x0^2, 3*x0^2, 6*x0^2, 9*x0^2;
    4*x0, 0, 0, 0, 20*x0^2, 4*x0^2, 8*x0^2, 12*x0^2] 3

#print axioms result
