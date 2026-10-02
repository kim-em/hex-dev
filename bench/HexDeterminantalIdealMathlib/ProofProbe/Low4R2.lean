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

-- symbolic low.n4.k2.d1.s4, threshold 2.
noncomputable def result (x0 x1 : ℚ) :=
  rank_locus% !![x0 + 2*x1 + 3, 0, 3*x0^2 + 10*x0*x1 + 14*x0 + 8*x1^2 + 22*x1 + 15, 4*x0^2 + 13*x0*x1 + 13*x0 + 10*x1^2 + 17*x1 + 3;
    0, 1, 4*x0 + 5*x1 + 1, 5*x0 + x1 + 2;
    4*x0 + 5*x1 + 1, 0, 12*x0^2 + 31*x0*x1 + 23*x0 + 20*x1^2 + 29*x1 + 5, 16*x0^2 + 40*x0*x1 + 8*x0 + 25*x1^2 + 10*x1 + 1;
    5*x0 + x1 + 2, 0, 15*x0^2 + 23*x0*x1 + 31*x0 + 4*x1^2 + 13*x1 + 10, 20*x0^2 + 29*x0*x1 + 13*x0 + 5*x1^2 + 11*x1 + 2] 2

#print axioms result
