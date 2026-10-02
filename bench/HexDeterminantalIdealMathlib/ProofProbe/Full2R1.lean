/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminantalIdealMathlib

set_option maxHeartbeats 0

-- symbolic full.n2.k1.d1.s1, threshold 1.
noncomputable def result (x0 : ℚ) :=
  rank_locus% !![x0, 2*x0;
    0, 1] 1

#print axioms result
