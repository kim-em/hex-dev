/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminantalIdealTheory


-- symbolic low.n2.k1.d1.s1, threshold 1.
noncomputable def result (x0 : ℚ) :=
  rank_locus% !![x0, 2*x0^2;
    3*x0, 6*x0^2] 1

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
