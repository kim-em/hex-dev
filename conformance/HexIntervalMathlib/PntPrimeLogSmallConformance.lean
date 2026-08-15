/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntPrimeLogSmall

/-!
# Source-pinned PNT+ small-prime logarithm conformance

The exact pinned proofs `RS_prime_helper.p_n_lower_small` and
`Rosser1938.p_n_gt_1` use the same thirty `(n, m)` coordinates.  These guards
pin that table and elaborate the two reusable bounded theorems that replace all
sixty `interval_auto` leaves after a localized PNT+ rewrite.
-/

namespace Hex.IntervalMathlib.PntPrimeLogSmallConformance

open Hex.IntervalMathlib.Experiment.PntPrimeLogSmall

#guard sourceRows.size == 30
#guard sourceRows.all fun row => sourceCut row.1 == row.2
#guard sourceRows[0]? == some (2, 3)
#guard sourceRows[29]? == some (31, 127)

/-- Reusable bounded evidence for all thirty ordinary-log leaves. -/
theorem allLogLeaves (n : Nat) (hn : 2 ≤ n) (hn31 : n ≤ 31) :
    (n : ℝ) * Real.log n < sourceCut n :=
  logLeaf n hn hn31

/-- Reusable bounded evidence for all thirty nested-log leaves. -/
theorem allNestedLogLeaves (n : Nat) (hn : 2 ≤ n) (hn31 : n ≤ 31) :
    (n : ℝ) * (Real.log n + Real.log (Real.log n) - 3 / 2) < sourceCut n :=
  nestedLogLeaf n hn hn31

example : ¬ ((31 : ℝ) * Real.log 31 < 20) := rejectWrongCut

/-- info: 'Hex.IntervalMathlib.Experiment.PntPrimeLogSmall.logLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logLeaf

/--
info: 'Hex.IntervalMathlib.Experiment.PntPrimeLogSmall.nestedLogLeaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nestedLogLeaf

/--
info: 'Hex.IntervalMathlib.Experiment.PntPrimeLogSmall.rejectWrongCut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejectWrongCut

end Hex.IntervalMathlib.PntPrimeLogSmallConformance
