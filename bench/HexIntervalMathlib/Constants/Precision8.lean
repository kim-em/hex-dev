/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib

public section

/-!
Dyadic source bounds on the 2^(-8) grid, with ordinary-kernel replay.
These validate analytic cuts; bounded runtime certificates are tested by their owner.
-/

namespace Hex.Interval.ConstantsProbe8

theorem pi_bounds : (804 / 2 ^ 8 : ℝ) ≤ Real.pi ∧
    Real.pi ≤ 805 / 2 ^ 8 := by
  apply Pi.enclosure 4 <;>
    norm_num [Pi.partialSum, Pi.error, Pi.arctanSum, Pi.arctanError,
      Finset.sum_range_succ]

theorem exp_bounds : (695 / 2 ^ 8 : ℝ) ≤ Real.exp 1 ∧
    Real.exp 1 ≤ 696 / 2 ^ 8 := by
  apply ExpOne.enclosure (n := 8) (by decide) <;>
    norm_num [ExpOne.partialSum, ExpOne.error, Finset.sum_range_succ]

theorem pi_sub_four : Real.pi - 4 < 0 := by
  have := pi_bounds.2
  norm_num at this
  linarith

theorem exp_comparison : 2 < Real.exp 1 ∧ Real.exp 1 < 3 := by
  have := exp_bounds
  norm_num at this
  constructor <;> linarith

example : ((805 / 2 ^ 8 : ℝ) - 804 / 2 ^ 8) = 1 / 2 ^ 8 := by norm_num
example : ((696 / 2 ^ 8 : ℝ) - 695 / 2 ^ 8) = 1 / 2 ^ 8 := by norm_num

/-- info: 'Hex.Interval.ConstantsProbe8.pi_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pi_bounds

/-- info: 'Hex.Interval.ConstantsProbe8.exp_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_bounds

/-- info: 'Hex.Interval.ConstantsProbe8.pi_sub_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pi_sub_four

/-- info: 'Hex.Interval.ConstantsProbe8.exp_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_comparison


#print axioms pi_bounds
#print axioms exp_bounds

end Hex.Interval.ConstantsProbe8
