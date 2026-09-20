/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib

public section

/-!
Dyadic source bounds on the 2^(-2) grid, with ordinary-kernel replay.
These validate analytic cuts; bounded runtime certificates are tested by their owner.
-/

namespace Hex.Interval.ConstantsProbe2

theorem pi_bounds : (12 / 2 ^ 2 : ℝ) ≤ Real.pi ∧
    Real.pi ≤ 13 / 2 ^ 2 := by
  apply Pi.enclosure 2 <;>
    norm_num [Pi.partialSum, Pi.error, Pi.arctanSum, Pi.arctanError,
      Finset.sum_range_succ]

theorem exp_bounds : (10 / 2 ^ 2 : ℝ) ≤ Real.exp 1 ∧
    Real.exp 1 ≤ 11 / 2 ^ 2 := by
  apply ExpOne.enclosure (n := 4) (by decide) <;>
    norm_num [ExpOne.partialSum, ExpOne.error, Finset.sum_range_succ]

theorem pi_sub_four : Real.pi - 4 < 0 := by
  have := pi_bounds.2
  norm_num at this
  linarith

theorem exp_comparison : 2 < Real.exp 1 ∧ Real.exp 1 < 3 := by
  have := exp_bounds
  norm_num at this
  constructor <;> linarith

example : ((13 / 2 ^ 2 : ℝ) - 12 / 2 ^ 2) = 1 / 2 ^ 2 := by norm_num
example : ((11 / 2 ^ 2 : ℝ) - 10 / 2 ^ 2) = 1 / 2 ^ 2 := by norm_num

/-- Dropping the positive-order premise would assert the false enclosure `[0,0]`. -/
example : ¬ (ExpOne.partialSum 0 - ExpOne.error 0 ≤ Real.exp 1 ∧
    Real.exp 1 ≤ ExpOne.partialSum 0 + ExpOne.error 0) := by
  simp [ExpOne.partialSum, ExpOne.error]
  exact fun _ => Real.exp_pos 1

/-- info: 'Hex.Interval.ConstantsProbe2.pi_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pi_bounds

/-- info: 'Hex.Interval.ConstantsProbe2.exp_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_bounds

/-- info: 'Hex.Interval.ConstantsProbe2.pi_sub_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pi_sub_four

/-- info: 'Hex.Interval.ConstantsProbe2.exp_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_comparison


#print axioms pi_bounds
#print axioms exp_bounds

end Hex.Interval.ConstantsProbe2
