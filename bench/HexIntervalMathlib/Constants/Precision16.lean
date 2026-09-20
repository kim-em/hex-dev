/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib

public section

/-!
Dyadic source bounds on the 2^(-16) grid, with ordinary-kernel replay.
These validate analytic cuts; bounded runtime certificates are tested by their owner.
-/

namespace Hex.Interval.ConstantsProbe16

theorem pi_bounds : (205887 / 2 ^ 16 : ℝ) ≤ Real.pi ∧
    Real.pi ≤ 205888 / 2 ^ 16 := by
  apply Pi.enclosure 8 <;>
    norm_num [Pi.partialSum, Pi.error, Pi.arctanSum, Pi.arctanError,
      Finset.sum_range_succ]

theorem exp_bounds : (178145 / 2 ^ 16 : ℝ) ≤ Real.exp 1 ∧
    Real.exp 1 ≤ 178146 / 2 ^ 16 := by
  apply ExpOne.enclosure (n := 12) (by decide) <;>
    norm_num [ExpOne.partialSum, ExpOne.error, Finset.sum_range_succ]

theorem pi_sub_four : Real.pi - 4 < 0 := by
  have := pi_bounds.2
  norm_num at this
  linarith

theorem exp_comparison : 2 < Real.exp 1 ∧ Real.exp 1 < 3 := by
  have := exp_bounds
  norm_num at this
  constructor <;> linarith

example : ((205888 / 2 ^ 16 : ℝ) - 205887 / 2 ^ 16) = 1 / 2 ^ 16 := by norm_num
example : ((178146 / 2 ^ 16 : ℝ) - 178145 / 2 ^ 16) = 1 / 2 ^ 16 := by norm_num

/-- info: 'Hex.Interval.ConstantsProbe16.pi_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pi_bounds

/-- info: 'Hex.Interval.ConstantsProbe16.exp_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_bounds

/-- info: 'Hex.Interval.ConstantsProbe16.pi_sub_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pi_sub_four

/-- info: 'Hex.Interval.ConstantsProbe16.exp_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_comparison


#print axioms pi_bounds
#print axioms exp_bounds

/-! The complete public source-proof trust surface. -/

/-- info: 'Hex.Interval.Pi.arctan_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pi.arctan_bound

/-- info: 'Hex.Interval.Pi.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pi.bounds

/-- info: 'Hex.Interval.Pi.enclosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pi.enclosure

/-- info: 'Hex.Interval.Pi.error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pi.error_le

/-- info: 'Hex.Interval.Pi.width_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pi.width_le

/-- info: 'Hex.Interval.ExpOne.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExpOne.bounds

/-- info: 'Hex.Interval.ExpOne.enclosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExpOne.enclosure

/-- info: 'Hex.Interval.ExpOne.error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExpOne.error_le

/-- info: 'Hex.Interval.ExpOne.width_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExpOne.width_le

end Hex.Interval.ConstantsProbe16
