/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFnMathlib.Infinitesimal
public import HexOrderedFn.InfinitesimalTests

public section

namespace Hex.OrderedFn.InfinitesimalProofs

attribute [local instance 2000] Field.toGrindField
open scoped Hex.OrderedFn.Infinitesimal
open Infinitesimal

abbrev First := RationalFn Rat
abbrev Second := RationalFn First

private theorem ratField : Field.toGrindField (K := Rat) = Lean.Grind.instFieldRat := by
  unfold Field.toGrindField Lean.Grind.instFieldRat
    CommRing.toGrindCommRing Ring.toGrindRing Semiring.toGrindSemiring
  dsimp only
  congr
  all_goals first
    | exact proof_irrel_heq _ _
    | (funext n; cases n with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => rfl)

example : InfinitesimalTests.First = First := by
  unfold InfinitesimalTests.First First
  rw [ratField]
example : InfinitesimalTests.Second = Second := by
  unfold InfinitesimalTests.Second InfinitesimalTests.First Second First
  rw [HexRationalFnMathlib.coreField_eq, ratField]

-- The same inequality for the carriers formed in the Mathlib-free test module.
theorem core_delta_lt_power (n : ℕ) : InfinitesimalTests.delta <
    InfinitesimalTests.lift (InfinitesimalTests.epsilon ^ n) := by
  unfold InfinitesimalTests.delta InfinitesimalTests.lift InfinitesimalTests.epsilon
    InfinitesimalTests.Second InfinitesimalTests.First
  rw [← ratField, ← HexRationalFnMathlib.coreField_eq]
  exact X_lt_pow n

theorem core_delta_pos : (0 : InfinitesimalTests.Second) < InfinitesimalTests.delta := by
  unfold InfinitesimalTests.delta InfinitesimalTests.Second InfinitesimalTests.First
  rw [← ratField, ← HexRationalFnMathlib.coreField_eq]
  exact X_pos

theorem core_reciprocal_gt_int (n : ℤ) :
    (n : InfinitesimalTests.First) < InfinitesimalTests.epsilon⁻¹ := by
  unfold InfinitesimalTests.epsilon InfinitesimalTests.First
  rw [← ratField]
  exact intCast_lt_inv_X n

example : Std.IsLinearOrder First := inferInstance
example : Std.LawfulOrderLT First := inferInstance
example : Lean.Grind.OrderedRing First := inferInstance
example : Std.IsLinearOrder Second := inferInstance
example : Lean.Grind.OrderedRing Second := inferInstance

theorem epsilon_pos : (0 : First) < RationalFn.X := X_pos
theorem delta_pos : (0 : Second) < RationalFn.X := X_pos
theorem delta_lt_epsilon : (RationalFn.X : Second) < RationalFn.C (RationalFn.X : First) :=
  X_lt_C _ epsilon_pos
theorem delta_lt_power (n : ℕ) :
    (RationalFn.X : Second) < RationalFn.C ((RationalFn.X : First) ^ n) := X_lt_pow n
theorem reciprocal_gt_int (n : ℤ) : (n : First) < RationalFn.X⁻¹ := intCast_lt_inv_X n

example (n : ℕ) (hn : 0 < n) : (RationalFn.X : First) < RationalFn.C (1 / (n : Rat)) :=
  X_lt_C _ (div_pos zero_lt_one (Nat.cast_pos.mpr hn))

example : sign orderSign (1 / ((RationalFn.X : First) - 1)) = -1 := by
  apply sign_of_neg
  apply one_div_neg.mpr
  apply sub_neg.mpr
  exact X_lt_C (1 : Rat) zero_lt_one
example : sign orderSign (((RationalFn.X : First) ^ 2 - 1) / (RationalFn.X - 1)) = 1 :=
  by
    apply sign_of_pos
    apply div_pos_of_neg_of_neg
    · exact sub_neg.mpr (pow_lt_one₀ epsilon_pos.le (X_lt_C (1 : Rat) zero_lt_one) (by decide))
    · exact sub_neg.mpr (X_lt_C (1 : Rat) zero_lt_one)

example : (ofLex (embed ((RationalFn.X : First)⁻¹))).order = -1 := by
  rw [embed_order _ (inv_ne_zero (ne_of_gt epsilon_pos))]
  decide +kernel

example (x : First) :
    (RationalFn.X * x ^ 2 - 1) * (RationalFn.X * x ^ 3 - 1) =
      RationalFn.X ^ 2 * x ^ 5 - RationalFn.X * x ^ 3 - RationalFn.X * x ^ 2 + 1 := by
  apply embed_injective
  simp only [map_add, map_sub, map_mul, map_pow, map_one]
  ring

example (f g : Second) : towerEmbed f < towerEmbed g ↔ f < g := towerEmbed_lt f g
example (a : First) :
    towerEmbed (RationalFn.C a) = toLex (HahnSeries.single 0 (embed a)) := towerEmbed_C a

/-- info: 'Hex.OrderedFn.Infinitesimal.sign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Infinitesimal.sign_eq
/-- info: 'Hex.OrderedFn.Infinitesimal.linearOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Infinitesimal.linearOrder
/-- info: 'Hex.OrderedFn.Infinitesimal.strictOrderedRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Infinitesimal.strictOrderedRing
/-- info: 'Hex.OrderedFn.InfinitesimalProofs.delta_lt_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms delta_lt_power

end Hex.OrderedFn.InfinitesimalProofs

/-- info: 'Hex.OrderedFn.InfinitesimalProofs.core_delta_lt_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.OrderedFn.InfinitesimalProofs.core_delta_lt_power
