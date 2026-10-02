/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFnMathlib.Infinitesimal
public import HexOrderedFn.InfinitesimalTests

public section

/-!
Kernel proofs of infinitesimal identities and inequalities on the core test carriers.
-/

namespace Hex.OrderedFn.InfinitesimalProofs

attribute [local instance 2000] Field.toGrindField
open scoped Hex.OrderedFn.Infinitesimal
open Infinitesimal

abbrev First := RationalFn Rat
abbrev Second := RationalFn First

/-- Factorization of the polynomial in de Moura–Passmore, Example 3, in the actual
polynomial ring over the infinitesimal field. -/
theorem product_identity (e x : DensePoly First) :
    (e * x^2 - 1) * (e * x^3 - 1) = e^2 * x^5 - e * x^3 - e * x^2 + 1 := by
  grind

-- Specialize to the same infinitesimal and polynomial as computational conformance.
example :
    let e : DensePoly First := DensePoly.C RationalFn.X
    let x : DensePoly First := DensePoly.monomial 1 1
    (e * x^2 - 1) * (e * x^3 - 1) = e^2 * x^5 - e * x^3 - e * x^2 + 1 := by
  exact product_identity _ _


-- Expressions through the companion's Field and LinearOrder remain computable.
def orderedFraction (f : First) : First := if f < 0 then -(f ^ (2 : Nat)) else f + 1
def orderedSecond (f : Second) : Second := if f < 0 then -(f ^ (2 : Nat)) else f + 1
def scale (c : Rat) (f : First) : First := c • f

example : Field.toGrindField (K := First) = RationalFn.instField := rfl
example : Field.toGrindField (K := Second) = RationalFn.instField := rfl
example : (inferInstance : LinearOrder First).toLE =
    (⟨fun f g => Infinitesimal.sign orderSign (f - g) ≤ 0⟩ : LE First) := rfl
example : (inferInstance : LinearOrder First).toLT =
    (⟨fun f g => Infinitesimal.sign orderSign (f - g) < 0⟩ : LT First) := rfl


example : InfinitesimalTests.First = First := by
  unfold InfinitesimalTests.First First
  rw [HexRationalFnMathlib.ratField_eq]
example : InfinitesimalTests.Second = Second := by
  unfold InfinitesimalTests.Second InfinitesimalTests.First Second First
  rw [HexRationalFnMathlib.coreField_eq, HexRationalFnMathlib.ratField_eq]

-- The same inequality for the carriers formed in the Mathlib-free test module.
theorem core_delta_lt_power (n : ℕ) : InfinitesimalTests.delta <
    InfinitesimalTests.lift (InfinitesimalTests.epsilon ^ n) := by
  unfold InfinitesimalTests.delta InfinitesimalTests.lift InfinitesimalTests.epsilon
    InfinitesimalTests.Second InfinitesimalTests.First
  rw [← HexRationalFnMathlib.ratField_eq]
  exact X_lt_pow n

theorem core_delta_pos : (0 : InfinitesimalTests.Second) < InfinitesimalTests.delta := by
  unfold InfinitesimalTests.delta InfinitesimalTests.Second InfinitesimalTests.First
  rw [← HexRationalFnMathlib.ratField_eq]
  exact X_pos

theorem core_reciprocal_gt_int (n : ℤ) :
    (n : InfinitesimalTests.First) < InfinitesimalTests.epsilon⁻¹ := by
  unfold InfinitesimalTests.epsilon InfinitesimalTests.First
  rw [← HexRationalFnMathlib.ratField_eq]
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


example (f g : Second) : towerEmbed f < towerEmbed g ↔ f < g := towerEmbed_lt f g
example (a : First) :
    towerEmbed (RationalFn.C a) = toLex (HahnSeries.single 0 (embed a)) := towerEmbed_C a

/-- The coefficient map from ℚ(ε) to ℝ(ε) preserves signs and order. -/
noncomputable example (q : First) :
    sign orderSign (HexRationalFnMathlib.mapHom (Rat.castHom ℝ) q) =
      sign orderSign q := by
  classical
  exact mapHom_sign (Rat.castHom ℝ) Rat.cast_strictMono q

noncomputable example (p q : First) (less : p < q) :
    HexRationalFnMathlib.mapHom (Rat.castHom ℝ) p <
      HexRationalFnMathlib.mapHom (Rat.castHom ℝ) q := by
  classical
  exact mapHom_strictMono (Rat.castHom ℝ) Rat.cast_strictMono less

/-- A nested coefficient embedding uses the actual first infinitesimal field. -/
example : StrictMono
    (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.constantHom (K := Rat))) := by
  exact mapHom_strictMono (HexRationalFnMathlib.constantHom (K := Rat))
    (fun a b less => (C_lt a b).mpr less)

/-- info: 'Hex.OrderedFn.Infinitesimal.sign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Infinitesimal.sign_eq
/-- info: 'Hex.OrderedFn.Infinitesimal.linearOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Infinitesimal.linearOrder
/-- info: 'Hex.OrderedFn.Infinitesimal.strictOrderedRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Infinitesimal.strictOrderedRing
/-- info: 'Hex.OrderedFn.Infinitesimal.mapHom_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Infinitesimal.mapHom_sign
/-- info: 'Hex.OrderedFn.Infinitesimal.mapHom_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Infinitesimal.mapHom_strictMono
/-- info: 'Hex.OrderedFn.InfinitesimalProofs.delta_lt_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms delta_lt_power

end Hex.OrderedFn.InfinitesimalProofs

/-- info: 'Hex.OrderedFn.InfinitesimalProofs.core_delta_lt_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.OrderedFn.InfinitesimalProofs.core_delta_lt_power
