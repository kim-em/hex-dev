/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.ModelEvaluation
public import HexRealClosureTheory.TransportInventory

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {context : Context registry}
variable {K G : Type} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [Field G] [LinearOrder G] [DecidableEq G]

private theorem cast_sign_zero {F : Type} [Zero F] [LinearOrder F] (a : F) :
    (SignType.sign a : Int) = 0 ↔ a = 0 := by
  constructor
  · intro zero
    apply sign_eq_zero_iff.mp
    cases sign : SignType.sign a <;> simp_all
  · intro zero
    subst a
    simp

omit [DecidableEq K] [IsStrictOrderedRing K] [DecidableEq G] in
/-- Finite native sign agreement supplies all zero reflection guards of the
literal transport inventory. There is no global injectivity premise on a
partial coefficient interpretation. -/
theorem inventory_agreement (model : Model context K)
    (interpretation : CoefficientMap model.field G) (xs : List context.Value)
    (members : ∀ x ∈ xs, model.domain interpretation x)
    (signs : ∀ x ∈ xs,
      (SignType.sign (model.read interpretation x) : Int) = context.sign x) :
    Transport.Inventory.Agreement (model.read interpretation) (model.domain interpretation)
      context.sign (fun a : G => (SignType.sign a : Int)) xs := by
  intro x member
  refine ⟨members x member, signs x member, ?_⟩
  rw [← cast_sign_zero, signs x member, model.sign, cast_sign_zero, model.zero_iff]

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.inventory_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.inventory_agreement
