/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.AlgebraicEvaluation
public import HexRealClosureMathlib.TowerTransport

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {K G : Type}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable [Field G] [LinearOrder G] [DecidableEq G] [IsStrictOrderedRing G] [IsRealClosed G]

/-- Every finite family at the end of a validated algebraic suffix has a
finite inventory in its original native context. Interpreting that inventory
with the correct signs extends the partial interpretation through the actual
selected roots and retains every previously interpreted coefficient exactly.
The inventory is chosen before the coefficient interpretation. -/
theorem extend_inventory {source : Context registry} (model : Model source K)
    (suffix : Suffix source) (values : List suffix.context.Value) :
    ∃ inventory : List source.Value,
      ∀ interpretation : CoefficientMap model.field G,
        (∀ a ∈ inventory, model.domain interpretation a) →
        (∀ a ∈ inventory,
          (SignType.sign (model.read interpretation a) : Int) = source.sign a) →
        ∃ extended : CoefficientMap (model.extend suffix).field G,
          (∀ a ∈ values, (model.extend suffix).domain extended a ∧
            (SignType.sign ((model.extend suffix).read extended a) : Int) =
              suffix.context.sign a) ∧
          (∀ a : source.Value, model.domain interpretation a →
            (model.extend suffix).domain extended (suffix.embed a) ∧
              (model.extend suffix).read extended (suffix.embed a) =
                model.read interpretation a) := by
  induction suffix with
  | nil =>
    refine ⟨values, ?_⟩
    intro interpretation members signs
    exact ⟨interpretation, fun a member => ⟨members a member, signs a member⟩,
      fun a member => ⟨member, rfl⟩⟩
  | @root parent descriptor rest ih =>
    obtain ⟨inventory, realizeTail⟩ := ih (model.adjoin descriptor) values
    obtain ⟨q, minimal, selected, built, realizeRoot⟩ :=
      model.adjoin_inventory (G := G) descriptor inventory
    refine ⟨adjoinCoefficients descriptor q inventory selected, ?_⟩
    intro interpretation members signs
    obtain ⟨data, middle, finite, coefficients, generator⟩ :=
      realizeRoot interpretation members signs
    obtain ⟨extended, finiteTail, oldTail⟩ := realizeTail middle
      (fun a member => (finite a member).1) (fun a member => (finite a member).2)
    refine ⟨extended, finiteTail, ?_⟩
    intro a member
    have old := coefficients a member
    have middleMember := (model.adjoin descriptor).domain_iff middle _ |>.mpr old.1
    have tail := oldTail ((parent.adjoin descriptor).embed a) middleMember
    refine ⟨tail.1, ?_⟩
    exact tail.2.trans (by simpa only [read_apply] using old.2)

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.extend_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.extend_inventory
