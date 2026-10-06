/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SharedRealization
public import HexRealClosureMathlib.SharedPresentation
public import HexRealClosureMathlib.ReconciledLive
import all HexRealClosureMathlib.SharedRealization
import all HexRealClosureMathlib.SharedPresentation
import all HexRealClosureMathlib.ReconciledContext

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {K : Type} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K]

/-- The common target has the declared base, so its reconciled reader agrees
with the ordered reader even when original owners require permutations. -/
theorem Shared.Model.target_ordered {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference) :
    shared.input.context.model? following reference = some model.target := by
  have accepted := (shared.input.context.model?_isSome following reference).mpr (by
    rw [shared.base_eq]
    exact ⟨List.Sublist.refl _, Nat.le_refl _⟩)
  have canonical := model.canonical
  change shared.input.context.reconciledModel? following reference = some model.target at canonical
  exact (Context.reconciledModel?_ordered _ following reference accepted).symm.trans canonical

/-- Every reconciled owner's actual native presentation denotes its canonical
value, including the selected roots transported through the shared cache. -/
theorem Shared.Model.presentation_reconciled {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference) (index : Fin owners.length) (a : (owners[index]).Value) :
    (shared.presentation index a).denote reference = (model.owners.get index).1.value a := by
  have canonical := model.target_ordered
  rw [Context.model?_origin] at canonical
  have target := shared.input.context.origin.presentation_denote shared.base_eq following reference
    model.target canonical (shared.value index a)
  exact target.trans (model.value index a)

/-- Reconciled owners enter the same prescribed algebraic union through their
actual finite presentations and selected embeddings. -/
theorem Shared.Model.toUnion_reconciled {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference) (index : Fin owners.length) (a : (owners[index]).Value) :
    (model.toUnion index a : K) = (model.owners.get index).1.value a :=
  model.presentation_reconciled index a

/-- Inherited provider coefficients follow the same checked reconciliation
used by the owner's canonical model. No source-target agreement is supplied. -/
theorem Origin.realValue_reconciled {context : Context registry} (origin : Origin context)
    (original : origin.base.Realization) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) K) (model : Tower.Model context K)
    (canonical : origin.reconciledModel? following reference = some model)
    (a : context.Value) (r : ℝ) (real : origin.RealValue original a r) :
    ∃ b, following.RealValue b r ∧ model.value a = reference.value b := by
  cases origin with
  | pack source suffix same =>
    cases same
    rw [Origin.reconciledModel?_pack] at canonical
    cases found : BaseReconciliation.make? (.pack source) base with
    | none =>
      have factory : (Context.base source).reconciledModel? following reference = none := by
        rw [Context.reconciledModel?, Context.origin_base]
        simp only [Origin.reconciledModel?, found]
        rfl
      rw [factory] at canonical
      contradiction
    | some inclusion =>
      erw [Context.reconciledModel?_baseMap (.pack source) following reference inclusion found]
        at canonical
      change some ((BaseReconciliation.Model.deriveCanonical following inclusion reference).source.extend
        suffix) = some model at canonical
      have aligned := Option.some.inj canonical
      obtain ⟨b, same, inherited⟩ := real
      subst a
      refine ⟨inclusion.value b, inclusion.realValue original following b r inherited, ?_⟩
      rw [← aligned]
      erw [Tower.Model.extend_embed]
      have preserved := (BaseReconciliation.Model.deriveCanonical following inclusion reference).value b
      rw [BaseReconciliation.Model.deriveCanonical_target] at preserved
      exact preserved.symm

/-- One ordinary partial reader simultaneously realizes all requested values
from reconciled owners, retaining their provider values and arithmetic domains. -/
theorem Shared.Model.realizeReconciled {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference)
    (values : (index : Fin owners.length) → List (owners[index]).Value)
    (extra : List shared.input.context.Value := []) :
    ∃ interpretation : CoefficientMap model.target.field ℝ,
      model.Realized values extra interpretation := by
  refine model.realizeWith model.target_ordered ?_ values extra
  intro index original a r inherited
  have canonical := model.canonicalOwners index
  change (owners[index]).origin.reconciledModel? following reference =
    some (model.owners.get index).1 at canonical
  exact (owners[index]).origin.realValue_reconciled original following reference
    (model.owners.get index).1 canonical a r inherited

/-- Interpret an accepted native reconciled gather without supplying a
symbolic model or separate realizations of the original owners. -/
theorem Shared.realizeReconciledValues {owners : List (Context registry)}
    (shared : Shared base owners) (following : base.Realization)
    (produced : Shared.gatherReconciled? base owners = some shared)
    (values : (index : Fin owners.length) → List (owners[index]).Value)
    (extra : List shared.input.context.Value := []) :
    ∃ read : shared.input.context.Value → ℝ, ∃ domain : shared.input.context.Value → Prop,
      shared.Realized following values extra read domain := by
  classical
  let reference := following.reference
  let model := Shared.Model.ofReconciledGather following reference.model owners shared produced
  obtain ⟨interpretation, data⟩ := model.realizeReconciled values extra
  exact model.realized_values values extra interpretation data

/-- Complete live requests use the same ordinary reader for every original
operand and replay coefficient in their finite inventories. -/
theorem Live.Collection.realizeReconciled {request : Live.Request registry}
    (collection : Live.Collection base request) (following : base.Realization)
    (produced : request.gatherReconciled? base = some collection)
    (extra : List collection.shared.input.context.Value := []) :
    ∃ read : collection.shared.input.context.Value → ℝ,
      ∃ domain : collection.shared.input.context.Value → Prop,
      collection.shared.Realized following request.inventory extra read domain :=
  collection.shared.realizeReconciledValues following
    (Live.Request.gatherReconciled?_shared base request collection produced) request.inventory extra

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Shared.Model.target_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.target_ordered

/-- info: 'Hex.RealClosure.Tower.Origin.realValue_reconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Origin.realValue_reconciled

/-- info: 'Hex.RealClosure.Tower.Shared.Model.realizeReconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.realizeReconciled

/-- info: 'Hex.RealClosure.Tower.Shared.realizeReconciledValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.realizeReconciledValues

/-- info: 'Hex.RealClosure.Tower.Live.Collection.realizeReconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Collection.realizeReconciled

/-- info: 'Hex.RealClosure.Tower.Shared.Model.presentation_reconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.presentation_reconciled

/-- info: 'Hex.RealClosure.Tower.Shared.Model.toUnion_reconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.toUnion_reconciled
