/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReconciledGather
public import HexRealClosureMathlib.BaseReconstruction
public import HexRealClosureMathlib.ContextModel
public import HexRealClosureMathlib.OwnerReader
import all HexRealClosureMathlib.ContextModel

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]

/-- Interpret an original owner using the actual reconciled base factory and
its stored algebraic suffix in the target's one ordered real-closed field. -/
noncomputable def Origin.reconciledModel? {context : Context registry} (origin : Origin context)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    Option (Tower.Model context R) := by
  cases origin with
  | pack original suffix same =>
    exact (BaseReconciliation.make? (.pack original) base).map fun inclusion =>
      let originalModel : Tower.Model (Context.base original) R :=
        (BaseReconciliation.Model.deriveCanonical (source := .pack original) (target := base)
          following inclusion target).source
      same ▸ originalModel.extend suffix

/-- Interpret an actual context after checking provider-key reconciliation
against the retained target realization. -/
noncomputable def Context.reconciledModel? (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    Option (Tower.Model context R) := context.origin.reconciledModel? following target

/-- An accepted ordered base factory retains exactly its existing owner model. -/
theorem Origin.reconciledModel?_ordered {context : Context registry} (origin : Origin context)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (accepted : (BaseInclusion.make? origin.base base).isSome = true) :
    origin.reconciledModel? following target = origin.model? following target := by
  cases origin with
  | pack original suffix same =>
    change (BaseInclusion.make? (.pack original) base).isSome = true at accepted
    obtain ⟨ordered, produced⟩ := Option.isSome_iff_exists.mp accepted
    simp only [Origin.reconciledModel?, Origin.model?, produced]
    rw [BaseReconciliation.make?_ordered ordered]
    simp only [Option.map_some]
    rw [BaseReconciliation.Model.deriveCanonical_ordered following _ ordered target]

/-- Reconciled context interpretation retains any existing ordered factory
result, including its exact choices of all selected algebraic roots. -/
theorem Context.reconciledModel?_ordered (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (accepted : (context.model? following target).isSome = true) :
    context.reconciledModel? following target = context.model? following target := by
  apply context.origin.reconciledModel?_ordered following target
  have compatible := (context.model?_isSome following target).mp accepted
  exact (BaseInclusion.make?_isSome context.origin.base base).mpr compatible

/-- At the declared target base, reconciliation retains the target model. -/
theorem Context.reconciledModel?_base
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (Context.ofBase base).reconciledModel? following target = some target := by
  rw [Context.reconciledModel?_ordered _ following target (by rw [Context.model?_base]; rfl),
    Context.model?_base]

/-- An accepted reconciled coefficient map supplies exactly the original base
owner model used by the reconciled context reader. -/
theorem Context.reconciledModel?_baseMap
    (source : BaseContext.PackedContext registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (inclusion : BaseReconciliation source base)
    (produced : BaseReconciliation.make? source base = some inclusion) :
    (Context.ofBase source).reconciledModel? following target =
      some (BaseReconciliation.Model.deriveCanonical following inclusion target).source := by
  cases source with
  | pack original =>
    change (Context.base original).reconciledModel? following target = _
    unfold Context.reconciledModel?
    rw [Context.origin_base]
    simp only [Origin.reconciledModel?, produced, Option.map_some]
    rfl

/-- The owner reader accepts exactly distinct source providers contained in
the realized target and sufficient target infinitesimal depth. -/
theorem Context.reconciledModel?_isSome (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (context.reconciledModel? following target).isSome = true ↔
      context.origin.base.signature.constants.Nodup ∧
        context.origin.base.signature.constants ⊆ base.signature.constants ∧
          context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  have packaged : (context.reconciledModel? following target).isSome =
      (BaseReconciliation.make? context.origin.base base).isSome := by
    simp only [Context.reconciledModel?, Origin.reconciledModel?, Origin.base, Option.isSome_map]
  rw [packaged, BaseReconciliation.make?_isSome]
  constructor
  · exact (BaseContext.PackedContext.reconcile?_isSome _ _ following.keys_nodup).mp
  · rintro ⟨unique, included, depth⟩
    exact BaseContext.PackedContext.reconcile?_success _ _ unique following.keys_nodup included depth

/-- A stored origin extends exactly its reconciled base's canonical model. -/
theorem Origin.reconciledModel?_pack
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign) (suffix : Suffix (Context.base original))
    {context : Context registry} (same : suffix.context = context)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (Origin.pack original suffix same).reconciledModel? following target =
      ((Context.base original).reconciledModel? following target).map
        (fun model => same ▸ model.extend suffix) := by
  cases same
  rw [Context.reconciledModel?, Context.origin_base]
  simp only [Origin.reconciledModel?]
  cases BaseReconciliation.make? (.pack original) base <;> rfl

private theorem Origin.reconciledModel?_snoc {context : Context registry} (origin : Origin context)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    (origin.snoc descriptor).reconciledModel? following target =
      (origin.reconciledModel? following target).map (fun model => model.adjoin descriptor) := by
  cases origin with
  | pack original suffix same =>
    cases same
    simp only [Origin.snoc, Context.castDescriptor, Origin.reconciledModel?,
      Option.map_map]
    congr 1
    funext inclusion
    exact eq_of_heq ((Model.cast_heq _ (Suffix.snoc_context suffix descriptor)).trans
      (Model.extend_snoc _ suffix descriptor))

/-- A reconciled child owner uses its canonical predecessor model and its
actual selected descriptor; the reader makes no separate root choice. -/
theorem Context.reconciledModel?_adjoin (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    (context.adjoin descriptor).context.reconciledModel? following target =
      (context.reconciledModel? following target).map (fun model => model.adjoin descriptor) := by
  simp only [Context.reconciledModel?, Context.origin_adjoin]
  exact context.origin.reconciledModel?_snoc following target descriptor

/-- Extending the actual suffix retains its canonical predecessor and each
stored selected root in the common target field. -/
theorem Context.reconciledModel?_extend {source : Context registry} (suffix : Suffix source)
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R) :
    ∀ model : Tower.Model source R, source.reconciledModel? following reference = some model →
      suffix.context.reconciledModel? following reference = some (model.extend suffix) := by
  induction suffix with
  | nil => intro model canonical; exact canonical
  | root descriptor rest ih =>
    intro model canonical
    exact ih (model.adjoin descriptor) (by
      rw [Context.reconciledModel?_adjoin, canonical, Option.map_some])

/-- The canonical owner factory using checked provider-key reconciliation. -/
@[expose] noncomputable def OwnerReader.reconciled {base : BaseContext.PackedContext registry}
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R) :
    OwnerReader registry R where
  read context := context.reconciledModel? following reference
  adjoin := fun context descriptor => context.reconciledModel?_adjoin following reference descriptor

/-- The checked reconciled reader agrees with the ordered factory on the
actual shared target base. This follows from the native factory agreement. -/
instance OwnerReader.agrees_reconciled {base : BaseContext.PackedContext registry} (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) :
    (OwnerReader.reconciled following reference).Agrees following reference where
  read_eq context same := by
    have accepted := (context.model?_isSome following reference).mpr (by
      rw [same]
      exact ⟨List.Sublist.refl _, Nat.le_refl _⟩)
    exact Context.reconciledModel?_ordered context following reference accepted

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.reconciledModel?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.reconciledModel?_ordered

/-- info: 'Hex.RealClosure.Tower.Context.reconciledModel?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.reconciledModel?_isSome

/-- info: 'Hex.RealClosure.Tower.Context.reconciledModel?_adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.reconciledModel?_adjoin

/-- info: 'Hex.RealClosure.Tower.Context.reconciledModel?_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.reconciledModel?_extend
