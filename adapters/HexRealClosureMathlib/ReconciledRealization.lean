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
import all HexRealClosure.ReconciledGather

public section

namespace Hex.RealClosure.Tower

open scoped Hex.OrderedFn.Infinitesimal

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
  have canonical := model.canonical
  rw [OwnerReader.Agrees.read_eq (following := following) (reference := reference) shared.input.context shared.base_eq] at canonical
  exact canonical

/-- Reconciled registration preserves every value already computed in the
shared target and its image in the prescribed algebraic union. -/
theorem Shared.Model.registerReconciled?_union {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ packet : Registration shared source,
      shared.registerReconciled? source = some packet ∧
        ∃ returned : Shared.Model (reader := OwnerReader.reconciled following reference)
            packet.shared following reference,
          (∀ a, returned.target.value (packet.previous.value a) = model.target.value a) ∧
          ∀ a, packet.shared.targetToUnion reference (packet.previous.value a) =
            shared.targetToUnion reference a := by
  obtain ⟨packet, produced, returned, preserved⟩ :=
    model.registerReconciled? source compatible
  refine ⟨packet, produced, returned, preserved, fun a => ?_⟩
  apply Subtype.ext
  rw [returned.targetToUnion_value, model.targetToUnion_value, preserved]

/-- Adding a reconciled owner retains the actual previous inclusion and all
already computed union images. -/
theorem Shared.Model.addReconciled?_union {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, shared.addReconciled? source = some result ∧
      ∃ returned : Shared.Model (reader := OwnerReader.reconciled following reference)
          result following reference,
        ∃ previous : Inclusion shared.input.context result.input.context,
          (∀ a, returned.target.value (previous.value a) = model.target.value a) ∧
          ∀ a, result.targetToUnion reference (previous.value a) =
            shared.targetToUnion reference a := by
  obtain ⟨packet, produced, returned, preserved, union⟩ :=
    model.registerReconciled?_union source compatible
  exact ⟨packet.shared, by simp only [Shared.addReconciled?, produced, Option.map_some],
    returned, packet.previous, preserved, union⟩

/-- Ordered and reconciled gathers give an original owner the same union
image whenever the ordered owner factory accepts it. -/
theorem Shared.Model.toUnion_ordered_reconciled
    {firstOwners secondOwners : List (Context registry)}
    {first : Shared base firstOwners} {second : Shared base secondOwners}
    {following : base.Realization} {reference : Tower.Model (Context.ofBase base) K}
    (firstModel : Shared.Model first following reference)
    (secondModel : Shared.Model (reader := OwnerReader.reconciled following reference)
      second following reference)
    (i : Fin firstOwners.length) (j : Fin secondOwners.length)
    (same : firstOwners[i] = secondOwners[j]) (a : (firstOwners[i]).Value) :
    firstModel.toUnion i a =
      secondModel.toUnion j (_root_.cast (congrArg Context.Value same) a) := by
  apply Subtype.ext
  rw [firstModel.toUnion_value, secondModel.toUnion_value]
  have firstCanonical := firstModel.canonicalOwners i
  have secondCanonical := secondModel.canonicalOwners j
  change (firstOwners[i]).model? following reference = some (firstModel.owners.get i).1
    at firstCanonical
  change (secondOwners[j]).reconciledModel? following reference =
    some (secondModel.owners.get j).1 at secondCanonical
  rw [Context.reconciledModel?_ordered _ following reference (by
    rw [← same, firstCanonical]; rfl)] at secondCanonical
  exact factory_value_cast (reader := OwnerReader.ordered following reference)
    same (firstModel.owners.get i).1
    (secondModel.owners.get j).1 firstCanonical secondCanonical a

/-- Reconciled readers retain the canonical selected-root interpretation of
an actual root producer over their declared target base. -/
theorem Root.reconciledModel?_factory (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) K) (root : Root (Context.ofBase base)) :
    root.context.reconciledModel? following reference = some (root.model reference) :=
  (OwnerReader.reconciled following reference).root_model root reference
    (Context.reconciledModel?_base following reference)

/-- Every element of the prescribed union is represented by an actual native
root producer entry and by its checked inclusion into an actual shared target. -/
theorem Shared.union_coverage_reconciled (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) K) (x : Union.Carrier reference.field K) :
    ∃ p : (Context.ofBase base).Poly, ∃ out,
      (Context.ofBase base).roots p = .finite out ∧ ∃ entry ∈ out,
        ∃ shared : Shared base [entry.root.context],
          Shared.gatherReconciled? base [entry.root.context] = some shared ∧
            ∃ model : Shared.Model (reader := OwnerReader.reconciled following reference) shared following reference,
              (model.toUnion 0 entry.root.value : K) = x := by
  obtain ⟨p, out, produced, entry, member, meaning⟩ := reference.union_coverage x
  have compatible : entry.root.context.origin.base.signature.constants.Nodup ∧
      entry.root.context.origin.base.signature.constants ⊆ base.signature.constants ∧
      entry.root.context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
    rw [entry.root.origin_base, Context.ofBase_origin_base]
    exact ⟨following.keys_nodup, fun _ member => member, Nat.le_refl _⟩
  obtain ⟨shared, sharedProduced, ⟨model⟩⟩ :=
    Shared.gatherReconciled?_models following reference [entry.root.context]
      (fun source present => by
        have same : source = entry.root.context := List.mem_singleton.mp present
        subst source
        exact compatible)
  refine ⟨p, out, produced, entry, member, shared, sharedProduced, model, ?_⟩
  have ownerFactory : entry.root.context.reconciledModel? following reference =
      some (model.owners.get 0).1 := by
    exact model.canonicalOwners 0
  have aligned := Option.some.inj (ownerFactory.symm.trans
    (entry.root.reconciledModel?_factory following reference))
  exact (model.toUnion_value 0 entry.root.value).trans
    ((congrArg (fun m : Tower.Model entry.root.context K => m.value entry.root.value) aligned).trans meaning)

/-- An existing gathering can add any element of the algebraic union through
an actual root-producer owner. Every retained original owner keeps its image. -/
theorem Shared.Model.union_extend_reconciled {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference) shared following reference) (x : Union.Carrier reference.field K) :
    ∃ p : (Context.ofBase base).Poly, ∃ out,
      (Context.ofBase base).roots p = .finite out ∧ ∃ entry ∈ out,
        ∃ added : Shared base (owners ++ [entry.root.context]),
          shared.addReconciled? entry.root.context = some added ∧
          ∃ next : Shared.Model (reader := OwnerReader.reconciled following reference) added following reference,
            (∃ (j : Fin (owners ++ [entry.root.context]).length)
              (same : entry.root.context = (owners ++ [entry.root.context])[j]),
              (next.toUnion j (_root_.cast (congrArg Context.Value same) entry.root.value) : K) = x) ∧
            ∀ (i : Fin owners.length) (a : (owners[i]).Value),
              ∃ (j : Fin (owners ++ [entry.root.context]).length)
                (same : owners[i] = (owners ++ [entry.root.context])[j]),
                next.toUnion j (_root_.cast (congrArg Context.Value same) a) = model.toUnion i a := by
  obtain ⟨p, out, produced, entry, member, meaning⟩ := reference.union_coverage x
  have compatible : entry.root.context.origin.base.signature.constants.Nodup ∧
      entry.root.context.origin.base.signature.constants ⊆ base.signature.constants ∧
      entry.root.context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
    rw [entry.root.origin_base, Context.ofBase_origin_base]
    exact ⟨following.keys_nodup, fun _ member => member, Nat.le_refl _⟩
  obtain ⟨added, addedProduced, ⟨next⟩⟩ := model.addReconciled? entry.root.context compatible
  refine ⟨p, out, produced, entry, member, added, addedProduced, next, ?_, ?_⟩
  · let j : Fin (owners ++ [entry.root.context]).length := ⟨owners.length, by simp⟩
    have same : entry.root.context = (owners ++ [entry.root.context])[j] := by simp [j]
    refine ⟨j, same, ?_⟩
    exact (next.toUnion_value j _).trans
      ((factory_value_cast (reader := OwnerReader.reconciled following reference)
        same (entry.root.model reference)
        (next.owners.get j).1 (entry.root.reconciledModel?_factory following reference)
        (next.canonicalOwners j) entry.root.value).symm.trans meaning)
  · intro i a
    let j : Fin (owners ++ [entry.root.context]).length :=
      ⟨i.val, by simp only [List.length_append, List.length_singleton]; omega⟩
    have same : owners[i] = (owners ++ [entry.root.context])[j] := by
      simp only [j, Fin.getElem_fin, List.getElem_append_left i.isLt]
    exact ⟨j, same, (model.toUnion_coherent next i j same a).symm⟩

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

/-- Every value computed in the previous target follows the retained
predecessor map into the public reconciled model. -/
theorem Live.Enlargement.reconciled_value {request : Live.Request registry}
    {original : Live.Collection base request} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (result : Live.Enlargement original)
    (old : Shared.Model (reader := OwnerReader.reconciled following reference)
      original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result)
    (a : original.shared.input.context.Value) :
    (result.reconciledModel old ambient produced).target.value (result.previous.value a) =
      Ambient.coefficientHom ambient (old.target.value a) := by
  obtain ⟨previous, aligned⟩ := result.reconciled_previous old ambient produced
  rw [← aligned, previous.value, Tower.Model.liftInfinitesimal_value]

/-- A representative of an inherited provider coefficient keeps both its
prescribed ordinary value and its equality to the next canonical base. -/
theorem Live.Enlargement.reconciled_coefficient {request : Live.Request registry}
    {original : Live.Collection base request} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (result : Live.Enlargement original)
    (old : Shared.Model (reader := OwnerReader.reconciled following reference)
      original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result)
    (b : (Context.ofBase base).Value) (r : ℝ) (real : following.RealValue b r)
    (a : original.shared.input.context.Value) (same : old.target.value a = reference.value b) :
    ∃ inherited : (Context.ofBase base.infinitesimal).Value,
      following.infinitesimal.RealValue inherited r ∧
        (result.reconciledModel old ambient produced).target.value (result.previous.value a) =
          (Tower.Model.next base reference ambient).value inherited := by
  refine ⟨Context.baseValue base.infinitesimal (RationalFn.C (Context.baseStored base b)),
    (BaseContext.PackedContext.Realization.realValue_infinitesimal following b r).mpr real, ?_⟩
  rw [result.reconciled_value old ambient produced, same]
  exact (Tower.Model.next_constant reference ambient b).symm

/-- One ordinary specialization realizes the reconciled enlargement's original
owner inventories, old and fresh target values, inherited provider coefficients
and positive new parameter. Its canonical model can come from any earlier
reconciled enlargement. -/
theorem Live.Enlargement.realizeReconciled_model {request : Live.Request registry}
    {original : Live.Collection base request} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) K}
    (result : Live.Enlargement original)
    (old : Shared.Model (reader := OwnerReader.reconciled following reference)
      original.shared following reference)
    (produced : original.enlarge? = some result)
    (values : List original.shared.input.context.Value)
    (fresh : List result.collection.shared.input.context.Value := []) :
    ∃ read : result.collection.shared.input.context.Value → ℝ,
      ∃ domain : result.collection.shared.input.context.Value → Prop,
        result.ModelRealized old values fresh read domain := by
  classical
  let ambient := Ambient.ofField (Hex.RationalFn K)
  let returned := result.reconciledModel old ambient produced
  obtain ⟨previous, aligned⟩ := result.reconciled_previous old ambient produced
  obtain ⟨interpretation, data⟩ := returned.realizeReconciled request.inventory
    (values.map result.previous.value ++ result.parameter :: fresh)
  exact result.realizeWith old ambient returned (result.reconciled_parameter old ambient produced)
    previous aligned values fresh interpretation data

/-- Specialize a first reconciled enlargement without caller-supplied models.
Subsequent enlargements use their retained canonical model directly. -/
theorem Live.Enlargement.realizeReconciled {request : Live.Request registry}
    {original : Live.Collection base request} (result : Live.Enlargement original)
    (following : base.Realization)
    (gathered : request.gatherReconciled? base = some original)
    (produced : original.enlarge? = some result)
    (values : List original.shared.input.context.Value)
    (fresh : List result.collection.shared.input.context.Value := []) :
    ∃ read : result.collection.shared.input.context.Value → ℝ,
      ∃ domain : result.collection.shared.input.context.Value → Prop,
        result.Realized following values fresh read domain := by
  classical
  let old := original.reconciledModel following following.reference.model gathered
  obtain ⟨read, domain, data⟩ := result.realizeReconciled_model old produced values fresh
  exact ⟨read, domain, data.toRealized⟩

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





/-- info: 'Hex.RealClosure.Tower.Shared.Model.registerReconciled?_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.registerReconciled?_union

/-- info: 'Hex.RealClosure.Tower.Shared.Model.addReconciled?_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.addReconciled?_union

/-- info: 'Hex.RealClosure.Tower.Shared.Model.toUnion_ordered_reconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.toUnion_ordered_reconciled

/-- info: 'Hex.RealClosure.Tower.Root.reconciledModel?_factory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.reconciledModel?_factory

/-- info: 'Hex.RealClosure.Tower.Shared.union_coverage_reconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.union_coverage_reconciled

/-- info: 'Hex.RealClosure.Tower.Shared.Model.union_extend_reconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.union_extend_reconciled

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.reconciled_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.reconciled_value

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.realizeReconciled_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.realizeReconciled_model

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.realizeReconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.realizeReconciled

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.reconciled_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.reconciled_coefficient
