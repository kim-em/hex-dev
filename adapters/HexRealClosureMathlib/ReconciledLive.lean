/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReconciledLive
public import HexRealClosureMathlib.ReconciledGatherModel
public import HexRealClosureMathlib.LiveRequest

public section

namespace Hex.RealClosure.Tower.Live

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K]

/-- Reconciled gathering succeeds for complete live requests whenever all
original owners fit the validated target. Every descriptor is revalidated
through its actual value-preserving map; no independent root agreement is used. -/
theorem Request.gatherReconciled?_models (following : base.Realization)
    (reference : Model (Context.ofBase base) K) (request : Request registry)
    (compatible : ∀ source ∈ request.owners,
      source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, request.gatherReconciled? base = some result ∧
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following reference)
        result.shared following reference) := by
  obtain ⟨shared, gathered, ⟨model⟩⟩ :=
    Shared.gatherReconciled?_models following reference request.owners compatible
  obtain ⟨frames, checked⟩ := request.transport?_success shared.maps model.target model.owners
  obtain ⟨result, produced, same⟩ :=
    request.gatherReconciled?_of_success base shared gathered frames checked
  exact ⟨result, produced, ⟨same.symm ▸ model⟩⟩

/-- Interpret an already accepted collection from its actual native gather,
deriving all owner and dependency-cache agreements from the target history. -/
noncomputable def Collection.reconciledModel {request : Request registry}
    (collection : Collection base request) (following : base.Realization)
    (reference : Model (Context.ofBase base) K)
    (produced : request.gatherReconciled? base = some collection) :
    Shared.Model (reader := OwnerReader.reconciled following reference)
      collection.shared following reference :=
  Shared.Model.ofReconciledGather following reference request.owners collection.shared
    (Request.gatherReconciled?_shared base request collection produced)

/-- Every finite live request survives actual shared enlargement. The new
collection carries its factory-derived model, ready for another enlargement. -/
theorem Collection.enlargeReconciled?_models {base : BaseContext.PackedContext registry}
    {request : Request registry} (original : Collection base request)
    {following : base.Realization} {reference : Model (Context.ofBase base) K}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference) original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) :
    ∃ result, original.enlarge? = some result ∧
      ∃ returned : Shared.Model (reader := OwnerReader.reconciled following.infinitesimal
          (Model.next base reference ambient)) result.shared.shared following.infinitesimal
          (Model.next base reference ambient),
        returned.target.value result.shared.parameter = ambient.inclusion Hex.RationalFn.X ∧
          ∃ previous : Inclusion.Model result.shared.previous
              (model.target.liftInfinitesimal ambient),
            previous.target = returned.target := by
  obtain ⟨packet, built, returned, parameter, previous, aligned⟩ := model.enlargeReconciled ambient
  obtain ⟨frames, checked⟩ := request.transport?_success packet.shared.maps
    returned.target returned.owners
  obtain ⟨result, produced, same⟩ := original.enlarge?_of_success packet built frames checked
  refine ⟨result, produced, ?_⟩
  rw [same]
  exact ⟨returned, parameter, previous, aligned⟩

private theorem Enlargement.reconciledModel_exists {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model (reader := OwnerReader.reconciled following reference) original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K))
    (produced : original.enlarge? = some result) :
    ∃ returned : Shared.Model (reader := OwnerReader.reconciled following.infinitesimal
        (Model.next base reference ambient)) result.collection.shared following.infinitesimal
        (Model.next base reference ambient),
      returned.target.value result.parameter = ambient.inclusion Hex.RationalFn.X ∧
        ∃ previous : Inclusion.Model result.previous (oldModel.target.liftInfinitesimal ambient),
          previous.target = returned.target := by
  apply result.project (fun shared _ previous parameter =>
    ∃ returned : Shared.Model (reader := OwnerReader.reconciled following.infinitesimal
      (Model.next base reference ambient)) shared following.infinitesimal (Model.next base reference ambient),
      returned.target.value parameter = ambient.inclusion Hex.RationalFn.X ∧
        ∃ checked : Inclusion.Model previous (oldModel.target.liftInfinitesimal ambient),
          checked.target = returned.target)
  obtain ⟨next, built, returned, parameter, previous, aligned⟩ := original.enlargeReconciled?_models oldModel ambient
  have same := Option.some.inj (built.symm.trans produced)
  cases same
  exact ⟨returned, parameter, previous, aligned⟩

/-- Retrieve the canonical model of an actual enlargement through its public
collection interface, directly usable by the next enlargement. -/
noncomputable def Enlargement.reconciledModel {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model (reader := OwnerReader.reconciled following reference) original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K))
    (produced : original.enlarge? = some result) :
    Shared.Model (reader := OwnerReader.reconciled following.infinitesimal
      (Model.next base reference ambient)) result.collection.shared following.infinitesimal (Model.next base reference ambient) :=
  Classical.choose (result.reconciledModel_exists oldModel ambient produced)

/-- The public model and parameter retain the actual new infinitesimal. -/
theorem Enlargement.reconciled_parameter {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model (reader := OwnerReader.reconciled following reference) original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result) :
    (result.reconciledModel oldModel ambient produced).target.value result.parameter =
      ambient.inclusion Hex.RationalFn.X :=
  (Classical.choose_spec (result.reconciledModel_exists oldModel ambient produced)).1

/-- The public predecessor inclusion uses exactly the public returned model,
so frame preservation and the next enlargement share one interpretation. -/
theorem Enlargement.reconciled_previous {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model (reader := OwnerReader.reconciled following reference) original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result) :
    ∃ previous : Inclusion.Model result.previous (oldModel.target.liftInfinitesimal ambient),
      previous.target = (result.reconciledModel oldModel ambient produced).target :=
  (Classical.choose_spec (result.reconciledModel_exists oldModel ambient produced)).2

/-- Complete frame preservation uses the public returned canonical model,
which can be passed directly to the next enlargement. -/
theorem Enlargement.preserveReconciled {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model (reader := OwnerReader.reconciled following reference) original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result) :
    let returned := (result.reconciledModel oldModel ambient produced).target
    let old := oldModel.target.liftInfinitesimal ambient
    List.Forall₂ (fun frame refreshed =>
      refreshed.values.map returned.value = frame.values.map old.value ∧
      refreshed.polynomials.map (HexPolyMathlib.Interpret.interpret returned.value returned.zero_iff) =
        frame.polynomials.map (HexPolyMathlib.Interpret.interpret old.value old.zero_iff) ∧
      (refreshed.descriptors.map fun d => d.root returned.value returned.zero_iff returned.one
        returned.add returned.sub returned.mul returned.nat returned.sign) =
      (frame.descriptors.map fun d => d.root old.value old.zero_iff old.one old.add old.sub old.mul
        old.nat old.sign)) original.frames result.collection.frames := by
  obtain ⟨previous, aligned⟩ := result.reconciled_previous oldModel ambient produced
  have preserved := result.semantics previous
  rw [aligned] at preserved
  exact preserved

/-- A selected root inside a composite request still agrees with its actual
refreshed predecessor descriptor after enlargement, through public accessors.
The retained parent model is canonical at the enlarged reference. -/
theorem Enlargement.reconciled_root {base : BaseContext.PackedContext registry}
    {parent : Context registry} (root : Root parent)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (selected : root.selection = .selected descriptor) {pre post : Request registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) (split : request = pre ++ rootRequest root ++ post)
    {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model (reader := OwnerReader.reconciled following reference) original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result) :
    let returned := (result.reconciledModel oldModel ambient produced).target
    ∃ (parentModel : Model parent ambient.Carrier)
        (predecessor child : Frame result.collection.shared.input.context)
        (fresh : SignDet.Descriptor result.collection.shared.input.context.Value Signature
          result.collection.shared.input.context.sign result.collection.shared.input.context.signature)
        (value : result.collection.shared.input.context.Value),
      result.collection.frames[pre.length]? = some predecessor ∧
        result.collection.frames[pre.length + 1]? = some child ∧
        predecessor.descriptors = [fresh] ∧ child.values = [value] ∧
        returned.value value = fresh.root returned.value returned.zero_iff returned.one returned.add
          returned.sub returned.mul returned.nat returned.sign ∧
        parent.reconciledModel? following.infinitesimal (Model.next base reference ambient) = some parentModel ∧
        fresh.root returned.value returned.zero_iff returned.one returned.add returned.sub
          returned.mul returned.nat returned.sign =
        descriptor.root parentModel.value parentModel.zero_iff parentModel.one parentModel.add parentModel.sub
          parentModel.mul parentModel.nat parentModel.sign :=
  Collection.root_agreement root descriptor selected result.collection split (result.reconciledModel oldModel ambient produced)

/-- Every frame of a gathered request keeps its values, polynomial coefficients
and selected roots through two actual enlargements under one composed inclusion. -/
theorem Collection.preserveReconciled_twice {base : BaseContext.PackedContext registry}
    {request : Request registry} (original : Collection base request)
    (following : base.Realization) (reference : Model (Context.ofBase base) K)
    (gathered : request.gatherReconciled? base = some original)
    (ambient : Ambient (Hex.RationalFn K)) (first : Enlargement original)
    (firstProduced : original.enlarge? = some first)
    (nextAmbient : Ambient (Hex.RationalFn ambient.Carrier)) (twice : Enlargement first.collection)
    (twiceProduced : first.collection.enlarge? = some twice) :
    let initial := original.reconciledModel following reference gathered
    let once := first.reconciledModel initial ambient firstProduced
    let returned := (twice.reconciledModel once nextAmbient twiceProduced).target
    let inclusion := (Ambient.coefficientHom nextAmbient).comp (Ambient.coefficientHom ambient)
    List.Forall₂ (fun frame refreshed =>
      refreshed.values.map returned.value = frame.values.map (fun v => inclusion (initial.target.value v)) ∧
      refreshed.polynomials.map (HexPolyMathlib.Interpret.interpret returned.value returned.zero_iff) =
        frame.polynomials.map (fun p =>
          (HexPolyMathlib.Interpret.interpret initial.target.value initial.target.zero_iff p).map inclusion) ∧
      refreshed.descriptors.map (selectedValue returned) =
        frame.descriptors.map (fun d => inclusion (selectedValue initial.target d)))
      original.frames twice.collection.frames := by
  let initial := original.reconciledModel following reference gathered
  let once := first.reconciledModel initial ambient firstProduced
  obtain ⟨previous, aligned⟩ := first.reconciled_previous initial ambient firstProduced
  obtain ⟨next, nextAligned⟩ := twice.reconciled_previous once nextAmbient twiceProduced
  have previousSame : previous.target = once.target := aligned
  let checked : Inclusion.Model twice.previous (previous.target.liftInfinitesimal nextAmbient) :=
    previousSame.symm ▸ next
  have result := first.preserve_pair initial.target ambient previous nextAmbient twice checked
  have castTarget (a b : Model first.collection.shared.input.context ambient.Carrier)
      (same : a = b) (entry : Inclusion.Model twice.previous (a.liftInfinitesimal nextAmbient)) :
      ((same ▸ entry) : Inclusion.Model twice.previous
        (b.liftInfinitesimal nextAmbient)).target = entry.target := by
    cases same
    rfl
  have targetSame : checked.target = next.target := castTarget _ _ previousSame.symm next
  rw [targetSame, nextAligned] at result
  exact result

end Hex.RealClosure.Tower.Live

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciled?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciled?_models

/-- info: 'Hex.RealClosure.Tower.Live.Collection.reconciledModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Collection.reconciledModel

/-- info: 'Hex.RealClosure.Tower.Live.Collection.enlargeReconciled?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Collection.enlargeReconciled?_models

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.reconciledModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.reconciledModel

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.preserveReconciled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.preserveReconciled

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.reconciled_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.reconciled_root

/-- info: 'Hex.RealClosure.Tower.Live.Collection.preserveReconciled_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Collection.preserveReconciled_twice
