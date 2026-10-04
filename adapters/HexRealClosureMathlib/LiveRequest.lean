/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveRequest
public import HexRealClosureMathlib.CacheGather
public import HexRealClosureMathlib.TowerRoots

public section

namespace Hex.RealClosure.Tower.Live

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {owner target : Context registry}
variable {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K]

private noncomputable def nativeModel {inclusion : Inclusion owner target}
    {original : Model owner K} (model : Inclusion.Model inclusion original) :
    Conversion.Model inclusion.native original where
  target := model.target
  value := model.value

/-- Descriptor rechecking adds no failure to a checked value-preserving
inclusion into the common ordered real closed model. -/
theorem Frame.transport?_success (frame : Frame owner) (inclusion : Inclusion owner target)
    (original : Model owner K) (model : Inclusion.Model inclusion original) :
    ∃ result, frame.transport? inclusion = some result := by
  have each (descriptor : SignDet.Descriptor owner.Value Signature owner.sign owner.signature) :
      ∃ converted, SignDet.Descriptor.validate target.sign target.signature
        (owner.mapDescriptor target inclusion.value descriptor) = some converted :=
    (nativeModel model).descriptor_exists descriptor
  have success : ∀ descriptors : List
      (SignDet.Descriptor owner.Value Signature owner.sign owner.signature),
      ∃ converted, descriptors.mapM (fun descriptor =>
        SignDet.Descriptor.validate target.sign target.signature
          (owner.mapDescriptor target inclusion.value descriptor)) = some converted := by
    intro descriptors
    induction descriptors with
    | nil => exact ⟨[], rfl⟩
    | cons descriptor rest ih =>
      obtain ⟨next, checked⟩ := each descriptor
      obtain ⟨remaining, later⟩ := ih
      exact ⟨next :: remaining, by simp [List.mapM_cons, checked, later]⟩
  obtain ⟨descriptors, checked⟩ := success frame.descriptors
  exact ⟨⟨frame.values.map inclusion.value, frame.polynomials.map inclusion.polynomial,
    descriptors⟩, by simp [Frame.transport?, checked]⟩

/-- Every requested value keeps its original meaning in the common target. -/
theorem Frame.transport?_value {inclusion : Inclusion owner target}
    {original : Model owner K} (model : Inclusion.Model inclusion original)
    (frame : Frame owner) (result : Frame target) (produced : frame.transport? inclusion = some result) :
    result.values.map model.target.value = frame.values.map original.value := by
  rw [Frame.transport?_values frame inclusion result produced, List.map_map]
  simp only [Function.comp_def, model.value]

/-- Requested polynomials retain their complete interpreted coefficients. -/
theorem Frame.transport?_polynomial {inclusion : Inclusion owner target}
    {original : Model owner K} (model : Inclusion.Model inclusion original)
    (frame : Frame owner) (result : Frame target) (produced : frame.transport? inclusion = some result) :
    result.polynomials.map (HexPolyMathlib.Interpret.interpret model.target.value model.target.zero_iff) =
      frame.polynomials.map (HexPolyMathlib.Interpret.interpret original.value original.zero_iff) := by
  rw [Frame.transport?_polynomials frame inclusion result produced, List.map_map]
  simp only [Function.comp_def, model.polynomial]

/-- Fresh descriptor evidence selects the same roots as the original frame,
in the same order, including its transported interval endpoints. -/
theorem Frame.transport?_root {inclusion : Inclusion owner target}
    {original : Model owner K} (model : Inclusion.Model inclusion original)
    (frame : Frame owner) (result : Frame target) (produced : frame.transport? inclusion = some result) :
    (result.descriptors.map fun descriptor => descriptor.root model.target.value model.target.zero_iff
      model.target.one model.target.add model.target.sub model.target.mul model.target.nat model.target.sign) =
    (frame.descriptors.map fun descriptor => descriptor.root original.value original.zero_iff
      original.one original.add original.sub original.mul original.nat original.sign) := by
  have bindings := Frame.transport?_descriptors frame inclusion result produced
  have preserved : ∀ descriptors : List
      (SignDet.Descriptor owner.Value Signature owner.sign owner.signature),
      ∀ converted : List (SignDet.Descriptor target.Value Signature target.sign target.signature),
      converted.map (·.raw) = descriptors.map (owner.mapDescriptor target inclusion.value) →
      (converted.map fun d => d.root model.target.value model.target.zero_iff model.target.one
        model.target.add model.target.sub model.target.mul model.target.nat model.target.sign) =
      (descriptors.map fun d => d.root original.value original.zero_iff original.one original.add
        original.sub original.mul original.nat original.sign) := by
    intro descriptors
    induction descriptors with
    | nil =>
      intro converted checked
      cases converted with
      | nil => rfl
      | cons next rest => simp at checked
    | cons descriptor rest ih =>
      intro converted checked
      cases converted with
      | nil => simp at checked
      | cons next remaining =>
        obtain ⟨first, later⟩ := List.cons.inj checked
        simp only [List.map_cons]
        have rootSame := (nativeModel model).root descriptor next first
        simp only [nativeModel] at rootSame
        exact congrArg₂ List.cons rootSame (ih remaining later)
  exact preserved frame.descriptors result.descriptors bindings

/-- A transported child generator is exactly the root selected by the
refreshed predecessor descriptor in their common model. -/
theorem Frame.selected_agreement {parent : Context registry} (original : Model parent K)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (parentMap : Inclusion parent target)
    (childMap : Inclusion (parent.adjoin descriptor).context target)
    (parentModel : Inclusion.Model parentMap original)
    (childModel : Inclusion.Model childMap (original.adjoin descriptor))
    (aligned : childModel.target = parentModel.target)
    (converted : SignDet.Descriptor target.Value Signature target.sign target.signature)
    (binding : converted.raw = parent.mapDescriptor target parentMap.value descriptor) :
    parentModel.target.value (childMap.value (parent.adjoin descriptor).generator) =
      converted.root parentModel.target.value parentModel.target.zero_iff parentModel.target.one
        parentModel.target.add parentModel.target.sub parentModel.target.mul parentModel.target.nat
        parentModel.target.sign := by
  rw [← aligned, childModel.value, original.adjoin_generator]
  have preserved := (nativeModel parentModel).root descriptor converted binding
  simp only [nativeModel] at preserved
  rw [aligned]
  exact preserved.symm

/-- The two entries requested by an actual selected root denote the same
root after transport: its cached child value equals the refreshed descriptor. -/
theorem rootRequest_semantics {parent : Context registry} (root : Root parent)
    (original : Model parent K)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (selected : root.selection = .selected descriptor)
    (parentMap : Inclusion parent target) (childMap : Inclusion root.context target)
    (parentModel : Inclusion.Model parentMap original)
    (childModel : Inclusion.Model childMap (root.model original))
    (aligned : childModel.target = parentModel.target)
    (converted : SignDet.Descriptor target.Value Signature target.sign target.signature)
    (binding : converted.raw = parent.mapDescriptor target parentMap.value descriptor) :
    parentModel.target.value (childMap.value root.value) =
      converted.root parentModel.target.value parentModel.target.zero_iff parentModel.target.one
        parentModel.target.add parentModel.target.sub parentModel.target.mul parentModel.target.nat
        parentModel.target.sign := by
  rw [← aligned, childModel.value]
  change root.denote original = _
  rw [root.denote_selection original, selected]
  change descriptor.root original.value original.zero_iff original.one original.add original.sub
    original.mul original.nat original.sign = _
  rw [aligned]
  have preserved := (nativeModel parentModel).root descriptor converted binding
  simp only [nativeModel] at preserved
  exact preserved.symm

/-- All frames transported through one inclusion preserve their ordered value,
coefficient and selected-root lists in the same target model. -/
theorem Frame.transportList_semantics {inclusion : Inclusion owner target}
    {original : Model owner K} (model : Inclusion.Model inclusion original)
    (frames : List (Frame owner)) (converted : List (Frame target))
    (produced : frames.mapM (fun frame => frame.transport? inclusion) = some converted) :
    List.Forall₂ (fun frame result =>
      result.values.map model.target.value = frame.values.map original.value ∧
      result.polynomials.map (HexPolyMathlib.Interpret.interpret model.target.value model.target.zero_iff) =
        frame.polynomials.map (HexPolyMathlib.Interpret.interpret original.value original.zero_iff) ∧
      (result.descriptors.map fun d => d.root model.target.value model.target.zero_iff model.target.one
        model.target.add model.target.sub model.target.mul model.target.nat model.target.sign) =
      (frame.descriptors.map fun d => d.root original.value original.zero_iff original.one
        original.add original.sub original.mul original.nat original.sign)) frames converted := by
  induction frames generalizing converted with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at produced
    cases produced
    exact .nil
  | cons frame rest ih =>
    cases first : frame.transport? inclusion with
    | none => simp [List.mapM_cons, first] at produced
    | some result =>
      cases later : rest.mapM (fun frame => frame.transport? inclusion) with
      | none => simp [List.mapM_cons, first, later] at produced
      | some tail =>
        simp only [List.mapM_cons, first, later, bind, Option.bind, pure, Option.some.injEq] at produced
        cases produced
        exact .cons ⟨frame.transport?_value model result first,
          frame.transport?_polynomial model result first, frame.transport?_root model result first⟩
          (ih tail later)

/-- Transport succeeds for every finite frame family in one common model.
The checked inclusion family supplies all descriptor validity premises. -/
theorem Request.transport?_success {target : Context registry}
    (request : Request registry) (maps : Inclusions target request.owners)
    (model : Model target K) (owners : Inclusions.Models model maps) :
    ∃ frames, Request.transport? request maps = some frames := by
  induction request with
  | nil =>
    cases maps
    exact ⟨[], rfl⟩
  | cons frame rest ih =>
    cases frame with
    | mk owner frame =>
      cases maps with
      | cons inclusion remaining =>
        cases owners with
        | cons original checked aligned later =>
          obtain ⟨first, firstProduced⟩ := frame.transport?_success inclusion original checked
          obtain ⟨tail, tailProduced⟩ := ih remaining later
          exact ⟨first :: tail, by simp [Request.transport?, firstProduced, tailProduced]⟩

/-- Every actual output frame preserves the requested value, coefficient and
selected-root lists in the single common model, at its original position. -/
theorem Request.transport?_semantics {target : Context registry}
    (request : Request registry) (maps : Inclusions target request.owners)
    (model : Model target K) (owners : Inclusions.Models model maps)
    (frames : List (Frame target)) (produced : Request.transport? request maps = some frames)
    (index : Fin request.length) :
    let original := (owners.get ⟨index.val, by simpa [Request.owners] using index.isLt⟩).1
    ∃ frame, frames[index.val]? = some frame ∧
      frame.values.map model.value = (request.frame index).values.map original.value ∧
      frame.polynomials.map (HexPolyMathlib.Interpret.interpret model.value model.zero_iff) =
        (request.frame index).polynomials.map
          (HexPolyMathlib.Interpret.interpret original.value original.zero_iff) ∧
      (frame.descriptors.map fun d => d.root model.value model.zero_iff model.one model.add
        model.sub model.mul model.nat model.sign) =
      ((request.frame index).descriptors.map fun d => d.root original.value original.zero_iff
        original.one original.add original.sub original.mul original.nat original.sign) := by
  obtain ⟨frame, atIndex, checked⟩ := request.transport?_frame maps frames produced index
  let interpreted := owners.get ⟨index.val, by simpa [Request.owners] using index.isLt⟩
  have values := Frame.transport?_value interpreted.2.val (request.frame index) frame checked
  have polynomials := Frame.transport?_polynomial interpreted.2.val (request.frame index) frame checked
  have roots := Frame.transport?_root interpreted.2.val (request.frame index) frame checked
  have aligned := interpreted.2.property
  rw [aligned] at values polynomials roots
  exact ⟨frame, atIndex, values, polynomials, roots⟩

/-- Gathering constructs a shared model and transports every requested value,
polynomial and descriptor from the canonical owner factory. -/
theorem Request.gather?_models {base : BaseContext.PackedContext registry}
    (following : base.Realization) (reference : Model (Context.ofBase base) K)
    (request : Request registry)
    (compatible : ∀ source ∈ request.owners,
      source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, request.gather? base = some result ∧
      Nonempty (Shared.Model result.shared following reference) := by
  obtain ⟨shared, gathered, ⟨model⟩⟩ :=
    Shared.gather?_models following reference request.owners compatible
  obtain ⟨frames, checked⟩ := request.transport?_success shared.maps model.target model.owners
  obtain ⟨result, produced, same⟩ := request.gather?_of_success base shared gathered frames checked
  exact ⟨result, produced, ⟨same.symm ▸ model⟩⟩

/-- Interpret an actual gathered collection through its canonical owner
factory, deriving compatibility from the successful native producer. -/
noncomputable def Collection.model {base : BaseContext.PackedContext registry}
    {request : Request registry} (collection : Collection base request)
    (following : base.Realization) (reference : Model (Context.ofBase base) K)
    (produced : request.gather? base = some collection) :
    Shared.Model collection.shared following reference :=
  Shared.Model.ofGather following reference request.owners collection.shared
    (Request.gather?_shared base request collection produced)

/-- Across enlargement, each refreshed frame preserves the ordered values,
coefficients and selected roots of the old frame in its lifted model. -/
theorem Enlargement.semantics {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original)
    {oldModel : Model original.shared.input.context K}
    (previous : Inclusion.Model result.shared.previous oldModel) :
    List.Forall₂ (fun frame refreshed =>
      refreshed.values.map previous.target.value = frame.values.map oldModel.value ∧
      refreshed.polynomials.map
          (HexPolyMathlib.Interpret.interpret previous.target.value previous.target.zero_iff) =
        frame.polynomials.map (HexPolyMathlib.Interpret.interpret oldModel.value oldModel.zero_iff) ∧
      (refreshed.descriptors.map fun d => d.root previous.target.value previous.target.zero_iff
        previous.target.one previous.target.add previous.target.sub previous.target.mul
        previous.target.nat previous.target.sign) =
      (frame.descriptors.map fun d => d.root oldModel.value oldModel.zero_iff oldModel.one oldModel.add
        oldModel.sub oldModel.mul oldModel.nat oldModel.sign)) original.frames result.frames :=
  Frame.transportList_semantics previous original.frames result.frames
    (result.frames_oneHop previous.zero)

/-- Every finite live request survives actual shared enlargement. The new
collection carries its factory-derived model, ready for another enlargement. -/
theorem Collection.enlarge?_models {base : BaseContext.PackedContext registry}
    {request : Request registry} (original : Collection base request)
    {following : base.Realization} {reference : Model (Context.ofBase base) K}
    (model : Shared.Model original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) :
    ∃ result, original.enlarge? = some result ∧
      ∃ returned : Shared.Model result.shared.shared following.infinitesimal
          (Model.next base reference ambient),
        returned.target.value result.shared.parameter = ambient.inclusion Hex.RationalFn.X ∧
          ∃ previous : Inclusion.Model result.shared.previous
              (model.target.liftInfinitesimal ambient),
            previous.target = returned.target := by
  obtain ⟨packet, built, returned, parameter, previous, aligned⟩ := model.enlarge ambient
  obtain ⟨frames, checked⟩ := request.transport?_success packet.shared.maps
    returned.target returned.owners
  obtain ⟨result, produced, same⟩ := original.enlarge?_of_success packet built frames checked
  refine ⟨result, produced, ?_⟩
  rw [same]
  exact ⟨returned, parameter, previous, aligned⟩

end Hex.RealClosure.Tower.Live

/-- info: 'Hex.RealClosure.Tower.Live.Frame.transport?_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Frame.transport?_root
/-- info: 'Hex.RealClosure.Tower.Live.Request.transport?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.transport?_success
/-- info: 'Hex.RealClosure.Tower.Live.Request.transport?_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.transport?_semantics
/-- info: 'Hex.RealClosure.Tower.Live.Request.gather?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gather?_models
/-- info: 'Hex.RealClosure.Tower.Live.Collection.enlarge?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Collection.enlarge?_models

/-- info: 'Hex.RealClosure.Tower.Live.Frame.selected_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Frame.selected_agreement

/-- info: 'Hex.RealClosure.Tower.Live.Frame.transportList_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Frame.transportList_semantics

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.semantics

/-- info: 'Hex.RealClosure.Tower.Live.rootRequest_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.rootRequest_semantics
