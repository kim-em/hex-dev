/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveRequest
public import HexRealClosureMathlib.CacheGather
public import HexRealClosureMathlib.TowerRoots
public import HexRealClosureMathlib.SharedPresentation

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

private theorem root_frames {base : BaseContext.PackedContext registry} {parent target : Context registry}
    (root : Root parent)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (selected : root.selection = .selected descriptor)
    (pre post : Request registry) {following : base.Realization}
    {reference : Model (Context.ofBase base) K} (targetModel : Model target K)
    (maps : Inclusions target (Request.owners (pre ++ rootRequest root ++ post)))
    (owners : Inclusions.Models targetModel maps)
    (canonical : ∀ i : Fin (Request.owners (pre ++ rootRequest root ++ post)).length,
      ((Request.owners (pre ++ rootRequest root ++ post))[i]).model? following reference = some (owners.get i).1)
    (frames : List (Frame target))
    (produced : Request.transport? (pre ++ rootRequest root ++ post) maps = some frames) :
    ∃ (predecessor child : Frame target)
        (fresh : SignDet.Descriptor target.Value Signature target.sign target.signature)
        (value : target.Value),
      frames[pre.length]? = some predecessor ∧ frames[pre.length + 1]? = some child ∧
        predecessor.descriptors = [fresh] ∧ child.values = [value] ∧
        targetModel.value value = fresh.root targetModel.value targetModel.zero_iff targetModel.one
          targetModel.add targetModel.sub targetModel.mul targetModel.nat targetModel.sign := by
  induction pre generalizing frames with
  | nil =>
    cases root with
    | point value => simp [Root.selection] at selected
    | selected original extension built =>
      simp only [Root.selection, Isolation.Root.selected.injEq] at selected
      cases selected
      cases built
      let root : Root parent := .selected descriptor (parent.adjoin descriptor) rfl
      let request := rootRequest root ++ post
      let firstIndex : Fin request.length := ⟨0, by simp [request, rootRequest, root]⟩
      let secondIndex : Fin request.length := ⟨1, by simp [request, rootRequest, root]⟩
      obtain ⟨predecessor, firstAt, firstBuilt⟩ := Request.transport?_frame request maps frames produced firstIndex
      obtain ⟨child, secondAt, secondBuilt⟩ := Request.transport?_frame request maps frames produced secondIndex
      let ownerIndex : Fin request.owners.length := ⟨0, by simp [request, Request.owners, rootRequest, root]⟩
      let childIndex : Fin request.owners.length := ⟨1, by simp [request, Request.owners, rootRequest, root]⟩
      have raw := Frame.transport?_descriptors (request.frame firstIndex) (maps.get ownerIndex) predecessor firstBuilt
      have length : predecessor.descriptors.length = 1 := by
        have measured := congrArg List.length raw
        simp only [List.length_map] at measured
        exact measured
      obtain ⟨fresh, only⟩ := List.length_eq_one_iff.mp length
      let originalModel : Model parent K := (owners.get ownerIndex).1
      have originalProduced : parent.model? following reference = some originalModel := canonical ownerIndex
      have childProduced := root.model?_ofModel following reference originalModel originalProduced
      have childSame : (owners.get childIndex).1 = root.model originalModel :=
        Option.some.inj ((canonical childIndex).symm.trans childProduced)
      have childValue := (owners.get childIndex).2.val.value root.value
      rw [(owners.get childIndex).2.property, childSame] at childValue
      have childValues := Frame.transport?_values (request.frame secondIndex) (maps.get childIndex) child secondBuilt
      have roots := Frame.transport?_root (owners.get ownerIndex).2.val (request.frame firstIndex) predecessor firstBuilt
      rw [(owners.get ownerIndex).2.property, only] at roots
      change [fresh.root targetModel.value targetModel.zero_iff targetModel.one
        targetModel.add targetModel.sub targetModel.mul targetModel.nat targetModel.sign] =
        [descriptor.root originalModel.value originalModel.zero_iff originalModel.one originalModel.add
          originalModel.sub originalModel.mul originalModel.nat originalModel.sign] at roots
      refine ⟨predecessor, child, fresh, (maps.get childIndex).value root.value,
        firstAt, secondAt, only, childValues, ?_⟩
      rw [childValue]
      change root.denote originalModel = _
      exact (root.denote_selection originalModel).trans (List.cons.inj roots |>.1).symm
  | cons entry pre ih =>
    cases entry with
    | mk owner frame =>
      cases maps with
      | cons inclusion remaining =>
        cases owners with
        | cons original checked aligned later =>
          obtain ⟨first, tail, firstBuilt, tailBuilt, same⟩ :=
            Request.transport?_cons frame (pre ++ rootRequest root ++ post) inclusion remaining frames produced
          cases same
          have canonicalTail (i : Fin (Request.owners (pre ++ rootRequest root ++ post)).length) :
              ((Request.owners (pre ++ rootRequest root ++ post))[i]).model? following reference = some (later.get i).1 := by
            exact canonical ⟨i.val + 1, by
              change i.val + 1 < (Request.owners (pre ++ rootRequest root ++ post)).length + 1
              exact Nat.succ_lt_succ i.isLt⟩
          obtain ⟨predecessor, child, fresh, value, firstAt, secondAt, only, values, meaning⟩ :=
            ih remaining later canonicalTail tail tailBuilt
          refine ⟨predecessor, child, fresh, value, ?_, ?_, only, values, meaning⟩
          · simpa only [List.length_cons, List.getElem?_cons_succ] using firstAt
          · simpa only [List.length_cons, Nat.succ_add, List.getElem?_cons_succ] using secondAt

/-- In a composite request, the actual retained child value equals the root
selected by its refreshed predecessor descriptor at the original offsets.
Both interpretations are derived from the collection's canonical factory. -/
theorem Collection.root_agreement {base : BaseContext.PackedContext registry}
    {parent : Context registry} (root : Root parent)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (selected : root.selection = .selected descriptor) {pre post : Request registry}
    {request : Request registry} (collection : Collection base request)
    (split : request = pre ++ rootRequest root ++ post)
    {following : base.Realization} {reference : Model (Context.ofBase base) K}
    (model : Shared.Model collection.shared following reference) :
    ∃ (predecessor child : Frame collection.shared.input.context)
        (fresh : SignDet.Descriptor collection.shared.input.context.Value Signature
          collection.shared.input.context.sign collection.shared.input.context.signature)
        (value : collection.shared.input.context.Value),
      collection.frames[pre.length]? = some predecessor ∧
        collection.frames[pre.length + 1]? = some child ∧
        predecessor.descriptors = [fresh] ∧ child.values = [value] ∧
        model.target.value value = fresh.root model.target.value model.target.zero_iff model.target.one
          model.target.add model.target.sub model.target.mul model.target.nat model.target.sign := by
  subst request
  exact root_frames root descriptor selected pre post model.target collection.shared.maps model.owners
    model.canonicalOwners collection.frames collection.produced

/-- Across enlargement, each refreshed frame preserves the ordered values,
coefficients and selected roots of the old frame in its lifted model. -/
theorem Enlargement.semantics {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original)
    {oldModel : Model original.shared.input.context K}
    (previous : Inclusion.Model result.previous oldModel) :
    List.Forall₂ (fun frame refreshed =>
      refreshed.values.map previous.target.value = frame.values.map oldModel.value ∧
      refreshed.polynomials.map
          (HexPolyMathlib.Interpret.interpret previous.target.value previous.target.zero_iff) =
        frame.polynomials.map (HexPolyMathlib.Interpret.interpret oldModel.value oldModel.zero_iff) ∧
      (refreshed.descriptors.map fun d => d.root previous.target.value previous.target.zero_iff
        previous.target.one previous.target.add previous.target.sub previous.target.mul
        previous.target.nat previous.target.sign) =
      (frame.descriptors.map fun d => d.root oldModel.value oldModel.zero_iff oldModel.one oldModel.add
        oldModel.sub oldModel.mul oldModel.nat oldModel.sign)) original.frames result.collection.frames :=
  Frame.transportList_semantics previous original.frames result.collection.frames
    (result.transport previous.zero)

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

private theorem Enlargement.model_exists {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K))
    (produced : original.enlarge? = some result) :
    ∃ returned : Shared.Model result.collection.shared following.infinitesimal
        (Model.next base reference ambient),
      returned.target.value result.parameter = ambient.inclusion Hex.RationalFn.X ∧
        ∃ previous : Inclusion.Model result.previous (oldModel.target.liftInfinitesimal ambient),
          previous.target = returned.target := by
  apply result.project (fun shared _ previous parameter =>
    ∃ returned : Shared.Model shared following.infinitesimal (Model.next base reference ambient),
      returned.target.value parameter = ambient.inclusion Hex.RationalFn.X ∧
        ∃ checked : Inclusion.Model previous (oldModel.target.liftInfinitesimal ambient),
          checked.target = returned.target)
  obtain ⟨next, built, returned, parameter, previous, aligned⟩ := original.enlarge?_models oldModel ambient
  have same := Option.some.inj (built.symm.trans produced)
  cases same
  exact ⟨returned, parameter, previous, aligned⟩

/-- Retrieve the canonical model of an actual enlargement through its public
collection interface, directly usable by the next enlargement. -/
noncomputable def Enlargement.model {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K))
    (produced : original.enlarge? = some result) :
    Shared.Model result.collection.shared following.infinitesimal (Model.next base reference ambient) :=
  Classical.choose (result.model_exists oldModel ambient produced)

/-- The public model and parameter retain the actual new infinitesimal. -/
theorem Enlargement.model_parameter {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result) :
    (result.model oldModel ambient produced).target.value result.parameter =
      ambient.inclusion Hex.RationalFn.X :=
  (Classical.choose_spec (result.model_exists oldModel ambient produced)).1

/-- The public predecessor inclusion uses exactly the public returned model,
so frame preservation and the next enlargement share one interpretation. -/
theorem Enlargement.model_previous {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result) :
    ∃ previous : Inclusion.Model result.previous (oldModel.target.liftInfinitesimal ambient),
      previous.target = (result.model oldModel ambient produced).target :=
  (Classical.choose_spec (result.model_exists oldModel ambient produced)).2

/-- Complete frame preservation uses the public returned canonical model,
which can be passed directly to the next enlargement. -/
theorem Enlargement.preserve {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result) :
    let returned := (result.model oldModel ambient produced).target
    let old := oldModel.target.liftInfinitesimal ambient
    List.Forall₂ (fun frame refreshed =>
      refreshed.values.map returned.value = frame.values.map old.value ∧
      refreshed.polynomials.map (HexPolyMathlib.Interpret.interpret returned.value returned.zero_iff) =
        frame.polynomials.map (HexPolyMathlib.Interpret.interpret old.value old.zero_iff) ∧
      (refreshed.descriptors.map fun d => d.root returned.value returned.zero_iff returned.one
        returned.add returned.sub returned.mul returned.nat returned.sign) =
      (frame.descriptors.map fun d => d.root old.value old.zero_iff old.one old.add old.sub old.mul
        old.nat old.sign)) original.frames result.collection.frames := by
  obtain ⟨previous, aligned⟩ := result.model_previous oldModel ambient produced
  have preserved := result.semantics previous
  rw [aligned] at preserved
  exact preserved

/-- A selected root inside a composite request still agrees with its actual
refreshed predecessor descriptor after enlargement, through public accessors. -/
theorem Enlargement.root_agreement {base : BaseContext.PackedContext registry}
    {parent : Context registry} (root : Root parent)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (selected : root.selection = .selected descriptor) {pre post : Request registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) (split : request = pre ++ rootRequest root ++ post)
    {following : base.Realization}
    {reference : Model (Context.ofBase base) K}
    (oldModel : Shared.Model original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (produced : original.enlarge? = some result) :
    let returned := (result.model oldModel ambient produced).target
    ∃ (predecessor child : Frame result.collection.shared.input.context)
        (fresh : SignDet.Descriptor result.collection.shared.input.context.Value Signature
          result.collection.shared.input.context.sign result.collection.shared.input.context.signature)
        (value : result.collection.shared.input.context.Value),
      result.collection.frames[pre.length]? = some predecessor ∧
        result.collection.frames[pre.length + 1]? = some child ∧
        predecessor.descriptors = [fresh] ∧ child.values = [value] ∧
        returned.value value = fresh.root returned.value returned.zero_iff returned.one returned.add
          returned.sub returned.mul returned.nat returned.sign :=
  Collection.root_agreement root descriptor selected result.collection split (result.model oldModel ambient produced)

/-- Public consumer: both root pairs remain accessible after two enlargements,
without changing the request index or casting a collection. -/
example {base : BaseContext.PackedContext registry} {firstParent secondParent : Context registry}
    (firstRoot : Root firstParent) (secondRoot : Root secondParent)
    (firstDescriptor : SignDet.Descriptor firstParent.Value Signature firstParent.sign firstParent.signature)
    (secondDescriptor : SignDet.Descriptor secondParent.Value Signature secondParent.sign secondParent.signature)
    (firstSelected : firstRoot.selection = .selected firstDescriptor)
    (secondSelected : secondRoot.selection = .selected secondDescriptor)
    (operands : Request registry)
    (original : Collection base (rootRequest firstRoot ++ rootRequest secondRoot ++ operands))
    {following : base.Realization} {reference : Model (Context.ofBase base) K}
    (model : Shared.Model original.shared following reference)
    (ambient : Ambient (Hex.RationalFn K)) (first : Enlargement original)
    (firstProduced : original.enlarge? = some first)
    (nextAmbient : Ambient (Hex.RationalFn ambient.Carrier)) (twice : Enlargement first.collection)
    (twiceProduced : first.collection.enlarge? = some twice) :
    ∃ a b c d : Frame twice.collection.shared.input.context,
      twice.collection.frames[0]? = some a ∧ twice.collection.frames[1]? = some b ∧
      twice.collection.frames[2]? = some c ∧ twice.collection.frames[3]? = some d := by
  have firstSplit : (rootRequest firstRoot ++ rootRequest secondRoot ++ operands) =
      [] ++ rootRequest firstRoot ++ (rootRequest secondRoot ++ operands) := by
    simp only [List.nil_append, List.append_assoc]
  have firstAgreement := original.root_agreement firstRoot firstDescriptor firstSelected
    (pre := []) (post := rootRequest secondRoot ++ operands) firstSplit model
  have secondAgreement := original.root_agreement secondRoot secondDescriptor secondSelected
    (pre := rootRequest firstRoot) (post := operands) rfl model
  have firstModel := first.model model ambient firstProduced
  obtain ⟨a, b, _, _, atA, atB, _⟩ := twice.root_agreement firstRoot firstDescriptor firstSelected
    (pre := []) (post := rootRequest secondRoot ++ operands) firstSplit firstModel nextAmbient twiceProduced
  obtain ⟨c, d, _, _, atC, atD, _⟩ := twice.root_agreement secondRoot secondDescriptor secondSelected
    (pre := rootRequest firstRoot) (post := operands) rfl firstModel nextAmbient twiceProduced
  refine ⟨a, b, c, d, atA, atB, ?_, ?_⟩
  · simpa only [rootRequest_length firstRoot firstDescriptor firstSelected] using atC
  · simpa only [rootRequest_length firstRoot firstDescriptor firstSelected] using atD

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

/-- info: 'Hex.RealClosure.Tower.Live.Collection.root_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Collection.root_agreement

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.model

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.model_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.model_parameter

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.model_previous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.model_previous

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.preserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.preserve

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.root_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.root_agreement
