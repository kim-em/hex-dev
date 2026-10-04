/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveContext
public import HexRealClosure.TowerRoots

public section

namespace Hex.RealClosure.Tower.Live

variable {registry : BaseContext.Registry}

/-- Live operands and checked root descriptors owned by one immutable context.
Each context retains the complete coefficient ancestry of these operands. -/
structure Frame (owner : Context registry) where
  values : List owner.Value := []
  polynomials : List owner.Poly := []
  descriptors : List (SignDet.Descriptor owner.Value Signature owner.sign owner.signature) := []

/-- Map live operands through one checked inclusion. Root descriptors are
validated again against the actual target and its new literal binding. -/
@[expose] def Frame.transport? {owner target : Context registry} (frame : Frame owner)
    (inclusion : Inclusion owner target) : Option (Frame target) := do
  let descriptors ← frame.descriptors.mapM fun descriptor =>
    SignDet.Descriptor.validate target.sign target.signature
      (owner.mapDescriptor target inclusion.value descriptor)
  return ⟨frame.values.map inclusion.value, frame.polynomials.map inclusion.polynomial,
    descriptors⟩

/-- Successful transport applies the retained map to every requested value. -/
theorem Frame.transport?_values {owner target : Context registry} (frame : Frame owner)
    (inclusion : Inclusion owner target) (result : Frame target)
    (produced : frame.transport? inclusion = some result) :
    result.values = frame.values.map inclusion.value := by
  unfold Frame.transport? at produced
  cases descriptors : frame.descriptors.mapM (fun descriptor =>
      SignDet.Descriptor.validate target.sign target.signature
        (owner.mapDescriptor target inclusion.value descriptor)) with
  | none => simp [descriptors] at produced
  | some converted =>
    simp only [descriptors, bind, Option.bind, pure, Option.some.injEq] at produced
    cases produced
    rfl

/-- Every polynomial uses the same inclusion as the frame's values. -/
theorem Frame.transport?_polynomials {owner target : Context registry} (frame : Frame owner)
    (inclusion : Inclusion owner target) (result : Frame target)
    (produced : frame.transport? inclusion = some result) :
    result.polynomials = frame.polynomials.map inclusion.polynomial := by
  unfold Frame.transport? at produced
  cases descriptors : frame.descriptors.mapM (fun descriptor =>
      SignDet.Descriptor.validate target.sign target.signature
        (owner.mapDescriptor target inclusion.value descriptor)) with
  | none => simp [descriptors] at produced
  | some converted =>
    simp only [descriptors, bind, Option.bind, pure, Option.some.injEq] at produced
    cases produced
    rfl

/-- Fresh descriptors retain the complete mapped head, bounds, derivative
positions and root-selection signs of each original descriptor. -/
theorem Frame.transport?_descriptors {owner target : Context registry} (frame : Frame owner)
    (inclusion : Inclusion owner target) (result : Frame target)
    (produced : frame.transport? inclusion = some result) :
    result.descriptors.map (·.raw) =
      frame.descriptors.map (owner.mapDescriptor target inclusion.value) := by
  have mapped : ∀ descriptors : List
      (SignDet.Descriptor owner.Value Signature owner.sign owner.signature),
      ∀ converted, descriptors.mapM (fun descriptor =>
        SignDet.Descriptor.validate target.sign target.signature
          (owner.mapDescriptor target inclusion.value descriptor)) = some converted →
      converted.map (·.raw) = descriptors.map (owner.mapDescriptor target inclusion.value) := by
    intro descriptors
    induction descriptors with
    | nil =>
      intro converted checked
      simp only [List.mapM_nil, pure, Option.some.injEq] at checked
      cases checked
      rfl
    | cons descriptor rest ih =>
      intro converted checked
      cases first : SignDet.Descriptor.validate target.sign target.signature
          (owner.mapDescriptor target inclusion.value descriptor) with
      | none => simp [List.mapM_cons, first] at checked
      | some next =>
        cases later : rest.mapM (fun descriptor =>
            SignDet.Descriptor.validate target.sign target.signature
              (owner.mapDescriptor target inclusion.value descriptor)) with
        | none => simp [List.mapM_cons, first, later] at checked
        | some remaining =>
          simp only [List.mapM_cons, first, later, bind, Option.bind, pure,
            Option.some.injEq] at checked
          cases checked
          simp only [List.map_cons]
          rw [SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp first),
            ih remaining later]
  unfold Frame.transport? at produced
  cases descriptors : frame.descriptors.mapM (fun descriptor =>
      SignDet.Descriptor.validate target.sign target.signature
        (owner.mapDescriptor target inclusion.value descriptor)) with
  | none => simp [descriptors] at produced
  | some converted =>
    simp only [descriptors, bind, Option.bind, pure, Option.some.injEq] at produced
    cases produced
    exact mapped frame.descriptors converted descriptors

private theorem map_coeff {E F : Type} [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]
    (read : E → F) (zero : read 0 = 0) (p : DensePoly E) (i : Nat) :
    (DensePoly.ofCoeffs (p.toArray.map read)).coeff i = read (p.coeff i) := by
  rw [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : p.toArray[i]? with
  | none =>
    have coefficient : p.coeff i = 0 := by
      rw [← DensePoly.toArray_getD, Array.getD_eq_getD_getElem?, h]
      rfl
    simp only [Option.map_none, Option.getD_none, coefficient, zero]
    rfl
  | some a =>
    have coefficient : p.coeff i = a := by
      rw [← DensePoly.toArray_getD, Array.getD_eq_getD_getElem?, h]
      rfl
    simp only [Option.map_some, Option.getD_some, coefficient]

private theorem map_ofCoeffs {E F : Type} [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]
    (read : E → F) (zero : read 0 = 0) (a : Array E) :
    DensePoly.ofCoeffs ((DensePoly.ofCoeffs a).toArray.map read) =
      DensePoly.ofCoeffs (a.map read) := by
  apply DensePoly.ext_coeff
  intro i
  rw [map_coeff read zero, DensePoly.coeff_ofCoeffs, DensePoly.coeff_ofCoeffs]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : a[i]? with
  | none => simp only [Option.map_none, Option.getD_none]; exact zero
  | some value => simp only [Option.map_some, Option.getD_some]

/-- Successive coefficient transport agrees with the retained composed map.
Only the second inclusion's zero value is needed for normalization. -/
theorem Frame.polynomial_comp {source middle target : Context registry}
    (first : Inclusion source middle) (next : Inclusion middle target)
    (zero : next.value 0 = 0) (p : source.Poly) :
    next.polynomial (first.polynomial p) = (first.comp next).polynomial p := by
  simp only [Inclusion.polynomial]
  rw [map_ofCoeffs next.value zero, Array.map_map]
  congr 1
  apply Array.map_congr_left
  intro a _
  exact (Inclusion.comp_value first next a).symm

private def mapRaw {source target : Context registry} (inclusion : Inclusion source target)
    (raw : SignDet.RawDescriptor source.Value Signature) : SignDet.RawDescriptor target.Value Signature :=
  { context := target.signature, head := inclusion.polynomial raw.head,
    lower := raw.lower.map inclusion.value, upper := raw.upper.map inclusion.value,
    indices := raw.indices, signs := raw.signs }

private theorem mapRaw_comp {source middle target : Context registry}
    (first : Inclusion source middle) (next : Inclusion middle target)
    (zero : next.value 0 = 0) (raw : SignDet.RawDescriptor source.Value Signature) :
    mapRaw next (mapRaw first raw) = mapRaw (first.comp next) raw := by
  cases raw with
  | mk context head lower upper indices signs =>
    simp only [mapRaw, Frame.polynomial_comp first next zero]
    have lowerEq : (lower.map first.value).map next.value = lower.map (first.comp next).value := by
      cases lower <;> simp [Endpoint.map, Inclusion.comp_value]
    have upperEq : (upper.map first.value).map next.value = upper.map (first.comp next).value := by
      cases upper <;> simp [Endpoint.map, Inclusion.comp_value]
    rw [lowerEq, upperEq]

/-- One-hop transport of already converted frames is the original transport
through the retained composed inclusion, including refreshed descriptor data. -/
theorem Frame.transport?_comp {source middle target : Context registry}
    (frame : Frame source) (first : Inclusion source middle) (converted : Frame middle)
    (produced : frame.transport? first = some converted) (next : Inclusion middle target)
    (zero : next.value 0 = 0) :
    converted.transport? next = frame.transport? (first.comp next) := by
  have descriptors := Frame.transport?_descriptors frame first converted produced
  have rawLists : converted.descriptors.map (fun d => mapRaw next d.raw) =
      frame.descriptors.map (fun d => mapRaw (first.comp next) d.raw) := by
    change converted.descriptors.map (·.raw) =
      frame.descriptors.map (fun d => mapRaw first d.raw) at descriptors
    calc
      _ = (converted.descriptors.map (·.raw)).map (mapRaw next) := by
        simp only [List.map_map, Function.comp_def]
      _ = (frame.descriptors.map (fun d => mapRaw first d.raw)).map (mapRaw next) := by
        rw [descriptors]
      _ = _ := by simp only [List.map_map, Function.comp_def, mapRaw_comp first next zero]
  have checked := congrArg
    (fun raws => raws.mapM (SignDet.Descriptor.validate target.sign target.signature)) rawLists
  simp only [List.mapM_map] at checked
  change (converted.descriptors.mapM (fun descriptor =>
      SignDet.Descriptor.validate target.sign target.signature
        (middle.mapDescriptor target next.value descriptor))) =
    frame.descriptors.mapM (fun descriptor =>
      SignDet.Descriptor.validate target.sign target.signature
        (source.mapDescriptor target (first.comp next).value descriptor)) at checked
  unfold Frame.transport?
  rw [checked, Frame.transport?_values frame first converted produced,
    Frame.transport?_polynomials frame first converted produced]
  simp only [List.map_map, Function.comp_def, Frame.polynomial_comp first next zero]
  have valueEq : (fun x => next.value (first.value x)) = (first.comp next).value :=
    funext (fun x => (Inclusion.comp_value first next x).symm)
  rw [valueEq]

/-- A finite request retains each original owner and its requested operands. -/
abbrev Request (registry : BaseContext.Registry) := List (Σ owner : Context registry, Frame owner)

/-- Owners are taken from the actual immutable handles, not serialized names. -/
@[expose] def Request.owners (request : Request registry) : List (Context registry) := request.map Sigma.fst

/-- Retrieve the operands owned by one original context, preserving request
order rather than identifying owners by names or equality searches. -/
@[expose] def Request.frame (request : Request registry) (index : Fin request.length) :
    Frame (request.owners[index.val]'(by simpa [Request.owners] using index.isLt)) :=
  match request, index with
  | [], index => nomatch index
  | ⟨_, frame⟩ :: _, ⟨0, _⟩ => frame
  | _ :: rest, ⟨n + 1, valid⟩ => Request.frame rest ⟨n, Nat.lt_of_succ_lt_succ valid⟩

/-- A selected root requests both its defining descriptor in the predecessor
and its actual generator in its cached child. Gathering follows each owner's
validated ancestry before converting either operand. -/
def rootRequest {parent : Context registry} (root : Root parent) : Request registry :=
  match root with
  | .point value => [⟨parent, { values := [value] }⟩]
  | .selected descriptor extension _ =>
    [⟨parent, { descriptors := [descriptor] }⟩,
      ⟨extension.context, { values := [extension.generator] }⟩]

/-- Convert a request in its original order using its retained owner maps. -/
@[expose] def Request.transport? {target : Context registry} (request : Request registry)
    (maps : Inclusions target request.owners) : Option (List (Frame target)) :=
  match request, maps with
  | [], .nil => some []
  | ⟨_, frame⟩ :: rest, .cons inclusion remaining => do
    let converted ← frame.transport? inclusion
    let later ← Request.transport? rest remaining
    return converted :: later

/-- Transport retains exactly one output frame for every original request. -/
theorem Request.transport?_length {target : Context registry} (request : Request registry)
    (maps : Inclusions target request.owners) (frames : List (Frame target))
    (produced : Request.transport? request maps = some frames) :
    frames.length = request.length := by
  induction request generalizing frames with
  | nil =>
    cases maps
    cases Option.some.inj produced
    rfl
  | cons frame rest ih =>
    cases frame with
    | mk owner frame =>
      cases maps with
      | cons inclusion remaining =>
        cases first : frame.transport? inclusion with
        | none => simp [Request.transport?, first] at produced
        | some converted =>
          cases later : Request.transport? rest remaining with
          | none => simp [Request.transport?, first, later] at produced
          | some tail =>
            simp only [Request.transport?, first, later, bind, Option.bind, pure,
              Option.some.injEq] at produced
            cases produced
            exact congrArg Nat.succ (ih remaining tail later)

/-- Each returned frame comes from the checked inclusion at the same original
request position. This connects the collection result to frame semantics. -/
theorem Request.transport?_frame {target : Context registry} (request : Request registry)
    (maps : Inclusions target request.owners) (frames : List (Frame target))
    (produced : Request.transport? request maps = some frames) (index : Fin request.length) :
    ∃ frame, frames[index.val]? = some frame ∧
      (request.frame index).transport?
        (maps.get ⟨index.val, by simpa [Request.owners] using index.isLt⟩) = some frame := by
  induction request generalizing frames with
  | nil => nomatch index
  | cons frame rest ih =>
    cases frame with
    | mk owner frame =>
      cases maps with
      | cons inclusion remaining =>
        cases first : frame.transport? inclusion with
        | none => simp [Request.transport?, first] at produced
        | some converted =>
          cases later : Request.transport? rest remaining with
          | none => simp [Request.transport?, first, later] at produced
          | some tail =>
            simp only [Request.transport?, first, later, bind, Option.bind, pure,
              Option.some.injEq] at produced
            cases produced
            rcases index with ⟨index, valid⟩
            cases index with
            | zero =>
              refine ⟨converted, rfl, ?_⟩
              exact first
            | succ n =>
              obtain ⟨returned, atIndex, checked⟩ :=
                ih remaining tail later ⟨n, Nat.lt_of_succ_lt_succ valid⟩
              refine ⟨returned, atIndex, ?_⟩
              exact checked

/-- The complete frame list follows one new inclusion without traversing
its historical inclusion closures again. -/
theorem Request.transport?_comp {source target : Context registry}
    (request : Request registry) (maps : Inclusions source request.owners)
    (frames : List (Frame source)) (produced : request.transport? maps = some frames)
    (next : Inclusion source target) (zero : next.value 0 = 0) :
    frames.mapM (fun frame => frame.transport? next) = request.transport? (maps.extend next) := by
  induction request generalizing frames with
  | nil =>
    cases maps
    simp only [Request.transport?, Option.some.injEq] at produced
    cases produced
    rfl
  | cons entry rest ih =>
    cases entry with
    | mk owner frame =>
      cases maps with
      | cons inclusion remaining =>
        cases first : frame.transport? inclusion with
        | none => simp [Request.transport?, first] at produced
        | some converted =>
          cases later : Request.transport? rest remaining with
          | none => simp [Request.transport?, first, later] at produced
          | some tail =>
            simp only [Request.transport?, first, later, bind, Option.bind, pure,
              Option.some.injEq] at produced
            cases produced
            simp only [List.mapM_cons, Request.transport?, Inclusions.extend,
              Frame.transport?_comp frame inclusion converted first next zero,
              ih remaining tail later]
            rfl

/-- One common context and the converted frames, with every original handle
and its checked map retained by the shared collection. -/
structure Collection (base : BaseContext.PackedContext registry) (request : Request registry) where
  private mk ::
  shared : Shared base request.owners
  frames : List (Frame shared.input.context)
  produced : request.transport? shared.maps = some frames

/-- Gather complete validated owner ancestry, then transport every requested
operand and revalidate every requested descriptor in the returned target. -/
def Request.gather? (base : BaseContext.PackedContext registry) (request : Request registry) :
    Option (Collection base request) := do
  let shared ← Shared.gather? base request.owners
  match checked : request.transport? shared.maps with
  | none => none
  | some frames => return ⟨shared, frames, checked⟩

/-- Successful gathering and descriptor transport produce a collection with
exactly that shared context; callers cannot supply a replacement context. -/
theorem Request.gather?_of_success (base : BaseContext.PackedContext registry)
    (request : Request registry) (shared : Shared base request.owners)
    (gathered : Shared.gather? base request.owners = some shared)
    (frames : List (Frame shared.input.context))
    (checked : request.transport? shared.maps = some frames) :
    ∃ result, request.gather? base = some result ∧ result.shared = shared := by
  refine ⟨⟨shared, frames, checked⟩, ?_, rfl⟩
  simp only [Request.gather?, gathered, bind, Option.bind]
  split
  next failed => simp [checked] at failed
  next converted produced =>
    cases Option.some.inj (produced.symm.trans checked)
    rfl

/-- An actual live collection retains the successful shared gather that
created its common context. -/
theorem Request.gather?_shared (base : BaseContext.PackedContext registry)
    (request : Request registry) (result : Collection base request)
    (produced : request.gather? base = some result) :
    Shared.gather? base request.owners = some result.shared := by
  unfold Request.gather? at produced
  cases gathered : Shared.gather? base request.owners with
  | none => simp [gathered] at produced
  | some shared =>
    simp only [gathered, bind, Option.bind] at produced
    split at produced
    next failed => simp at produced
    next converted checked =>
      cases Option.some.inj produced
      rfl

/-- Index the actual converted frames by their original request positions. -/
def Collection.frame {base : BaseContext.PackedContext registry} {request : Request registry}
    (collection : Collection base request) (index : Fin request.length) :
    Frame collection.shared.input.context :=
  collection.frames[index.val]'(by
    rw [Request.transport?_length request collection.shared.maps collection.frames collection.produced]
    exact index.isLt)

/-- An enlargement retains the actual shared producer packet, every original
request and freshly checked descriptors in its one returned target. -/
structure Enlargement {base : BaseContext.PackedContext registry} {request : Request registry}
    (original : Collection base request) where
  private mk ::
  shared : SharedEnlargement original.shared
  sharedProduced : original.shared.enlarge? = some shared
  frames : List (Frame shared.shared.input.context)
  produced : request.transport? shared.shared.maps = some frames

/-- Rebuild the shared suffix once, carry every retained owner through its
checked map, and refresh the requested descriptors against the new binding. -/
def Collection.enlarge? {base : BaseContext.PackedContext registry} {request : Request registry}
    (original : Collection base request) : Option (Enlargement original) :=
  match built : original.shared.enlarge? with
  | none => none
  | some shared =>
    if zero : shared.previous.value 0 = 0 then
      match checked : original.frames.mapM (fun frame => frame.transport? shared.previous) with
      | none => none
      | some frames =>
        have composed : request.transport? shared.shared.maps = some frames := by
          rw [original.shared.enlarge?_maps shared built]
          rw [← Request.transport?_comp request original.shared.maps original.frames
            original.produced shared.previous zero]
          exact checked
        some ⟨shared, built, frames, composed⟩
    else
      match checked : request.transport? shared.shared.maps with
      | none => none
      | some frames => some ⟨shared, built, frames, checked⟩

/-- The actual enlargement packet and successful frame transport determine
the returned collection, including its shared target and retained maps. -/
theorem Collection.enlarge?_of_success {base : BaseContext.PackedContext registry}
    {request : Request registry} (original : Collection base request)
    (shared : SharedEnlargement original.shared)
    (built : original.shared.enlarge? = some shared)
    (frames : List (Frame shared.shared.input.context))
    (checked : request.transport? shared.shared.maps = some frames) :
    ∃ result, original.enlarge? = some result ∧ result.shared = shared := by
  refine ⟨⟨shared, built, frames, checked⟩, ?_, rfl⟩
  unfold Collection.enlarge?
  split
  next failed => simp [built] at failed
  next packet produced =>
    cases Option.some.inj (produced.symm.trans built)
    split
    next zero =>
      have oneHop : original.frames.mapM (fun frame => frame.transport? shared.previous) = some frames := by
        rw [Request.transport?_comp request original.shared.maps original.frames
          original.produced shared.previous zero]
        rw [← original.shared.enlarge?_maps shared built]
        exact checked
      split
      next failed => simp [oneHop] at failed
      next converted produced =>
        cases Option.some.inj (produced.symm.trans oneHop)
        rfl
    next nonzero =>
      split
      next failed => simp [checked] at failed
      next converted produced =>
        cases Option.some.inj (produced.symm.trans checked)
        rfl

/-- The enlarged collection keeps the original request, ready for further
enlargement and checked readings in the new context. -/
def Enlargement.collection {base : BaseContext.PackedContext registry} {request : Request registry}
    {original : Collection base request} (result : Enlargement original) :
    Collection base.infinitesimal request := ⟨result.shared.shared, result.frames, result.produced⟩

/-- Further collection operations use the actual enlarged shared packet. -/
theorem Enlargement.collection_shared {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) : result.collection.shared = result.shared.shared := by
  unfold Enlargement.collection
  rfl

/-- The previously computed target values have one retained checked map. -/
def Enlargement.previous {base : BaseContext.PackedContext registry} {request : Request registry}
    {original : Collection base request} (result : Enlargement original) :
    Inclusion original.shared.input.context result.collection.shared.input.context :=
  result.shared.previous

/-- The new parameter belongs to the same context as every translated frame. -/
def Enlargement.parameter {base : BaseContext.PackedContext registry} {request : Request registry}
    {original : Collection base request} (result : Enlargement original) :
    result.collection.shared.input.context.Value := result.shared.parameter

/-- Every original owner map uses the same checked target enlargement. -/
theorem Enlargement.maps {base : BaseContext.PackedContext registry} {request : Request registry}
    {original : Collection base request} (result : Enlargement original) :
    result.collection.shared.maps = original.shared.maps.extend result.previous :=
  original.shared.enlarge?_maps result.shared result.sharedProduced

/-- Refreshed frames are obtained by the single retained predecessor map.
The equation follows from the original producer certificate, so computing
it never traverses the historical owner maps. -/
theorem Enlargement.frames_oneHop {base : BaseContext.PackedContext registry}
    {request : Request registry} {original : Collection base request}
    (result : Enlargement original) (zero : result.shared.previous.value 0 = 0) :
    original.frames.mapM (fun frame => frame.transport? result.shared.previous) = some result.frames := by
  rw [Request.transport?_comp request original.shared.maps original.frames original.produced
    result.shared.previous zero, ← original.shared.enlarge?_maps result.shared result.sharedProduced]
  exact result.produced

end Hex.RealClosure.Tower.Live
