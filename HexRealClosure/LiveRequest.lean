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

end Hex.RealClosure.Tower.Live
