/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.FrameFormat
public import HexRealClosure.TowerCatalog
public import HexSignDet.Codec.GraphLaws
public import HexSignDet.DagReplay
public import HexSignDet.DagExpand
public import HexSignDet.DagBounds
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node

public section

namespace Hex.RealClosure.Tower
open SignDet
open SignDet.Codec (Json)
variable {registry : BaseContext.Registry}

private theorem node_bindings {E C : Type} [Zero E] [DecidableEq E] [DecidableEq C]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] {sign : E → Int} {parent : C}
    {head : DensePoly E} {lower upper : Endpoint E} {queries : List (DensePoly E)}
    {node : Node E C} (h : node.check sign parent head lower upper queries = true) :
    Codec.bindings parent head lower upper node = true := by
  obtain ⟨subject, _⟩ := Node.check_bindings h
  simp only [Codec.bindings, subject.1, subject.2.1, subject.2.2.1,
    subject.2.2.2.1, and_self, decide_true, Bool.true_and]
  apply List.all_eq_true.mpr
  intro cert mem
  obtain ⟨i, hi, same⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp mem)
  subst cert
  have checked := Sturm.check_bindings sign parent head _ lower upper _ node.moments[i]
    (checkMoment_query (Node.check_moment h ⟨i, hi⟩))
  simp only [checked.1, checked.2.1, checked.2.2.2.1, checked.2.2.2.2.1,
    and_self, decide_true]

/-- Checked descriptors provide every graph parser bound and literal binding.
Decoding uses the actual shared graph codec and retains the original tree. -/
theorem Context.readGraph_data (parent : Context registry)
    (descriptor : Descriptor parent.Value Signature parent.sign parent.signature) :
    letI : Hashable parent.Value := ⟨fun a => hash (parent.codec.encode a)⟩
    letI : Hashable Signature := ⟨fun _ => 0⟩
    Codec.readGraph parent.codec (contextCodec parent.signature) parent.signature
      descriptor.raw.head descriptor.raw.lower descriptor.raw.upper
      (Codec.graph parent.codec (contextCodec parent.signature) (Dag.encode descriptor.evidence)) =
        .ok (Dag.encode descriptor.evidence) := by
  letI : Hashable parent.Value := ⟨fun a => hash (parent.codec.encode a)⟩
  letI : Hashable Signature := ⟨fun _ => 0⟩
  obtain ⟨_, _, accepted, _⟩ := RawDescriptor.check_eq descriptor.accepted
  have replay := Dag.replay_encode accepted
  cases hv : (Dag.encode descriptor.evidence).validate? parent.sign parent.signature
      descriptor.raw.head descriptor.raw.lower descriptor.raw.upper with
  | none => simp [Dag.replay?, hv, bind, Option.bind] at replay
  | some memo =>
    apply Codec.read_graph parent.codec (contextCodec parent.signature) parent.codec_lawful
      (contextCodec_lawful parent.signature) parent.signature descriptor.raw.head
      descriptor.raw.lower descriptor.raw.upper (Dag.encode descriptor.evidence)
      (Dag.encode_root descriptor.evidence) (Codec.Shape.of_validate hv) _
      (Dag.encode_bounds descriptor.evidence)
    intro entry member
    have nodes := Dag.validate_nodes parent.sign parent.signature descriptor.raw.head
      descriptor.raw.lower descriptor.raw.upper (Dag.encode descriptor.evidence) memo hv
    have mapped : entry.node ∈ (Dag.encode descriptor.evidence).entries.map Dag.Entry.node :=
      Array.mem_map.mpr ⟨entry, member, rfl⟩
    rw [← nodes] at mapped
    obtain ⟨checked, _, same⟩ := Array.mem_map.mp mapped
    rw [← same]
    exact node_bindings (Replay.check_node checked.accepted)

private theorem descriptor_replay (parent : Context registry)
    (descriptor : Descriptor parent.Value Signature parent.sign parent.signature) :
    Descriptor.ofReplay? parent.sign parent.signature descriptor.raw descriptor.evidence =
      some descriptor := by
  have accepted := (Descriptor.ofReplay_isSome parent.sign parent.signature
    descriptor.raw descriptor.evidence).mpr descriptor.accepted
  cases produced : Descriptor.ofReplay? parent.sign parent.signature
      descriptor.raw descriptor.evidence with
  | none => simp [produced] at accepted
  | some restored =>
    have raw := Descriptor.ofReplay_raw produced
    have evidence := Descriptor.ofReplay_evidence produced
    have same : restored = descriptor := by
      have factories : Descriptor.ofChecked parent.sign parent.signature
          restored.raw restored.evidence restored.accepted =
          Descriptor.ofChecked parent.sign parent.signature descriptor.raw
            descriptor.evidence descriptor.accepted := by
        congr 1
      exact (Descriptor.ofChecked_eq restored).symm.trans
        (factories.trans (Descriptor.ofChecked_eq descriptor))
    exact congrArg some same

/-- Read the descriptor fields and independently replay the supplied graph
over the exact native predecessor. All mathematical acceptance comes from
the shared descriptor checker, including its derived formal derivatives. -/
def Context.readDescriptor (parent : Context registry) (j : Json) :
    Except String (Descriptor parent.Value Signature parent.sign parent.signature) := do
  let fields ← Codec.tuple 7 j
  let binding ← (contextCodec parent.signature).decode fields[0]
  if binding ≠ parent.signature then throw "root predecessor mismatch"
  let head ← Codec.readPoly parent.codec fields[1]
  let lower ← Codec.readEndpoint parent.codec fields[2]
  let upper ← Codec.readEndpoint parent.codec fields[3]
  let indices ← Codec.Json.decode (α := List Nat) fields[4]
  let signs ← Codec.Json.decode (α := List Int) fields[5]
  let raw : RawDescriptor parent.Value Signature :=
    ⟨binding, head, lower, upper, indices, signs⟩
  let graph ← Codec.readGraph parent.codec (contextCodec parent.signature)
    parent.signature head lower upper fields[6]
  match graph.descriptor? parent.sign parent.signature raw with
  | none => throw "root descriptor replay rejected"
  | some descriptor => return descriptor

/-- Reading the actual finite descriptor printer recovers its exact original
checked descriptor. No graph-shape or parser-success premise is supplied. -/
theorem Context.readDescriptor_data (parent : Context registry)
    (descriptor : Descriptor parent.Value Signature parent.sign parent.signature) :
    parent.readDescriptor (rootData parent.codec descriptor) = .ok descriptor := by
  letI : Hashable parent.Value := ⟨fun a => hash (parent.codec.encode a)⟩
  letI : Hashable Signature := ⟨fun _ => 0⟩
  have graph := parent.readGraph_data descriptor
  have binding := (RawDescriptor.check_eq descriptor.accepted).2.1
  have ctx := contextCodec_lawful parent.signature parent.signature
  have indices : Codec.Json.decode (Codec.Json.of descriptor.raw.indices) =
      .ok descriptor.raw.indices := by
    change Array.toList <$> Codec.Json.decode (Codec.Json.of descriptor.raw.indices.toArray) = _
    rw [Codec.read_jsonArray Codec.read_nat]
    rfl
  have signs : Codec.Json.decode (Codec.Json.of descriptor.raw.signs) =
      .ok descriptor.raw.signs := by
    change Array.toList <$> Codec.Json.decode (Codec.Json.of descriptor.raw.signs.toArray) = _
    rw [Codec.read_jsonArray Codec.read_int]
    rfl
  have raw : RawDescriptor.mk parent.signature descriptor.raw.head descriptor.raw.lower
      descriptor.raw.upper descriptor.raw.indices descriptor.raw.signs = descriptor.raw := by
    exact congrArg (fun context => RawDescriptor.mk context descriptor.raw.head descriptor.raw.lower
      descriptor.raw.upper descriptor.raw.indices descriptor.raw.signs) binding.symm
  simp [Context.readDescriptor, rootData, Codec.tuple, Codec.Json.getArr_arr,
    ctx, binding, indices, signs, Codec.read_poly parent.codec parent.codec_lawful,
    Codec.read_endpoint parent.codec parent.codec_lawful, graph,
    bind, Except.bind, pure, Except.pure, Dag.descriptor_encode, raw,
    descriptor_replay parent descriptor]

/-- A reconstructed root owns both the checked descriptor and the actual
native extension. Exact frame equality retains the requested full identity,
including replay sharing and every coefficient representation. -/
structure RestoredRoot (parent : Context registry) (frame : Literal) : Type 1 where
  private mk ::
  descriptor : Descriptor parent.Value Signature parent.sign parent.signature
  extension : Extension parent descriptor
  accepted : parent.readDescriptor frame.toJson = .ok descriptor
  constructed : extension = parent.adjoin descriptor
  frame_eq : extension.frame = frame

/-- Reconstruct one new native algebraic level from supplied structured data.
An accepted but differently encoded replay is rejected as a different binding;
the reader never silently replaces a full requested context identity. -/
def Context.readFrame (parent : Context registry) (frame : Literal) :
    Except String (RestoredRoot parent frame) :=
  match hd : parent.readDescriptor frame.toJson with
  | .error message => .error message
  | .ok descriptor =>
    let extension := parent.adjoin descriptor
    if hf : extension.frame = frame then
      .ok ⟨descriptor, extension, hd, rfl, hf⟩
    else .error "noncanonical root frame"

/-- A newly printed canonical level reconstructs the original descriptor and
native extension directly, without an installed catalog entry. -/
theorem Context.readFrame_adjoin (parent : Context registry)
    (descriptor : Descriptor parent.Value Signature parent.sign parent.signature) :
    ∃ restored : RestoredRoot parent (parent.adjoin descriptor).frame,
      parent.readFrame (parent.adjoin descriptor).frame = .ok restored ∧
      restored.descriptor = descriptor ∧ HEq restored.extension (parent.adjoin descriptor) ∧
      restored.extension.context = (parent.adjoin descriptor).context := by
  have encoded : (parent.adjoin descriptor).frame.toJson = rootData parent.codec descriptor :=
    Literal.toJson_ofJson _ _ (parent.adjoin descriptor).encoded
  have accepted : parent.readDescriptor (parent.adjoin descriptor).frame.toJson = .ok descriptor := by
    rw [encoded, parent.readDescriptor_data]
  refine ⟨⟨descriptor, parent.adjoin descriptor, accepted, rfl, rfl⟩,
    ?_, rfl, HEq.rfl, rfl⟩
  unfold Context.readFrame
  split
  · rename_i message decoded
    rw [accepted] at decoded
    cases decoded
  · rename_i decoded checked
    have same : decoded = descriptor := Except.ok.inj (checked.symm.trans accepted)
    cases same
    dsimp only
    split
    · rfl
    · rename_i different
      exact (different rfl).elim

/-- Fresh canonical frame reconstruction retains the original native owner. -/
theorem Context.readFrame_context (parent : Context registry)
    (descriptor : Descriptor parent.Value Signature parent.sign parent.signature) :
    ∃ restored : RestoredRoot parent (parent.adjoin descriptor).frame,
      parent.readFrame (parent.adjoin descriptor).frame = .ok restored ∧
      restored.extension.context = (parent.adjoin descriptor).context := by
  obtain ⟨restored, read, _, _, context⟩ := parent.readFrame_adjoin descriptor
  exact ⟨restored, read, context⟩

theorem RestoredRoot.binding (result : RestoredRoot parent frame) :
    result.extension.context.signature = parent.signature.extend frame := by
  rw [result.extension.binding, result.frame_eq]

/-- The retained descriptor re-encodes to the exact input frame, including its
complete replay graph. This is a property of every successful reconstruction. -/
theorem RestoredRoot.frame_data (result : RestoredRoot parent frame) :
    frame.toJson = rootData parent.codec result.descriptor := by
  exact (congrArg Literal.toJson result.frame_eq).symm.trans
    (Literal.toJson_ofJson _ _ result.extension.encoded)

@[expose] def Signature.append (signature : Signature) (frames : List Literal) : Signature :=
  { signature with roots := signature.roots ++ frames }

theorem Signature.append_nil (signature : Signature) : signature.append [] = signature := by
  cases signature
  simp [Signature.append]

theorem Signature.append_cons (signature : Signature) (frame : Literal) (frames : List Literal) :
    (signature.extend frame).append frames = signature.append (frame :: frames) := by
  simp [Signature.extend, Signature.append, List.append_assoc]

/-- Reconstruct successive levels in predecessor order. A validated cached
prefix is reused; every missing prefix goes through the actual frame reader.
The returned context's full binding is proved, rather than a hash assertion. -/
def Catalog.readFrames (catalog : Catalog registry) (parent : Context registry) :
    (frames : List Literal) →
      Except String { context : Context registry // context.signature = parent.signature.append frames }
  | [] => .ok ⟨parent, (Signature.append_nil parent.signature).symm⟩
  | frame :: frames =>
    let next : Except String { context : Context registry //
        context.signature = parent.signature.extend frame } :=
      match hl : catalog.lookup (parent.signature.extend frame) with
      | some context => .ok ⟨context, catalog.lookup_signature _ context hl⟩
      | none => match parent.readFrame frame with
        | .error message => .error message
        | .ok root => .ok ⟨root.extension.context, root.binding⟩
    match next with
    | .error message => .error message
    | .ok child => match catalog.readFrames child.val frames with
      | .error message => .error message
      | .ok result => .ok ⟨result.val, by
          rw [result.property, child.property, Signature.append_cons]⟩

/-- Recover a native tower from a supplied whole-context identity. Exact
catalog hits return immediately. Otherwise a validated real base supplies its
erased search progress, cached algebraic prefixes are reused, and missing
levels are checked from replay frames. -/
def Catalog.reconstruct (catalog : Catalog registry) (binding : Signature) :
    Except String { context : Context registry // context.signature = binding } :=
  match hl : catalog.lookup binding with
  | some context => .ok ⟨context, catalog.lookup_signature _ context hl⟩
  | none => match hb : catalog.lookup ⟨binding.base, []⟩ with
    | none => .error "unknown validated base"
    | some base => match catalog.readFrames base binding.roots with
      | .error message => .error message
      | .ok result => .ok ⟨result.val, by
          rw [result.property, catalog.lookup_signature _ base hb]
          cases binding
          rfl⟩

theorem Catalog.reconstruct_lookup (catalog : Catalog registry) (binding : Signature)
    (context : Context registry) (h : catalog.lookup binding = some context) :
    catalog.reconstruct binding = .ok ⟨context, catalog.lookup_signature _ context h⟩ := by
  unfold Catalog.reconstruct
  split
  · rename_i found hf
    have he : found = context := Option.some.inj (hf.symm.trans h)
    subst found
    rfl
  · rename_i hn
    rw [hn] at h
    contradiction

/-- Reconstruct the full native context before checking the scalar payload.
The catalog is immutable; the returned value owns the newly reconstructed
context whether or not the caller chooses to install it for subsequent reads. -/
def Catalog.restoreElement (catalog : Catalog registry) (raw : Serialized) :
    Except String (PackedElement registry) :=
  match catalog.reconstruct raw.binding with
  | .error message => .error message
  | .ok context => match context.val.codec.decode raw.value with
    | .error message => .error message
    | .ok value => .ok ⟨context.val, value⟩

def Catalog.restorePolynomial (catalog : Catalog registry) (raw : Serialized) :
    Except String (PackedPolynomial registry) :=
  match catalog.reconstruct raw.binding with
  | .error message => .error message
  | .ok context => match Codec.readPoly context.val.codec raw.value with
    | .error message => .error message
    | .ok value => .ok ⟨context.val, value⟩

theorem Catalog.restoreElement_signature (catalog : Catalog registry) (raw : Serialized)
    (result : PackedElement registry) (h : catalog.restoreElement raw = .ok result) :
    result.context.signature = raw.binding := by
  simp only [Catalog.restoreElement] at h
  cases hc : catalog.reconstruct raw.binding with
  | error message => simp [hc] at h
  | ok context =>
    simp only [hc] at h
    cases hr : context.val.codec.decode raw.value with
    | error message => simp [hr] at h
    | ok value =>
      simp only [hr, Except.ok.injEq] at h
      subst result
      exact context.property

theorem Catalog.restorePolynomial_signature (catalog : Catalog registry) (raw : Serialized)
    (result : PackedPolynomial registry) (h : catalog.restorePolynomial raw = .ok result) :
    result.context.signature = raw.binding := by
  simp only [Catalog.restorePolynomial] at h
  cases hc : catalog.reconstruct raw.binding with
  | error message => simp [hc] at h
  | ok context =>
    simp only [hc] at h
    cases hr : Codec.readPoly context.val.codec raw.value with
    | error message => simp [hr] at h
    | ok value =>
      simp only [hr, Except.ok.injEq] at h
      subst result
      exact context.property

theorem Catalog.restoreElement_write (catalog : Catalog registry) (context : Context registry)
    (a : context.Value) (h : catalog.lookup context.signature = some context) :
    catalog.restoreElement (context.write a) = .ok ⟨context, a⟩ := by
  simp only [Catalog.restoreElement, Context.write]
  rw [catalog.reconstruct_lookup _ context h]
  simp [context.codec_lawful a]

theorem Catalog.restorePolynomial_write (catalog : Catalog registry) (context : Context registry)
    (p : context.Poly) (h : catalog.lookup context.signature = some context) :
    catalog.restorePolynomial (context.writePoly p) = .ok ⟨context, p⟩ := by
  simp only [Catalog.restorePolynomial, Context.writePoly]
  rw [catalog.reconstruct_lookup _ context h]
  simp [Codec.read_poly context.codec context.codec_lawful p]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.readGraph_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readGraph_data

/-- info: 'Hex.RealClosure.Tower.Context.readDescriptor_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readDescriptor_data

/-- info: 'Hex.RealClosure.Tower.Context.readFrame_adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readFrame_adjoin

/-- info: 'Hex.RealClosure.Tower.Context.readFrame_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readFrame_context
