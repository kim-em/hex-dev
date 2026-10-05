/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.FrameRoundtrip
public import HexRealClosure.TowerRoots
import all HexSignDet.Codec.Basic

public section

namespace Hex.RealClosure.Tower
open SignDet
open SignDet.Codec (Json)
variable {registry : BaseContext.Registry}

/-- A point retains its literal coefficient. A selected root retains the
complete canonical descriptor frame, including its finite replay graph. -/
@[expose] def Root.data {parent : Context registry} : Root parent → Json
  | .point value => .arr #[Json.of (0 : Nat), parent.codec.encode value]
  | .selected _ extension _ => .arr #[Json.of (1 : Nat), extension.frame.toJson]

@[expose] def RootFormat.readTagged (data : Json) : Except String (Nat × Json) := do
  let fields ← Codec.tuple 2 data
  let kind ← Json.decode (α := Nat) fields[0]
  return (kind, fields[1])

/-- Reconstruct a root in its actual predecessor. A selected root is accepted
only through the canonical frame reader; its native child and generator are
constructed by the same checked adjunction as the original root. -/
@[expose] def Context.readRoot (parent : Context registry) (data : Json) :
    Except String (Root parent) :=
  match RootFormat.readTagged data with
  | .error message => .error message
  | .ok (0, value) => match parent.codec.decode value with
    | .error message => .error message
    | .ok value => .ok (.point value)
  | .ok (1, frame) => do
    let restored ← parent.readFrame frame
    return Root.ofSelection parent (.selected restored.descriptor)
  | .ok _ => .error "unknown root kind"

/-- Reading a printed root preserves the original kind, descriptor, cached
native extension and selected generator. -/
theorem Context.readRoot_data (parent : Context registry) (root : Root parent) :
    parent.readRoot root.data = .ok root := by
  cases root with
  | point value =>
    simp [Context.readRoot, RootFormat.readTagged, Root.data, Codec.tuple, Json.getArr_arr,
      Codec.read_nat, parent.codec_lawful value, bind, Except.bind, pure, Except.pure]
  | selected descriptor extension built =>
    cases built
    obtain ⟨restored, read, same, _, _⟩ := parent.readFrame_adjoin descriptor
    simp [Context.readRoot, RootFormat.readTagged, Root.data, Codec.tuple, Json.getArr_arr,
      Codec.read_nat, Literal.toJson, read, same, Root.ofSelection, bind, Except.bind, pure, Except.pure]
    have extensions (d e : Descriptor parent.Value Signature parent.sign parent.signature)
        (same : d = e) : HEq (parent.adjoin d) (parent.adjoin e) := by
      cases same
      rfl
    exact extensions _ _ same

/-- The outer binding names the full predecessor, independently of the root
kind and its own child context. -/
@[expose] def Root.write {parent : Context registry} (root : Root parent) : Serialized :=
  ⟨parent.signature, root.data⟩

@[expose] def RootEntry.data {parent : Context registry} (entry : RootEntry parent) : Json :=
  .arr #[entry.root.data, Json.of entry.multiplicity]

@[expose] def RootFormat.readEntryFields (data : Json) : Except String (Json × Nat) := do
  let fields ← Codec.tuple 2 data
  let multiplicity ← Json.decode (α := Nat) fields[1]
  return (fields[0], multiplicity)

/-- Root multiplicities are decoded exactly and must be positive. -/
@[expose] def Context.readRootEntry (parent : Context registry) (data : Json) :
    Except String (RootEntry parent) :=
  match RootFormat.readEntryFields data with
  | .error message => .error message
  | .ok (data, multiplicity) => do
    let root ← parent.readRoot data
    if positive : 0 < multiplicity then return ⟨root, multiplicity, positive⟩
    else throw "nonpositive root multiplicity"

theorem Context.readRootEntry_data (parent : Context registry) (entry : RootEntry parent) :
    parent.readRootEntry entry.data = .ok entry := by
  cases entry with
  | mk root multiplicity positive =>
    simp [Context.readRootEntry, RootFormat.readEntryFields, RootEntry.data, Codec.tuple, Json.getArr_arr,
      Context.readRoot_data, Codec.read_nat, positive, bind, Except.bind, pure, Except.pure]

/-- Complete root results preserve the universal result and the exact finite
entry order. Each entry retains its root kind, native owner and multiplicity. -/
@[expose] def RootSet.data {parent : Context registry} : RootSet parent → Json
  | .all => .arr #[Json.of (0 : Nat), .arr #[]]
  | .finite entries => .arr #[Json.of (1 : Nat), Json.arr (entries.map RootEntry.data).toArray]

/-- Read finite entries in their literal input order. -/
@[expose] def Context.readRootEntries (parent : Context registry) :
    List Json → Except String (List (RootEntry parent))
  | [] => .ok []
  | data :: rest => do
    return (← parent.readRootEntry data) :: (← parent.readRootEntries rest)

theorem Context.readRootEntries_data (parent : Context registry) (entries : List (RootEntry parent)) :
    parent.readRootEntries (entries.map RootEntry.data) = .ok entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp [Context.readRootEntries, parent.readRootEntry_data, ih, bind, Except.bind, pure, Except.pure]

@[expose] def Context.readRootSet (parent : Context registry) (data : Json) :
    Except String (RootSet parent) :=
  match RootFormat.readTagged data with
  | .error message => .error message
  | .ok (0, payload) =>
    if payload = Json.arr #[] then .ok .all
    else .error "nonempty universal root payload"
  | .ok (1, payload) => match payload.getArr? with
    | .error message => .error message
    | .ok entries => do return .finite (← parent.readRootEntries entries.toList)
  | .ok _ => .error "unknown root-set kind"

theorem Context.readRootSet_data (parent : Context registry) (roots : RootSet parent) :
    parent.readRootSet roots.data = .ok roots := by
  cases roots with
  | all =>
    simp [Context.readRootSet, RootFormat.readTagged, RootSet.data, Codec.tuple, Json.getArr_arr,
      Codec.read_nat, bind, Except.bind, pure, Except.pure]
  | finite entries =>
    simp [Context.readRootSet, RootFormat.readTagged, RootSet.data, Codec.tuple, Json.getArr_arr,
      Codec.read_nat, parent.readRootEntries_data, bind, Except.bind, pure, Except.pure]

@[expose] def RootSet.write {parent : Context registry} (roots : RootSet parent) : Serialized :=
  ⟨parent.signature, roots.data⟩

/-- Require the complete original predecessor binding before reading a root
payload in a caller-supplied context. -/
@[expose] def Context.readRootPacket (parent : Context registry) (data : Serialized) :
    Except String (Root parent) :=
  if data.binding = parent.signature then parent.readRoot data.value
  else .error "root predecessor mismatch"

@[expose] def Context.readRootSetPacket (parent : Context registry) (data : Serialized) :
    Except String (RootSet parent) :=
  if data.binding = parent.signature then parent.readRootSet data.value
  else .error "root-set predecessor mismatch"

theorem Context.readRoot_write (parent : Context registry) (root : Root parent) :
    parent.readRootPacket root.write = .ok root := by
  simp [Context.readRootPacket, Root.write, parent.readRoot_data]

theorem Context.readRootSet_write (parent : Context registry) (roots : RootSet parent) :
    parent.readRootSetPacket roots.write = .ok roots := by
  simp [Context.readRootSetPacket, RootSet.write, parent.readRootSet_data]

theorem Context.readRoot_stale (parent : Context registry) (data : Serialized)
    (different : data.binding ≠ parent.signature) :
    parent.readRootPacket data = .error "root predecessor mismatch" := by
  simp [Context.readRootPacket, different]

theorem Context.readRootSet_stale (parent : Context registry) (data : Serialized)
    (different : data.binding ≠ parent.signature) :
    parent.readRootSetPacket data = .error "root-set predecessor mismatch" := by
  simp [Context.readRootSetPacket, different]

/-- A reconstructed root retains its original predecessor as well as the
native root context selected by its kind and descriptor. -/
structure PackedRoot (registry : BaseContext.Registry) : Type 1 where
  parent : Context registry
  root : Root parent

structure PackedRootSet (registry : BaseContext.Registry) : Type 1 where
  parent : Context registry
  roots : RootSet parent

@[expose] def Catalog.restoreRoot (catalog : Catalog registry) (data : Serialized) :
    Except String (PackedRoot registry) := do
  let parent ← catalog.reconstruct data.binding
  let root ← parent.val.readRoot data.value
  return ⟨parent.val, root⟩

@[expose] def Catalog.restoreRootSet (catalog : Catalog registry) (data : Serialized) :
    Except String (PackedRootSet registry) := do
  let parent ← catalog.reconstruct data.binding
  let roots ← parent.val.readRootSet data.value
  return ⟨parent.val, roots⟩

/-- A root roundtrip does not require the predecessor's algebraic suffix to
be installed. The base catalog retains the actual provider progress premises. -/
theorem Catalog.restoreRoot_origin (catalog : BaseContext.Catalog registry)
    (parent : Context registry)
    (available : catalog.read parent.origin.base.signature = some parent.origin.base)
    (root : Root parent) :
    (Catalog.ofBase catalog).restoreRoot root.write = .ok ⟨parent, root⟩ := by
  obtain ⟨⟨context, binding⟩, reconstructed, same⟩ := Catalog.reconstruct_origin catalog parent available
  change context = parent at same
  cases same
  simp [Catalog.restoreRoot, Root.write, reconstructed, parent.readRoot_data,
    bind, Except.bind, pure, Except.pure]

/-- The complete finite or universal root result roundtrips with exact root
identity, multiplicities and order, including a freshly reconstructed parent. -/
theorem Catalog.restoreRootSet_origin (catalog : BaseContext.Catalog registry)
    (parent : Context registry)
    (available : catalog.read parent.origin.base.signature = some parent.origin.base)
    (roots : RootSet parent) :
    (Catalog.ofBase catalog).restoreRootSet roots.write = .ok ⟨parent, roots⟩ := by
  obtain ⟨⟨context, binding⟩, reconstructed, same⟩ := Catalog.reconstruct_origin catalog parent available
  change context = parent at same
  cases same
  simp [Catalog.restoreRootSet, RootSet.write, reconstructed, parent.readRootSet_data,
    bind, Except.bind, pure, Except.pure]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.readRoot_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRoot_data

/-- info: 'Hex.RealClosure.Tower.Context.readRootSet_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootSet_data

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreRoot_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreRoot_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreRootSet_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreRootSet_origin

/-- info: 'Hex.RealClosure.Tower.Context.readRoot_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRoot_write

/-- info: 'Hex.RealClosure.Tower.Context.readRootSet_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootSet_write

/-- info: 'Hex.RealClosure.Tower.Context.readRoot_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRoot_stale

/-- info: 'Hex.RealClosure.Tower.Context.readRootSet_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.readRootSet_stale
