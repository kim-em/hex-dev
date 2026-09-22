/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Node
public import HexSignDet.Codec.Bytes

public section

namespace Hex.SignDet
open Lean

variable {E Ctx : Type} [Zero E] [DecidableEq E]

namespace Codec

/-- A graph entry stores its complete node and zero or one child-index pair. -/
def entry (value : ValueCodec E) (context : ValueCodec Ctx) (e : Dag.Entry E Ctx) : Json :=
  .arr #[node value context e.node,
    option (fun (i, j) => Json.arr #[toJson i, toJson j]) e.children]

/-- Version 1 is `[1, root, entries]`. Coefficient/context codecs use JSON
values with integer numeric tokens. Every record has an exact positional
field count, so extra fields cannot be silently ignored. -/
def graph (value : ValueCodec E) (context : ValueCodec Ctx) (d : Dag E Ctx) : Json :=
  .arr #[toJson (1 : Nat), toJson d.root, array (entry value context) d.entries]

def readChildren (earlier : Nat) (j : Json) : Except String (Option (Nat × Nat)) :=
  readOption (fun j => do
    let a ← tuple 2 j
    let left ← index earlier a[0]
    let right ← index earlier a[1]
    return (left.val, right.val)) j

/-- Decode one entry against its position and the caller's exact root domain. -/
def readEntry [DecidableEq Ctx] (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E) (earlier : Nat) (j : Json) :
    Except String (Dag.Entry E Ctx) := do
  let fields ← tuple 2 j
  let children ← readChildren earlier fields[1]
  let n ← readNode value ctx fields[0]
  if !bindings context p lo hi n then throw "graph context or domain mismatch"
  return ⟨n, children⟩

/-- Validate all references, including unreachable entries, and bind every
node and query certificate to the supplied full context and root domain.
This constructs raw graph data; integer identities and support completeness
are still checked by independent replay. -/
def readGraph [DecidableEq Ctx] (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E) (j : Json) :
    Except String (Dag E Ctx) := do
  let a ← tuple 3 j
  if (← fromJson? (α := Nat) a[0]) != 1 then throw "unsupported graph version"
  let root ← fromJson? (α := Nat) a[1]
  let raw ← a[2].getArr?
  if root ≥ raw.size then throw "graph root out of range"
  let entries ← raw.foldlM (init := #[]) fun entries j => do
    return entries.push (← readEntry value ctx context p lo hi entries.size j)
  return ⟨entries, root⟩

/-- Decode versioned UTF-8 graph data after bounded lexical validation. -/
def decodeGraph [DecidableEq Ctx] (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E) (input : ByteArray)
    (limits : Limits := {}) : Except String (Dag E Ctx) := do
  readGraph value ctx context p lo hi (← parse limits input)

end Codec

/-- Serialize every literal graph field, without running a producer or checker.
Malformed graph data can be encoded; decoding and replay still reject it. -/
def Dag.encodeBytes (value : ValueCodec E) (context : ValueCodec Ctx) (d : Dag E Ctx) : ByteArray :=
  (Codec.graph value context d).compress.toUTF8

variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Decode and independently replay supplied graph bytes. Parsing failures and
false certificates return errors, never a mathematical root-nonexistence
result. Success retains ordinary finite tree-checker evidence. -/
def Dag.decodeBytes (value : ValueCodec E) (ctx : ValueCodec Ctx) (sign : E → Int)
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E) (qs : List (DensePoly E))
    (input : ByteArray) (limits : Codec.Limits := {}) :
    Except String { t : Replay E Ctx // t.check sign context p lo hi qs = true } := do
  let dag ← Codec.decodeGraph value ctx context p lo hi input limits
  match dag.replay? sign context p lo hi qs with
  | none => throw "graph replay rejected"
  | some checked => return checked

/-- Decode graph bytes for an exact caller-supplied Thom descriptor. Formal
derivatives are derived from that descriptor's head and indices by the existing
checker; no serialized derivative vector or count-one claim is trusted. -/
def Dag.decodeDescriptor (value : ValueCodec E) (ctx : ValueCodec Ctx) (sign : E → Int)
    (context : Ctx) (raw : RawDescriptor E Ctx) (input : ByteArray)
    (limits : Codec.Limits := {}) : Except String (Descriptor E Ctx sign context) := do
  let dag ← Codec.decodeGraph value ctx context raw.head raw.lower raw.upper input limits
  match dag.descriptor? sign context raw with
  | none => throw "descriptor replay rejected"
  | some d => return d

/-- Descriptor byte replay preserves the entire requested root identity,
including its exact derivative slots and signs. -/
theorem Dag.decodeDescriptor_raw (value : ValueCodec E) (ctx : ValueCodec Ctx) (sign : E → Int)
    (context : Ctx) (raw : RawDescriptor E Ctx) (input : ByteArray) (limits : Codec.Limits)
    {d : Descriptor E Ctx sign context}
    (h : decodeDescriptor value ctx sign context raw input limits = .ok d) : d.raw = raw := by
  unfold decodeDescriptor at h
  cases hd : Codec.decodeGraph value ctx context raw.head raw.lower raw.upper input limits with
  | error e => simp [hd, bind, Except.bind] at h
  | ok dag =>
    simp only [hd, bind, Except.bind] at h
    cases hr : dag.descriptor? sign context raw with
    | none => simp [hr] at h
    | some result =>
      simp only [hr, pure, Except.pure, Except.ok.injEq] at h
      subst d
      exact Dag.descriptor_raw hr

/-- Acceptance comes from replay of the actual decoded graph. This finite
correspondence theorem applies to arbitrary supplied bytes and value codecs;
it does not assume that the bytes were produced by the encoder. -/
theorem Dag.decode_replays (value : ValueCodec E) (ctx : ValueCodec Ctx) (sign : E → Int)
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E) (qs : List (DensePoly E))
    (input : ByteArray) (limits : Codec.Limits)
    {t : { t : Replay E Ctx // t.check sign context p lo hi qs = true }}
    (h : decodeBytes value ctx sign context p lo hi qs input limits = .ok t) :
    ∃ dag, Codec.decodeGraph value ctx context p lo hi input limits = .ok dag ∧
      dag.replay? sign context p lo hi qs = some t := by
  unfold decodeBytes at h
  cases hd : Codec.decodeGraph value ctx context p lo hi input limits with
  | error e => simp [hd, bind, Except.bind] at h
  | ok dag =>
    simp only [hd, bind, Except.bind] at h
    cases hr : dag.replay? sign context p lo hi qs with
    | none => simp [hr] at h
    | some checked =>
      simp only [hr, pure, Except.pure, Except.ok.injEq] at h
      subst t
      exact ⟨dag, rfl, hr⟩

end Hex.SignDet
