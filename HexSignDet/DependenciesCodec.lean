/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Dependencies
public import HexSignDet.Codec.Laws
public import HexSignDet.Codec.Bytes
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json

public section

namespace Hex.SignDet.Dependencies

open Codec (Json)

variable {Result : Entry → Type u} {required : Array (Nat × Json)}

/-- Literal dependency references use the proved integer-only JSON backend. -/
def Reference.codec : ValueCodec Reference where
  encode reference := .arr #[Json.of reference.index, Json.of reference.level, reference.subject]
  decode json := do
    let fields ← Codec.tuple 3 json
    let index ← Json.decode fields[0]
    let level ← Json.decode fields[1]
    return ⟨index, level, fields[2]⟩

theorem Reference.codec_lawful : Reference.codec.Lawful := by
  intro reference
  cases reference
  simp [codec, Codec.tuple, Codec.Json.getArr_arr,
    bind, Except.bind, pure, Except.pure]

/-- Packet subjects and payloads retain their complete literal JSON values.
This decoder supplies data; it does not assert packet or graph validity. -/
def Entry.codec : ValueCodec Entry where
  encode entry := .arr #[Json.of entry.level, entry.subject, entry.payload,
    Codec.array Reference.codec.encode entry.children]
  decode json := do
    let fields ← Codec.tuple 4 json
    let level ← Json.decode fields[0]
    let children ← Codec.readArray Reference.codec.decode fields[3]
    return ⟨level, fields[1], fields[2], children⟩

theorem Entry.codec_lawful : Entry.codec.Lawful := by
  intro entry
  cases entry
  simp [codec, Codec.tuple, Codec.Json.getArr_arr,
    Codec.read_array _ _ Reference.codec_lawful,
    bind, Except.bind, pure, Except.pure]

/-- Versioned finite coefficient-dependency envelope. Selected results and
every entry retain wire order; graph validity is checked separately. -/
def Graph.codec : ValueCodec Graph where
  encode graph := .arr #[Json.of (1 : Nat), Codec.array Entry.codec.encode graph.entries,
    Codec.array Reference.codec.encode graph.roots]
  decode json := do
    let fields ← Codec.tuple 3 json
    let version ← Json.decode (α := Nat) fields[0]
    if version != 1 then throw "unsupported dependency graph version"
    let entries ← Codec.readArray Entry.codec.decode fields[1]
    let roots ← Codec.readArray Reference.codec.decode fields[2]
    return ⟨entries, roots⟩

theorem Graph.codec_lawful : Graph.codec.Lawful := by
  intro graph
  cases graph
  simp [codec, Codec.tuple, Codec.Json.getArr_arr,
    Codec.read_array _ _ Entry.codec_lawful, Codec.read_array _ _ Reference.codec_lawful,
    bind, Except.bind, pure, Except.pure]

/-- Printing and actual byte parsing preserve the whole envelope, including
shared references and literal bindings, whenever its bytes pass the stated
syntax and resource precheck. No parser-success premise is needed. -/
theorem Graph.codec_bytes (graph : Graph) (limits : Codec.Limits)
    (bytes : Codec.checkBytes limits (Graph.codec.encodeBytes graph) = .ok ()) :
    Graph.codec.decodeBytes (Graph.codec.encodeBytes graph) limits = .ok graph :=
  Graph.codec.decode_encode_of graph (Graph.codec_lawful graph) limits bytes

/-- A decoded envelope retains the checked memo, the declared result indices
and their full caller bindings. The local reader supplies the typed values. -/
structure Decoded (Result : Entry → Type u) (required : Array (Nat × Json)) where
  graph : Graph
  memo : Array (Checked Result)
  bound : graph.roots.map (fun root => (root.level, root.subject)) = required
  structural : graph.check = true
  entries : memo.map Checked.entry = graph.entries

/-- Select the declared results in order, retaining shared memo values.
Reference bounds follow from checking, so selection cannot fail. -/
@[expose] def Decoded.results (decoded : Decoded Result required) : Array (Checked Result) :=
  decoded.graph.roots.attach.map fun root =>
    decoded.memo[root.val.index]'(by
      obtain ⟨bound, _⟩ := decoded.graph.check_roots decoded.structural root.val root.property
      have size := congrArg Array.size decoded.entries
      simp only [Array.size_map] at size
      omega)

/-- Decode one complete envelope and bind its ordered results to the caller's
full subjects before running any local packet reader. Returned indices remain
those of the serialized graph. -/
def Graph.decode (read : (entry : Entry) → Array (Checked Result) → Option (Result entry))
    (required : Array (Nat × Json)) (bytes : ByteArray) (limits : Codec.Limits := {}) :
    Except String (Decoded Result required) :=
  match Graph.codec.decodeBytes bytes limits with
  | .error reason => .error reason
  | .ok graph =>
    if bound : graph.roots.map (fun root => (root.level, root.subject)) = required then
      match accepted : graph.validate? read with
      | none => .error "invalid dependency evidence"
      | some memo => .ok ⟨graph, memo, bound, graph.validate_check read memo accepted,
          graph.validate_entries read memo accepted⟩
    else .error "dependency result binding mismatch"

/-- The actual printer, byte parser and typed packet checker retain the exact
memo from local checking. The byte premise is only the shared lexical precheck. -/
theorem Graph.decode_encode
    (read : (entry : Entry) → Array (Checked Result) → Option (Result entry))
    (graph : Graph) (memo : Array (Checked Result)) (limits : Codec.Limits)
    (accepted : graph.validate? read = some memo)
    (bytes : Codec.checkBytes limits (Graph.codec.encodeBytes graph) = .ok ()) :
    Graph.decode read (graph.roots.map (fun root => (root.level, root.subject)))
      (Graph.codec.encodeBytes graph) limits = .ok
        ⟨graph, memo, rfl, graph.validate_check read memo accepted,
          graph.validate_entries read memo accepted⟩ := by
  simp only [Graph.decode, Graph.codec_bytes graph limits bytes]
  split
  · split
    · rename_i empty
      rw [accepted] at empty
      contradiction
    · rename_i stored same
      have equal := Option.some.inj (same.symm.trans accepted)
      subst stored
      rfl
  · contradiction

end Hex.SignDet.Dependencies

/-- info: 'Hex.SignDet.Dependencies.Graph.codec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dependencies.Graph.codec_bytes
/-- info: 'Hex.SignDet.Dependencies.Graph.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dependencies.Graph.decode_encode
