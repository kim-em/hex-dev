/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Word
public import Lean.Data.Json.Parser
public import Lean.Data.Json.FromToJson.Basic

public section

namespace Hex.PermGroup.Program

open Lean

/-- Wire format: identity `[0]`, generator `[1,i]`, inverse `[2,i]`, and
product `[3,i,j]`. Indices are exact natural numbers. -/
@[expose] def encodeNode : Node → Json
  | .id => toJson (#[0] : Array Nat)
  | .generator i => toJson #[1, i]
  | .inv i => toJson #[2, i]
  | .comp i j => toJson #[3, i, j]

/-- Encode the raw program as a versioned JSON object. -/
@[expose] def encode (program : Program) : String :=
  (Json.mkObj [("version", toJson (1 : Nat)),
    ("nodes", Json.arr (program.nodes.map encodeNode)),
    ("root", toJson program.root)]).compress

/-- Decode a node, rejecting references outside the already decoded prefix. -/
@[expose] def decodeNode (generatorCount earlier : Nat) (json : Json) : Except String Node := do
  let a ← fromJson? (α := Array Nat) json
  match a.toList with
  | [0] => return .id
  | [1, i] =>
    if i < generatorCount then return .generator i
    else throw "generator index out of range"
  | [2, i] =>
    if i < earlier then return .inv i
    else throw "inverse reference is not earlier"
  | [3, i, j] =>
    if i < earlier && j < earlier then return .comp i j
    else throw "product reference is not earlier"
  | _ => throw "invalid program node"

/-- Decode within explicit byte and node limits. The byte limit is checked before
JSON parsing, and the node limit before constructing program nodes. All references
are validated, including nodes unreachable from the root. -/
@[expose] def decode (maxBytes maxNodes generatorCount : Nat) (input : String) :
    Except String Program := do
  if input.utf8ByteSize > maxBytes then throw "program byte limit exceeded"
  let json ← Json.parse input
  let version ← json.getObjValAs? Nat "version"
  if version != 1 then throw "unsupported program version"
  let raw ← json.getObjValAs? (Array Json) "nodes"
  if raw.size > maxNodes then throw "program node limit exceeded"
  let root ← json.getObjValAs? Nat "root"
  if root ≥ raw.size then throw "program root out of range"
  let mut nodes := #[]
  for node in raw do
    nodes := nodes.push (← decodeNode generatorCount nodes.size node)
  return ⟨nodes, root⟩

end Hex.PermGroup.Program
