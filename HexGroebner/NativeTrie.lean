/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Native

@[expose] public section

namespace Hex.Groebner.Native.Trie

/-- One little-endian u32 word. -/
def word (bytes : @& ByteArray) (i : Nat) : Nat := Native.read bytes 4 (i*4)

/-- Check a bounded rooted tree and all packed spans before creating its witness.
Node records contain depth, edge start/count, reducer-plus-one, term count and
leading monomial. Edges contain exponent/child pairs. Every nonroot has exactly
one parent; depths increase along edges. -/
def validPortable (arity : Nat) (nodes edges : ByteArray) (maxLeading : UInt64) : Bool := Id.run do
  let n := nodes.size/24
  let e := edges.size/8
  if arity > 4096 || nodes.size%24 != 0 || n == 0 || n > 2048 ||
      edges.size%8 != 0 || e+1 != n || maxLeading.toNat > 4294967295 || word nodes 0 != 0 then return false
  let mut parents := Array.replicate n 0
  let mut cursor := 0
  for i in [:n] do
    let depth := word nodes (6*i)
    let start := word nodes (6*i+1)
    let count := word nodes (6*i+2)
    let key := word nodes (6*i+3)
    let terms := word nodes (6*i+4)
    let leading := word nodes (6*i+5)
    if depth > arity || start != cursor || start+count > e ||
        (depth == arity && count != 0) then return false
    if key == 0 then
      if terms != 0 || leading != 0 then return false
    else if depth != arity || terms == 0 || leading > maxLeading.toNat then return false
    for k in [:count] do
      let child := word edges (2*(start+k)+1)
      if child == 0 || child ≥ n || word nodes (6*child) != depth+1 then return false
      parents := parents.modify child (·+1)
      if parents[child]! != 1 then return false
    cursor := cursor+count
  if cursor != e || parents[0]! != 0 then return false
  for i in [1:n] do
    if parents[i]! != 1 then return false
  return true

/-- The same bounded representation check without boxed per-node temporaries. -/
@[extern "lean_hex_groebner_validate_trie"]
def valid (arity : @& Nat) (nodes edges : @& ByteArray) (maxLeading : UInt64) : Bool :=
  validPortable arity nodes edges maxLeading

/-- The executable validator establishes the representation witness. -/
structure View where
  arity : Nat
  nodes : ByteArray
  edges : ByteArray
  maxLeading : UInt64
  lawful : validPortable arity nodes edges maxLeading = true

namespace View

def check (arity : Nat) (nodes edges : ByteArray) (maxLeading : UInt64) : Option View :=
  if h : valid arity nodes edges maxLeading = true then some ⟨arity,nodes,edges,maxLeading,h⟩ else none

end View

/-- Status 1 is complete, 2 exhausts work, and 3 declines an unsupported query.
All work is charged before the corresponding visit or edge scan. -/
structure Result where
  reducer : Option Nat := none
  work : Nat := 0
  status : UInt8 := 1

def degree (metadata : @& ByteArray) (id : Nat) : Nat := Native.read metadata 8 (24*id)
def mask (metadata : @& ByteArray) (id : Nat) : UInt64 := (Native.read metadata 8 (24*id+8)).toUInt64

/-- Read-only bounded lookup over a validated tree. Quality prefers sparse rows,
then greater leading degree; traversal preserves insertion-order tie breaking. -/
def lookupPortable (view : @& View) (width : UInt8) (count monomial : UInt64)
    (arena metadata : @& ByteArray) (remaining : UInt64) : Result := Id.run do
  let n := view.nodes.size/24
  let w := width.toNat
  if (w != 1 && w != 2 && w != 4) || count.toNat > 4294967295 ||
      monomial ≥ count || view.maxLeading ≥ count ||
      arena.size != count.toNat*view.arity*w || metadata.size != count.toNat*24 then
    return { status := 3 }
  let query := monomial.toNat
  let queryDegree := degree metadata query
  let queryMask := mask metadata query
  let mut pending := #[0]
  let mut out : Result := {}
  let mut bestSize := 0
  let mut bestLeading := 0
  for _ in [:n] do
    if pending.isEmpty then break
    let node := pending.back!
    pending := pending.pop
    if out.work+1 > remaining.toNat then return { out with status := 2 }
    out := { out with work := out.work+1 }
    let depth := word view.nodes (6*node)
    if depth == view.arity then
      let key := word view.nodes (6*node+3)
      if key != 0 then
        let terms := word view.nodes (6*node+4)
        let leading := word view.nodes (6*node+5)
        if degree metadata leading ≤ queryDegree && mask metadata leading &&& queryMask == mask metadata leading then
          if out.reducer.isNone || terms < bestSize ||
              (terms == bestSize && degree metadata leading > degree metadata bestLeading) then
            out := { out with reducer := some (key-1) }
            bestSize := terms
            bestLeading := leading
    else
      let start := word view.nodes (6*node+1)
      let count := word view.nodes (6*node+2)
      if out.work+count > remaining.toNat then return { out with status := 2 }
      out := { out with work := out.work+count }
      let exponent := Native.read arena w ((query*view.arity+depth)*w)
      for i in [:count] do
        if word view.edges (2*(start+i)) ≤ exponent then
          pending := pending.push (word view.edges (2*(start+i)+1))
  return out

/-- Native lookup consumes only the validated tree witness and borrowed arenas.
Its node/edge visits fit the fixed 4096-unit bound. -/
@[extern "lean_hex_groebner_lookup_trie"]
def lookup (view : @& View) (width : UInt8) (count monomial : UInt64)
    (arena metadata : @& ByteArray) (remaining : UInt64) : Result :=
  lookupPortable view width count monomial arena metadata remaining

end Hex.Groebner.Native.Trie
