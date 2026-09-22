/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Dag
public import Std.Data.HashMap

public section

namespace Hex

namespace SignDet.Dag

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] [DecidableEq Ctx]
    [Hashable E] [Hashable Ctx]

/-- Hashing narrows the search; exact equality still compares every node field,
including all witnesses and literal context bindings. A collision never licenses
sharing. Child indices distinguish nodes with different descendants. -/
instance : Hashable (Entry E Ctx) where
  hash e := hash (e.node.context, e.node.queries.map (·.toArray), e.node.size,
    e.node.system.columns.toArray, e.children)

/-- Construction state for bottom-up hash consing. This is producer state, not
trusted checker evidence. The graph checker validates its output independently. -/
structure Encoder (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E]
    [DecidableEq Ctx] [Hashable E] [Hashable Ctx] where
  entries : Array (Entry E Ctx) := #[]
  indices : Std.HashMap (Entry E Ctx) Nat := {}

/-- Retain the first exact occurrence and its stable index. -/
@[expose] def Encoder.insert (state : Encoder E Ctx) (entry : Entry E Ctx) : Encoder E Ctx × Nat :=
  match state.indices[entry]? with
  | some i => (state, i)
  | none =>
    let i := state.entries.size
    (⟨state.entries.push entry, state.indices.insert entry i⟩, i)

/-- Left-to-right postorder traversal. The parent is interned only after both
children, so generated child references point into the preceding prefix. -/
@[expose] def encodeFrom (state : Encoder E Ctx) : Replay E Ctx → Encoder E Ctx × Nat
  | .leaf n => state.insert ⟨n, none⟩
  | .split n l r =>
    let (state, left) := encodeFrom state l
    let (state, right) := encodeFrom state r
    state.insert ⟨n, some (left, right)⟩

/-- Encode an arbitrary supplied replay tree, sharing exactly repeated literal
nodes with the same child references. This does not validate the input or attach
an acceptance proof; use `replay?` to check the resulting graph. Hash consing
visits every input occurrence and retains the first occurrence of each entry.
Traversal follows every tree occurrence. Expansion can have exponentially
more occurrences than graph entries; re-encoding shared trees is not bounded
by entry count alone. Graph transformations should traverse entries with an
index remapping, retaining their shared representation.
It does not serialize coefficient values or lower-level coefficient proofs. -/
@[expose] def encode (tree : Replay E Ctx) : Dag E Ctx :=
  let (state, root) := encodeFrom {} tree
  ⟨state.entries, root⟩

end SignDet.Dag

end Hex
