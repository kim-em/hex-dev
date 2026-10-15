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

namespace SignDet.Replay

/-- All literal node occurrences, retaining repeated children without hashing. -/
@[expose] def nodes {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] :
    Replay E Ctx → List (Node E Ctx)
  | .leaf n => [n]
  | .split n l r => n :: (l.nodes ++ r.nodes)

end SignDet.Replay

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
  /-- Literal entries retained in their insertion order. -/
  entries : Array (Entry E Ctx) := #[]
  /-- Cached indices for exact entries; coherence is a separate invariant. -/
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

/-- Inserting an entry preserves any property shared by its node and the
previous entries, independent of the hash lookup result. -/
private theorem Encoder.insert_nodes (P : Node E Ctx → Prop)
    (state : Encoder E Ctx) (entry : Entry E Ctx)
    (before : ∀ e ∈ state.entries, P e.node) (current : P entry.node) :
    ∀ e ∈ (state.insert entry).1.entries, P e.node := by
  unfold Encoder.insert
  split
  · exact before
  · intro e he
    rcases Array.mem_push.mp he with he | he
    · exact before e he
    · subst e
      exact current

/-- Carry a node property through postorder encoding from a possibly nonempty
state. Both prior entries and inserted tree nodes retain the property. -/
private theorem encodeFrom_nodes (P : Node E Ctx → Prop) (tree : Replay E Ctx)
    (state : Encoder E Ctx) (before : ∀ e ∈ state.entries, P e.node)
    (covered : ∀ n ∈ tree.nodes, P n) :
    ∀ e ∈ (encodeFrom state tree).1.entries, P e.node := by
  induction tree generalizing state with
  | leaf n =>
    exact Encoder.insert_nodes P state ⟨n, none⟩ before (covered n (by simp [Replay.nodes]))
  | split n l r ihl ihr =>
    have left := ihl state before (fun m hm => covered m (by simp [Replay.nodes, hm]))
    have right := ihr (encodeFrom state l).1 left
      (fun m hm => covered m (by simp [Replay.nodes, hm]))
    exact Encoder.insert_nodes P _ _ right (covered n (by simp [Replay.nodes]))

/-- Every encoded entry inherits any property of all literal tree nodes.
Callers can establish finite coverage without reducing hash-table lookups. -/
theorem encode_nodes (P : Node E Ctx → Prop) (tree : Replay E Ctx)
    (covered : ∀ n ∈ tree.nodes, P n) :
    ∀ e ∈ (encode tree).entries, P e.node :=
  encodeFrom_nodes P tree {} (by simp) covered

end SignDet.Dag

end Hex
