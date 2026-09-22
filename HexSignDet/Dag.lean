/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Descriptor

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

namespace Dag

/-- A literal BKR node with optional references to its two children. References
are checked against the already accepted prefix, so cycles and forward edges
cannot be accepted. Ordered query slots remain part of each node. -/
structure Entry (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E] where
  node : Node E Ctx
  children : Option (Nat × Nat)

instance [DecidableEq Ctx] : DecidableEq (Entry E Ctx) := fun a b =>
  decidable_of_iff (a.node = b.node ∧ a.children = b.children)
    (by cases a; cases b; simp only [Entry.mk.injEq])

end Dag

/-- A topologically ordered graph of same-level BKR nodes. Every serialized
entry is checked, including entries not reachable from the selected root.
Coefficient-sign dependencies and their level ordering are separate inputs;
this graph does not encode lower-level coefficient proofs. -/
structure Dag (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E] where
  entries : Array (Dag.Entry E Ctx)
  root : Nat

namespace Dag

variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- A memoized accepted subtree on the fixed caller context and root domain.
Only the ordered query list varies within this graph. Proofs are erased at run
time; tree values share the already accepted child values. -/
structure Checked (sign : E → Int) (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) where
  value : Replay E Ctx
  accepted : value.check sign context p a b value.node.queries = true

/-- Check one node, reusing accepted children after exact list binding checks.
The local node checker still validates every supplied query and matrix witness. -/
@[expose] def step (sign : E → Int) (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (memo : Array (Checked sign context p a b)) (entry : Entry E Ctx)
    (shared : Option (TarskiCertificate.Domain.Checked (Ctx := Ctx) sign
      (EndpointSigns.ofSign sign)) := none) :
    Option (Checked sign context p a b) := do
  let n := entry.node
  match entry.children with
  | none =>
    if h : (decide (n.queries.length ≤ 1) &&
        decide (n.system.columns.toList = leafColumns n.queries.length) &&
        decide (n.system.rows.toList = leafRows n.queries.length) &&
        n.check sign context p a b n.queries shared) = true then
      return ⟨.leaf n, by
        change (decide (n.queries.length ≤ 1) &&
          decide (n.system.columns.toList = leafColumns n.queries.length) &&
          decide (n.system.rows.toList = leafRows n.queries.length) &&
          n.check sign context p a b n.queries) = true
        rw [Node.check_cache] at h
        exact h⟩
    else none
  | some (left, right) =>
    let l ← memo[left]?
    let r ← memo[right]?
    if hl : l.value.node.queries = n.queries.take (n.queries.length / 2) then
      if hr : r.value.node.queries = n.queries.drop (n.queries.length / 2) then
        if h : (decide (1 < n.queries.length) &&
            decide (n.system.columns.toList = product l.value.node.system.support
              r.value.node.system.support) &&
            decide (n.system.rows.toList = product l.value.node.rows r.value.node.rows) &&
            n.check sign context p a b n.queries shared) = true then
          return ⟨.split n l.value r.value, by
            have hleft := l.accepted
            have hright := r.accepted
            rw [hl] at hleft
            rw [hr] at hright
            simp only [Node.check_cache, Bool.and_eq_true] at h
            simp only [Replay.node, Replay.check, Bool.and_eq_true]
            exact ⟨⟨⟨⟨⟨h.1.1.1, hleft⟩, hright⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩⟩
        else none
      else none
    else none

/-- Sharing domain evidence preserves the exact checked step, including its
returned literal tree and every rejection branch. -/
theorem step_eq (sign : E → Int) (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (memo : Array (Checked sign context p a b)) (entry : Entry E Ctx)
    (shared : Option (TarskiCertificate.Domain.Checked (Ctx := Ctx) sign
      (EndpointSigns.ofSign sign))) :
    step sign context p a b memo entry shared = (do
  let n := entry.node
  match entry.children with
  | none =>
    if h : (Replay.leaf n).check sign context p a b n.queries = true then
      return ⟨.leaf n, h⟩
    else none
  | some (left, right) =>
    let l ← memo[left]?
    let r ← memo[right]?
    if hl : l.value.node.queries = n.queries.take (n.queries.length / 2) then
      if hr : r.value.node.queries = n.queries.drop (n.queries.length / 2) then
        if h : (decide (1 < n.queries.length) &&
            decide (n.system.columns.toList = product l.value.node.system.support
              r.value.node.system.support) &&
            decide (n.system.rows.toList = product l.value.node.rows r.value.node.rows) &&
            n.check sign context p a b n.queries) = true then
          return ⟨.split n l.value r.value, by
            have hleft := l.accepted
            have hright := r.accepted
            rw [hl] at hleft
            rw [hr] at hright
            simp only [Bool.and_eq_true] at h
            simp only [Replay.node, Replay.check, Bool.and_eq_true]
            exact ⟨⟨⟨⟨⟨h.1.1.1, hleft⟩, hright⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩⟩
        else none
      else none
    else none) := by
  simp only [step, Node.check_cache, Replay.check]
  rfl

/-- A supplied validated domain does not affect the checked graph step. -/
theorem step_cache (sign : E → Int) (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (memo : Array (Checked sign context p a b)) (entry : Entry E Ctx)
    (shared : Option (TarskiCertificate.Domain.Checked (Ctx := Ctx) sign
      (EndpointSigns.ofSign sign))) :
    step sign context p a b memo entry shared = step sign context p a b memo entry := by
  simp only [step_eq]

/-- Validate all references and nodes once, then bind the selected root's exact
query list. The returned evidence proves acceptance by the literal tree checker;
no recursive replay is rerun on cache hits or on the final root. This does not
assert root-count semantics, which still require the companion query bridge. -/
@[expose] def replay? (sign : E → Int) (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (dag : Dag E Ctx) :
    Option { t : Replay E Ctx // t.check sign context p a b qs = true } := do
  let shared := dag.entries[0]?.bind fun entry =>
    entry.node.moments.toArray[0]?.bind fun cert =>
      TarskiCertificate.Domain.replay? sign (EndpointSigns.ofSign sign) cert.domain
  let memo ← dag.entries.foldlM (init := #[]) fun memo entry => do
    let next ← step sign context p a b memo entry shared
    pure (memo.push next)
  let root ← memo[dag.root]?
  if h : root.value.node.queries = qs then
    return ⟨root.value, by simpa only [h] using root.accepted⟩
  else none

/-- Domain sharing across graph nodes preserves the original prefix replay,
including the exact returned tree, literal bindings and every rejection. -/
theorem replay_eq (sign : E → Int) (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (dag : Dag E Ctx) :
    replay? sign context p a b qs dag = (do
  let memo ← dag.entries.foldlM (init := #[]) fun memo entry => do
    let next ← step sign context p a b memo entry
    pure (memo.push next)
  let root ← memo[dag.root]?
  if h : root.value.node.queries = qs then
    return ⟨root.value, by simpa only [h] using root.accepted⟩
  else none) := by
  simp only [replay?, step_cache]

/-- Boolean acceptance for supplied graph literals. -/
@[expose] def check (sign : E → Int) (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (dag : Dag E Ctx) : Bool :=
  (replay? sign context p a b qs dag).isSome

/-- Every accepted graph has an accepted literal-tree expansion on exactly the
caller-supplied context, head, interval and ordered query list. -/
theorem check_replay {sign : E → Int} {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} {dag : Dag E Ctx}
    (h : check sign context p a b qs dag = true) :
    ∃ t, replay? sign context p a b qs dag = some t ∧ t.val.check sign context p a b qs = true := by
  unfold check at h
  cases he : replay? sign context p a b qs dag with
  | none => simp [he] at h
  | some t => exact ⟨t, rfl, t.property⟩

/-- Extract a selected root from graph evidence without a second whole-tree
replay. Raw shape, immutable context and the exact count-one condition are
still checked. Invalid supplied evidence does not decide root nonexistence. -/
@[expose] def descriptor? (sign : E → Int) (context : Ctx) (raw : RawDescriptor E Ctx)
    (dag : Dag E Ctx) : Option (Descriptor E Ctx sign context) := do
  if hw : raw.wellFormed = true then
    if hctx : raw.context = context then
      let t ← replay? sign context raw.head raw.lower raw.upper raw.queries dag
      if hone : (t.val.table t.property).count raw.signs = 1 then
        return Descriptor.ofTable raw t.val hw hctx t.property hone
      else none
    else none
  else none

/-- Descriptor extraction from any accepted supplied graph agrees exactly
with the tree-level interface on that graph's actual replay result. -/
theorem descriptor_replay {sign : E → Int} {context : Ctx} {raw : RawDescriptor E Ctx}
    {dag : Dag E Ctx}
    {t : {t : Replay E Ctx // t.check sign context raw.head raw.lower raw.upper raw.queries = true}}
    (h : replay? sign context raw.head raw.lower raw.upper raw.queries dag = some t) :
    descriptor? sign context raw dag = Descriptor.ofReplay? sign context raw t.val := by
  by_cases hw : raw.wellFormed = true
  · by_cases hctx : raw.context = context
    · simp only [descriptor?, hw, hctx, dite_eq_left, h, bind, Option.bind]
      by_cases hone : (t.val.table t.property).count raw.signs = 1
      · rw [dite_eq_left hone]
        exact (Descriptor.ofReplay_ofTable raw t.val hw hctx t.property hone).symm
      · have hn : t.val.node.system.count raw.signs ≠ 1 := by
          simpa only [Replay.table_lookup] using hone
        rw [dite_eq_right hone]
        exact (Descriptor.ofReplay_none (by simp [RawDescriptor.check, hn])).symm
    · simp only [descriptor?, hw, dite_eq_left, hctx]
      exact (Descriptor.ofReplay_none (by simp [RawDescriptor.check, hctx])).symm
  · simp only [descriptor?, hw]
    exact (Descriptor.ofReplay_none (by simp [RawDescriptor.check, hw])).symm

/-- Graph descriptor extraction preserves the entire supplied raw descriptor. -/
theorem descriptor_raw {sign : E → Int} {context : Ctx} {raw : RawDescriptor E Ctx}
    {dag : Dag E Ctx} {d : Descriptor E Ctx sign context}
    (h : descriptor? sign context raw dag = some d) : d.raw = raw := by
  unfold descriptor? at h
  split at h
  · split at h
    · cases ht : replay? sign context raw.head raw.lower raw.upper raw.queries dag with
      | none => simp [ht, bind, Option.bind] at h
      | some t =>
        simp only [ht, bind, Option.bind] at h
        split at h
        · simp only [pure, Option.some.injEq] at h
          subst d
          exact Descriptor.ofTable_raw _ _ _ _ _ _
        · simp at h
    · simp at h
  · simp at h

end Dag
end Hex.SignDet
