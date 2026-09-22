/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.DagReplay
import all HexSignDet.Descriptor

public section

namespace Hex.SignDet.Dag

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

namespace Expansion

/-- Expand one entry using only earlier tree references. No mathematical or
certificate validity decision is made here. -/
@[expose] def step (memo : Array (Replay E Ctx)) (entry : Entry E Ctx) : Option (Replay E Ctx) := do
  match entry.children with
  | none => return .leaf entry.node
  | some (left, right) =>
    let l ← memo[left]?
    let r ← memo[right]?
    return .split entry.node l r

/-- Expand every entry in order, rejecting missing, forward or cyclic references. -/
@[expose] def run (entries : Array (Entry E Ctx)) : Option (Array (Replay E Ctx)) :=
  entries.foldlM (init := #[]) fun memo entry => do
    let tree ← step memo entry
    pure (memo.push tree)

theorem step_mono {before after : Array (Replay E Ctx)} (hm : Prefix before after)
    {entry : Entry E Ctx} {t : Replay E Ctx} (h : step before entry = some t) :
    step after entry = some t := by
  unfold step at h ⊢
  cases hc : entry.children with
  | none => simpa only [hc] using h
  | some children =>
    obtain ⟨left, right⟩ := children
    simp only [hc] at h ⊢
    cases hl : before[left]? with
    | none => simp [hl, bind, Option.bind] at h
    | some l =>
      cases hr : before[right]? with
      | none => simp [hl, hr, bind, Option.bind] at h
      | some r => simpa only [hl, hr, hm left l hl, hm right r hr] using h

variable [DecidableEq Ctx] [Hashable E] [Hashable Ctx]

/-- The shared encoder invariant specialized to structural expansion. -/
abbrev Valid (state : Encoder E Ctx) (memo : Array (Replay E Ctx)) : Prop :=
  Encoder.Valid step state memo

theorem valid_empty : Valid ({} : Encoder E Ctx) #[] := Encoder.valid_empty step

theorem insert_valid {state : Encoder E Ctx} {memo : Array (Replay E Ctx)}
    (hv : Valid state memo) {entry : Entry E Ctx} {t : Replay E Ctx}
    (ht : step memo entry = some t) :
    ∃ next, Valid (state.insert entry).1 next ∧ Prefix memo next ∧
      next[(state.insert entry).2]? = some t :=
  Encoder.insert_valid step_mono hv ht

/-- Expansion follows the actual encoder even when the supplied tree fails
replay. Every node and every child occurrence is retained literally. -/
theorem encodeFrom_expands {state : Encoder E Ctx} {memo : Array (Replay E Ctx)}
    (hv : Valid state memo) (tree : Replay E Ctx) :
    ∃ next, Valid (encodeFrom state tree).1 next ∧ Prefix memo next ∧
      next[(encodeFrom state tree).2]? = some tree := by
  induction tree generalizing state memo with
  | leaf n => exact insert_valid hv (by simp [step])
  | split n l r ihl ihr =>
    obtain ⟨lm, hvl, hel, hal⟩ := ihl hv
    obtain ⟨rm, hvr, her, har⟩ := ihr hvl
    have hs : step rm
        ⟨n, some ((encodeFrom state l).2, (encodeFrom (encodeFrom state l).1 r).2)⟩ =
        some (.split n l r) := by
      simp only [step, her _ _ hal, har, bind, Option.bind, pure]
    obtain ⟨next, hvn, hen, han⟩ := insert_valid hvr hs
    exact ⟨next, hvn, hel.trans (her.trans hen), han⟩

end Expansion

/-- Expand the selected graph root without validating its certificates. Every
entry must have valid earlier references, including unreachable entries. -/
@[expose] def expand? (dag : Dag E Ctx) : Option (Replay E Ctx) := do
  let memo ← Expansion.run dag.entries
  memo[dag.root]?

/-- Encoding and expanding any literal tree returns that exact tree, without
assuming its mathematical claims or checked replay are valid. -/
theorem expand_encode [DecidableEq Ctx] [Hashable E] [Hashable Ctx] (tree : Replay E Ctx) :
    expand? (encode tree) = some tree := by
  obtain ⟨memo, hv, _, hi⟩ := Expansion.encodeFrom_expands Expansion.valid_empty tree
  unfold expand? encode Expansion.run
  rw [hv.replay]
  simp only [bind, Option.bind, hi]

variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
    {sign : E → Int} {context : Ctx} {p : DensePoly E} {a b : Endpoint E}

/-- The checked local step returns the same tree as structural expansion. -/
theorem step_expands {memo : Array (Checked sign context p a b)} {entry : Entry E Ctx}
    {t : Checked sign context p a b} (h : step sign context p a b memo entry = some t) :
    Expansion.step (memo.map Checked.value) entry = some t.value := by
  unfold step at h
  cases hc : entry.children with
  | none =>
    simp only [hc] at h
    split at h
    · simp only [pure, Option.some.injEq] at h
      subst t
      simp [Expansion.step, hc]
    · simp at h
  | some children =>
    obtain ⟨left, right⟩ := children
    simp only [hc] at h
    cases hl : memo[left]? with
    | none => simp [hl, bind, Option.bind] at h
    | some l =>
      cases hr : memo[right]? with
      | none => simp [hl, hr, bind, Option.bind] at h
      | some r =>
        simp only [hl, hr, bind, Option.bind] at h
        split at h
        · split at h
          · split at h
            · simp only [pure, Option.some.injEq] at h
              subst t
              simp [Expansion.step, hc, hl, hr]
            · simp at h
          · simp at h
        · simp at h

private theorem fold_expands (entries : List (Entry E Ctx))
    {memo result : Array (Checked sign context p a b)}
    (h : entries.foldlM (fun memo entry => do
      let t ← step sign context p a b memo entry
      pure (memo.push t)) memo = some result) :
    entries.foldlM (fun memo entry => do
      let t ← Expansion.step memo entry
      pure (memo.push t)) (memo.map Checked.value) = some (result.map Checked.value) := by
  induction entries generalizing memo with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    subst result
    rfl
  | cons entry entries ih =>
    simp only [List.foldlM_cons] at h ⊢
    cases hs : step sign context p a b memo entry with
    | none => simp [hs, bind, Option.bind] at h
    | some t =>
      simp only [hs, bind, Option.bind, pure] at h
      rw [step_expands hs]
      simpa only [bind, Option.bind, pure, Array.map_push] using ih h

/-- An accepted graph expands to exactly the tree returned by checked replay.
This applies to arbitrary supplied graph literals, including shared children. -/
theorem replay_expands {dag : Dag E Ctx} {qs : List (DensePoly E)}
    {t : {tree : Replay E Ctx // tree.check sign context p a b qs = true}}
    (h : replay? sign context p a b qs dag = some t) : expand? dag = some t.val := by
  unfold replay? at h
  cases hm : dag.entries.foldlM (init := #[]) (fun memo entry => do
      let next ← step sign context p a b memo entry
      pure (memo.push next)) with
  | none =>
    rw [hm] at h
    simp [bind, Option.bind] at h
  | some memo =>
    have hexp : Expansion.run dag.entries = some (memo.map Checked.value) := by
      unfold Expansion.run
      rw [← Array.foldlM_toList] at hm ⊢
      simpa using fold_expands dag.entries.toList hm
    rw [hm] at h
    simp only [bind, Option.bind] at h
    cases hr : memo[dag.root]? with
    | none => simp [hr] at h
    | some root =>
      simp only [hr] at h
      split at h
      · simp only [pure, Option.some.injEq] at h
        subst t
        simp [expand?, hexp, hr]
      · simp at h

/-- Exact graph encoding preserves acceptance and rejection of every supplied
tree; the encoder cannot repair an invalid literal witness or binding. -/
theorem check_encode_eq [Hashable E] [Hashable Ctx] (tree : Replay E Ctx)
    (qs : List (DensePoly E)) :
    check sign context p a b qs (encode tree) = tree.check sign context p a b qs := by
  cases ht : tree.check sign context p a b qs with
  | true => exact check_encode ht
  | false =>
    cases hg : check sign context p a b qs (encode tree) with
    | false => rfl
    | true =>
      obtain ⟨t, hr, _⟩ := check_replay hg
      have he : tree = t.val := Option.some.inj ((expand_encode tree).symm.trans (replay_expands hr))
      have ha := t.property
      rw [← he, ht] at ha
      cases ha

/-- Graph and tree descriptor extraction agree on every encoded literal tree,
including malformed descriptors and rejected certificate contents. -/
theorem descriptor_encode [Hashable E] [Hashable Ctx] {raw : RawDescriptor E Ctx} (tree : Replay E Ctx) :
    descriptor? sign context raw (encode tree) = Descriptor.ofReplay? sign context raw tree := by
  by_cases hw : raw.wellFormed = true
  · by_cases hctx : raw.context = context
    · by_cases hc : tree.check sign context raw.head raw.lower raw.upper raw.queries = true
      · simp only [descriptor?, hw, hctx, dite_eq_left, replay_encode hc, bind, Option.bind]
        by_cases hone : (tree.table hc).count raw.signs = 1
        · rw [dite_eq_left hone]
          exact (Descriptor.ofReplay_ofTable raw tree hw hctx hc hone).symm
        · have hn : tree.node.system.count raw.signs ≠ 1 := by
            simpa only [Replay.table_lookup] using hone
          simp [hone, Descriptor.ofReplay?, RawDescriptor.check, hw, hctx, hc, hn]
      · have hn : replay? sign context raw.head raw.lower raw.upper raw.queries (encode tree) = none := by
          have he := check_encode_eq (sign := sign) (context := context)
            (p := raw.head) (a := raw.lower) (b := raw.upper) (qs := raw.queries) tree
          simp only [check] at he
          cases hr : replay? sign context raw.head raw.lower raw.upper raw.queries (encode tree) with
          | none => rfl
          | some t => simp [hr, hc] at he
        simp [descriptor?, hw, hctx, hn, bind, Option.bind,
          Descriptor.ofReplay?, RawDescriptor.check, hc]
    · simp [descriptor?, hw, hctx, Descriptor.ofReplay?, RawDescriptor.check]
  · simp [descriptor?, hw, Descriptor.ofReplay?, RawDescriptor.check]

end Hex.SignDet.Dag
