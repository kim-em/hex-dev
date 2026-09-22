/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.DagMemo

public section

namespace Hex.SignDet.Dag

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] [DecidableEq Ctx]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E]
    {sign : E → Int} {context : Ctx} {p : DensePoly E} {a b : Endpoint E}

/-- Once a local replay step succeeds, appending accepted entries cannot change
its exact result. Only successful earlier child references are consulted. -/
theorem step_mono {before after : Array (Checked sign context p a b)}
    (hm : Prefix before after) {entry : Entry E Ctx} {t : Checked sign context p a b}
    (h : step sign context p a b before entry = some t) :
    step sign context p a b after entry = some t := by
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
      | some r =>
        simpa only [hl, hr, hm left l hl, hm right r hr] using h

theorem step_leaf (memo : Array (Checked sign context p a b)) {n : Node E Ctx}
    (h : (Replay.leaf n).check sign context p a b n.queries = true) :
    step sign context p a b memo ⟨n, none⟩ = some ⟨.leaf n, h⟩ := by
  simp only [step, h, dite_eq_left, pure]

theorem step_split {memo : Array (Checked sign context p a b)} {n : Node E Ctx}
    {l r : Checked sign context p a b} {left right : Nat}
    (hl : memo[left]? = some l) (hr : memo[right]? = some r)
    (h : (Replay.split n l.value r.value).check sign context p a b n.queries = true) :
    step sign context p a b memo ⟨n, some (left, right)⟩ =
      some ⟨.split n l.value r.value, h⟩ := by
  have hc := Replay.check_children h
  have hlq := (Node.check_bindings (Replay.check_node hc.1)).1.2.2.2.2
  have hrq := (Node.check_bindings (Replay.check_node hc.2.1)).1.2.2.2.2
  have hn : (decide (1 < n.queries.length) &&
      decide (n.system.columns.toList = product l.value.node.system.support r.value.node.system.support) &&
      decide (n.system.rows.toList = product l.value.node.rows r.value.node.rows) &&
      n.check sign context p a b n.queries) = true := by
    simp only [Replay.check, Bool.and_eq_true] at h
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨h.1.1.1.1.1, h.1.1.2⟩, h.1.2⟩, h.2⟩
  simp only [step, hl, hr, bind, Option.bind, hlq, hrq, dite_eq_left, hn, pure]

variable [Hashable E] [Hashable Ctx]

/-- The actual recursive encoder preserves an accepted tree literally, extends
all prior memo bindings, and leaves every generated graph entry checked. -/
theorem encodeFrom_checks {state : Encoder E Ctx}
    {memo : Array (Checked sign context p a b)} (hv : state.Valid (step sign context p a b) memo)
    (tree : Replay E Ctx) (h : tree.check sign context p a b tree.node.queries = true) :
    ∃ next : Array (Checked sign context p a b),
      (encodeFrom state tree).1.Valid (step sign context p a b) next ∧ Prefix memo next ∧
      next[(encodeFrom state tree).2]? = some ⟨tree, h⟩ := by
  induction tree generalizing state memo with
  | leaf n =>
    exact Encoder.insert_valid step_mono hv (step_leaf memo h)
  | split n l r ihl ihr =>
    have hc := Replay.check_children h
    have hlq := (Node.check_bindings (Replay.check_node hc.1)).1.2.2.2.2
    have hrq := (Node.check_bindings (Replay.check_node hc.2.1)).1.2.2.2.2
    have hl : l.check sign context p a b l.node.queries = true := by
      simpa only [hlq] using hc.1
    have hr : r.check sign context p a b r.node.queries = true := by
      simpa only [hrq] using hc.2.1
    obtain ⟨lm, hvl, hel, hal⟩ := ihl hv hl
    obtain ⟨rm, hvr, her, har⟩ := ihr hvl hr
    have has : step sign context p a b rm
        ⟨n, some ((encodeFrom state l).2, (encodeFrom (encodeFrom state l).1 r).2)⟩ =
        some ⟨.split n l r, h⟩ :=
      step_split (her _ _ hal) har h
    obtain ⟨next, hvn, hen, han⟩ := Encoder.insert_valid step_mono hvr has
    exact ⟨next, hvn, hel.trans (her.trans hen), han⟩

/-- Encoding an accepted literal tree yields a graph whose checked replay
returns that same tree, with the original caller's exact query binding. This
uses no root-sum or semantic soundness premise. -/
theorem replay_encode {tree : Replay E Ctx} {qs : List (DensePoly E)}
    (h : tree.check sign context p a b qs = true) :
    replay? sign context p a b qs (encode tree) = some ⟨tree, h⟩ := by
  have hq := (Node.check_bindings (Replay.check_node h)).1.2.2.2.2
  have ht : tree.check sign context p a b tree.node.queries = true := by
    simpa only [hq] using h
  obtain ⟨memo, hv, _, hi⟩ := encodeFrom_checks (Encoder.valid_empty _) tree ht
  unfold replay? encode
  rw [hv.replay]
  simp only [bind, Option.bind, hi, hq, dite_eq_left, pure]

/-- Graph encoding cannot fail checked replay for an accepted tree. -/
theorem check_encode {tree : Replay E Ctx} {qs : List (DensePoly E)}
    (h : tree.check sign context p a b qs = true) :
    check sign context p a b qs (encode tree) = true := by
  simp only [check, replay_encode h, Option.isSome_some]

end Hex.SignDet.Dag
