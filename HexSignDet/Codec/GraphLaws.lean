/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec
public import HexSignDet.Codec.NodeLaws
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all Lean.Data.Json.Basic

public section

namespace Hex.SignDet.Codec
open Lean

variable {E Ctx : Type} [Zero E] [DecidableEq E]

/-- The node decoder's structural bounds. These do not assert any arithmetic,
rank, support-completeness or root-count identity. -/
structure Shape (n : Node E Ctx) : Prop where
  rows : ∀ x ∈ n.system.rows.toList, x.length = n.queries.length
  columns : ∀ x ∈ n.system.columns.toList, x.length = n.queries.length
  rankRows : n.basis.rank ≤ n.size
  rankCols : n.basis.rank ≤ n.system.positive.length
  reductions : ∀ r ∈ n.reductions.toList, ∀ t ∈ r, ∀ s ∈ t.steps,
    s.index < n.queries.length
  preparation : ∀ t ∈ n.preparation, ∀ s ∈ t.steps, s.index < n.queries.length

theorem Shape.read_node (h : Shape n) (value : ValueCodec E) (context : ValueCodec Ctx)
    (hv : value.Lawful) (hc : context.Lawful) :
    readNode value context (node value context n) = .ok n :=
  Codec.read_node value context hv hc n h.rows h.columns h.rankRows h.rankCols
    h.reductions h.preparation

/-- Earlier child indices roundtrip without changing their left/right order. -/
theorem read_children (children : Option (Nat × Nat))
    (bounds : ∀ pair ∈ children, pair.1 < earlier ∧ pair.2 < earlier) :
    readChildren earlier (option (fun (i, j) => Json.arr #[toJson i, toJson j]) children) =
      .ok children := by
  unfold readChildren
  apply read_option_of
  intro pair hp
  obtain ⟨left, right⟩ := pair
  obtain ⟨hl, hr⟩ := bounds (left, right) hp
  simp [tuple, Json.getArr?, index, read_nat, hl, hr, bind, Except.bind, pure, Except.pure]

variable [DecidableEq Ctx]

/-- Entry roundtrips retain the complete literal node and both references. -/
theorem read_entry (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (context : Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (e : Dag.Entry E Ctx)
    (shape : Shape e.node) (subject : bindings context p lo hi e.node = true)
    (bounds : ∀ pair ∈ e.children, pair.1 < earlier ∧ pair.2 < earlier) :
    readEntry value ctx context p lo hi earlier (entry value ctx e) = .ok e := by
  simp [readEntry, entry, tuple, Json.getArr?, bind, Except.bind, pure, Except.pure,
    read_children e.children bounds, shape.read_node value ctx hv hc, subject]

/-- The actual left fold reconstructs every entry in order, including entries
unreachable from the requested root. -/
theorem read_entries (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (context : Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (entries : Array (Dag.Entry E Ctx))
    (shape : ∀ e ∈ entries, Shape e.node)
    (subjects : ∀ e ∈ entries, bindings context p lo hi e.node = true)
    (bounds : ∀ (i : Nat) (h : i < entries.size), ∀ pair ∈ entries[i].children,
      pair.1 < i ∧ pair.2 < i) :
    (entries.map (entry value ctx)).foldlM
      (fun earlier j => do
        return earlier.push (← readEntry value ctx context p lo hi earlier.size j)) #[] =
      .ok entries := by
  have array_induction {α : Type} (P : Array α → Prop) (empty : P #[])
      (push : ∀ xs x, P xs → P (xs.push x)) (xs : Array α) : P xs := by
    have aux (ys : List α) : P ys.reverse.toArray := by
      induction ys with
      | nil => exact empty
      | cons y ys ih => simpa using push ys.reverse.toArray y ih
    simpa using aux xs.toList.reverse
  induction entries using array_induction with
  | empty => simp [pure, Except.pure]
  | @push entries e ih =>
    have he := shape e (by simp)
    have hs := subjects e (by simp)
    have hb : ∀ pair ∈ e.children, pair.1 < entries.size ∧ pair.2 < entries.size := by
      simpa using bounds entries.size (by simp)
    have hp := ih (fun x hx => shape x (by simp [hx]))
      (fun x hx => subjects x (by simp [hx]))
      (fun i hi => by simpa [Array.getElem_push_lt hi] using bounds i (by simpa using Nat.lt_succ_of_lt hi))
    rw [Array.map_push, Array.foldlM_push, hp]
    simp [bind, Except.bind, pure, Except.pure, read_entry value ctx hv hc context p lo hi e he hs hb]

/-- Structured graph encoding and decoding preserve every supplied literal
field. The hypotheses are exactly structural bounds and literal bindings;
independent arithmetic replay may still reject the decoded graph. -/
theorem read_graph (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (context : Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (d : Dag E Ctx)
    (root : d.root < d.entries.size)
    (shape : ∀ e ∈ d.entries, Shape e.node)
    (subjects : ∀ e ∈ d.entries, bindings context p lo hi e.node = true)
    (bounds : ∀ (i : Nat) (h : i < d.entries.size), ∀ pair ∈ d.entries[i].children,
      pair.1 < i ∧ pair.2 < i) :
    readGraph value ctx context p lo hi (graph value ctx d) = .ok d := by
  have he := read_entries value ctx hv hc context p lo hi d.entries shape subjects bounds
  simp only [Array.size_map, bind, Except.bind, pure, Except.pure] at he
  simp [readGraph, graph, tuple, array, Json.getArr?, bind, Except.bind, pure, Except.pure,
    Nat.not_le.mpr root, he]

end Hex.SignDet.Codec
