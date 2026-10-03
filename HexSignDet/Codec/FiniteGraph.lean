/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.FiniteLaws
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Bytes

public section

namespace Hex.SignDet.Codec

variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]

/-- All stored node and moment contexts, including unreachable entries. -/
@[expose] def graphContexts (d : Dag E Ctx) : List Ctx :=
  d.entries.toList.flatMap (fun e => nodeContexts e.node)

private theorem read_entries_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E)
    (entries : Array (Dag.Entry E Ctx))
    (hv : ∀ e ∈ entries, value.Covers (Coefficients.node e.node))
    (hc : ∀ e ∈ entries, ctx.Covers (nodeContexts e.node))
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
    have he := read_node_covered value ctx e.node
      (hv e (by simp)) (hc e (by simp)) (shape e (by simp))
    have hs := subjects e (by simp)
    have hb : ∀ pair ∈ e.children, pair.1 < entries.size ∧ pair.2 < entries.size := by
      simpa using bounds entries.size (by simp)
    have hp := ih (fun x hx => hv x (by simp [hx]))
      (fun x hx => hc x (by simp [hx]))
      (fun x hx => shape x (by simp [hx]))
      (fun x hx => subjects x (by simp [hx]))
      (fun i hi => by
        simpa [Array.getElem_push_lt hi] using bounds i (by simpa using Nat.lt_succ_of_lt hi))
    rw [Array.map_push, Array.foldlM_push, hp]
    simp [bind, Except.bind, pure, Except.pure, readEntry, entry, tuple,
      Json.getArr_arr, read_children e.children hb, he, hs]

/-- The complete graph roundtrips with finite coverage of its actual stored
coefficients and contexts. No global law for a partial reader is assumed. -/
theorem read_graph_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E) (d : Dag E Ctx)
    (hv : value.Covers (Coefficients.graph d)) (hc : ctx.Covers (graphContexts d))
    (root : d.root < d.entries.size) (shape : ∀ e ∈ d.entries, Shape e.node)
    (subjects : ∀ e ∈ d.entries, bindings context p lo hi e.node = true)
    (bounds : ∀ (i : Nat) (h : i < d.entries.size), ∀ pair ∈ d.entries[i].children,
      pair.1 < i ∧ pair.2 < i) :
    readGraph value ctx context p lo hi (graph value ctx d) = .ok d := by
  simp only [Coefficients.graph, graphContexts, ValueCodec.covers_flatMap] at hv hc
  have entries := read_entries_covered value ctx context p lo hi d.entries
    (fun e he => hv e (by simpa using he)) (fun e he => hc e (by simpa using he))
    shape subjects bounds
  simp only [Array.size_map, bind, Except.bind, pure, Except.pure] at entries
  simp [readGraph, graph, tuple, array, Json.getArr_arr, bind, Except.bind,
    pure, Except.pure, Nat.not_le.mpr root, entries]

/-- Finite-reader correspondence for the actual byte printer and parser.
Lexical acceptance and graph shape/bindings retain their usual checks. -/
theorem decode_graph_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E) (d : Dag E Ctx)
    (hv : value.Covers (Coefficients.graph d)) (hc : ctx.Covers (graphContexts d))
    (root : d.root < d.entries.size) (shape : ∀ e ∈ d.entries, Shape e.node)
    (subjects : ∀ e ∈ d.entries, bindings context p lo hi e.node = true)
    (bounds : ∀ (i : Nat) (h : i < d.entries.size), ∀ pair ∈ d.entries[i].children,
      pair.1 < i ∧ pair.2 < i) (limits : Limits)
    (bytes : checkBytes limits (d.encodeBytes value ctx) = .ok ()) :
    decodeGraph value ctx context p lo hi (d.encodeBytes value ctx) limits = .ok d := by
  unfold decodeGraph Dag.encodeBytes at *
  rw [parse_write _ _ bytes]
  simp only [bind, Except.bind]
  exact read_graph_covered value ctx context p lo hi d hv hc root shape subjects bounds

/-- info: 'Hex.SignDet.Codec.decode_graph_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decode_graph_covered

end Hex.SignDet.Codec
