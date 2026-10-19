/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Dag

/-! Structural transformations of literal BKR graphs, preserving every entry
and child reference. A transformation produces raw evidence; its target must
be validated with the target coefficient operations and caller bindings. -/

public section

namespace Hex.SignDet.Dag

variable {E : Type u} {F : Type v} {Ctx : Type w} {Target : Type z}
variable [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]

/-- Transform each literal node once, retaining its index, both child edges and
the selected root. This works across coefficient and context types without
expanding a shared graph to a tree. It does not transport acceptance proofs:
call `validate?` or `replay?` with the target operations and full bindings. -/
@[expose] def mapNodes (f : Node E Ctx → Node F Target) (graph : SignDet.Dag E Ctx) :
    SignDet.Dag F Target :=
  ⟨graph.entries.map (fun entry => ⟨f entry.node, entry.children⟩), graph.root⟩

/-- Structural conversion retains all entries, including unreachable ones. -/
@[simp] theorem size_mapNodes (f : Node E Ctx → Node F Target) (graph : SignDet.Dag E Ctx) :
    (graph.mapNodes f).entries.size = graph.entries.size := by
  simp [mapNodes]

/-- Each retained entry contains the transformed original literal node. -/
@[simp] theorem node_mapNodes (f : Node E Ctx → Node F Target)
    (graph : SignDet.Dag E Ctx) (i : Nat) (h : i < graph.entries.size) :
    ((graph.mapNodes f).entries[i]'(by simpa using h)).node =
      f (graph.entries[i]'h).node := by
  simp [mapNodes]

/-- Every shared edge retains its exact original index after conversion. -/
@[simp] theorem children_mapNodes (f : Node E Ctx → Node F Target)
    (graph : SignDet.Dag E Ctx) (i : Nat) (h : i < graph.entries.size) :
    ((graph.mapNodes f).entries[i]'(by simpa using h)).children =
      (graph.entries[i]'h).children := by
  simp [mapNodes]

/-- The root index is retained even on malformed raw graphs. -/
@[simp] theorem root_mapNodes (f : Node E Ctx → Node F Target) (graph : SignDet.Dag E Ctx) :
    (graph.mapNodes f).root = graph.root := rfl

end Hex.SignDet.Dag
