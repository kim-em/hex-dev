/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib
public import Mathlib.Data.Fintype.Powerset
public meta import HexGraphIsoMathlib
public meta import Mathlib.Data.Fintype.Powerset

/-!
Regression tests for the `graph_iso` extension to `SimpleGraph` goals:
every supported goal shape, distinct vertex types of equal cardinality,
unequal-cardinality negatives, ordered colours preserved and violated,
empty-graph goal shapes, graphs built through `SimpleGraph.fromRel`, and
the diagnostics on unprovable goals and exhausted limits.
-/

namespace HexGraphIsoMathlib.TacticTests

open Hex.GraphIso.Mathlib SimpleGraph

/-! # Cycles and paths on `Fin 5` through transparent constructors -/

/-- The five-cycle, joined by the successor relation. -/
def c5a : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun i j => j = i + 1
/-- The five-cycle again, joined by adding two: isomorphic to `c5a`. -/
def c5b : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun i j => j = i + 2
/-- The path on five vertices, which is not isomorphic to `c5a`. -/
def p5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun i j => j.val = i.val + 1

instance : DecidableRel c5a.Adj := fun _ _ =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj ..).symm
instance : DecidableRel c5b.Adj := fun _ _ =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj ..).symm
instance : DecidableRel p5.Adj := fun _ _ =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj ..).symm

example : Nonempty (c5a ≃g c5b) := by graph_iso
example : c5a ≃g c5b := by graph_iso
example : IsEmpty (c5a ≃g p5) := by graph_iso
example : ¬ Nonempty (c5a ≃g p5) := by graph_iso
example : c5a ≃g c5b := by
  graph_iso (maxSearchNodes := 200000) (maxKernelSteps := 10000000)

/-! # The Petersen graph three ways, with distinct vertex types -/

/-- The generalized Petersen presentation `G(5, 2)`: outer pentagon,
inner star, spokes. -/
def petersenDrawing : SimpleGraph (Fin 10) where
  Adj i j :=
    (i.val < 5 ∧ j.val < 5 ∧
      (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
    (5 ≤ i.val ∧ 5 ≤ j.val ∧
      (j.val = 5 + ((i.val + 2) % 5) ∨ i.val = 5 + ((j.val + 2) % 5))) ∨
    (i.val < 5 ∧ j.val = i.val + 5) ∨ (j.val < 5 ∧ i.val = j.val + 5)
  symm := ⟨by intro i j h; omega⟩
  loopless := ⟨by intro i h; omega⟩

instance : DecidableRel petersenDrawing.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- The Kneser presentation `K(5, 2)`: two-element subsets of `Fin 5`,
joined when disjoint. -/
def kneser52 : SimpleGraph {s : Finset (Fin 5) // s.card = 2} where
  Adj s t := Disjoint s.val t.val ∧ s ≠ t
  symm := ⟨by intro s t h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro s h; exact h.2 rfl⟩

instance : DecidableRel kneser52.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The pentagonal prism: cubic on ten vertices like the Petersen graph,
so degree refinement alone cannot separate them. -/
def pentagonalPrism : SimpleGraph (Fin 10) where
  Adj i j :=
    (i.val < 5 ∧ j.val < 5 ∧
      (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
    (5 ≤ i.val ∧ 5 ≤ j.val ∧
      (j.val = 5 + ((i.val + 1) % 5) ∨ i.val = 5 + ((j.val + 1) % 5))) ∨
    (i.val < 5 ∧ j.val = i.val + 5) ∨ (j.val < 5 ∧ i.val = j.val + 5)
  symm := ⟨by intro i j h; omega⟩
  loopless := ⟨by intro i h; omega⟩

instance : DecidableRel pentagonalPrism.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 400000 in
example : Nonempty (petersenDrawing ≃g kneser52) := by graph_iso

set_option maxRecDepth 400000 in
example : IsEmpty (petersenDrawing ≃g pentagonalPrism) := by graph_iso

/-! # Unequal cardinalities close immediately -/

example : IsEmpty (c5a ≃g petersenDrawing) := by graph_iso
example : ¬ Nonempty (c5a ≃g petersenDrawing) := by graph_iso

/-! # Empty-graph goal shapes -/

/-- The graph on no vertices. -/
def emptyG : SimpleGraph (Fin 0) := ⊥
instance : DecidableRel emptyG.Adj := fun v _ => v.elim0

example : emptyG ≃g emptyG := by graph_iso
example : Nonempty (emptyG ≃g emptyG) := by graph_iso
example : IsEmpty (emptyG ≃g c5a) := by graph_iso
example : ¬ Nonempty (c5a ≃g emptyG) := by graph_iso

/-! # Ordered colours constrain isomorphisms

Two edge-marked and one nonedge-marked two-colourings of the six-cycle:
`graph_iso` proves the edge-marked pair isomorphic and refutes the
nonedge-marked colouring against either. -/

/-- The six-cycle. -/
def c6 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun i j => j = i + 1

instance : DecidableRel c6.Adj := fun _ _ =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj ..).symm

/-- The six-cycle with the two-colouring `f`. -/
def mark (f : Fin 6 → Fin 2)
    (h : Function.Surjective f) : Colored (Fin 6) 2 :=
  { graph := c6, color := f, onto := h }

/-- The six-cycle with the endpoints of one edge marked colour `0`. -/
def edgeMarkA : Colored (Fin 6) 2 :=
  mark (fun i => if i.val ≤ 1 then 0 else 1)
    (fun c => by
      match c with
      | 0 => exact ⟨0, by decide⟩
      | 1 => exact ⟨3, by decide⟩)

/-- The six-cycle with the endpoints of a different edge marked
colour `0`. -/
def edgeMarkB : Colored (Fin 6) 2 :=
  mark (fun i => if 3 ≤ i.val ∧ i.val ≤ 4 then 0 else 1)
    (fun c => by
      match c with
      | 0 => exact ⟨3, by decide⟩
      | 1 => exact ⟨0, by decide⟩)

/-- The six-cycle with two non-adjacent vertices marked colour `0`. -/
def nonedgeMark : Colored (Fin 6) 2 :=
  mark (fun i => if i.val = 0 ∨ i.val = 3 then 0 else 1)
    (fun c => by
      match c with
      | 0 => exact ⟨0, by decide⟩
      | 1 => exact ⟨1, by decide⟩)

instance : DecidableRel edgeMarkA.graph.Adj :=
  inferInstanceAs (DecidableRel c6.Adj)
instance : DecidableRel edgeMarkB.graph.Adj :=
  inferInstanceAs (DecidableRel c6.Adj)
instance : DecidableRel nonedgeMark.graph.Adj :=
  inferInstanceAs (DecidableRel c6.Adj)

example : Colored.Isomorphic edgeMarkA edgeMarkB := by graph_iso
example : Colored.Iso edgeMarkA edgeMarkB := by graph_iso
example : ¬ Colored.Isomorphic edgeMarkA nonedgeMark := by graph_iso
example : IsEmpty (Colored.Iso edgeMarkB nonedgeMark) := by graph_iso

/-! # Diagnostics -/

/-- error: graph_iso: the graphs are not isomorphic; the positive goal is not provable -/
#guard_msgs in
example : Nonempty (c5a ≃g p5) := by graph_iso

/-- error: graph_iso: the graphs are isomorphic; the negative goal is not provable -/
#guard_msgs in
example : IsEmpty (c5a ≃g c5b) := by graph_iso

/-- error: graph_iso: the vertex types have cardinalities 5 and 10; the positive goal is not provable -/
#guard_msgs in
example : Nonempty (c5a ≃g petersenDrawing) := by graph_iso

/-- error: graph_iso: search exhausted: visited 12 nodes but maxSearchNodes := 0 -/
#guard_msgs in
example : Nonempty (c5a ≃g c5b) := by graph_iso (maxSearchNodes := 0)

end HexGraphIsoMathlib.TacticTests
