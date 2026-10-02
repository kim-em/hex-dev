/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraph.Sparse.Relabel
public import HexGraphIso.Colored

public section

namespace Hex.GraphIso.Sparse

/-- A sparse graph with the same ordered, surjective colouring as dense graphs. -/
structure Colored (n k : Nat) where
  graph : SparseGraph n
  coloring : Coloring n k
deriving DecidableEq

namespace Colored

variable {n k : Nat}

/-- Explicitly materialize a dense coloured graph. -/
@[expose] def toDense (G : Colored n k) : GraphIso.Colored n k :=
  ⟨G.graph.toDense, G.coloring⟩

@[expose] def relabel (G : Colored n k) (l : Label n) : Colored n k where
  graph := G.graph.relabel l.perm
  coloring := {
    cells := Hex.Vector.ofFn' fun i => G.coloring.cells[l.get i]
    onto := fun c => by
      rcases G.coloring.onto c with ⟨v, hv⟩
      rcases l.perm.get_surj v with ⟨i, hi⟩
      subst hi
      refine ⟨i, ?_⟩
      simpa [Hex.Vector.get_eq_getElem, Label.get] using hv }

@[simp] theorem toDense_relabel (G : Colored n k) (l : Label n) :
    (G.relabel l).toDense = G.toDense.relabel l := by
  apply GraphIso.Colored.ext <;> intro i <;> try intro j
  · simp [toDense, relabel, Label.get]
  · rfl

theorem toDense_injective : Function.Injective (toDense (n := n) (k := k)) := by
  intro G H h
  have hg : G.graph = H.graph := by
    apply SparseGraph.ext
    intro i j
    have he := congrArg (fun A : GraphIso.Colored n k => A.graph.adj i j) h
    simpa [toDense] using he
  have hc : G.coloring = H.coloring := congrArg (·.coloring) h
  cases G; cases H; cases hg; cases hc; rfl

@[simp] theorem relabel_id (G : Colored n k) : G.relabel (Label.id n) = G := by
  apply toDense_injective
  simp

theorem relabel_relabel (G : Colored n k) (l m : Label n) :
    (G.relabel l).relabel m = G.relabel (l.comp m) := by
  apply toDense_injective
  simp [GraphIso.Colored.relabel_relabel]

end Colored

structure CanonResult (n k : Nat) where
  form : Colored n k
  label : Label n
deriving DecidableEq

end Hex.GraphIso.Sparse
