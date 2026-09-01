/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Perm

public section

/-!
Coloured graphs: a finite simple undirected graph together with an ordered
vertex colouring in which every colour is used.

nauty calls a vertex colouring a partition and its colour classes cells.
Colours are ordered: the first cell comes before the second cell in every
canonical labelling, and an isomorphism preserves each colour index. The
executable representation is a colour vector plus a surjectivity proof, so
there is no empty cell and no redundant colour count in the public type.

`DecidableEq (Coloring n k)` compares only `cells`; proof irrelevance
handles `onto`. Equality of `Colored n k` is equality of the graph and the
colour vector, which keeps fixture comparison kernel-reducible.
-/

namespace Hex.GraphIso

/-- An ordered vertex colouring of `Fin n` by colours `Fin k` in which every
colour is used. -/
structure Coloring (n k : Nat) where
  /-- The colour of each vertex. -/
  cells : Vector (Fin k) n
  /-- Every colour is used. -/
  onto : Function.Surjective cells.get

/-- `Vector.get` agrees with element access; core states no lemmas about
`Vector.get`, so the `onto` field is used through this bridge. -/
theorem _root_.Vector.get_eq_getElem {α : Type u} {m : Nat} (v : Vector α m) (i : Fin m) :
    v.get i = v[i] := rfl

namespace Coloring

variable {n k : Nat}

theorem ext_cells {c d : Coloring n k} (h : c.cells = d.cells) : c = d := by
  cases c; cases d; cases h; rfl

@[ext] theorem ext {c d : Coloring n k} (h : ∀ i : Fin n, c.cells[i] = d.cells[i]) :
    c = d := by
  refine ext_cells (Vector.ext fun i hi => h ⟨i, hi⟩)

@[expose] instance : DecidableEq (Coloring n k) := fun c d =>
  if h : c.cells = d.cells then
    .isTrue (ext_cells h)
  else
    .isFalse fun e => h (congrArg Coloring.cells e)

/-- Checked construction: accepts exactly the colour vectors using every
colour. -/
@[expose] def ofVector? (v : Vector (Fin k) n) : Option (Coloring n k) :=
  if h : ∀ c : Fin k, ∃ i : Fin n, v.get i = c then
    some ⟨v, fun c => h c⟩
  else
    none

theorem isSome_ofVector? (v : Vector (Fin k) n) :
    (ofVector? v).isSome = true ↔ ∀ c : Fin k, ∃ i : Fin n, v.get i = c := by
  rw [ofVector?]
  split <;> simp_all

/-- The constant zero colouring: the one-cell colouring of a nonempty vertex
set. -/
@[expose] def trivial (n : Nat) (h : 0 < n) : Coloring n 1 where
  cells := Hex.Vector.ofFn' fun _ => 0
  onto c := ⟨⟨0, h⟩, by
    have : c = 0 := Fin.ext (Nat.lt_one_iff.mp c.isLt)
    simp [Vector.get_eq_getElem, this]⟩

/-- The colouring `i ↦ i % k`, onto whenever `k ≤ n`. -/
@[expose] def mod (n k : Nat) (hk : 0 < k) (hkn : k ≤ n) : Coloring n k where
  cells := Hex.Vector.ofFn' fun i => ⟨i.val % k, Nat.mod_lt _ hk⟩
  onto c := by
    refine ⟨⟨c.val, Nat.lt_of_lt_of_le c.isLt hkn⟩, ?_⟩
    rw [Vector.get_eq_getElem]
    simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn']
    exact Fin.ext (Nat.mod_eq_of_lt c.isLt)

/-- The number of vertices with each colour. -/
@[expose] def cellSizes (c : Coloring n k) : Vector Nat k :=
  Hex.Vector.ofFn' fun j => ((List.finRange n).filter fun i => c.cells[i] == j).length

end Coloring

/-- A coloured graph: a simple undirected graph on `Fin n` together with an
ordered onto colouring by `Fin k`. -/
structure Colored (n k : Nat) where
  /-- The underlying simple graph. -/
  graph : Graph n
  /-- The ordered vertex colouring. -/
  coloring : Coloring n k

namespace Colored

variable {n k : Nat}

@[expose] instance : DecidableEq (Colored n k) := fun G H =>
  if h : G.graph = H.graph ∧ G.coloring = H.coloring then
    .isTrue (by cases G; cases H; cases h.1; cases h.2; rfl)
  else
    .isFalse fun e => h (by cases e; exact ⟨rfl, rfl⟩)

@[ext] theorem ext {G H : Colored n k}
    (hg : ∀ i j, G.graph.adj i j = H.graph.adj i j)
    (hc : ∀ i : Fin n, G.coloring.cells[i] = H.coloring.cells[i]) : G = H := by
  cases G; cases H
  have h1 := Graph.ext hg
  have h2 := Coloring.ext hc
  cases h1; cases h2; rfl

/-- Relabel a coloured graph by a labelling `l`: new vertex `i` is old
vertex `l[i]`, so `(relabel G l).graph.adj i j = G.graph.adj l[i] l[j]` and
`(relabel G l).coloring.cells[i] = G.coloring.cells[l[i]]`. -/
@[expose] def relabel (G : Colored n k) (l : Label n) : Colored n k where
  graph := G.graph.relabel fun i => l.get i
  coloring :=
    { cells := Hex.Vector.ofFn' fun i => G.coloring.cells[l.get i]
      onto := fun c => by
        rcases G.coloring.onto c with ⟨v, hv⟩
        rcases l.perm.get_surj v with ⟨i, hi⟩
        subst hi
        refine ⟨i, ?_⟩
        rw [Vector.get_eq_getElem] at hv ⊢
        simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn', Fin.eta]
        exact hv }

@[simp] theorem adj_relabel (G : Colored n k) (l : Label n) (i j : Fin n) :
    (G.relabel l).graph.adj i j = G.graph.adj (l.get i) (l.get j) :=
  Graph.adj_relabel ..

@[simp] theorem cells_relabel (G : Colored n k) (l : Label n) (i : Nat)
    (hi : i < n) :
    (G.relabel l).coloring.cells[i] = G.coloring.cells[l.get ⟨i, hi⟩] := by
  show (Hex.Vector.ofFn' fun j => G.coloring.cells[l.get j])[i] = _
  simp

@[simp] theorem relabel_id (G : Colored n k) : G.relabel (Label.id n) = G :=
  Colored.ext (fun i j => by simp) (fun i => by simp)

theorem relabel_relabel (G : Colored n k) (l m : Label n) :
    (G.relabel l).relabel m = G.relabel (l.comp m) :=
  Colored.ext (fun i j => by simp) (fun i => by simp)

end Colored

end Hex.GraphIso
