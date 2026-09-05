/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Ops

public section

/-!
The uncoloured surface.

Colours are the general input, but most callers have a bare `Graph n`.
This module states isomorphism directly on `Graph n` and wraps every
public operation, so an uncoloured caller neither builds a `Colored n 1`
at the call nor unwraps one from the conclusion.

`Graph.singleColor` is the one-cell view, and
`Graph.isomorphic_singleColor_iff` identifies the two notions of
isomorphism through it. Every theorem here is transported along that
equivalence rather than reproved, so the uncoloured surface makes
exactly the promises the coloured one does, completeness and canonical
invariance included.
-/

namespace Hex.Graph

variable {n : Nat}

/-! # Uncoloured isomorphism -/

/-- The forward permutation `p` (old vertex to image) is an isomorphism
from `G` to `H`: it transports adjacency. -/
def IsIso (G H : Graph n) (p : GraphIso.Perm n) : Prop :=
  ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j

/-- Two graphs are isomorphic when some forward permutation transports
one onto the other. -/
def Isomorphic (G H : Graph n) : Prop :=
  ∃ p, IsIso G H p

theorem Isomorphic.intro {G H : Graph n} (p : GraphIso.Perm n)
    (h : IsIso G H p) : Isomorphic G H :=
  ⟨p, h⟩

theorem Isomorphic.elim {G H : Graph n} (h : Isomorphic G H) :
    ∃ p, IsIso G H p :=
  h

namespace IsIso

theorem adj_eq {G H : Graph n} {p : GraphIso.Perm n} (h : IsIso G H p) :
    ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j :=
  h

theorem refl (G : Graph n) : IsIso G G (GraphIso.Perm.id n) :=
  fun _ _ => by simp

theorem symm {G H : Graph n} {p : GraphIso.Perm n} (h : IsIso G H p) :
    IsIso H G p.inv := by
  intro i j
  have := h (p.inv.get i) (p.inv.get j)
  simp only [GraphIso.Perm.get_inv_get] at this
  exact this.symm

theorem trans {G H K : Graph n} {p q : GraphIso.Perm n}
    (hGH : IsIso G H p) (hHK : IsIso H K q) : IsIso G K (q.comp p) := by
  intro i j
  simp only [GraphIso.Perm.get_comp]
  rw [hHK, hGH]

end IsIso

namespace Isomorphic

theorem refl (G : Graph n) : Isomorphic G G :=
  ⟨GraphIso.Perm.id n, IsIso.refl G⟩

theorem symm {G H : Graph n} (h : Isomorphic G H) : Isomorphic H G := by
  rcases h with ⟨p, hp⟩
  exact ⟨p.inv, hp.symm⟩

theorem trans {G H K : Graph n} (hGH : Isomorphic G H)
    (hHK : Isomorphic H K) : Isomorphic G K := by
  rcases hGH with ⟨p, hp⟩
  rcases hHK with ⟨q, hq⟩
  exact ⟨q.comp p, hp.trans hq⟩

end Isomorphic

/-! # The one-cell correspondence -/

/-- A coloured isomorphism transports the underlying graphs. -/
theorem _root_.Hex.GraphIso.IsIso.graph {n k : Nat}
    {A B : GraphIso.Colored n k} {p : GraphIso.Perm n}
    (h : GraphIso.IsIso A B p) : IsIso A.graph B.graph p :=
  h.adj_eq

/-- Coloured isomorphic graphs are isomorphic. -/
theorem _root_.Hex.GraphIso.Isomorphic.graph {n k : Nat}
    {A B : GraphIso.Colored n k} (h : GraphIso.Isomorphic A B) :
    Isomorphic A.graph B.graph := by
  rcases h.elim with ⟨p, hp⟩
  exact ⟨p, hp.graph⟩

/-- At one colour there is nothing to compare but the graph: colour
vectors into `Fin 1` are constant. -/
theorem _root_.Hex.GraphIso.Colored.ext_graph {n : Nat}
    {A B : GraphIso.Colored n 1} (h : A.graph = B.graph) : A = B :=
  GraphIso.Colored.ext (fun _ _ => by rw [h]) (fun _ => by simp)

/-- Colouring every vertex alike neither adds nor removes isomorphisms:
the colour clause of the coloured predicate is vacuous at one colour. -/
theorem isIso_singleColor_iff (G H : Graph n) (p : GraphIso.Perm n)
    (h : 0 < n) :
    GraphIso.IsIso (G.singleColor h) (H.singleColor h) p ↔ IsIso G H p := by
  constructor
  · intro hc
    exact hc.adj_eq
  · intro ha
    exact GraphIso.IsIso.mk (fun _ => by simp) ha

/-- The equivalence every uncoloured theorem below is transported
along. -/
theorem isomorphic_singleColor_iff (G H : Graph n) (h : 0 < n) :
    GraphIso.Isomorphic (G.singleColor h) (H.singleColor h) ↔
      Isomorphic G H := by
  constructor
  · intro hc
    rcases hc.elim with ⟨p, hp⟩
    exact Isomorphic.intro p ((isIso_singleColor_iff G H p h).mp hp)
  · intro hg
    rcases hg.elim with ⟨p, hp⟩
    exact GraphIso.Isomorphic.intro p ((isIso_singleColor_iff G H p h).mpr hp)

/-! # Canonical forms and isomorphism search -/

/-- The canonical form of a graph: the underlying graph of the
one-cell coloured canonical form. -/
@[expose] def canon (G : Graph n) (h : 0 < n := by first | decide | omega) :
    Graph n :=
  (GraphIso.canon (G.singleColor h)).graph

/-- The label producing the canonical form. -/
@[expose] def label (G : Graph n) (h : 0 < n := by first | decide | omega) :
    GraphIso.Label n :=
  GraphIso.label (G.singleColor h)

/-- Find one isomorphism from `G` to `H` when one exists. -/
@[expose] def findIso (G H : Graph n)
    (h : 0 < n := by first | decide | omega) : Option (GraphIso.Perm n) :=
  GraphIso.findIso (G.singleColor h) (H.singleColor h)

/-- The Boolean isomorphism decision. -/
@[expose] def isIso (G H : Graph n)
    (h : 0 < n := by first | decide | omega) : Bool :=
  GraphIso.isIso (G.singleColor h) (H.singleColor h)

/-- Relabelling by the canonical label produces the canonical form. -/
theorem relabel_label (G : Graph n) (h : 0 < n) :
    G.relabel (label G h).get = canon G h :=
  congrArg GraphIso.Colored.graph (GraphIso.relabel_label (G.singleColor h))

/-- Every graph is isomorphic to its canonical form. -/
theorem canon_iso (G : Graph n) (h : 0 < n) : Isomorphic G (canon G h) :=
  (GraphIso.canon_iso (G.singleColor h)).graph

/-- Two graphs are isomorphic exactly when their canonical forms are
equal. -/
theorem iso_iff_canon_eq (G H : Graph n) (h : 0 < n) :
    Isomorphic G H ↔ canon G h = canon H h := by
  constructor
  · intro hiso
    exact congrArg GraphIso.Colored.graph
      ((GraphIso.iso_iff_canon_eq _ _).mp
        ((isomorphic_singleColor_iff G H h).mpr hiso))
  · intro he
    exact (isomorphic_singleColor_iff G H h).mp
      ((GraphIso.iso_iff_canon_eq _ _).mpr
        (GraphIso.Colored.ext_graph he))

/-- Isomorphic graphs have equal canonical forms. -/
theorem canon_invariant {G H : Graph n} (h : 0 < n) (hiso : Isomorphic G H) :
    canon G h = canon H h :=
  (iso_iff_canon_eq G H h).mp hiso

/-- Soundness of the search: any permutation it returns really is an
isomorphism. -/
theorem findIso_sound {G H : Graph n} {p : GraphIso.Perm n} {h : 0 < n}
    (hp : findIso G H h = some p) : IsIso G H p :=
  (isIso_singleColor_iff G H p h).mp (GraphIso.findIso_sound hp)

/-- Completeness of the search: it returns a permutation exactly when
one exists. -/
theorem findIso_isSome_iff (G H : Graph n) (h : 0 < n) :
    (findIso G H h).isSome = true ↔ Isomorphic G H :=
  (GraphIso.findIso_isSome_iff _ _).trans (isomorphic_singleColor_iff G H h)

/-- The decision answers `true` exactly on isomorphic pairs. -/
theorem isIso_eq_true_iff (G H : Graph n) (h : 0 < n) :
    isIso G H h = true ↔ Isomorphic G H :=
  findIso_isSome_iff G H h

/-- The decision answers `false` exactly on non-isomorphic pairs. -/
theorem isIso_eq_false_iff (G H : Graph n) (h : 0 < n) :
    isIso G H h = false ↔ ¬Isomorphic G H := by
  rw [← isIso_eq_true_iff G H h]
  rcases hb : isIso G H h <;> simp

/-- A positive answer proves isomorphism. -/
theorem isomorphic_of_isIso {G H : Graph n} {h : 0 < n}
    (hi : isIso G H h = true) : Isomorphic G H :=
  (isIso_eq_true_iff G H h).mp hi

end Hex.Graph
