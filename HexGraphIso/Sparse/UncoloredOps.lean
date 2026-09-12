/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Uncolored
public import HexGraphIso.Sparse.Canonical
import all HexGraphIso.Sparse.Uncolored
import all HexGraphIso.Sparse.Iso

public section

namespace Hex.SparseGraph

variable {n : Nat}

/-- The native uncoloured view has one colour on nonempty graphs and no
colours on the empty graph. Both cases retain the original sparse graph. -/
@[expose] def toColored (G : SparseGraph n) : GraphIso.Sparse.Colored n (min n 1) where
  graph := G
  coloring := {
    cells := Hex.Vector.ofFn' fun i : Fin n => ⟨0, by have := i.isLt; omega⟩
    onto := fun c => by
      have hc := c.isLt
      refine ⟨⟨0, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [Vector.get_eq_getElem]
      omega }

/-- The zero-or-one-colour view has precisely the bare graph's forward
isomorphisms, including the empty graph. -/
theorem isIso_toColored_iff (G H : SparseGraph n) (p : Perm n) :
    GraphIso.Sparse.IsIso G.toColored H.toColored p ↔ IsIso G H p := by
  refine ⟨fun h => h.adj_eq, fun h => GraphIso.Sparse.IsIso.mk ?_ h⟩
  intro i
  apply Fin.ext
  simp [toColored]

theorem isomorphic_toColored_iff (G H : SparseGraph n) :
    GraphIso.Sparse.Isomorphic G.toColored H.toColored ↔ Isomorphic G H := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h.elim
    exact ⟨p, (isIso_toColored_iff ..).mp hp⟩
  · rintro ⟨p, hp⟩
    exact GraphIso.Sparse.Isomorphic.intro p ((isIso_toColored_iff ..).mpr hp)

/-- A bare sparse canonical form and its new-to-old labelling. -/
structure CanonResult (n : Nat) where
  form : SparseGraph n
  label : GraphIso.Label n
deriving DecidableEq

/-- Total native canonicalization of a bare sparse graph. The internal
colouring represents its sole cell, including the zero-cell empty case. -/
@[expose] def canonicalize (G : SparseGraph n) : CanonResult n :=
  let r := GraphIso.Sparse.canonicalize G.toColored
  ⟨r.form.graph, r.label⟩

@[expose] def canon (G : SparseGraph n) : SparseGraph n := (canonicalize G).form

@[expose] def label (G : SparseGraph n) : GraphIso.Label n := (canonicalize G).label

@[expose] def findIso (G H : SparseGraph n) : Option (Perm n) :=
  GraphIso.Sparse.findIso G.toColored H.toColored

@[expose] def isIso (G H : SparseGraph n) : Bool := (findIso G H).isSome

/-- The bare result uses precisely the native coloured search's form. -/
theorem canon_toColored (G : SparseGraph n) :
    canon G = (GraphIso.Sparse.canon G.toColored).graph := rfl

theorem label_toColored (G : SparseGraph n) : label G = GraphIso.Sparse.label G.toColored := rfl

theorem relabel_label (G : SparseGraph n) : G.relabel (label G).perm = canon G :=
  congrArg GraphIso.Sparse.Colored.graph (GraphIso.Sparse.relabel_label G.toColored)

/-- The wrapper exposes the literal optimized search's canonical-label array. -/
theorem label_toArray (G : SparseGraph n) :
    (label G).toArray = (GraphIso.Nauty.Sparse.runColored G.toColored).canonlab :=
  GraphIso.Sparse.label_toArray G.toColored

theorem canon_iso (G : SparseGraph n) : Isomorphic G (canon G) := by
  obtain ⟨p, hp⟩ := (GraphIso.Sparse.canon_iso G.toColored).elim
  exact ⟨p, hp.adj_eq⟩

/-- Every returned bare transporter preserves native adjacency. -/
theorem findIso_sound {G H : SparseGraph n} {p : Perm n} (h : findIso G H = some p) : IsIso G H p :=
  (isIso_toColored_iff ..).mp (GraphIso.Sparse.findIso_sound h)

theorem isomorphic_of_isIso {G H : SparseGraph n} (h : isIso G H = true) : Isomorphic G H := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  exact ⟨p, findIso_sound hp⟩

/-- Bare sparse canonical forms are invariant at every order, including
the zero-colour empty case of the native wrapper. -/
theorem canon_invariant {G H : SparseGraph n} (h : Isomorphic G H) : canon G = canon H :=
  congrArg GraphIso.Sparse.Colored.graph
    (GraphIso.Sparse.canon_invariant ((isomorphic_toColored_iff G H).mpr h))

theorem iso_iff_canon_eq (G H : SparseGraph n) : Isomorphic G H ↔ canon G = canon H := by
  refine ⟨canon_invariant, ?_⟩
  intro he
  have hh := canon_iso H
  rw [← he] at hh
  exact (canon_iso G).trans hh.symm

theorem canon_idempotent (G : SparseGraph n) : canon (canon G) = canon G :=
  (canon_invariant (canon_iso G)).symm

theorem findIso_complete {G H : SparseGraph n} (h : Isomorphic G H) :
    ∃ p, findIso G H = some p :=
  GraphIso.Sparse.findIso_complete ((isomorphic_toColored_iff G H).mpr h)

theorem findIso_isSome_iff (G H : SparseGraph n) :
    (findIso G H).isSome = true ↔ Isomorphic G H :=
  (GraphIso.Sparse.findIso_isSome_iff G.toColored H.toColored).trans (isomorphic_toColored_iff G H)

theorem isIso_eq_true_iff (G H : SparseGraph n) : isIso G H = true ↔ Isomorphic G H :=
  findIso_isSome_iff G H

theorem isIso_eq_false_iff (G H : SparseGraph n) : isIso G H = false ↔ ¬ Isomorphic G H := by
  rw [← isIso_eq_true_iff]
  exact Bool.eq_false_iff

theorem findIso_eq_none_iff (G H : SparseGraph n) : findIso G H = none ↔ ¬ Isomorphic G H :=
  (GraphIso.Sparse.findIso_eq_none_iff G.toColored H.toColored).trans
    (not_congr (isomorphic_toColored_iff G H))

end Hex.SparseGraph
