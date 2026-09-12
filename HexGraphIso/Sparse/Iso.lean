/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Colored
public import HexGraphIso.Iso

public section

namespace Hex.GraphIso.Sparse

variable {n k : Nat}

/-- A forward permutation preserving adjacency and each ordered colour. -/
def IsIso (G H : Colored n k) (p : Perm n) : Prop :=
  (∀ i, H.coloring.cells[p.get i] = G.coloring.cells[i]) ∧
    ∀ i j, H.graph.adj (p.get i) (p.get j) = G.graph.adj i j

/-- Explicit dense conversion preserves the isomorphism relation. -/
theorem isIso_toDense (G H : Colored n k) (p : Perm n) :
    GraphIso.IsIso G.toDense H.toDense p ↔ IsIso G H p := by
  constructor
  · intro h
    exact ⟨h.cells_eq, fun i j => by
      simpa only [Colored.toDense, SparseGraph.adj_toDense] using h.adj_eq i j⟩
  · intro h
    exact GraphIso.IsIso.mk h.1 (fun i j => by
      simpa only [Colored.toDense, SparseGraph.adj_toDense] using h.2 i j)

namespace IsIso

theorem mk {G H : Colored n k} {p : Perm n}
    (hc : ∀ i, H.coloring.cells[p.get i] = G.coloring.cells[i])
    (ha : ∀ i j, H.graph.adj (p.get i) (p.get j) = G.graph.adj i j) :
    IsIso G H p := ⟨hc, ha⟩

theorem cells_eq {G H : Colored n k} {p : Perm n} (h : IsIso G H p) :
    ∀ i, H.coloring.cells[p.get i] = G.coloring.cells[i] := h.1

theorem adj_eq {G H : Colored n k} {p : Perm n} (h : IsIso G H p) :
    ∀ i j, H.graph.adj (p.get i) (p.get j) = G.graph.adj i j := h.2

theorem refl (G : Colored n k) : IsIso G G (Perm.id n) :=
  (isIso_toDense ..).mp (GraphIso.IsIso.refl G.toDense)

theorem symm {G H : Colored n k} {p : Perm n} (h : IsIso G H p) :
    IsIso H G p.inv :=
  (isIso_toDense ..).mp ((isIso_toDense ..).mpr h).symm

theorem trans {G H K : Colored n k} {p q : Perm n}
    (hp : IsIso G H p) (hq : IsIso H K q) : IsIso G K (q.comp p) :=
  (isIso_toDense ..).mp (((isIso_toDense ..).mpr hp).trans
    ((isIso_toDense ..).mpr hq))

end IsIso

/-- Two sparse coloured graphs are isomorphic if a transporter exists. -/
def Isomorphic (G H : Colored n k) : Prop := ∃ p, IsIso G H p

theorem isomorphic_toDense (G H : Colored n k) :
    GraphIso.Isomorphic G.toDense H.toDense ↔ Isomorphic G H := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h.elim
    exact ⟨p, (isIso_toDense ..).mp hp⟩
  · rintro ⟨p, hp⟩
    exact GraphIso.Isomorphic.intro p ((isIso_toDense ..).mpr hp)

namespace Isomorphic

theorem intro {G H : Colored n k} (p : Perm n) (h : IsIso G H p) :
    Isomorphic G H := ⟨p, h⟩

theorem elim {G H : Colored n k} (h : Isomorphic G H) : ∃ p, IsIso G H p := h

theorem refl (G : Colored n k) : Isomorphic G G := ⟨_, IsIso.refl G⟩

theorem symm {G H : Colored n k} (h : Isomorphic G H) : Isomorphic H G := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.inv, hp.symm⟩

theorem trans {G H K : Colored n k} (h : Isomorphic G H)
    (h' : Isomorphic H K) : Isomorphic G K := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  exact ⟨q.comp p, hp.trans hq⟩

end Isomorphic

theorem isIso_relabel (G : Colored n k) (l : Label n) :
    IsIso G (G.relabel l) l.toPerm := by
  apply (isIso_toDense ..).mp
  rw [Colored.toDense_relabel]
  exact GraphIso.isIso_relabel ..

theorem isomorphic_relabel (G : Colored n k) (l : Label n) :
    Isomorphic G (G.relabel l) := ⟨l.toPerm, isIso_relabel G l⟩

theorem relabel_eq_of_isIso {G H : Colored n k} {p : Perm n}
    (h : IsIso G H p) : G.relabel p.toLabel = H := by
  apply Colored.toDense_injective
  rw [Colored.toDense_relabel]
  exact GraphIso.relabel_eq_of_isIso ((isIso_toDense ..).mpr h)

theorem isIso_iff_relabel (G H : Colored n k) (p : Perm n) :
    IsIso G H p ↔ G.relabel p.toLabel = H := by
  refine ⟨relabel_eq_of_isIso, ?_⟩
  rintro rfl
  simpa using isIso_relabel G p.toLabel

theorem isomorphic_iff_exists_relabel {G H : Colored n k} :
    Isomorphic G H ↔ ∃ l : Label n, G.relabel l = H := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.toLabel, relabel_eq_of_isIso hp⟩
  · rintro ⟨l, rfl⟩
    exact isomorphic_relabel G l

/-- Check a given transporter by native sparse relabelling and equality.
This operation constructs no dense adjacency matrix and does no search. -/
@[expose] def checkIso (G H : Colored n k) (p : Perm n) : Bool :=
  G.relabel p.toLabel == H

theorem checkIso_iff (G H : Colored n k) (p : Perm n) :
    checkIso G H p = true ↔ IsIso G H p := by
  rw [checkIso, beq_iff_eq, isIso_iff_relabel]

instance (G H : Colored n k) (p : Perm n) : Decidable (IsIso G H p) :=
  if h : checkIso G H p = true then .isTrue ((checkIso_iff ..).mp h)
  else .isFalse (fun hp => h ((checkIso_iff ..).mpr hp))

end Hex.GraphIso.Sparse
