/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Iso

public section

namespace Hex.SparseGraph

variable {n : Nat}

/-- Isomorphism of bare sparse graphs, in the forward permutation direction. -/
def IsIso (G H : SparseGraph n) (p : Perm n) : Prop :=
  ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j

def Isomorphic (G H : SparseGraph n) : Prop := ∃ p, IsIso G H p

theorem IsIso.refl (G : SparseGraph n) : IsIso G G (Perm.id n) := by
  intro i j
  simp

theorem IsIso.symm {G H : SparseGraph n} {p : Perm n} (h : IsIso G H p) :
    IsIso H G p.inv := by
  intro i j
  have he := h (p.inv.get i) (p.inv.get j)
  simpa using he.symm

theorem IsIso.trans {G H K : SparseGraph n} {p q : Perm n}
    (h : IsIso G H p) (h' : IsIso H K q) : IsIso G K (q.comp p) := by
  intro i j
  simp only [Perm.get_comp]
  rw [h', h]

theorem Isomorphic.refl (G : SparseGraph n) : Isomorphic G G := ⟨_, IsIso.refl G⟩

theorem Isomorphic.symm {G H : SparseGraph n} (h : Isomorphic G H) : Isomorphic H G := by
  obtain ⟨p, hp⟩ := h
  exact ⟨_, hp.symm⟩

theorem Isomorphic.trans {G H K : SparseGraph n} (h : Isomorphic G H)
    (h' : Isomorphic H K) : Isomorphic G K := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  exact ⟨_, hp.trans hq⟩

theorem isIso_iff_relabel (G H : SparseGraph n) (p : Perm n) :
    IsIso G H p ↔ G.relabel p.inv = H := by
  constructor
  · intro h
    apply SparseGraph.ext
    intro i j
    rw [adj_relabel]
    simpa using (h (p.inv.get i) (p.inv.get j)).symm
  · rintro rfl
    intro i j
    simp

/-- Verify a supplied transporter without adding a colour or a dense matrix.
This also covers the empty graph, where the colour count is zero. -/
@[expose] def checkIso (G H : SparseGraph n) (p : Perm n) : Bool :=
  G.relabel p.inv == H

theorem checkIso_iff (G H : SparseGraph n) (p : Perm n) :
    checkIso G H p = true ↔ IsIso G H p := by
  rw [checkIso, beq_iff_eq, isIso_iff_relabel]

instance (G H : SparseGraph n) (p : Perm n) : Decidable (IsIso G H p) :=
  if h : checkIso G H p = true then .isTrue ((checkIso_iff ..).mp h)
  else .isFalse (fun hp => h ((checkIso_iff ..).mpr hp))

@[expose] def singleColor (G : SparseGraph n) (h : 0 < n) : GraphIso.Sparse.Colored n 1 :=
  ⟨G, GraphIso.Coloring.trivial n h⟩

theorem isIso_singleColor_iff (G H : SparseGraph n) (p : Perm n) (h : 0 < n) :
    GraphIso.Sparse.IsIso (G.singleColor h) (H.singleColor h) p ↔ IsIso G H p := by
  refine ⟨fun hp => hp.adj_eq, fun hp => GraphIso.Sparse.IsIso.mk ?_ hp⟩
  intro i
  exact Subsingleton.elim _ _

theorem isomorphic_singleColor_iff (G H : SparseGraph n) (h : 0 < n) :
    GraphIso.Sparse.Isomorphic (G.singleColor h) (H.singleColor h) ↔ Isomorphic G H := by
  constructor
  · intro hi
    obtain ⟨p, hp⟩ := hi.elim
    exact ⟨p, (isIso_singleColor_iff ..).mp hp⟩
  · rintro ⟨p, hp⟩
    exact GraphIso.Sparse.Isomorphic.intro p ((isIso_singleColor_iff ..).mpr hp)

end Hex.SparseGraph
