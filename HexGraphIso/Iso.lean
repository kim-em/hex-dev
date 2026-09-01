/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Colored

public section

/-!
Isomorphism of coloured graphs.

`IsIso G H p` states that the forward permutation `p` (old vertex to image)
transports `G` onto `H`, preserving each ordered colour index. `checkIso`
is the executable Boolean checker, sound and complete for `IsIso`.

The section ends with the two bridges between isomorphism and relabelling:
every labelling produces an isomorphic graph, and every isomorphism arises
from a labelling. These carry the reference canonical-form proofs.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-- The forward permutation `p` is an isomorphism from `G` to `H`: it
preserves each ordered colour index and transports adjacency. -/
def IsIso (G H : Colored n k) (p : Perm n) : Prop :=
  (∀ i, H.coloring.cells[p.get i] = G.coloring.cells[i]) ∧
    ∀ i j, H.graph.adj (p.get i) (p.get j) = G.graph.adj i j

/-- Executable isomorphism check, sound and complete for `IsIso`
(`checkIso_iff`). A plain Boolean fold so the kernel replays it without
unfolding `Decidable` instances. -/
@[expose] def checkIso (G H : Colored n k) (p : Perm n) : Bool :=
  ((List.finRange n).all fun i =>
    H.coloring.cells[p.get i] == G.coloring.cells[i]) &&
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    H.graph.adj (p.get i) (p.get j) == G.graph.adj i j

theorem checkIso_iff (G H : Colored n k) (p : Perm n) :
    checkIso G H p = true ↔ IsIso G H p := by
  rw [checkIso, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  simp only [List.mem_finRange, List.all_eq_true, beq_iff_eq, true_implies,
    forall_const]
  exact Iff.rfl

@[expose] instance (G H : Colored n k) (p : Perm n) : Decidable (IsIso G H p) :=
  if h : checkIso G H p then
    .isTrue ((checkIso_iff G H p).mp h)
  else
    .isFalse fun hi => h ((checkIso_iff G H p).mpr hi)

/-- Two coloured graphs are isomorphic when some colour-preserving forward
permutation transports one onto the other. -/
def Isomorphic (G H : Colored n k) : Prop :=
  ∃ p, IsIso G H p

theorem Isomorphic.intro {G H : Colored n k} (p : Perm n) (h : IsIso G H p) :
    Isomorphic G H :=
  ⟨p, h⟩

theorem Isomorphic.elim {G H : Colored n k} (h : Isomorphic G H) :
    ∃ p, IsIso G H p :=
  h

namespace IsIso

theorem cells_eq {G H : Colored n k} {p : Perm n} (h : IsIso G H p) :
    ∀ i, H.coloring.cells[p.get i] = G.coloring.cells[i] :=
  h.1

theorem adj_eq {G H : Colored n k} {p : Perm n} (h : IsIso G H p) :
    ∀ i j, H.graph.adj (p.get i) (p.get j) = G.graph.adj i j :=
  h.2

theorem refl (G : Colored n k) : IsIso G G (Perm.id n) :=
  ⟨fun i => by simp, fun i j => by simp⟩

theorem symm {G H : Colored n k} {p : Perm n} (h : IsIso G H p) :
    IsIso H G p.inv := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · have := h.1 (p.inv.get i)
    simp only [Perm.get_inv_get] at this
    exact this.symm
  · have := h.2 (p.inv.get i) (p.inv.get j)
    simp only [Perm.get_inv_get] at this
    exact this.symm

theorem trans {G H K : Colored n k} {p q : Perm n}
    (hGH : IsIso G H p) (hHK : IsIso H K q) : IsIso G K (q.comp p) := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · simp only [Perm.get_comp]
    rw [hHK.1, hGH.1]
  · simp only [Perm.get_comp]
    rw [hHK.2, hGH.2]

end IsIso

namespace Isomorphic

theorem refl (G : Colored n k) : Isomorphic G G :=
  ⟨Perm.id n, IsIso.refl G⟩

theorem symm {G H : Colored n k} (h : Isomorphic G H) : Isomorphic H G := by
  rcases h with ⟨p, hp⟩
  exact ⟨p.inv, hp.symm⟩

theorem trans {G H K : Colored n k} (hGH : Isomorphic G H)
    (hHK : Isomorphic H K) : Isomorphic G K := by
  rcases hGH with ⟨p, hp⟩
  rcases hHK with ⟨q, hq⟩
  exact ⟨q.comp p, hp.trans hq⟩

end Isomorphic

/-! # Isomorphism and relabelling -/

/-- Relabelling produces an isomorphic coloured graph, transported by the
forward permutation of the labelling. -/
theorem isIso_relabel (G : Colored n k) (l : Label n) :
    IsIso G (G.relabel l) l.toPerm := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · simp
  · simp

theorem isomorphic_relabel (G : Colored n k) (l : Label n) :
    Isomorphic G (G.relabel l) :=
  ⟨l.toPerm, isIso_relabel G l⟩

/-- Every isomorphism arises from a labelling: transporting along `p`
relabels by `p.toLabel`. -/
theorem relabel_eq_of_isIso {G H : Colored n k} {p : Perm n}
    (h : IsIso G H p) : G.relabel p.toLabel = H := by
  refine Colored.ext (fun i j => ?_) (fun i => ?_)
  · rw [Colored.adj_relabel]
    have := h.2 (p.toLabel.get i) (p.toLabel.get j)
    simp only [Perm.get_toLabel, Perm.get_inv_get] at this
    exact this.symm
  · simp only [Fin.getElem_fin, Colored.cells_relabel, Perm.get_toLabel, Fin.eta]
    have := h.1 (p.inv.get i)
    simp only [Perm.get_inv_get] at this
    exact this.symm

/-- Two coloured graphs are isomorphic exactly when one is a relabelling of
the other. -/
theorem isomorphic_iff_exists_relabel {G H : Colored n k} :
    Isomorphic G H ↔ ∃ l : Label n, G.relabel l = H := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.toLabel, relabel_eq_of_isIso hp⟩
  · rintro ⟨l, rfl⟩
    exact isomorphic_relabel G l

end Hex.GraphIso
