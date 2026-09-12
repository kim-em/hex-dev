/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecIso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The declarative sparse canonical form, attained by a leaf of the complete
unpruned sparse tree. Production equality is a separate search theorem. -/
@[expose] def specCanon (G : GraphIso.Sparse.Colored n k) : GraphIso.Sparse.Colored n k :=
  G.relabel (canonSpecLabel G)

theorem specCanon_iso (G : GraphIso.Sparse.Colored n k) :
    GraphIso.Sparse.Isomorphic G (specCanon G) :=
  GraphIso.Sparse.isomorphic_relabel G (canonSpecLabel G)

/-- Isomorphic sparse inputs have equal declarative forms, including their
ordered colour sequences. Canonical labels themselves need not coincide. -/
theorem specCanon_invariant {G H : GraphIso.Sparse.Colored n k}
    (h : GraphIso.Sparse.Isomorphic G H) : specCanon G = specCanon H := by
  obtain ⟨p, hp⟩ := h.elim
  have hkey := canonSpecKey_map hp
  have hg := congrArg Key.graph hkey
  rw [canonSpecLabel_attains, canonSpecLabel_attains] at hg
  have hseq : sortedColorSeq G.toDense = sortedColorSeq H.toDense := by
    rw [sortedColorSeq, sortedColorSeq]
    refine flatMap_congr_mem _ fun c _ => ?_
    rw [length_colorClass_eq ((GraphIso.Sparse.isIso_toDense G H p).mpr hp) c]
  apply GraphIso.Sparse.Colored.toDense_injective
  apply GraphIso.Colored.ext
  · intro i j
    change (G.graph.relabel (canonSpecLabel G).perm).toDense.adj i j =
      (H.graph.relabel (canonSpecLabel H).perm).toDense.adj i j
    rw [hg]
  · intro i
    apply Fin.ext
    change ((G.relabel (canonSpecLabel G)).coloring.cells[i]).val =
      ((H.relabel (canonSpecLabel H)).coloring.cells[i]).val
    rw [canonSpecLabel_colors, canonSpecLabel_colors, hseq]

/-- Equality of the sparse declarative canonical forms characterizes
isomorphism, at every order including the empty graph. -/
theorem iso_iff_specCanon_eq (G H : GraphIso.Sparse.Colored n k) :
    GraphIso.Sparse.Isomorphic G H ↔ specCanon G = specCanon H := by
  refine ⟨specCanon_invariant, ?_⟩
  intro he
  have hh := specCanon_iso H
  rw [← he] at hh
  exact (specCanon_iso G).trans hh.symm

end Hex.GraphIso.Nauty.Sparse
