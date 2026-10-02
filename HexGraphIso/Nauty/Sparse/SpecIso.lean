/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecTransport
public import HexGraphIso.Nauty.Sparse.SpecColors
public import HexGraphIso.Sparse.Iso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Isomorphic roots have corresponding leaves in the native sparse tree.
The colour-bucket correspondence concerns the initializer only; all recursive
refinement and target selection in this theorem are sparse operations. -/
theorem rootLeaves_map {G H : GraphIso.Sparse.Colored n k} {p : Perm n}
    (h : GraphIso.Sparse.IsIso G H p) {leaf : SpecLeaf n} (hm : leaf ∈ rootLeaves G) :
    leaf.map p ∈ rootLeaves H := by
  by_cases hn : n = 0
  · simp only [rootLeaves, hn, ite_true, List.mem_singleton] at hm ⊢
    rw [hm]
    have hp : p.comp (Label.id n).perm = (Label.id n).perm := by
      apply Perm.ext
      intro i
      have := i.isLt
      omega
    simp only [SpecLeaf.map, hp]
  · have hn' : 0 < n := by omega
    have hd := (GraphIso.Sparse.isIso_toDense G H p).mpr h
    have hends : (initialPartitionWith n k H.coloring.cells.toArray Fin.val).2 =
        (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2 := by
      rw [initialPartition_eq, initialPartition_eq]
      exact cellEnds_eq hd
    have hc := initial_cellsPerm hd hn'
    rw [← initialPartition_eq, ← initialPartition_eq] at hc
    have hh := SpecNode.initial H hn'
    dsimp only at hh
    rw [hends] at hh
    simp only [rootLeaves, hn, ite_false] at hm ⊢
    rw [hends]
    exact specLeaves_map G.graph H.graph p h.adj_eq 100 (n + 2) 1 _ _ _ _ _
      (SpecNode.initial G hn') hh hc hm

/-- Sparse nauty's declarative maximum is invariant under every
colour-preserving graph isomorphism. Both inequalities follow from actual
tree leaves, without an assumption about the production search. -/
theorem canonSpecKey_map {G H : GraphIso.Sparse.Colored n k} {p : Perm n}
    (h : GraphIso.Sparse.IsIso G H p) : canonSpecKey G = canonSpecKey H := by
  apply Key.le_antisymm
  · have hb := canonSpecKey_bound H (rootLeaves_map h (specBest_mem G))
    rw [SpecLeaf.map_key G.graph H.graph p h.adj_eq] at hb
    exact hb
  · have hb := canonSpecKey_bound G (rootLeaves_map h.symm (specBest_mem H))
    rw [SpecLeaf.map_key H.graph G.graph p.inv h.symm.adj_eq] at hb
    exact hb

theorem canonSpecKey_iso {G H : GraphIso.Sparse.Colored n k}
    (h : GraphIso.Sparse.Isomorphic G H) : canonSpecKey G = canonSpecKey H := by
  obtain ⟨p, hp⟩ := h.elim
  exact canonSpecKey_map hp

end Hex.GraphIso.Nauty.Sparse
