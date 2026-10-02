/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexTransport

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native row transports its vertex multiset under an isomorphism.
Its stored neighbour order is allowed to change. -/
theorem Graph.row_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v) (vertex : Fin n) :
    ((Graph.ofGraph H).row (p.get vertex).val).Perm
      (((Graph.ofGraph G).row vertex.val).map (renamingOf p).toFun) := by
  apply (List.perm_ext_iff_of_nodup (Graph.row_nodup H (p.get vertex))
    ((Graph.row_nodup G vertex).map _ (fun _ _ hn he => hn ((renamingOf p).inj _ _ he)))).mpr
  intro v
  constructor
  · intro hv
    have hb := Graph.row_bound H (p.get vertex) v hv
    obtain ⟨w, hw⟩ := p.get_surj ⟨v, hb⟩
    apply List.mem_map.mpr
    refine ⟨w.val, ?_, (renamingOf_lt p w.isLt).trans (congrArg Fin.val hw)⟩
    apply (Graph.neighbor_mem G vertex w).mpr
    rw [← hiso, hw]
    exact (Graph.neighbor_mem H (p.get vertex) ⟨v, hb⟩).mp hv
  · intro hin
    obtain ⟨v, hmem, rfl⟩ := List.mem_map.mp hin
    have hb := Graph.row_bound G vertex v hmem
    rw [renamingOf_lt p hb]
    apply (Graph.neighbor_mem H (p.get vertex) (p.get ⟨v, hb⟩)).mpr
    rw [hiso]
    exact (Graph.neighbor_mem G vertex ⟨v, hb⟩).mp hmem

/-- Mapping each native neighbour to its cached cell preserves the full
multiset, for arbitrary admissible caches and orders within the cells. -/
theorem Graph.cell_row_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v) (vertex : Fin n)
    (hi : Index.Valid n lab ptn level starts ends)
    (hj : Index.Valid n out ptn level other final)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hc : cellsPerm ptn level out (lab.map (renamingOf p).toFun)) :
    (((Graph.ofGraph H).row (p.get vertex).val).map (fun v => other[v]!)).Perm
      (((Graph.ofGraph G).row vertex.val).map (fun v => starts[v]!)) := by
  have h := (Graph.row_map G H p hiso vertex).map (fun v => other[v]!)
  rw [List.map_map] at h
  apply h.trans (List.Perm.of_eq ?_)
  apply List.map_congr_left
  intro v hv
  exact hi.starts_map (renamingOf p) hj hp hs hend hc (Graph.row_bound G vertex v hv)

end Hex.GraphIso.Nauty.Sparse
