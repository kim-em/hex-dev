/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TouchRun
public import HexGraphIso.Nauty.Sparse.TouchSort
public import HexGraphIso.Nauty.Sparse.IndexVertex
public import HexGraphIso.Nauty.Sparse.Rows

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Packed neighbour-loop membership is native sparse adjacency. -/
theorem Graph.neighbor_mem (G : Hex.SparseGraph n) (i v : Fin n) :
    v.val ∈ (List.range' G.offsets[i.val]!
      (G.offsets[i.val + 1]! - G.offsets[i.val]!)).map (Graph.ofGraph G).neighbor ↔
      G.adj i v = true := by
  rw [← Hex.SparseGraph.mem_nbrs]
  have hlo := G.offset_mono (i := i.val) (j := i.val + 1) (by omega) (by omega)
  constructor
  · intro hm
    obtain ⟨e, he, hv⟩ := List.mem_map.mp hm
    simp only [List.mem_range'_1] at he
    have hhi : e < G.offsets[i.val + 1]! := by omega
    have hh := G.edge_mem i he.1 hhi
    have hval : G.neighbors[e]'(G.edge_lt hhi) = v := by
      apply Fin.ext
      simpa only [Graph.neighbor_ofGraph G e (G.edge_lt hhi)] using hv
    simpa only [hval] using hh
  · intro hm
    obtain ⟨e, he, he', hv⟩ := G.mem_edge hm
    have hb := G.edge_lt he'
    rw [getElem?_pos G.neighbors e hb, Option.some.injEq] at hv
    refine List.mem_map.mpr ⟨e, ?_, ?_⟩
    · simp only [List.mem_range'_1]
      omega
    · rw [Graph.neighbor_ofGraph G e hb, hv]

/-- A vertex marked in the new generation occurs in the executed scan. -/
theorem Index.Writes.marked (h : Index.Writes n before after seen (stamp + 1))
    (hb : Scratch.Marks n stamp before) (hv : v < n) :
    after[v]! = stamp + 1 ↔ v ∈ seen := by
  rw [h.get v hv]
  by_cases hm : v ∈ seen
  · simp [hm]
  · simp [hm, hb.fresh hv]

/-- For a simple graph row, equal mark predicates imply equal native counts. -/
theorem Index.Writes.count (h : Index.Writes n before after seen (stamp + 1))
    (hb : Scratch.Marks n stamp before) (hn : seen.Nodup)
    (hv : v < n) (hw : w < n)
    (he : (after[v]! == stamp + 1) = (after[w]! == stamp + 1)) :
    seen.count v = seen.count w := by
  have hm : v ∈ seen ↔ w ∈ seen := by
    rw [← h.marked hb hv, ← h.marked hb hw]
    simpa only [beq_iff_eq] using Bool.eq_iff_iff.mp he
  simp only [hn.count, hm]

end Hex.GraphIso.Nauty.Sparse
