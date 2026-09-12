/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountNeighbors

public section

namespace Hex.GraphIso.Nauty.Sparse.Graph

/-- The executed native row scan retains exactly the packed neighbour order. -/
theorem row_eq (G : Hex.SparseGraph n) (v : Fin n) :
    (Graph.ofGraph G).row v.val = (G.nbrs v).toList.map Fin.val := by
  have hlo := G.offset_mono (i := v.val) (j := v.val + 1) (by omega) (by omega)
  have hhi := G.offset_le (i := v.val + 1) (by omega)
  apply List.ext_getElem
  · simp only [Graph.row, Graph.ofGraph, List.length_map, List.length_range',
      Hex.SparseGraph.nbrs, Hex.SparseGraph.row, Array.length_toList, Array.size_extract]
    omega
  · intro i hi hj
    have hb : G.offsets[v.val]! + i < G.neighbors.size := by
      simp only [Graph.row, Graph.ofGraph, List.length_map, List.length_range'] at hi
      omega
    simp only [Graph.row, List.getElem_map, List.getElem_range', Nat.one_mul,
      Graph.ofGraph, Hex.SparseGraph.nbrs, Hex.SparseGraph.row, Array.getElem_toList,
      Array.getElem_extract]
    exact Graph.neighbor_ofGraph G _ hb

/-- Native simple graph rows cannot count a vertex twice. -/
theorem row_nodup (G : Hex.SparseGraph n) (v : Fin n) :
    ((Graph.ofGraph G).row v.val).Nodup := by
  rw [row_eq]
  exact (G.sorted v).map Fin.val (fun _ _ h he => Fin.ne_of_lt h (Fin.ext he))

theorem row_bound (G : Hex.SparseGraph n) (v : Fin n) :
    ∀ j ∈ (Graph.ofGraph G).row v.val, j < n := by
  rw [row_eq]
  intro j hj
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hj
  exact w.isLt

/-- One native row contributes exactly its adjacency indicator. -/
theorem row_count (G : Hex.SparseGraph n) (u v : Fin n) :
    ((Graph.ofGraph G).row u.val).count v.val = if G.adj u v then 1 else 0 := by
  rw [(row_nodup G u).count]
  change (if v.val ∈ (List.range' G.offsets[u.val]!
    (G.offsets[u.val + 1]! - G.offsets[u.val]!)).map (Graph.ofGraph G).neighbor then 1 else 0) = _
  simp only [Graph.neighbor_mem]

/-- Summing native row counts counts precisely the adjacent splitter vertices. -/
theorem count_vertices (G : Hex.SparseGraph n) (vertices : List (Fin n)) (v : Fin n) :
    (vertices.flatMap fun u => (Graph.ofGraph G).row u.val).count v.val =
      (vertices.filter fun u => G.adj u v).length := by
  induction vertices with
  | nil => simp
  | cons u us ih =>
    simp only [List.flatMap_cons, List.count_append, row_count, ih, List.filter_cons]
    split <;> simp_all <;> omega

/-- Each splitter vertex contributes at most one to a neighbour's count. -/
theorem count_rows (G : Hex.SparseGraph n) (lab : Array Nat)
    (hp : lab.toList.Perm (List.range n)) (positions : List Nat)
    (hb : ∀ q ∈ positions, q < n) (v : Nat) :
    (positions.flatMap fun q => (Graph.ofGraph G).row lab[q]!).count v ≤ positions.length := by
  induction positions with
  | nil => simp
  | cons q qs ih =>
    have hq := perm_bound hp (hb q (by simp))
    have hc := List.nodup_iff_count.mp (row_nodup G ⟨lab[q]!, hq⟩) v
    change ((Graph.ofGraph G).row lab[q]!).count v ≤ 1 at hc
    have ht := ih (fun q hq => hb q (by simp [hq]))
    simp only [List.flatMap_cons, List.count_append, List.length_cons]
    omega

end Hex.GraphIso.Nauty.Sparse.Graph

namespace Hex.GraphIso.Nauty.Sparse.CountScan

/-- Every touched key names a complete original cell, and every count in
that cell is bounded by the number of traversed splitter vertices. -/
theorem cells {lab ptn starts ends before marks touched hits : Array Nat}
    {n stamp level : Nat} (G : Hex.SparseGraph n) (positions : List Nat)
    (h : CountScan n stamp before marks touched starts hits
      (positions.flatMap fun q => (Graph.ofGraph G).row lab[q]!))
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hi : Index.Valid n lab ptn level starts ends)
    (hb : ∀ q ∈ positions, q < n) :
    ∀ a ∈ touched.toList,
      IsCell ptn level a (ends[a]! + 1 - a) ∧ a < ends[a]! ∧ ends[a]! < n ∧
      ∀ q, a ≤ q → q ≤ ends[a]! → hits[lab[q]!]! ≤ positions.length := by
  intro a ha
  have ha' := (h.touch.members a).mp ha
  obtain ⟨v, hv, he⟩ := List.mem_map.mp ha'.2
  obtain ⟨q, hq, hrow⟩ := List.mem_flatMap.mp hv
  have hvertex := perm_bound hp (hb q hq)
  have hv' := Graph.row_bound G ⟨lab[q]!, hvertex⟩ v hrow
  have hc := hi.vertex_cell hs hend hp hv' (by rw [he]; omega)
  simp only [he] at hc
  refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
  intro q hq hu
  have hvq := perm_bound hp (by omega : q < n)
  have hkey := hi.starts_eq a (ends[a]! + 1 - a) hc.1 (by omega) (by omega)
    q hq (by omega)
  rw [ite_eq_right (by omega)] at hkey
  rw [h.counts.get _ hvq (by omega) (by simpa only [hkey] using ha'.2)]
  exact Graph.count_rows G lab hp positions hb _

end Hex.GraphIso.Nauty.Sparse.CountScan
