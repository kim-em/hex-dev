/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BfsRun
public import HexGraphIso.Nauty.Sparse.CountBound

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem Walk.eq_root {G : Hex.SparseGraph n} {root v : Fin n} (h : Walk G root v 0) :
    v = root := by cases h; rfl

theorem Walk.one {G : Hex.SparseGraph n} {root v : Fin n} :
    Walk G root v 1 ↔ G.adj root v = true := by
  constructor
  · intro h
    cases h with
    | step hw he => cases hw; exact he
  · intro he
    exact .step .nil he

namespace Distances

variable {G : Hex.SparseGraph n} {root : Fin n} {dist : Array Nat}

/-- For graphs with at least two vertices, distance one is exactly adjacency
to the root; the unreachable sentinel cannot be mistaken for an edge. -/
theorem adj_iff (h : Distances G root dist) (hn : 1 < n) (v : Fin n) :
    dist[v.val]! = 1 ↔ G.adj root v = true := by
  constructor
  · intro he
    have hw := h.sound v (by omega)
    rw [he] at hw
    exact Walk.one.mp hw
  · intro he
    have hb := h.complete (Walk.one.mpr he)
    by_cases hz : dist[v.val]! = 0
    · have hw := h.sound v hb.1
      rw [hz] at hw
      have hv := hw.eq_root
      subst v
      rw [G.adj_self] at he
      cases he
    · omega

/-- Equal distance keys have equal adjacency to the splitter, including
the one-vertex graph where every adjacency value is false. -/
theorem adj_congr (h : Distances G root dist) (v w : Fin n)
    (he : dist[v.val]! = dist[w.val]!) : G.adj root v = G.adj root w := by
  by_cases hn : 1 < n
  · apply Bool.eq_iff_iff.mpr
    rw [← h.adj_iff hn v, ← h.adj_iff hn w, he]
  · have hvw : v = w := by apply Fin.ext; have := v.isLt; have := w.isLt; omega
    rw [hvw]

/-- The semantic neighbour count into a singleton is constant on a distance
class, which is the key interpretation used by the shallow distance pass. -/
theorem count_congr (h : Distances G root dist) (v w : Fin n)
    (he : dist[v.val]! = dist[w.val]!) :
    ((Graph.ofGraph G).row root.val).count v.val = ((Graph.ofGraph G).row root.val).count w.val := by
  simp only [Graph.row_count, h.adj_congr v w he]

end Distances
end Hex.GraphIso.Nauty.Sparse
