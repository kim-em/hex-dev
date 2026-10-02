/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.VertexMarks

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Native singleton marking computes adjacency exactly and records only
bounded nontrivial cells. The valid graph and cache discharge every loop
lookup bound, including graphs with isolated vertices. -/
theorem mark_neighbors (G : Hex.SparseGraph n) (vertex : Fin n)
    (lab ptn starts ends marks vmarks : Array Nat) (level stamp : Nat)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level starts ends)
    (hm : Scratch.Marks n stamp marks) (hvm : Scratch.Marks n stamp vmarks) :
    let r : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := marks
      let mut touched := #[]
      let mut hitVertices := vmarks
      for e in [G.offsets[vertex.val]!:G.offsets[vertex.val + 1]!] do
        let j := (Graph.ofGraph G).neighbor e
        hitVertices := hitVertices.set! j (stamp + 1)
        let k := starts[j]!
        if k != n && marks[k]! != stamp + 1 then
          marks := marks.set! k (stamp + 1)
          touched := touched.push k
      return (marks, touched, hitVertices)
    Touched n stamp marks r.1 (sortCells r.2.1)
        ((List.range' G.offsets[vertex.val]!
          (G.offsets[vertex.val + 1]! - G.offsets[vertex.val]!)).map
          fun e => starts[(Graph.ofGraph G).neighbor e]!) ∧
      (∀ v : Fin n, r.2.2[v.val]! = stamp + 1 ↔ G.adj vertex v = true) ∧
      (∀ a ∈ (sortCells r.2.1).toList,
        IsCell ptn level a (ends[a]! + 1 - a) ∧ a < ends[a]! ∧ ends[a]! < n) := by
  have hh := touch_scan (Graph.ofGraph G).neighbor starts marks vmarks n stamp
    G.offsets[vertex.val]! G.offsets[vertex.val + 1]! hm hvm.size
    (fun e _ he => Graph.neighbor_lt G vertex he)
    (fun e _ he => hi.vertex_le hs hend hp (Graph.neighbor_lt G vertex he))
  refine ⟨hh.1.sorted, ?_, ?_⟩
  · intro v
    exact (hh.2.marked hvm v.isLt).trans (Graph.neighbor_mem G vertex v)
  · intro a ha
    have ha' := (hh.1.sorted.members a).mp ha
    obtain ⟨e, he, hv⟩ := List.mem_map.mp ha'.2
    simp only [List.mem_range'_1] at he
    have hlo := G.offset_mono (i := vertex.val) (j := vertex.val + 1) (by omega) (by omega)
    have hhi : e < G.offsets[vertex.val + 1]! := by omega
    have hc := hi.vertex_cell hs hend hp (Graph.neighbor_lt G vertex hhi)
      (by rw [hv]; omega)
    simpa only [hv] using hc

end Hex.GraphIso.Nauty.Sparse
