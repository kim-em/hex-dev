/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TouchCompare

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The executed singleton neighbour loops agree on the sorted touched
cells and on transported mark predicates. Their generations, retained mark
values and native neighbour orders may differ. -/
theorem mark_neighbors_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v) (vertex : Fin n)
    (s t : RefineSt n) (ptn : Array Nat) (level : Nat)
    (hi : Index.Valid n s.lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n t.lab ptn level t.cellstart t.cellend)
    (hp : s.lab.toList.Perm (List.range n)) (hq : t.lab.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hc : cellsPerm ptn level t.lab (s.lab.map (renamingOf p).toFun))
    (hm : Scratch.Marks n s.stamp s.marks) (hvm : Scratch.Marks n s.stamp s.vmarks)
    (hn : Scratch.Marks n t.stamp t.marks) (hvn : Scratch.Marks n t.stamp t.vmarks) :
    let r : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := s.marks
      let mut touched := #[]
      let mut hitVertices := s.vmarks
      for e in [G.offsets[vertex.val]!:G.offsets[vertex.val + 1]!] do
        let j := (Graph.ofGraph G).neighbor e
        hitVertices := hitVertices.set! j (s.stamp + 1)
        let k := s.cellstart[j]!
        if k != n && marks[k]! != s.stamp + 1 then
          marks := marks.set! k (s.stamp + 1)
          touched := touched.push k
      return (marks, touched, hitVertices)
    let u : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := t.marks
      let mut touched := #[]
      let mut hitVertices := t.vmarks
      for e in [H.offsets[(p.get vertex).val]!:H.offsets[(p.get vertex).val + 1]!] do
        let j := (Graph.ofGraph H).neighbor e
        hitVertices := hitVertices.set! j (t.stamp + 1)
        let k := t.cellstart[j]!
        if k != n && marks[k]! != t.stamp + 1 then
          marks := marks.set! k (t.stamp + 1)
          touched := touched.push k
      return (marks, touched, hitVertices)
    sortCells r.2.1 = sortCells u.2.1 ∧
      ∀ v : Fin n, (r.2.2[v.val]! == s.stamp + 1) =
        (u.2.2[(p.get v).val]! == t.stamp + 1) := by
  dsimp only
  have hleft := mark_neighbors G vertex s.lab ptn s.cellstart s.cellend s.marks s.vmarks
    level s.stamp hp hs hend hi hm hvm
  have hright := mark_neighbors H (p.get vertex) t.lab ptn t.cellstart t.cellend t.marks t.vmarks
    level t.stamp hq hs hend hj hn hvn
  dsimp only at hleft hright
  constructor
  · apply Touched.neighbors_eq G H p hiso vertex hi hj hp hs hend hc
    · simpa only [Graph.row, Graph.ofGraph, List.map_map, Function.comp_def] using hleft.1
    · simpa only [Graph.row, Graph.ofGraph, List.map_map, Function.comp_def] using hright.1
    · exact sortCells_order _
    · exact sortCells_order _
  · intro v
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [hleft.2.1 v, hright.2.1 (p.get v), hiso]

end Hex.GraphIso.Nauty.Sparse
