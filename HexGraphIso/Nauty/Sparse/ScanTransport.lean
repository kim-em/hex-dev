/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ScanCompare

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The executed nontrivial native scans return the same sorted touched
cells and transported hit values on those cells. Both their incoming scratch
and their traversal orders may differ. -/
theorem count_neighbors_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (s t : RefineSt n) (ptn : Array Nat) (level first len : Nat)
    (hi : Index.Valid n s.lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n t.lab ptn level t.cellstart t.cellend)
    (hp : s.lab.toList.Perm (List.range n)) (hq : t.lab.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hc : IsCell ptn level first len) (hb : first + len ≤ n)
    (hperm : cellsPerm ptn level t.lab (s.lab.map (renamingOf p).toFun))
    (hm : Scratch.Marks n s.stamp s.marks) (hh : s.hits.size = n)
    (hn : Scratch.Marks n t.stamp t.marks) (hk : t.hits.size = n) :
    let r : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := s.marks
      let mut hits := s.hits
      let mut touched := #[]
      for i in [first:first + len] do
        let vertex := s.lab[i]!
        for e in [G.offsets[vertex]!:G.offsets[vertex + 1]!] do
          let j := (Graph.ofGraph G).neighbor e
          let k := s.cellstart[j]!
          if k != n then
            if marks[k]! != s.stamp + 1 then
              marks := marks.set! k (s.stamp + 1)
              touched := touched.push k
              for l in [k:s.cellend[k]! + 1] do hits := hits.set! s.lab[l]! 0
            hits := hits.set! j (hits[j]! + 1)
      return (marks, sortCells touched, hits)
    let u : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := t.marks
      let mut hits := t.hits
      let mut touched := #[]
      for i in [first:first + len] do
        let vertex := t.lab[i]!
        for e in [H.offsets[vertex]!:H.offsets[vertex + 1]!] do
          let j := (Graph.ofGraph H).neighbor e
          let k := t.cellstart[j]!
          if k != n then
            if marks[k]! != t.stamp + 1 then
              marks := marks.set! k (t.stamp + 1)
              touched := touched.push k
              for l in [k:t.cellend[k]! + 1] do hits := hits.set! t.lab[l]! 0
            hits := hits.set! j (hits[j]! + 1)
      return (marks, sortCells touched, hits)
    r.2.1 = u.2.1 ∧ ∀ v, v < n → s.cellstart[v]! ∈ r.2.1.toList →
      u.2.2[(renamingOf p) v]! = r.2.2[v]! := by
  have hleft := count_neighbors G s.lab ptn s.cellstart s.cellend s.marks s.hits
    level s.stamp first (first + len) hp hs hend hi hm hh (by omega) hb
  have hright := count_neighbors H t.lab ptn t.cellstart t.cellend t.marks t.hits
    level t.stamp first (first + len) hq hs hend hj hn hk (by omega) hb
  dsimp only at hleft hright ⊢
  apply hleft.equiv (renamingOf p) hright (sortCells_order _) (sortCells_order _) ?_ ?_ ?_
  · intro v hv
    obtain ⟨q, hq, hv⟩ := List.mem_flatMap.mp hv
    have hq' : q < n := by simp only [List.mem_range'_1] at hq; omega
    exact Graph.row_bound G ⟨s.lab[q]!, perm_bound hp hq'⟩ v hv
  · exact fun v hv => hi.starts_map (renamingOf p) hj hp hs hend hperm hv
  · simpa only [Nat.add_sub_cancel_left] using Graph.cell_rows_map G H p hiso hp hb hc hperm

end Hex.GraphIso.Nauty.Sparse
