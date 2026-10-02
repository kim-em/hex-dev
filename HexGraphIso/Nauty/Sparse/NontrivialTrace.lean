/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountLoop
public import HexGraphIso.Nauty.Sparse.CountSemantics
public import HexGraphIso.Nauty.Sparse.CountBound

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The complete production nontrivial pass admits its exact count-split
trace. Native first-touch clearing derives the semantic count and local
bound required at every processed cell. -/
theorem splitNontrivial_trace (G : Hex.SparseGraph n) (level split len : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hc : IsCell s.ptn level split len) (hb : split + len ≤ n)
    (hm : Scratch.Marks n s.stamp s.marks) (hh : s.hits.size = n) :
    let seen := (List.range' split (s.cellend[split]! + 1 - split)).flatMap
      fun q => (Graph.ofGraph G).row s.lab[q]!
    let r : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := s.marks
      let mut hits := s.hits
      let mut touched := #[]
      for i in [split:s.cellend[split]! + 1] do
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
    let initial := ({ s with marks := r.1, hits := r.2.2, stamp := s.stamp + 1 }).hash r.2.1.size
    CountTrace.Pass level false seen.count r.2.1.toList initial
      (splitNontrivial (.ofGraph G) level split s) := by
  have hlen := hc.1
  have he := hi.ends_eq split len hc hb (by omega)
  have hf : split ≤ s.cellend[split]! + 1 := by omega
  have hu : s.cellend[split]! + 1 ≤ n := by omega
  let seen := (List.range' split (s.cellend[split]! + 1 - split)).flatMap
    fun q => (Graph.ofGraph G).row s.lab[q]!
  let r : Array Nat × Array Nat × Array Nat := Id.run do
    let mut marks := s.marks
    let mut hits := s.hits
    let mut touched := #[]
    for i in [split:s.cellend[split]! + 1] do
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
  let initial := ({ s with marks := r.1, hits := r.2.2, stamp := s.stamp + 1 }).hash r.2.1.size
  have hscan : CountScan n s.stamp s.marks r.1 r.2.1 s.cellstart r.2.2 seen :=
    count_neighbors G s.lab s.ptn s.cellstart s.cellend s.marks s.hits level s.stamp
      split (s.cellend[split]! + 1) hp hs hend hi hm hh hf hu
  have hcells := hscan.cells G _ hp hs hend hi (by
    intro q hq
    simp only [List.mem_range'_1] at hq
    omega)
  have hpass := CountTrace.count_pass level false seen.count r.2.1 initial hp hs hi hscan.touch.nodup (by
    intro a ha
    change CountTrace.Ready level seen.count a s.cellend[a]! initial
    have hc := hcells a ha
    refine ⟨hc.1, by omega, hc.2.2.1, ?_, ?_⟩
    · intro q hq heq
      have hkey := hc.2.2.2 q hq heq
      simp only [List.length_range'] at hkey
      change r.2.2[s.lab[q]!]! < n + 2
      omega
    · exact hscan.cell_key hp hi hc.1 (by omega) (by omega) ha)
  apply Eq.mp (congrArg (CountTrace.Pass level false seen.count r.2.1.toList initial) ?_) hpass
  unfold splitNontrivial
  rfl

end Hex.GraphIso.Nauty.Sparse
