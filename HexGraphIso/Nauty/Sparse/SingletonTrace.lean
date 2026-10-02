/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryExecution
public import HexGraphIso.Nauty.Sparse.MarkTransport
public import HexGraphIso.Nauty.Sparse.PassEquiv

public section

namespace Hex.GraphIso.Nauty.Sparse

set_option maxHeartbeats 1000000

/-- The production singleton splitter is its native marking loop followed
by the proved touched-cell trace, including its initial touched-count hash. -/
theorem splitSingleton_trace (G : Hex.SparseGraph n) (level split : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level) (hsp : split < n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hm : Scratch.Marks n s.stamp s.marks) (hv : Scratch.Marks n s.stamp s.vmarks) :
    let vertex := s.lab[split]!
    let r : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := s.marks
      let mut touched := #[]
      let mut hitVertices := s.vmarks
      for e in [G.offsets[vertex]!:G.offsets[vertex + 1]!] do
        let j := (Graph.ofGraph G).neighbor e
        hitVertices := hitVertices.set! j (s.stamp + 1)
        let k := s.cellstart[j]!
        if k != n && marks[k]! != s.stamp + 1 then
          marks := marks.set! k (s.stamp + 1)
          touched := touched.push k
      return (marks, touched, hitVertices)
    let touched := sortCells r.2.1
    let initial := ({ s with marks := r.1, vmarks := r.2.2, stamp := s.stamp + 1 }).hash touched.size
    Binary.Pass level (s.stamp + 1) touched.toList initial
      (splitSingleton (.ofGraph G) level split s) := by
  let vertex := s.lab[split]!
  have hroot : vertex < n := perm_bound hp hsp
  let r : Array Nat × Array Nat × Array Nat := Id.run do
    let mut marks := s.marks
    let mut touched := #[]
    let mut hitVertices := s.vmarks
    for e in [G.offsets[vertex]!:G.offsets[vertex + 1]!] do
      let j := (Graph.ofGraph G).neighbor e
      hitVertices := hitVertices.set! j (s.stamp + 1)
      let k := s.cellstart[j]!
      if k != n && marks[k]! != s.stamp + 1 then
        marks := marks.set! k (s.stamp + 1)
        touched := touched.push k
    return (marks, touched, hitVertices)
  let touched := sortCells r.2.1
  let initial := ({ s with marks := r.1, vmarks := r.2.2, stamp := s.stamp + 1 }).hash touched.size
  have hmark := mark_neighbors G ⟨vertex, hroot⟩ s.lab s.ptn s.cellstart s.cellend s.marks s.vmarks
    level s.stamp hp hs hend hi hm hv
  have hpass := Binary.binary_pass level (s.stamp + 1) touched initial hp hs hi
    hmark.1.nodup hmark.2.2
  apply Eq.mp (congrArg (Binary.Pass level (s.stamp + 1) touched.toList initial) ?_) hpass
  unfold splitSingleton
  simp only [Id.run, bind, pure, apply_ite ForInStep.yield]
  congr 1

end Hex.GraphIso.Nauty.Sparse
