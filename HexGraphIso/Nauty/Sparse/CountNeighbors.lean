/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountScan
public import HexGraphIso.Nauty.Sparse.VertexMarks
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

/-- The native neighbour sequence traversed for one vertex. -/
@[expose] def Graph.row (g : Graph n) (v : Nat) : List Nat :=
  (List.range' g.offsets[v]! (g.offsets[v + 1]! - g.offsets[v]!)).map g.neighbor

/-- The nontrivial splitter's executed neighbour loops maintain exact counts
on all touched cells, including the first-touch clearing loop. -/
theorem count_neighbors (G : Hex.SparseGraph n) (lab ptn starts ends marks hits : Array Nat)
    (level stamp first last : Nat) (hp : lab.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level starts ends)
    (hm : Scratch.Marks n stamp marks) (hh : hits.size = n)
    (hf : first ≤ last) (hb : last ≤ n) :
    let r : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := marks
      let mut hits := hits
      let mut touched := #[]
      for i in [first:last] do
        let vertex := lab[i]!
        for e in [G.offsets[vertex]!:G.offsets[vertex + 1]!] do
          let j := (Graph.ofGraph G).neighbor e
          let k := starts[j]!
          if k != n then
            if marks[k]! != stamp + 1 then
              marks := marks.set! k (stamp + 1)
              touched := touched.push k
              for l in [k:ends[k]! + 1] do
                hits := hits.set! lab[l]! 0
            hits := hits.set! j (hits[j]! + 1)
      return (marks, sortCells touched, hits)
    CountScan n stamp marks r.1 r.2.1 starts r.2.2
      ((List.range' first (last - first)).flatMap fun q => (Graph.ofGraph G).row lab[q]!) := by
  have edge_bound (q e : Nat) (hq : q < n) (ep es : List Nat)
      (hr : [G.offsets[lab[q]!]!:G.offsets[lab[q]! + 1]!].toList = ep ++ e :: es) :
      (Graph.ofGraph G).neighbor e < n := by
    have hv := perm_bound hp hq
    have he := range_cursor (G.offset_mono (i := lab[q]!) (j := lab[q]! + 1)
      (by omega) (by omega)) hr
    exact Graph.neighbor_lt G ⟨lab[q]!, hv⟩ (by omega : e < G.offsets[lab[q]! + 1]!)
  simp only
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × Array Nat × Array Nat =>
    CountScan n stamp marks r.1 r.2.1 starts r.2.2
      ((List.range' first (last - first)).flatMap fun q => (Graph.ofGraph G).row lab[q]!))
  mvcgen +jp
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜CountScan n stamp marks state.1 state.2.2 starts state.2.1
      (cursor.prefix.flatMap fun q => (Graph.ofGraph G).row lab[q]!)⌝)
  case inv2 =>
    rename_i pref cur suff hr b hin
    exact (⇓⟨cursor, state⟩ => ⌜CountScan n stamp marks state.1 state.2.2 starts state.2.1
      ((pref.flatMap fun q => (Graph.ofGraph G).row lab[q]!) ++
        cursor.prefix.map (Graph.ofGraph G).neighbor)⌝)
  case inv3 =>
    rename_i pref cur suff hr b hin ep e es he r hscan hk hm'
    exact (⇓⟨cursor, state⟩ => ⌜Index.Writes n r.2.1 state
      (cursor.prefix.map fun q => lab[q]!) 0⌝)
  all_goals simp +zetaDelta [Std.Legacy.Range.toList] at *
  all_goals try assumption
  case vc8.pre => exact CountScan.initial hm hh
  case vc9.post.success =>
    rename_i r hscan
    exact hscan.sorted
  case vc2.step.isTrue.isTrue.pre =>
    rename_i pref q suff hr b hout ep e es he r hscan hk hm'
    exact Index.Writes.initial hscan.counts.size
  case vc5.step.isFalse =>
    rename_i pref q suff hr b hout ep e es he r hscan hk
    simpa only [List.append_assoc] using hscan.sentinel hk
  case vc4.step.isTrue.isFalse =>
    rename_i pref q suff hr b hout ep e es he r hscan hk hm'
    have hq := range_cursor hf hr
    have hj := edge_bound q e (by omega) ep es (by simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using he)
    have hk' := hi.vertex_le hs hend hp hj
    simpa only [List.append_assoc] using hscan.repeated hj (by omega) hm'
  case vc1.step =>
    rename_i pref q suff hr b hout ep e es he r hscan before cur after hclear out hw hk hm'
    have hq := range_cursor hf hr
    have hj := edge_bound q e (by omega) ep es (by simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using he)
    have hc := hi.vertex_cell hs hend hp hj hk
    have hb' := range_cursor (by omega) hclear
    exact hw.step (perm_bound hp (by omega))
  case vc3.step.isTrue.isTrue.post.success =>
    rename_i pref q suff hr b hout ep e es he r hscan out hk hm' hw
    have hq := range_cursor hf hr
    have hj := edge_bound q e (by omega) ep es (by simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using he)
    have hc := hi.vertex_cell hs hend hp hj hk
    have hz := hscan.fresh hj (by omega) hm' hw.size (by
      intro v hv
      rw [hw.get v hv]
      simp only [hi.cell_mem hp hs hend hc.1 (by omega) (by omega) hv])
    simpa only [List.append_assoc] using hz

end Hex.GraphIso.Nauty.Sparse
