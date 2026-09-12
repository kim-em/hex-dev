/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountBound
public import HexGraphIso.Nauty.Sparse.CountOther
public import HexGraphIso.Nauty.Sparse.CountPerm
public import HexGraphIso.Nauty.Sparse.CountSize
public import HexGraphIso.Nauty.Sparse.CountQueue
public import HexGraphIso.Nauty.Sparse.CountPending
public import HexGraphIso.Nauty.Sparse.CountActivation
public import HexGraphIso.Nauty.Sparse.WindowCells
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

/-- The complete nontrivial pass preserves the labelling and partition cache.
Native neighbour counting supplies the local hit bound for every count split,
whose counter changes and inherited boundary values compose through the pass. -/
theorem splitNontrivial_state (G : Hex.SparseGraph n) (level split len : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hc : IsCell s.ptn level split len) (hcell : split + len ≤ n)
    (hm : Scratch.Marks n s.stamp s.marks) (hh : s.hits.size = n) :
    let t := splitNontrivial (.ofGraph G) level split s
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend ∧
      Cuts level n s.ptn t.ptn s.numcells t.numcells n ∧
      cellsPerm s.ptn level t.lab s.lab ∧
      (CellQueue s.ptn level s.active s.queue → CellQueue t.ptn level t.active t.queue) ∧
      Pending n level ((List.range' split (s.cellend[split]! + 1 - split)).flatMap
        fun q => (Graph.ofGraph G).row s.lab[q]!).count s.cellend [] t.lab t.ptn ∧
      Activation n level s.ptn t.ptn s.active t.active := by
  have hpos := hc.1
  have hend' := hi.ends_eq split len hc hcell (by omega)
  have hf : split ≤ s.cellend[split]! + 1 := by omega
  have hb : s.cellend[split]! + 1 ≤ n := by omega
  have edge_bound (q e : Nat) (hq : q < n) (ep es : List Nat)
      (hr : [G.offsets[s.lab[q]!]!:G.offsets[s.lab[q]! + 1]!].toList = ep ++ e :: es) :
      (Graph.ofGraph G).neighbor e < n := by
    have hv := perm_bound hp hq
    have he := range_cursor (G.offset_mono (i := s.lab[q]!) (j := s.lab[q]! + 1)
      (by omega) (by omega)) hr
    exact Graph.neighbor_lt G ⟨s.lab[q]!, hv⟩ (by omega : e < G.offsets[s.lab[q]! + 1]!)
  unfold splitNontrivial
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend ∧
      Cuts level n s.ptn t.ptn s.numcells t.numcells n ∧
      cellsPerm s.ptn level t.lab s.lab ∧
      (CellQueue s.ptn level s.active s.queue → CellQueue t.ptn level t.active t.queue) ∧
      Pending n level ((List.range' split (s.cellend[split]! + 1 - split)).flatMap
        fun q => (Graph.ofGraph G).row s.lab[q]!).count s.cellend [] t.lab t.ptn ∧
      Activation n level s.ptn t.ptn s.active t.active)
  mvcgen +jp
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜CountScan n s.stamp s.marks state.1 state.2.2 s.cellstart state.2.1
      (cursor.prefix.flatMap fun q => (Graph.ofGraph G).row s.lab[q]!)⌝)
  case inv2 =>
    rename_i pref cur suff hr b hin
    exact (⇓⟨cursor, state⟩ => ⌜CountScan n s.stamp s.marks state.1 state.2.2 s.cellstart state.2.1
      ((pref.flatMap fun q => (Graph.ofGraph G).row s.lab[q]!) ++
        cursor.prefix.map (Graph.ofGraph G).neighbor)⌝)
  case inv3 =>
    rename_i pref cur suff hr b hin ep e es he r hscan hk hm'
    exact (⇓⟨cursor, state⟩ => ⌜Index.Writes n r.2.1 state
      (cursor.prefix.map fun q => s.lab[q]!) 0⌝)
  case inv4 =>
    let r : Array Nat × Array Nat × Array Nat := by assumption
    exact (⇓⟨cursor, state⟩ => ⌜
      state.lab.toList.Perm (List.range n) ∧ state.ptn.size = n ∧
      Index.Valid n state.lab state.ptn level state.cellstart state.cellend ∧
      (∀ a ∈ cursor.suffix, IsCell state.ptn level a (s.cellend[a]! + 1 - a) ∧
        a < s.cellend[a]! ∧ s.cellend[a]! < n ∧
        ∀ q, a ≤ q → q ≤ s.cellend[a]! → state.hits[state.lab[q]!]! ≤ len) ∧
      Cuts level n s.ptn state.ptn s.numcells state.numcells n ∧
      cellsPerm s.ptn level state.lab s.lab ∧
      (CellQueue s.ptn level s.active s.queue → CellQueue state.ptn level state.active state.queue) ∧
      state.hits = r.2.1 ∧
      Pending n level ((List.range' split (s.cellend[split]! + 1 - split)).flatMap
        fun q => (Graph.ofGraph G).row s.lab[q]!).count s.cellend cursor.suffix state.lab state.ptn ∧
      Activation n level s.ptn state.ptn s.active state.active⌝)
  all_goals simp +zetaDelta [RefineSt.hash, Std.Legacy.Range.toList] at *
  all_goals try assumption
  case vc2.step.isTrue.isTrue.pre =>
    rename_i pref q suff hr b hout ep e es he r hscan hk hm'
    exact Index.Writes.initial hscan.counts.size
  case vc5.step.isFalse =>
    rename_i pref q suff hr b hout ep e es he r hscan hk
    simpa only [List.append_assoc] using hscan.sentinel hk
  case vc4.step.isTrue.isFalse =>
    rename_i pref q suff hr b hout ep e es he r hscan hk hm'
    have hq := range_cursor hf hr
    have hj := edge_bound q e (by omega) ep es (by simpa only [Graph.ofGraph, Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using he)
    have hk' := hi.vertex_le hs hend hp hj
    simpa only [List.append_assoc] using hscan.repeated hj (by omega) hm'
  case vc1.step =>
    rename_i pref q suff hr b hout ep e es he r hscan before cur after hclear out hw hk hm'
    have hq := range_cursor hf hr
    have hj := edge_bound q e (by omega) ep es (by simpa only [Graph.ofGraph, Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using he)
    have hc := hi.vertex_cell hs hend hp hj hk
    have hb' := range_cursor (by omega) hclear
    exact hw.step (perm_bound hp (by omega))
  case vc3.step.isTrue.isTrue.post.success =>
    rename_i pref q suff hr b hout ep e es he r hscan out hk hm' hw
    have hq := range_cursor hf hr
    have hj := edge_bound q e (by omega) ep es (by simpa only [Graph.ofGraph, Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using he)
    have hc := hi.vertex_cell hs hend hp hj hk
    have hz := hscan.fresh hj (by omega) hm' hw.size (by
      intro v hv
      rw [hw.get v hv]
      simp only [hi.cell_mem hp hs hend hc.1 (by omega) (by omega) hv])
    simpa only [List.append_assoc] using hz
  case vc8.pre => exact CountScan.initial hm hh
  case vc10.post.success.pre =>
    rename_i r hscan
    have hcells := hscan.sorted.cells G _ hp hs hend hi (by
      intro q hq
      simp only [List.mem_range'_1] at hq
      omega)
    refine ⟨hp, hs, hi, ?_, Cuts.refl level n s.ptn s.numcells n, cellsPerm_refl _ _ _,
      Pending.initial hscan.sorted hi, Activation.refl _ _ _⟩
    intro a ha
    have hlen : s.cellend[split]! + 1 - split = len := by omega
    simpa only [List.length_range', hlen] using hcells a (by simpa using ha)
  case vc9.step =>
    rename_i r pref cur suff hlist b hscan hout
    rcases hout with ⟨hlab, hsize, hindex, hremaining, hcuts, hcells, hqueue, hhits, hpending, hactive⟩
    have hcur := hremaining.1
    have he' := hindex.ends_eq cur (s.cellend[cur]! + 1 - cur) hcur.1 (by omega) (by omega)
    have he : b.cellend[cur]! = s.cellend[cur]! := by omega
    have hl : b.lab.size = n := by simpa using hlab.length_eq
    have hk : ∀ q, cur ≤ q → q ≤ b.cellend[cur]! → b.hits[b.lab[q]!]! < n + 2 := by
      intro q hq hu
      have := hcur.2.2.2 q hq (by omega)
      omega
    have hperm := (splitCounts_perm level cur false b (by omega) (by omega)).trans hlab
    have hcellperm := splitCounts_cells level cur false b (by omega) (by omega)
      (by simpa only [he] using hcur.1)
    have hmem : cur ∈ (sortCells r.2.2).toList := by rw [hlist]; simp
    have horiginal := hscan.sorted.cells G _ hp hs hend hi (by
      intro q hq
      simp only [List.mem_range'_1] at hq
      omega)
    have hoc := horiginal cur hmem
    have hkey := hscan.sorted.cell_key hp hi hoc.1 (by omega) (by omega) hmem
    have hsemantic := hpending.step level cur b hl hsize
      (by simpa only [he] using hcur.1) (by omega) he hk (by
        intro v hv
        rw [hhits]
        exact hkey v ((hcells cur _ hoc.1).mem_iff.mp (by simpa only [he] using hv)))
    have hglobal := hcuts.perm hs hl (by simpa using hperm.length_eq) hend hcellperm
    refine ⟨hperm,
      (splitCounts_frame level cur false b).ptn_size.trans hsize,
      splitCounts_index level cur (s.cellend[cur]! + 1 - cur) false b hlab hsize
        hindex hcur.1 (by omega) (fun q hq hu => hk q hq (by omega)), ?_,
      hcuts.trans (splitCounts_cuts level cur false b hl hsize
        (by omega) (by simpa only [he] using hcur.1) hk),
      cellsPerm_trans hglobal hcells,
      fun hq => splitCounts_queue level cur false b hl hsize (by omega)
        (by simpa only [he] using hcur.1) hk (hqueue hq),
      (splitCounts_frame level cur false b).hits.trans hhits, hsemantic,
      hactive.counts level cur false b (by simpa only [he] using hoc.1)
        (by simpa only [he] using hcur.1) hl hsize (by omega) hk⟩
    intro a ha
    have hother := hremaining.2 a ha
    have hne : a ≠ cur := by
      have hn := hscan.touch.sorted.nodup
      rw [hlist] at hn
      have hn' := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
      intro heq
      exact hn' (heq ▸ ha)
    have ho := splitCounts_other level cur a (s.cellend[a]! + 1 - a) len false b hl hsize
      (by omega) (by omega) (by simpa only [he] using hcur.1) hk hother.1 hne
      (fun q hq hu => hother.2.2.2 q hq (by omega))
    exact ⟨ho.1, hother.2.1, hother.2.2.1, fun q hq hu => ho.2 q hq (by omega)⟩
  case vc11.post.success.post.success =>
    rename_i hin
    rcases hin with ⟨hp, hs, hi, hc, hcells, hqueue, _, hconstant, hactive⟩
    exact ⟨hp, hs, hi, hc, hcells, hqueue, hconstant, hactive⟩

/-- The complete nontrivial pass preserves a valid partition cache. -/
theorem splitNontrivial_index (G : Hex.SparseGraph n) (level split len : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hc : IsCell s.ptn level split len) (hcell : split + len ≤ n)
    (hm : Scratch.Marks n s.stamp s.marks) (hh : s.hits.size = n) :
    let t := splitNontrivial (.ofGraph G) level split s
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend := by
  have h := splitNontrivial_state G level split len s hp hs hend hi hc hcell hm hh
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Every output cell has constant native neighbour count into the captured
splitter cell, including cells that were never touched by the neighbour scan. -/
theorem splitNontrivial_constant (G : Hex.SparseGraph n) (level split len : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hc : IsCell s.ptn level split len) (hcell : split + len ≤ n)
    (hm : Scratch.Marks n s.stamp s.marks) (hh : s.hits.size = n) :
    let seen := (List.range' split len).flatMap fun q => (Graph.ofGraph G).row s.lab[q]!
    let t := splitNontrivial (.ofGraph G) level split s
    ∀ a size, IsCell t.ptn level a size → a + size ≤ n →
      ∀ q r, a ≤ q → q < a + size → a ≤ r → r < a + size →
        seen.count t.lab[q]! = seen.count t.lab[r]! := by
  have h := splitNontrivial_state G level split len s hp hs hend hi hc hcell hm hh
  have he := hi.ends_eq split len hc hcell (by have := hc.1; omega)
  have hlen : s.cellend[split]! + 1 - split = len := by have := hc.1; omega
  simpa only [hlen] using h.2.2.2.2.2.2.1.done

/-- Every original cell satisfies sparse nauty's fragment-activation rule
through the complete nontrivial pass, including largest-fragment replacement. -/
theorem splitNontrivial_active (G : Hex.SparseGraph n) (level split len : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hc : IsCell s.ptn level split len) (hcell : split + len ≤ n)
    (hm : Scratch.Marks n s.stamp s.marks) (hh : s.hits.size = n) :
    let t := splitNontrivial (.ofGraph G) level split s
    Activation n level s.ptn t.ptn s.active t.active := by
  exact (splitNontrivial_state G level split len s hp hs hend hi hc hcell hm hh).2.2.2.2.2.2.2

end Hex.GraphIso.Nauty.Sparse
