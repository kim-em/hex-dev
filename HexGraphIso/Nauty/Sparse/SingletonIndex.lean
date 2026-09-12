/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SingletonMarks
public import HexGraphIso.Nauty.Sparse.CompactScan
public import HexGraphIso.Nauty.Sparse.CompactRun
public import HexGraphIso.Nauty.Sparse.FillRun
public import HexGraphIso.Nauty.Sparse.Cuts
public import HexGraphIso.Nauty.Sparse.CellQueue
public import HexGraphIso.Nauty.Sparse.WindowCells
public import HexGraphIso.Nauty.Sparse.SingletonPending
public import HexGraphIso.Nauty.Sparse.ActiveCells
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

/-- The complete singleton pass preserves the labelling permutation and
partition cache, including all touched cells and uniform-cell returns. Every new boundary
is charged once, and inherited closed values are retained literally. -/
theorem splitSingleton_state (G : Hex.SparseGraph n) (level split : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level) (hsp : split < n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hm : Scratch.Marks n s.stamp s.marks) (hv : Scratch.Marks n s.stamp s.vmarks) :
    let t := splitSingleton (.ofGraph G) level split s
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend ∧
      Cuts level n s.ptn t.ptn s.numcells t.numcells n ∧
      (CellQueue s.ptn level s.active s.queue → CellQueue t.ptn level t.active t.queue) ∧
      cellsPerm s.ptn level t.lab s.lab ∧
      Pending n level ((Graph.ofGraph G).row s.lab[split]!).count s.cellend [] t.lab t.ptn ∧
      Activation n level s.ptn t.ptn s.active t.active := by
  have hroot : s.lab[split]! < n := perm_bound hp hsp
  have original {marks touched : Array Nat}
      (ht : Touched n s.stamp s.marks marks touched
        ((List.range' (Graph.ofGraph G).offsets[s.lab[split]!]!
          ((Graph.ofGraph G).offsets[s.lab[split]! + 1]! -
            (Graph.ofGraph G).offsets[s.lab[split]!]!)).map
              fun e => s.cellstart[(Graph.ofGraph G).neighbor e]!)) :
      ∀ a ∈ (sortCells touched).toList,
        IsCell s.ptn level a (s.cellend[a]! + 1 - a) ∧ a < s.cellend[a]! ∧ s.cellend[a]! < n := by
    intro a ha
    have ha' := (ht.sorted.members a).mp (by simpa using ha)
    obtain ⟨e, he, hread⟩ := List.mem_map.mp ha'.2
    simp only [List.mem_range'_1, Graph.ofGraph] at he
    have hlo := G.offset_mono (i := s.lab[split]!) (j := s.lab[split]! + 1) (by omega) (by omega)
    have hhi : e < G.offsets[s.lab[split]! + 1]! := by omega
    have hc := hi.vertex_cell hs hend hp (Graph.neighbor_lt G ⟨s.lab[split]!, hroot⟩ hhi)
      (by rw [hread]; omega)
    simpa only [hread] using hc
  unfold splitSingleton
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend ∧
      Cuts level n s.ptn t.ptn s.numcells t.numcells n ∧
      (CellQueue s.ptn level s.active s.queue → CellQueue t.ptn level t.active t.queue) ∧
      cellsPerm s.ptn level t.lab s.lab ∧
      Pending n level ((Graph.ofGraph G).row s.lab[split]!).count s.cellend [] t.lab t.ptn ∧
      Activation n level s.ptn t.ptn s.active t.active)
  mvcgen +jp
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜
      Touched n s.stamp s.marks state.1 state.2.1
        (cursor.prefix.map fun e => s.cellstart[(Graph.ofGraph G).neighbor e]!) ∧
      Index.Writes n s.vmarks state.2.2 (cursor.prefix.map (Graph.ofGraph G).neighbor) (s.stamp + 1)⌝)
  case inv2 =>
    exact (⇓⟨cursor, state⟩ => ⌜
      state.lab.toList.Perm (List.range n) ∧ state.ptn.size = n ∧
      Index.Valid n state.lab state.ptn level state.cellstart state.cellend ∧
      (∀ a ∈ cursor.suffix, IsCell state.ptn level a (s.cellend[a]! + 1 - a) ∧
        a < s.cellend[a]! ∧ s.cellend[a]! < n) ∧
      Cuts level n s.ptn state.ptn s.numcells state.numcells n ∧
      (CellQueue s.ptn level s.active s.queue → CellQueue state.ptn level state.active state.queue) ∧
      cellsPerm s.ptn level state.lab s.lab ∧
      (∀ v w, v < n → w < n →
        (state.vmarks[v]! == s.stamp + 1) = (state.vmarks[w]! == s.stamp + 1) →
        ((Graph.ofGraph G).row s.lab[split]!).count v =
          ((Graph.ofGraph G).row s.lab[split]!).count w) ∧
      Pending n level ((Graph.ofGraph G).row s.lab[split]!).count s.cellend
        cursor.suffix state.lab state.ptn ∧
      Activation n level s.ptn state.ptn s.active state.active⌝)
  case inv3 =>
    rename_i r hmark pref cur suff hlist b hout
    exact (⇓⟨cursor, state⟩ => ⌜
      Compact b.lab (fun v => b.vmarks[v]! == s.stamp + 1) cur (cur + cursor.prefix.length)
        (cursor.prefix.map fun q => b.lab[q]!) state.1 state.2.2 state.2.1⌝)
  case inv4 =>
    rename_i marks hmark pref cur suff hlist b hout r hcomp
    exact (⇓⟨cursor, state⟩ => ⌜
      Fill r.1 r.2.2.toList.reverse r.2.1 cursor.prefix.length state.1 ∧
      Index.Writes n b.cellstart state.2.1 (r.2.2.toList.reverse.take cursor.prefix.length) r.2.1 ∧
      state.2.2 = r.2.1 + cursor.prefix.length⌝)
  all_goals simp +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList] at *
  all_goals try assumption
  case vc3.pre => exact ⟨Touched.empty hm, Index.Writes.initial hv.size⟩
  case vc1.step.isTrue =>
    rename_i pref cur suff hr b hin hf
    have he := range_cursor (G.offset_mono (i := s.lab[split]!) (j := s.lab[split]! + 1)
      (by omega) (by omega)) hr
    have hv' := Graph.neighbor_lt G ⟨s.lab[split]!, hroot⟩ (by omega : cur < G.offsets[s.lab[split]! + 1]!)
    have hk := hi.vertex_le hs hend hp hv'
    exact ⟨hin.1.fresh (by omega) hf.2, hin.2.step hv'⟩
  case vc2.step.isFalse =>
    rename_i pref cur suff hr b hin hf
    have he := range_cursor (G.offset_mono (i := s.lab[split]!) (j := s.lab[split]! + 1)
      (by omega) (by omega)) hr
    have hv' := Graph.neighbor_lt G ⟨s.lab[split]!, hroot⟩ (by omega : cur < G.offsets[s.lab[split]! + 1]!)
    have hk := hi.vertex_le hs hend hp hv'
    refine ⟨?_, hin.2.step hv'⟩
    by_cases heq : s.cellstart[(Graph.ofGraph G).neighbor cur]! = n
    · simpa only [heq] using hin.1.sentinel
    · exact hin.1.repeated (by omega) (hf heq)
  case vc6.step.pre =>
    rename_i marks pref cur suff hlist b hmark hout
    exact Compact.initial b.lab _ cur (by
      have hh : b.lab.size = n := by simpa using hout.1.length_eq
      have := hout.2.2.2.1.1.2
      omega)
  case vc4.step.isTrue =>
    rename_i marks pref first suff hlist b before q after hr r hin hmark hout hkey
    have hc := hout.2.2.2.1.1
    have hend' := hout.2.2.1.ends_eq first (s.cellend[first]! + 1 - first)
      hc.1 (by omega) (by omega)
    have hsize : b.lab.size = n := by simpa using hout.1.length_eq
    have hcur : q = first + before.length := by
      have hh := List.eq_of_range'_eq_append_cons (show
        List.range' first (b.cellend[first]! + 1 - first) = before ++ q :: after from by
          simpa only [RefineSt.hash, Std.Legacy.Range.toList, Nat.div_one,
            Nat.add_sub_cancel] using hr)
      simpa only [Nat.one_mul] using hh
    have hbound := range_cursor (by simpa only [RefineSt.hash] using
      (show first ≤ b.cellend[first]! + 1 by omega)) hr
    simp only [RefineSt.hash] at hbound
    have hread := hin.exterior q (by omega) (Or.inr (by omega))
    rw [hread] at hkey ⊢
    have hh := hin.collect (by omega) (by simpa only [hcur, beq_iff_eq] using hkey)
    simpa only [Nat.add_assoc, hcur] using hh
  case vc5.step.isFalse =>
    rename_i marks pref first suff hlist b before q after hr r hin hmark hout hkey
    have hc := hout.2.2.2.1.1
    have hend' := hout.2.2.1.ends_eq first (s.cellend[first]! + 1 - first)
      hc.1 (by omega) (by omega)
    have hsize : b.lab.size = n := by simpa using hout.1.length_eq
    have hcur : q = first + before.length := by
      have hh := List.eq_of_range'_eq_append_cons (show
        List.range' first (b.cellend[first]! + 1 - first) = before ++ q :: after from by
          simpa only [RefineSt.hash, Std.Legacy.Range.toList, Nat.div_one,
            Nat.add_sub_cancel] using hr)
      simpa only [Nat.one_mul] using hh
    have hbound := range_cursor (by simpa only [RefineSt.hash] using
      (show first ≤ b.cellend[first]! + 1 by omega)) hr
    simp only [RefineSt.hash] at hbound
    have hread := hin.exterior q (by omega) (Or.inr (by omega))
    rw [hread] at hkey ⊢
    have hh := hin.keep (by omega) (by simpa only [hcur, beq_eq_false_iff_ne] using hkey)
    simpa only [Nat.add_assoc, hcur] using hh
  case vc8.step.post.success.pre =>
    rename_i marks pref first suff hlist b r hmark hout hc
    have he := hc.extent (by simp)
    refine ⟨Fill.initial _ _ _ ?_, Index.Writes.initial hout.2.2.1.starts_size⟩
    simp only [List.length_reverse, Array.length_toList]
    have := hc.bounds
    have := hc.size
    omega
  case vc7.step =>
    rename_i marks pref first suff hlist b r before q after hr state hin hmark hout hc
    have hcur : q = before.length := by
      have hh := List.eq_of_range'_eq_append_cons (show
        List.range' 0 r.2.2.size = before ++ q :: after from by
          simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel, Nat.sub_zero] using hr)
      simpa only [Nat.one_mul, Nat.zero_add] using hh
    have hbound := range_cursor (Nat.zero_le r.2.2.size) hr
    have hlen : before.length < r.2.2.toList.reverse.length := by
      simp only [List.length_reverse, Array.length_toList]
      omega
    have hmem : r.2.2.toList.reverse[before.length]! ∈ r.2.2.toList.reverse := by
      rw [getElem!_pos r.2.2.toList.reverse before.length hlen]
      exact List.getElem_mem _
    have hverts := hc.hit_bound (n := n) (by
      intro v hv'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv'
      simp only [List.mem_range'_1] at hj
      apply perm_bound hout.1
      have hsize : b.lab.size = n := by simpa using hout.1.length_eq
      have := hc.bounds
      omega)
    have hv' := hverts _ (by simpa only [List.mem_reverse] using hmem)
    rw [reverse_read r.2.2 q (by omega), hcur, hin.2.2]
    refine ⟨hin.1.step hlen, ?_, by omega⟩
    have hh := hin.2.1.step hv'
    simpa only [List.take_succ_eq_append_getElem hlen,
      getElem!_pos r.2.2.toList.reverse before.length hlen] using hh
  case vc18.post.success.pre =>
    rename_i r hh
    refine ⟨hp, hs, hi, ?_, Cuts.refl level n s.ptn s.numcells n,
      cellsPerm_refl _ _ _, ?_, ?_, Activation.refl _ _ _⟩
    · exact original hh.1
    · intro v w hv' hw' he
      exact hh.2.count hv (Graph.row_nodup G ⟨s.lab[split]!, hroot⟩) hv' hw' he
    · apply Pending.touched (hi := hi)
      simpa only [Graph.row, Graph.ofGraph, List.map_map, Function.comp_def] using hh.1.sorted
  case vc17.step.post.success.post.success.isFalse =>
    rename_i marks pref first suff hlist b r out hmark hout hcomp hguard hr
    have hc := hout.2.2.2.1.1
    have hend' := hout.2.2.1.ends_eq first (s.cellend[first]! + 1 - first)
      hc.1 (by omega) (by omega)
    have he : b.cellend[first]! = s.cellend[first]! := by omega
    rw [he] at hcomp
    have hf : first ≤ s.cellend[first]! + 1 := by omega
    have hh := hcomp.scan_slice hf
    have hr' : Fill r.1 r.2.2.toList.reverse r.2.1 r.2.2.toList.reverse.length out.1 := by
      simpa using hr.1
    have hw' : Index.Writes n b.cellstart out.2.1 r.2.2.toList.reverse r.2.1 := by
      simpa only [show r.2.2.size = r.2.2.toList.reverse.length by simp, List.take_length]
        using hr.2.1
    have hext := hcomp.extent (by simp)
    have hlast : out.2.2 = s.cellend[first]! + 1 := by have := hr.2.2; omega
    have hperm := (hh.restore rfl hr').perm.trans hout.1
    have hcellperm := (hh.restore rfl hr').cells hf (by have := hh.bounds; omega) hc.1
    have hglobal := hout.2.2.2.2.1.perm hs (by simpa using hout.1.length_eq)
      (by simpa using hperm.length_eq) hend hcellperm
    have hcache := hh.cache rfl hr' hw' hout.1 hout.2.1 hout.2.2.1 hc.1 (by omega)
    have hconstant := hout.2.2.2.2.2.2.2.2.1.compact hh hr' hout.1 hout.2.1 hc.1 rfl
      hout.2.2.2.2.2.2.2.1
    have hd : ¬(r.2.1 ≠ s.cellend[first]! + 1 ∧ r.2.1 ≠ first) := by omega
    exact ⟨hperm, hout.2.1,
      by simpa only [ite_eq_right hd] using hcache, hout.2.2.2.1.2, hout.2.2.2.2.1, hout.2.2.2.2.2.1, cellsPerm_trans hglobal hout.2.2.2.2.2.2.1,
      hout.2.2.2.2.2.2.2.1, (by simpa only [ite_eq_right hd] using hconstant), hout.2.2.2.2.2.2.2.2.2⟩
  case vc19.post.success.post.success =>
    rename_i marks r hmark hin
    rcases hin with ⟨hp, hs, hi, hc, hq, hperm, _, hconstant, hactive⟩
    exact ⟨hp, hs, hi, hc, hq, hperm, hconstant, hactive⟩
  all_goals
    rename_i marks pref first suff hlist b r out hmark hout hcomp hguard hfirst hsecond hqueue hr
    have hc := hout.2.2.2.1.1
    have hend' := hout.2.2.1.ends_eq first (s.cellend[first]! + 1 - first)
      hc.1 (by omega) (by omega)
    have he : b.cellend[first]! = s.cellend[first]! := by omega
    rw [he] at hcomp
    have hf : first ≤ s.cellend[first]! + 1 := by omega
    have hh := hcomp.scan_slice hf
    have hr' : Fill r.1 r.2.2.toList.reverse r.2.1 r.2.2.toList.reverse.length out.1 := by
      simpa using hr.1
    have hw' : Index.Writes n b.cellstart out.2.1 r.2.2.toList.reverse r.2.1 := by
      simpa only [show r.2.2.size = r.2.2.toList.reverse.length by simp, List.take_length]
        using hr.2.1
    have hext := hcomp.extent (by simp)
    have hlast : out.2.2 = s.cellend[first]! + 1 := by have := hr.2.2; omega
    have hperm := (hh.restore rfl hr').perm.trans hout.1
    have hcellperm := (hh.restore rfl hr').cells hf (by have := hh.bounds; omega) hc.1
    have hglobal := hout.2.2.2.2.1.perm hs (by simpa using hout.1.length_eq)
      (by simpa using hperm.length_eq) hend hcellperm
    have hcache := hh.cache rfl hr' hw' hout.1 hout.2.1 hout.2.2.1 hc.1 (by omega)
    have hconstant := hout.2.2.2.2.2.2.2.2.1.compact hh hr' hout.1 hout.2.1 hc.1 rfl
      hout.2.2.2.2.2.2.2.1
    have hd : r.2.1 ≠ s.cellend[first]! + 1 ∧ r.2.1 ≠ first := by omega
    refine ⟨hperm, hout.2.1, ?_, ?_, ?_, ?_,
      cellsPerm_trans hglobal hout.2.2.2.2.2.2.1, hout.2.2.2.2.2.2.2.1,
      (by simpa only [ite_eq_left hd] using hconstant), ?_⟩
    · dsimp only at hcache
      simp only [ite_eq_left hd] at hcache
      rw [← hlast] at hcache
      first
      | simpa only [ite_eq_left hfirst, ite_eq_left hsecond] using hcache
      | simpa only [ite_eq_left hfirst, ite_eq_right hsecond] using hcache
      | simpa only [ite_eq_right hfirst, ite_eq_left hsecond] using hcache
      | simpa only [ite_eq_right hfirst, ite_eq_right hsecond] using hcache
    · intro a ha
      have had := hout.2.2.2.1.2 a ha
      refine ⟨?_, had.2⟩
      have hn := hmark.1.sorted.nodup
      rw [hlist] at hn
      have hne : a ≠ first := by
        have hn' := (List.nodup_append.mp hn).2.1
        have hn'' := (List.nodup_cons.mp hn').1
        intro heq
        exact hn'' (heq ▸ ha)
      simpa only [ite_eq_left hd] using hh.preserve hc.1 had.1 hne
    · have hbounds := hh.bounds
      exact hout.2.2.2.2.1.insert (by omega) (by rw [hout.2.1]; omega)
        (hc.1.2.2.1 _ (by omega) (by omega))
    · intro hq
      have hbounds := hh.bounds
      have hq' := hout.2.2.2.2.2.1 hq
      have hcut := hq'.cut (r.2.1 - 1)
      first
      | exact hcut.push (v := first) (by omega)
          (CellCut.left hc.1 (by omega) (by omega) (by rw [hout.2.1]; omega)).2.1 hqueue.2
      | exact hcut.push (v := r.2.1) (by omega)
          (CellCut.right hc.1 (by omega) (by omega) (by rw [hout.2.1]; omega)).2.1
          (hq'.fresh (by omega) (hc.1.2.2.1 _ (by omega) (by omega)))

    · have ho := original hmark.1 first (by rw [Array.mem_def, hlist]; simp)
      have hbounds := hh.bounds
      first
      | exact hout.2.2.2.2.2.2.2.2.2.cut_left ho.1 hc.1
          (by omega) (by omega) (by omega) hqueue.2
      | exact hout.2.2.2.2.2.2.2.2.2.cut_right ho.1 hc.1
          (by omega) (by omega) (by omega)

/-- Every output cell has constant native neighbour count into the captured
singleton splitter, including untouched cells and uniform compaction returns. -/
theorem splitSingleton_constant (G : Hex.SparseGraph n) (level split : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level) (hsp : split < n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hm : Scratch.Marks n s.stamp s.marks) (hv : Scratch.Marks n s.stamp s.vmarks) :
    let t := splitSingleton (.ofGraph G) level split s
    ∀ a len, IsCell t.ptn level a len → a + len ≤ n →
      ∀ q r, a ≤ q → q < a + len → a ≤ r → r < a + len →
        ((Graph.ofGraph G).row s.lab[split]!).count t.lab[q]! =
          ((Graph.ofGraph G).row s.lab[split]!).count t.lab[r]! := by
  exact (splitSingleton_state G level split s hp hs hend hsp hi hm hv).2.2.2.2.2.2.1.done

/-- The full singleton pass satisfies the fragment-activation rule for every
original cell, including cells absent from the touched list. -/
theorem splitSingleton_active (G : Hex.SparseGraph n) (level split : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level) (hsp : split < n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hm : Scratch.Marks n s.stamp s.marks) (hv : Scratch.Marks n s.stamp s.vmarks) :
    let t := splitSingleton (.ofGraph G) level split s
    Activation n level s.ptn t.ptn s.active t.active := by
  exact (splitSingleton_state G level split s hp hs hend hsp hi hm hv).2.2.2.2.2.2.2

/-- The complete singleton pass preserves a valid partition cache. -/
theorem splitSingleton_index (G : Hex.SparseGraph n) (level split : Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hend : s.ptn[n - 1]! ≤ level) (hsp : split < n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hm : Scratch.Marks n s.stamp s.marks) (hv : Scratch.Marks n s.stamp s.vmarks) :
    let t := splitSingleton (.ofGraph G) level split s
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Index.Valid n t.lab t.ptn level t.cellstart t.cellend := by
  have h := splitSingleton_state G level split s hp hs hend hsp hi hm hv
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end Hex.GraphIso.Nauty.Sparse
