/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexScan
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 4000000

/-- The actual count splitter installs all constant-count run indices and
preserves cache entries outside the original cell. -/
theorem splitCounts_cache (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n))
    (hs : s.cellstart.size = n) (he : s.cellend.size = n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
    (hc : ∀ q, first ≤ q → q ≤ s.cellend[first]! →
      s.cellstart[s.lab[q]!]! = if first = s.cellend[first]! then n else first)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    Index.Complete n first s.cellend[first]! s.lab s.hits s.cellstart s.cellend
      (splitCounts level first distance s) := by
  have hl : s.lab.size = n := by simpa using hp.length_eq
  rw [Index.Complete.iff]
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    Sort.Window s.lab t.lab first (s.cellend[first]! + 1) ∧
    Index.Runs n first s.cellend[first]! (s.cellend[first]! + 1) t.lab s.hits t.cellstart t.cellend ∧
    Index.Frame n first s.cellend[first]! s.lab t.lab s.cellstart t.cellstart s.cellend t.cellend)
  mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨cursor, state⟩ => ⌜
          Index.Tail n first s.cellend[first]! state.2.2.2
            s.lab s.hits s.cellstart s.cellend state.1 ∧
          s.cellend[first]! ≤ state.2.2.2 + cursor.suffix.length⌝)
      | exact (let r : RefineSt n × Option Nat × Nat × Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜
            r.2.2.2 + 1 ≤ state.2 ∧ state.2 + cursor.suffix.length ≤ s.cellend[first]! ∧
            state.1.lab = r.1.lab ∧ state.1.hits = s.hits ∧ state.1.cellend = r.1.cellend ∧
            Index.Scatter n r.1.lab r.1.cellstart state.1.cellstart
              (r.2.2.2 + 1 + 1) (state.2 + 1) (r.2.2.2 + 1) ∧
            s.hits[state.1.lab[state.2]!]! = s.hits[r.1.lab[r.2.2.2 + 1]!]! ∧
            (state.2 = r.2.2.2 + 1 + cursor.prefix.length ∨
              s.hits[state.1.lab[state.2 + 1]!]! ≠ s.hits[r.1.lab[r.2.2.2 + 1]!]!)⌝)
      | exact (⇓⟨cursor, state⟩ => ⌜
          Minima.Permuted s.lab state.2.2.2.2 s.hits first (s.cellend[first]! + 1)
            state.2.1 state.2.2.2.1 (s.cellend[first]! + 1 - cursor.suffix.length)
            state.1 state.2.2.1 (n + 2)⌝)
      | exact (⇓⟨cursor, state⟩ => ⌜first < state ∧ state ≤ s.cellend[first]! + 1 ∧
          (∀ q, first ≤ q → q < state → s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) ∧
          (state = first + 1 + cursor.prefix.length ∨
            s.hits[s.lab[state]!]! ≠ s.hits[s.lab[first]!]!)⌝)
      | exact (let r : Nat × Nat × Nat × Nat × Array Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜
            Minima.Permuted s.lab r.2.2.2.2 s.hits first (s.cellend[first]! + 1)
              r.2.1 r.2.2.2.1 (s.cellend[first]! + 1) r.1 r.2.2.1 (n + 2) ∧
            Index.Two n first r.2.1 r.2.2.2.1 (r.2.1 + cursor.prefix.length) r.2.2.2.2 state ∧
            Index.Frame n first s.cellend[first]! s.lab r.2.2.2.2
              s.cellstart state s.cellend s.cellend⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList]
    try omega
  case vc3.pre =>
    intro q hq hq'
    have he : q = first := by omega
    rw [he]
  case vc10.post.success.isFalse.pre =>
    rename_i r hne hin
    have he : s.cellend[first]! + 1 - (s.cellend[first]! + 1 - r) = r := by omega
    rw [he]
    exact Minima.Permuted.initial hin.1 hin.2.1 (by omega)
      (fun q hq he => hk q hq (by omega)) hin.2.2.1
  case vc2.step.isFalse =>
    rename_i pref j suff hr b he hin
    have hj := range_cursor (by omega : first + 1 ≤ s.cellend[first]! + 1) hr
    have hp : j = first + 1 + pref.length := by
      have hp := List.eq_of_range'_eq_append_cons (show
        List.range' (first + 1) (s.cellend[first]! - first) = pref ++ j :: suff from by
          simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel,
            Nat.add_sub_add_right] using hr)
      simpa only [Nat.one_mul] using hp
    refine ⟨by omega, by omega, ?_, Or.inl (by omega)⟩
    intro q hq hq'
    by_cases heq : q = b
    · simpa only [heq, hin.2.2.2] using he
    · exact hin.2.2.1 q hq (by omega)
  case vc5.step.isTrue =>
    rename_i r pref j suff hr b hne hscan hkey hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    have bounds := hin.bounds
    have hjb : j < b.2.2.2.2.size := by have := hin.size; omega
    have hread := rotate_read b.2.2.2.2 j b.2.2.2.1 b.2.1 (by omega) (by omega) hjb
    simp only [Array.set!_eq_setIfInBounds] at hread
    rw [hread]
    exact hin.hit_min (by omega) hkey
  case vc6.step.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hkey hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    exact hin.hit_second (by omega) hkey
  case vc7.step.isFalse.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hkey hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    have bounds := hin.bounds
    have hjb : j < b.2.2.2.2.size := by have := hin.size; omega
    have hread := rotate_read b.2.2.2.2 j b.2.1 first (by omega) (by omega) hjb
    simp only [Array.set!_eq_setIfInBounds] at hread
    rw [hread]
    exact hin.new_min (by omega) hkey
  case vc8.step.isFalse.isFalse.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hlo hhi hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    exact hin.new_second (by omega) (by omega) hhi
  case vc9.step.isFalse.isFalse.isFalse.isFalse =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hlo hhi hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    exact hin.above (by omega) (by omega)


  case vc4.post.success.isTrue =>
    rename_i r heq hin
    exact Index.Complete.iff.mp (Index.Complete.constant (s := s)
      (Sort.Window.refl _ _ _) rfl rfl hs he (by omega) hf rfl hc
      (fun q hq hu => hin.2.1 q hq (by omega)))
  case vc11.post.success.isFalse.post.success.isTrue =>
    rename_i r b hn heq hin
    have hw : Sort.Window s.lab b.2.2.2.2 first (s.cellend[first]! + 1) := by
      simpa only [heq] using hin.window
    have hb' : s.cellend[first]! < b.2.2.2.2.size := by
      have := hin.window.size
      omega
    have hh := Index.Complete.constant (s := { s with lab := b.2.2.2.2 }) hw
      rfl rfl hs he hb' hf rfl hc
      (fun q hq hu => hin.minimum q hq (by omega))
    simpa only [heq] using Index.Complete.iff.mp hh
  all_goals try
    rename_i hin
    have bounds := hin.1.bounds
    have heq := Nat.le_antisymm bounds.2 hin.2
    exact ⟨hin.1.window, by simpa only [heq] using hin.1.runs, hin.1.frame⟩
  all_goals try
    rename_i hin
    have bounds := hin.1.bounds
    exact ⟨hin.1, by omega⟩
  all_goals try
    rename_i hin
    exact ⟨by omega, hin.1.hits_eq, Index.Scatter.initial hin.1.runs.starts_size⟩
  all_goals try
    rename_i hout hkey hin
    have perm := hout.1.window.perm.trans hp
    have hstep := hin.2.2.2.2.2.1.step (fun i hi => perm_bound perm hi)
      (fun i j hi hj he => perm_injective perm hi hj he) (by omega) (by omega)
    simp only [Array.set!_eq_setIfInBounds] at hstep
    grind [Index.Tail.hits_eq]
  all_goals try grind [Index.Tail.hits_eq, Index.Tail.bounds]
  all_goals try
    rename_i hout hsize hin
    have bounds := hout.1.bounds
    let r : RefineSt n × Nat := by assumption
    have hk' := hin.2.2.2.2.2.2.1
    have hn' := hin.2.2.2.2.2.2.2
    rw [hin.2.2.1] at hk' hn'
    have hh := hout.1.scanned r.1 hp (by omega) hb hin.1 hin.2.1 hk' hn' hin.2.2.2.2.2.1
    refine ⟨?_, by omega⟩
    simpa only [ite_eq_left hsize] using hh
  all_goals try
    rename_i hout hsize hbig hin
    have bounds := hout.1.bounds
    let r : RefineSt n × Nat := by assumption
    have hk' := hin.2.2.2.2.2.2.1
    have hn' := hin.2.2.2.2.2.2.2
    rw [hin.2.2.1] at hk' hn'
    have hh := hout.1.scanned r.1 hp (by omega) hb hin.1 hin.2.1 hk' hn' hin.2.2.2.2.2.1
    refine ⟨?_, by omega⟩
    simpa only [ite_eq_right hsize] using hh
  all_goals try
    rename_i hin
    have bounds := hin.bounds
    have hh := hin.indices hp (by omega) hs (by
      intro q hq hu
      rw [hc q hq (by omega), ite_eq_right (by omega)])
    simp_all only [Nat.add_sub_cancel, ite_true, ite_false, and_true]
    done
  case vc194.step =>
    rename_i r0 r pref cur suff hr b hn hscan hfirst hv2 hv3 hm hin
    have bounds := hm.bounds
    have hi : cur = first + 1 + pref.length := by
      have hh := List.eq_of_range'_eq_append_cons (show
        List.range' (first + 1) (r.2.2.2.1 - (first + 1)) = pref ++ cur :: suff from by
          simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel, hv2] using hr)
      simpa only [Nat.one_mul] using hh
    have hc := List.mem_of_range'_eq_append_cons (show
      List.range' (first + 1) (r.2.2.2.1 - (first + 1)) = pref ++ cur :: suff from by
        simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel, hv2] using hr)
    have hcur : cur < r.2.2.2.1 := by
      have hh := List.mem_range'.mp hc
      omega
    rw [hi]
    have hh := hin.1.set_long hin.2 (hm.window.perm.trans hp)
      (by omega) (by omega) (by omega) (by omega) hv3
    simpa only [Nat.add_assoc] using hh
  case vc560.step =>
    rename_i r0 r pref cur suff hr b hn hscan hfirst hv2 hv3 hm hin
    have bounds := hm.bounds
    have hi : cur = r.2.1 + pref.length := by
      have hh := List.eq_of_range'_eq_append_cons (show
        List.range' r.2.1 (r.2.2.2.1 - r.2.1) = pref ++ cur :: suff from by
          simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using hr)
      simpa only [Nat.one_mul] using hh
    have hc := List.mem_of_range'_eq_append_cons (show
      List.range' r.2.1 (r.2.2.2.1 - r.2.1) = pref ++ cur :: suff from by
        simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using hr)
    have hcur : cur < r.2.2.2.1 := by
      have hh := List.mem_range'.mp hc
      omega
    rw [hi]
    have hh := hin.1.set_long hin.2 (hm.window.perm.trans hp)
      (by omega) (by omega) (by omega) (by omega) hv3
    simpa only [Nat.add_assoc] using hh
  all_goals try
    rename_i hm
    have bounds := hm.bounds
    have hi := hm.indices_single hp (by omega) hs (by
      intro q hq hu
      first
      | exact hc q hq (by omega)
      | have hh := hc q hq (by omega)
        split at hh <;> first | omega | exact hh) (by omega)
    have ht := Index.Complete.of_two hm hi.1 hi.2 (by omega) (by omega) he
    have hh := Index.Complete.iff.mp ht
    simp_all only [Nat.add_sub_cancel, ite_true, ite_false, and_true]
    done
  all_goals try
    rename_i hin
    have bounds := hin.1.bounds
    have hh := Index.Complete.of_scatter hin.1 hin.2.1 hin.2.2 (by omega)
      (by omega) (by omega) he
    simpa only [Nat.add_sub_cancel] using hh
  all_goals try
    rename_i hm
    have bounds := hm.bounds
    have hi := hm.indices_single hp (by omega) hs (by
      intro q hq hu
      first
      | exact hc q hq (by omega)
      | have hh := hc q hq (by omega)
        split at hh <;> first | omega | exact hh) (by omega)
    have ht := Index.Tail.initial hm hi.1 hi.2 (by omega) (by omega) he
    simp only [Nat.add_sub_cancel] at ht
    refine ⟨?_, by omega⟩
    apply ht.transfer <;> simp_all only [Nat.add_sub_cancel, Nat.add_sub_add_right, ite_true, ite_false]
  all_goals try
    rename_i hm hn hd hbig hin
    have bounds := hm.bounds
    have gap := hm.toBounded.second_pos (by omega)
    have ht := Index.Tail.initial hm
      (by simpa only [Nat.add_sub_of_le bounds.2.1] using hin.1)
      (by simpa only [Nat.add_sub_cancel] using hin.2) gap (by omega) he
    simp only [Nat.add_sub_cancel] at ht
    refine ⟨?_, by omega⟩
    apply ht.transfer <;> rfl

end Hex.GraphIso.Nauty.Sparse
