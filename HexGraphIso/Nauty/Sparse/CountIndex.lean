/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexScan
public import HexGraphIso.Nauty.Sparse.Refine.CountSpec
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 4000000

private theorem range_position {first last cur : Nat} {pref suff : List Nat}
    (h : [first:last].toList = pref ++ cur :: suff) :
    cur = first + pref.length ∧ cur < last := by
  have hr : List.range' first (last - first) = pref ++ cur :: suff := by
    simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using h
  have hp := List.eq_of_range'_eq_append_cons hr
  have hb := List.mem_of_range'_eq_append_cons hr
  simp only [Nat.one_mul] at hp
  simp only [List.mem_range'] at hb
  exact ⟨hp, by obtain ⟨i, hi, rfl⟩ := hb; omega⟩

/-- Fragment installation indexes every constant-count run and preserves
cache entries outside the original cell. -/
theorem CountSort.finish_cache (level first : Nat) (distance : Bool) (s : RefineSt n)
    (lab : Array Nat) (w1 v2 w2 v3 : Nat)
    (hp : s.lab.toList.Perm (List.range n))
    (hs : s.cellstart.size = n) (he : s.cellend.size = n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
    (hc : ∀ q, first ≤ q → q ≤ s.cellend[first]! →
      s.cellstart[s.lab[q]!]! = if first = s.cellend[first]! then n else first)
    (hm : Minima.Permuted s.lab lab s.hits first (s.cellend[first]! + 1)
      v2 v3 (s.cellend[first]! + 1) w1 w2 (n + 2)) :
    Index.Complete n first s.cellend[first]! s.lab s.hits s.cellstart s.cellend
      (CountSort.finish level first (s.cellend[first]! + 1) distance { s with lab } w1 v2 w2 v3) := by
  have hl : s.lab.size = n := by simpa using hp.length_eq
  have bounds := hm.bounds
  rw [Index.Complete.iff]
  cases distance <;> unfold CountSort.finish
  all_goals simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
  all_goals apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    Sort.Window s.lab t.lab first (s.cellend[first]! + 1) ∧
    Index.Runs n first s.cellend[first]! (s.cellend[first]! + 1) t.lab s.hits t.cellstart t.cellend ∧
    Index.Frame n first s.cellend[first]! s.lab t.lab s.cellstart t.cellstart s.cellend t.cellend)
  all_goals mvcgen +jp
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
          Index.Two n first v2 v3 (v2 + cursor.prefix.length) lab state ∧
          Index.Frame n first s.cellend[first]! s.lab lab
            s.cellstart state s.cellend s.cellend⌝)
  all_goals try
    rename_i hi
    change Index.Two n first v2 v3 _ lab _ ∧
      Index.Frame n first s.cellend[first]! s.lab lab s.cellstart _ s.cellend s.cellend at hi
    obtain ⟨ht, hframe⟩ := hi
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList]
    try omega
  all_goals try
    have hin := And.intro ht hframe
  all_goals try
    have bounds := hm.bounds
    have hw : Sort.Window s.lab lab first (s.cellend[first]! + 1) := by simpa only [*] using hm.window
    have hh := Index.Complete.constant (s := { s with lab }) hw
      rfl rfl hs he (by change s.cellend[first]! < lab.size; have := hm.window.size; omega) hf rfl hc
      (fun q hq hu => hm.minimum q hq (by omega))
    simpa only [*] using Index.Complete.iff.mp hh
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
    have bounds := hm.bounds
    have hh := hm.indices (s := s) hp (by omega) hs (by
      intro q hq hu
      rw [hc q hq (by omega), ite_eq_right (by omega)])
    simp_all only [Nat.add_sub_cancel, ite_true, ite_false, and_true]
    done
  all_goals try
    rename_i hin
    have bounds := hm.bounds
    have pos := range_position (by assumption)
    simp_all only []
    have hh := hin.1.set_long hin.2 (hm.window.perm.trans hp)
      (by omega) (by omega) (by omega) (by omega) (by simp_all)
    simpa only [Nat.add_assoc] using hh
  all_goals try
    have bounds := hm.bounds
    have hi := hm.indices_single (s := s) hp (by omega) hs (by
      intro q hq hu
      have hh := hc q hq (by omega)
      first | exact hh | split at hh <;> first | omega | exact hh) (by omega)
    have ht := Index.Complete.of_two (s := s) hm hi.1 hi.2 (by omega) (by omega) he
    have hh := Index.Complete.iff.mp ht
    simp_all only [Nat.add_sub_cancel, ite_true, ite_false, and_true]
    done
  all_goals try
    rename_i hin
    have bounds := hm.bounds
    have hh := Index.Complete.of_scatter (s := s) hm
      (by simpa only [Nat.add_sub_of_le bounds.2.1] using hin.1) hin.2
      (by omega) (by omega) (by omega) he
    simpa only [Nat.add_sub_cancel] using hh
  all_goals try
    have bounds := hm.bounds
    have hi := hm.indices_single (s := s) hp (by omega) hs (by
      intro q hq hu
      have hh := hc q hq (by omega)
      first | exact hh | split at hh <;> first | omega | exact hh) (by omega)
    have ht := Index.Tail.initial (s := s) hm hi.1 hi.2 (by omega) (by omega) he
    simp only [Nat.add_sub_cancel] at ht
    first
    | apply ht.transfer <;> simp_all only [Nat.add_sub_cancel, Nat.add_sub_add_right, ite_true, ite_false]
    | refine ⟨?_, by omega⟩
      apply ht.transfer <;> simp_all only [Nat.add_sub_cancel, Nat.add_sub_add_right, ite_true, ite_false]
  all_goals try
    rename_i hin
    have bounds := hm.bounds
    have gap := hm.toBounded.second_pos (by omega)
    have ht := Index.Tail.initial (s := s) hm
      (by simpa only [Nat.add_sub_of_le bounds.2.1] using hin.1)
      (by simpa only [Nat.add_sub_cancel] using hin.2) gap (by omega) he
    simp only [Nat.add_sub_cancel] at ht
    first
    | apply ht.transfer <;> simp_all only [Nat.add_sub_cancel, Nat.add_sub_add_right, ite_true, ite_false]
    | refine ⟨?_, by omega⟩
      apply ht.transfer <;> rfl

/-- Count splitting installs all constant-count run indices and preserves
the cache outside its original cell. -/
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
  apply splitCounts_induct level first distance s
    (Index.Complete n first s.cellend[first]! s.lab s.hits s.cellstart s.cellend)
    hf (by omega) hk
  · intro hu
    exact Index.Complete.constant (Sort.Window.refl _ _ _) rfl rfl hs he (by simpa only [RefineSt.hash] using (show s.cellend[first]! < s.lab.size by omega)) hf rfl hc hu
  · intro lab w1 v2 w2 v3 hm
    exact CountSort.finish_cache level first distance (s.hash first) lab w1 v2 w2 v3
      hp hs he hf hb hc hm

end Hex.GraphIso.Nauty.Sparse
