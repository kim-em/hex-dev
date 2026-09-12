/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountProgress
public import HexGraphIso.Nauty.Sparse.CountUniform
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do CountTrace
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- The hash and active queue returned by the executed count splitter
admit its exact count-run control trace. -/
private theorem trace_nonuniform (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hn : ∃ q, first ≤ q ∧ q < s.cellend[first]! + 1 ∧
      s.hits[s.lab[q]!]! ≠ s.hits[s.lab[first]!]!) :
    Result distance first (s.cellend[first]! + 1) s
      (splitCounts level first distance s).lab (control (splitCounts level first distance s)) := by
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    Result distance first (s.cellend[first]! + 1) s t.lab (control t))
  mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨cursor, state⟩ => ⌜state.1.hits = s.hits ∧
          Progress distance first (s.cellend[first]! + 1) s state.1.lab state.2.2.2
            (control state.1) state.2.1 state.2.2.1 ∧
          s.cellend[first]! ≤ state.2.2.2 + cursor.suffix.length⌝)
      | exact (let r : RefineSt n × Option Nat × Nat × Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜
            state.1.lab = r.1.lab ∧ state.1.hits = s.hits ∧
            control state.1 = (control r.1).advance distance r.2.2.2 s.hits[r.1.lab[r.2.2.2 + 1]!]! ∧
            CountTrace.Scan r.1.lab s.hits (r.2.2.2 + 1) s.cellend[first]!
              state.2 cursor.prefix.length cursor.suffix.length⌝)
      | exact (⇓⟨cursor, state⟩ => ⌜
          Minima.Permuted s.lab state.2.2.2.2 s.hits first (s.cellend[first]! + 1)
            state.2.1 state.2.2.2.1 (s.cellend[first]! + 1 - cursor.suffix.length)
            state.1 state.2.2.1 (n + 2)⌝)
      | exact (⇓⟨cursor, state⟩ => ⌜first < state ∧ state ≤ s.cellend[first]! + 1 ∧
          (∀ q, first ≤ q → q < state → s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) ∧
          (state = first + 1 + cursor.prefix.length ∨
            s.hits[s.lab[state]!]! ≠ s.hits[s.lab[first]!]!)⌝)
      | exact (let r : Nat × Nat × Nat × Nat × Array Nat := by assumption
          ⇓⟨_, state⟩ => ⌜(state : Array Nat).size = state.size ∧
            Minima.Permuted s.lab r.2.2.2.2 s.hits first (s.cellend[first]! + 1)
              r.2.1 r.2.2.2.1 (s.cellend[first]! + 1) r.1 r.2.2.1 (n + 2)⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, CountTrace.control, Std.Legacy.Range.toList, ← Option.eq_none_iff_forall_ne_some]
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
    rename_i r he hin
    obtain ⟨q, hq, he, hnq⟩ := hn
    exact False.elim (hnq (hin.2.1 q hq he))
  case vc11.post.success.isFalse.post.success.isTrue =>
    rename_i r b hn0 he hin
    obtain ⟨q, hq, heq, hnq⟩ := hn
    exact False.elim (hnq (hin.constant rfl hq heq))
  all_goals try
    rename_i hin
    have bounds := hin.positions
    have hv := hin.toBounded.second_pos (by omega)
    refine Result.divided hn hin.toMinima hv ?_
    simp_all [Control.base, Control.hash, Control.pair, Control.push, CountTrace.control]
  all_goals try
    rename_i hin
    have hp := hin.2.1
    have bounds := hp.bounds
    have hd := hp.done (by omega)
    simp_all [Control.finish, Control.hash, Array.set!_eq_setIfInBounds]
  all_goals try
    rename_i hm h1 h2 h3
    have bounds := hm.positions
    have hv := hm.toBounded.second_pos (by omega)
    have hi := Progress.initial (distance := distance) hn (hm.toMinima.indirect hm.size) hv (by omega)
    simp_all [Control.more, Control.base, Control.hash, Control.push, CountTrace.control]
    all_goals try simp (disch := omega) only [ite_eq_right] at hi
    all_goals try simp_all
    all_goals omega
  all_goals try
    rename_i hm h1 h2
    have bounds := hm.positions
    have hv := hm.toBounded.second_pos (by omega)
    have hi := Progress.initial (distance := distance) hn (hm.toMinima.indirect hm.size) hv (by omega)
    simp_all [Control.more, Control.base, Control.hash, Control.push, CountTrace.control]
    all_goals try simp (disch := omega) only [ite_eq_right] at hi
    all_goals try simp_all
    all_goals omega
  all_goals try
    rename_i hm h1
    have bounds := hm.positions
    have hv := hm.toBounded.second_pos (by omega)
    have hi := Progress.initial (distance := distance) hn (hm.toMinima.indirect hm.size) hv (by omega)
    simp_all [Control.more, Control.base, Control.hash, Control.push, CountTrace.control]
    all_goals try simp (disch := omega) only [ite_eq_right] at hi
    all_goals try simp_all
    all_goals omega
  all_goals try
    rename_i hm
    have bounds := hm.positions
    have hv := hm.toBounded.second_pos (by omega)
    have hi := Progress.initial (distance := distance) hn (hm.toMinima.indirect hm.size) hv (by omega)
    simp_all [Control.more, Control.base, Control.hash, Control.push, CountTrace.control]
    all_goals try simp (disch := omega) only [ite_eq_right] at hi
    all_goals try simp_all
    all_goals omega
  all_goals try
    rename_i hi0
    have hi := hi0.2.2.2
    first
      | exact hi.step (by assumption)
      | exact hi.stop (by assumption)
  all_goals try
    constructor
    · rfl
    · exact CountTrace.Scan.initial (by omega)
  all_goals try
    rename_i ho hh hi
    have hr := hi.2.2.2.run
    have hp := ho.2.1.next (by omega) hr
    have bounds := hr.bounds
    have budget := ho.2.2
    have hq := congrArg Control.queue hi.2.2.1
    simp_all [Control.choose, Control.advance, Control.hash, Control.push]
    all_goals try simp (disch := omega) only [ite_eq_right] at hp
    all_goals try simp_all
    all_goals omega
  all_goals try
    rename_i ho hh hh2 hi
    have hr := hi.2.2.2.run
    have hp := ho.2.1.next (by omega) hr
    have bounds := hr.bounds
    have budget := ho.2.2
    have hq := congrArg Control.queue hi.2.2.1
    simp_all [Control.choose, Control.advance, Control.hash, Control.push]
    all_goals try simp (disch := omega) only [ite_eq_right] at hp
    all_goals try simp_all
    all_goals omega


/-- Every executed count split has its literal hash and queue trace. The
only count bound is on the cell being divided; stale counts outside that
cell and the other scratch fields are unrestricted. -/
theorem splitCounts_trace (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    Result distance first (s.cellend[first]! + 1) s
      (splitCounts level first distance s).lab (control (splitCounts level first distance s)) := by
  classical
  by_cases hu : ∀ q, first ≤ q → q < s.cellend[first]! + 1 →
      s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!
  · rw [splitCounts_uniform level first distance s hf (fun q hq he => hu q hq (by omega))]
    exact Result.uniform hu
  · apply trace_nonuniform level first distance s hl hf hb hk
    apply Classical.byContradiction
    intro hn
    apply hu
    intro q hq he
    apply Classical.byContradiction
    intro hne
    exact hn ⟨q, hq, he, hne⟩

end Hex.GraphIso.Nauty.Sparse
