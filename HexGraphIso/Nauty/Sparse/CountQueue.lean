/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Sparse.MinimaBound
public import HexGraphIso.Nauty.Sparse.Cuts
public import HexGraphIso.Nauty.Sparse.CellQueue
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- The executed count splitter preserves the exact active queue, including
its largest-fragment replacement and bounded tail scan. -/
theorem splitCounts_queue (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hq : CellQueue s.ptn level s.active s.queue) :
    let t := splitCounts level first distance s
    CellQueue t.ptn level t.active t.queue := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  have hopen (q : Nat) (hq : first ≤ q) (he : q < s.cellend[first]!) :
      level < s.ptn[q]! := hc.2.2.1 q hq (by omega)
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    CellQueue t.ptn level t.active t.queue)
  mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜first ≤ state.2.2.2 ∧ state.2.2.2 ≤ s.cellend[first]! ∧
          Cuts level n s.ptn state.1.ptn s.numcells state.1.numcells state.2.2.2 ∧
          CellQueue state.1.ptn level state.1.active state.1.queue ∧
          0 < state.1.queue.size ∧ ∀ p, state.2.1 = some p → p < state.1.queue.size⌝)
      | exact (let r : RefineSt n × Option Nat × Nat × Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜first ≤ state.2 ∧
          state.2 + cursor.suffix.length ≤ s.cellend[first]! ∧
          Cuts level n s.ptn state.1.ptn s.numcells state.1.numcells state.2 ∧
          CellQueue state.1.ptn level state.1.active state.1.queue ∧
          0 < state.1.queue.size ∧ ∀ p, r.2.1 = some p → p < state.1.queue.size⌝)
      | exact (⇓⟨cursor, state⟩ => ⌜
          Minima.Bounded state.2.2.2.2 s.hits first (s.cellend[first]! + 1)
            state.2.1 state.2.2.2.1 (s.cellend[first]! + 1 - cursor.suffix.length)
            state.1 state.2.2.1 (n + 2)⌝)
      | exact (⇓⟨cursor, state⟩ => ⌜first < state ∧ state ≤ s.cellend[first]! + 1 ∧
          (∀ q, first ≤ q → q < state → s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) ∧
          (state = first + 1 + cursor.prefix.length ∨
            s.hits[s.lab[state]!]! ≠ s.hits[s.lab[first]!]!)⌝)
      | exact (let r : Nat × Nat × Nat × Nat × Array Nat := by assumption
          ⇓⟨_, state⟩ => ⌜(state : Array Nat).size = state.size ∧
            Minima.Bounded r.2.2.2.2 s.hits first (s.cellend[first]! + 1)
              r.2.1 r.2.2.2.1 (s.cellend[first]! + 1) r.1 r.2.2.1 (n + 2)⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList]
    try omega
    try exact hq
  case vc3.pre =>
    intro q hq hq'
    have he : q = first := by omega
    rw [he]
  case vc10.post.success.isFalse.pre =>
    rename_i r hne hin
    have he : s.cellend[first]! + 1 - (s.cellend[first]! + 1 - r) = r := by omega
    rw [he]
    exact Minima.Bounded.initial hin.1 hin.2.1 (by omega)
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

  all_goals try
    rename_i hin
    exact ⟨by omega, by omega, hin.2.2.1.move (by omega)⟩
  all_goals try
    rename_i hin
    exact hin.2.2.2.1.replace_get hin.2.2.2.2.2 (by omega)
      (hc.2.1.imp_right (fun he => by rw [hin.2.2.1.closed _ he]; exact he)) (by simp_all)
  all_goals try
    rename_i hin
    obtain ⟨hfirst, hend, hcuts, hqueue, hpos, hbig⟩ := hin
    refine ⟨by omega, by omega,
      hcuts.cut (by omega) (by omega) (by omega) (hopen _ (by omega) (by omega)), ?_, ?_⟩
    · apply hqueue.cut_next
      · omega
      · have := hcuts.size; omega
      · rw [hcuts.tail _ (by omega)]
        exact hopen _ (by omega) (by omega)
    · intro p hp
      have := hbig p hp
      omega
    done
  all_goals try
    first
    | (rename_i hmin; have bounds := hmin.positions)
    | (rename_i hmin h1; have bounds := hmin.positions)
    | (rename_i hmin h1 h2; have bounds := hmin.positions)
    | (rename_i hmin h1 h2 h3; have bounds := hmin.positions)
    | (rename_i hmin h1 h2 h3 h4; have bounds := hmin.positions)
    | (rename_i hmin h1 h2 h3 h4 h5; have bounds := hmin.positions)
    have gap := hmin.second_pos (by omega)
  all_goals try omega
  all_goals try
    exact (hq.push (by omega) hc.2.1 (by simp_all)).cut _
  all_goals try
    apply hq.cut_next
    · omega
    · omega
    · exact hopen _ (by omega) (by omega)
    done
  all_goals try
    exact ⟨by omega, by omega,
      Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
        (hopen _ (by omega) (by omega)),
      hq.cut_next _ (by omega) (by omega) (hopen _ (by omega) (by omega))⟩
  all_goals try
    exact ⟨by omega,
      Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
        (hopen _ (by omega) (by omega)),
      hq.cut_next _ (by omega) (by omega) (hopen _ (by omega) (by omega))⟩

  all_goals try
    exact hq.cut_push (by omega) (by omega) (by omega) (hopen _ (by omega) (by omega))
  all_goals try
    exact ⟨by omega, by omega,
      Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
        (hopen _ (by omega) (by omega)),
      hq.cut_push (by omega) (by omega) (by omega) (hopen _ (by omega) (by omega))⟩

end Hex.GraphIso.Nauty.Sparse
