/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Sparse.CountPartition
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- The executed count splitter closes exactly the boundaries between unequal
adjacent counts inside the original cell, retaining every other value. -/
theorem splitCounts_partition (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hf : first ≤ s.cellend[first]!)
    (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    CountPartition level first s.cellend[first]!
      (splitCounts level first distance s).lab s.hits s.ptn
      (splitCounts level first distance s).ptn := by
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    CountPartition level first s.cellend[first]! t.lab s.hits s.ptn t.ptn)
  mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨cursor, state⟩ => ⌜
          CountPartition level first state.2.2.2 state.1.lab s.hits s.ptn state.1.ptn ∧
          first ≤ state.2.2.2 ∧ state.2.2.2 ≤ s.cellend[first]! ∧
          (state.2.2.2 = s.cellend[first]! ∨
            s.hits[state.1.lab[state.2.2.2]!]! ≠ s.hits[state.1.lab[state.2.2.2 + 1]!]!) ∧
          s.cellend[first]! ≤ state.2.2.2 + cursor.suffix.length ∧ state.1.hits = s.hits⌝)
      | exact (let r : RefineSt n × Option Nat × Nat × Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜
            r.2.2.2 + 1 ≤ state.2 ∧ state.2 + cursor.suffix.length ≤ s.cellend[first]! ∧
            state.1.lab = r.1.lab ∧ state.1.hits = s.hits ∧
            CountPartition level first state.2 state.1.lab s.hits s.ptn state.1.ptn ∧
            s.hits[state.1.lab[state.2]!]! = s.hits[r.1.lab[r.2.2.2 + 1]!]! ∧
            (state.2 = r.2.2.2 + 1 + cursor.prefix.length ∨
              s.hits[state.1.lab[state.2 + 1]!]! ≠ s.hits[r.1.lab[r.2.2.2 + 1]!]!)⌝)
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

  case vc4.post.success.isTrue =>
    rename_i r he hin
    exact CountPartition.constant (fun q hq hu => hin.2.1 q hq (by omega))
  case vc11.post.success.isFalse.post.success.isTrue =>
    rename_i r b hn he hin
    exact CountPartition.constant (fun q hq hu => hin.minimum q hq (by omega))
  all_goals try
    rename_i hin
    have he := Nat.le_antisymm hin.2.2.1 hin.2.2.2.2.1
    simpa only [he] using hin.1
  all_goals try
    rename_i hin
    have bounds := hin.positions
    have gap := hin.second_pos (by omega)
    have hp := CountPartition.minima (level := level) hin.toMinima gap (by omega : _ < s.ptn.size)
    grind
  all_goals try grind [CountPartition.equal, CountPartition.different]
  all_goals try
    rename_i hin
    have bounds := hin.positions
    have gap := hin.second_pos (by omega)
    have ht := hin.toMinima.indirect hin.size
    have hp := CountPartition.minima (level := level) ht gap (by omega : _ < s.ptn.size)
    have hn := ht.next_different gap (by omega)
    grind
  all_goals try
    rename_i hin ha hb hd
    have bounds := hin.positions
    have gap := hin.second_pos (by omega)
    have ht := hin.toMinima.indirect hin.size
    have hp := CountPartition.minima (level := level) ht gap (by omega : _ < s.ptn.size)
    have hn := ht.next_different gap (by omega)
    grind

end Hex.GraphIso.Nauty.Sparse
