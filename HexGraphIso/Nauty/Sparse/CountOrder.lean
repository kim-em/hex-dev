/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Sparse.MinimaSort
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- The executed count splitter orders the whole cell by its hit values.
Its initial key lies below the `n + 2` sentinel used for the second minimum. -/
theorem splitCounts_sorted (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size)
    (hk : s.hits[s.lab[first]!]! < n + 2) :
    Sort.Sorted (splitCounts level first distance s).lab s.hits first
      (s.cellend[first]! + 1 - first) := by
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    Sort.Sorted t.lab s.hits first (s.cellend[first]! + 1 - first))
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜Sort.Sorted state.1.lab s.hits first (s.cellend[first]! + 1 - first)⌝)
    | exact (⇓⟨cursor, state⟩ => ⌜
        Minima state.2.2.2.2 s.hits first state.2.1 state.2.2.2.1
          (s.cellend[first]! + 1 - cursor.suffix.length) state.1 state.2.2.1 ∧
        state.2.2.2.2.size = s.lab.size⌝)
    | exact (⇓⟨cursor, state⟩ => ⌜first < state ∧ state ≤ s.cellend[first]! + 1 ∧
        (∀ q, first ≤ q → q < state → s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) ∧
        (state = first + 1 + cursor.prefix.length ∨
          s.hits[s.lab[state]!]! ≠ s.hits[s.lab[first]!]!)⌝)
    | exact (let r : Nat × Nat × Nat × Nat × Array Nat := by assumption
        ⇓⟨_, state⟩ => ⌜(state : Array Nat).size = state.size ∧
          Minima r.2.2.2.2 s.hits first r.2.1 r.2.2.2.1 (s.cellend[first]! + 1) r.1 r.2.2.1 ∧
          r.2.2.2.2.size = s.lab.size⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList]
    try grind [Minima.initial, Minima.constant_sorted, Minima.done_sorted,
      Minima.sort_tail, Minima.bounds, range_cursor]
  all_goals try first
    | (rename_i hin; exact hin.1.done_sorted (by omega))
    | (rename_i hin; exact hin.done_sorted (by omega))
    | (rename_i hin; simpa using hin.1.sort_tail (by have := hin.2; omega))
    | (rename_i hin hn hsize hd; simpa using hin.1.sort_tail (by have := hin.2; omega))
  case vc3.pre =>
    intro q hq hq'
    have he : q = first := by omega
    rw [he]
  case vc4.post.success.isTrue =>
    rename_i r he hin
    exact Minima.constant_sorted hin.2.1
  case vc10.post.success.isFalse.pre =>
    rename_i r hne hin
    have he : s.cellend[first]! + 1 - (s.cellend[first]! + 1 - r) = r := by omega
    rw [he]
    exact Minima.initial hin.1 hk hin.2.2.1
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
    have bounds := hin.1.bounds
    have hjb : j < b.2.2.2.2.size := by omega
    have hread := rotate_read b.2.2.2.2 j b.2.2.2.1 b.2.1 (by omega) (by omega) hjb
    simp only [Array.set!_eq_setIfInBounds] at hread
    rw [hread]
    exact hin.1.hit_min hjb hkey
  case vc6.step.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hkey hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    exact hin.1.hit_second (by omega) hkey
  case vc7.step.isFalse.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hkey hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    have bounds := hin.1.bounds
    have hjb : j < b.2.2.2.2.size := by omega
    have hread := rotate_read b.2.2.2.2 j b.2.1 first (by omega) (by omega) hjb
    simp only [Array.set!_eq_setIfInBounds] at hread
    rw [hread]
    exact hin.1.new_min hjb hkey
  case vc8.step.isFalse.isFalse.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hlo hhi hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    exact hin.1.new_second (by omega) (by omega) hhi
  case vc9.step.isFalse.isFalse.isFalse.isFalse =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hlo hhi hin
    have hj := range_cursor hscan.2.1 hr
    have hj0 : s.cellend[first]! - suff.length = j := by omega
    have hj1 : s.cellend[first]! + 1 - suff.length = j + 1 := by omega
    rw [hj0] at hin
    rw [hj1]
    exact hin.1.above (by omega)

end Hex.GraphIso.Nauty.Sparse
