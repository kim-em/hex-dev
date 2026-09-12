/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Sparse.MinimaBound
public import HexGraphIso.Nauty.Sparse.Cuts
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- Every increment of the executed count splitter's cell counter corresponds
exactly to a newly closed partition boundary. Scratch counts are bounded only
on the cell being divided, and old closed boundary values are retained. -/
theorem splitCounts_cuts (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    Cuts level n s.ptn (splitCounts level first distance s).ptn
      s.numcells (splitCounts level first distance s).numcells n := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  have hopen (q : Nat) (hq : first ≤ q) (he : q < s.cellend[first]!) :
      level < s.ptn[q]! := hc.2.2.1 q hq (by omega)
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    Cuts level n s.ptn t.ptn s.numcells t.numcells n)
  mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜first ≤ state.2.2.2 ∧ state.2.2.2 ≤ s.cellend[first]! ∧
          Cuts level n s.ptn state.1.ptn s.numcells state.1.numcells state.2.2.2⌝)
      | exact (⇓⟨cursor, state⟩ => ⌜first ≤ state.2 ∧
          state.2 + cursor.suffix.length ≤ s.cellend[first]! ∧
          Cuts level n s.ptn state.1.ptn s.numcells state.1.numcells state.2⌝)
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
    try exact Cuts.refl _ _ _ _ _
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
    exact hin.2.2.move (by omega)
  all_goals try
    rename_i hin
    exact ⟨by omega, by omega, hin.2.2.move (by omega)⟩
  all_goals try
    rename_i hin
    exact ⟨by omega, by omega,
      hin.2.2.cut (by omega) (by omega) (by omega) (hopen _ (by omega) (by omega))⟩
  all_goals try
    rename_i hin
    have bounds := hin.positions
    exact Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
      (hopen _ (by omega) (by omega))
  all_goals try first
    | (rename_i hin
       have bounds := hin.positions
       first
       | omega
       | (have gap := hin.second_pos (by omega)
          exact ⟨by omega, by omega,
            Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
              (hopen _ (by omega) (by omega))⟩))
    | (rename_i hin hn ha hd
       have bounds := hin.positions
       have gap := hin.second_pos (by omega)
       exact ⟨by omega, by omega,
         Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
           (hopen _ (by omega) (by omega))⟩)
  all_goals
    exact ⟨by omega, Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
      (hopen _ (by omega) (by omega))⟩

/-- The counter increment is exactly the number of newly closed boundaries. -/
theorem splitCounts_count (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    bcount (splitCounts level first distance s).ptn level n + s.numcells =
      bcount s.ptn level n + (splitCounts level first distance s).numcells :=
  (splitCounts_cuts level first distance s hl hs hb hc hk).count

/-- Closed partition values, including boundaries inherited from ancestors,
are retained literally by the count splitter. -/
theorem splitCounts_closed (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (q : Nat) (hq : s.ptn[q]! ≤ level) :
    (splitCounts level first distance s).ptn[q]! = s.ptn[q]! :=
  (splitCounts_cuts level first distance s hl hs hb hc hk).closed q hq

end Hex.GraphIso.Nauty.Sparse
