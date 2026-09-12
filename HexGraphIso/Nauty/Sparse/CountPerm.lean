/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Sparse.Rotate
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- The actual count splitter permutes the label array. The initial cell
window is nonempty and bounded; no assumptions on the hit values are needed. -/
theorem splitCounts_perm (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size) :
    (splitCounts level first distance s).lab.toList.Perm s.lab.toList := by
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => t.lab.toList.Perm s.lab.toList)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜state.1.lab.toList.Perm s.lab.toList⌝)
    | exact (⇓⟨cursor, state⟩ => ⌜state.2.2.2.2.toList.Perm s.lab.toList ∧
        first < state.2.1 ∧ state.2.1 ≤ state.2.2.2.1 ∧
        state.2.2.2.1 ≤ s.cellend[first]! + 1 - cursor.suffix.length⌝)
    | exact (⇓⟨cursor, state⟩ => ⌜first < state ∧ state ≤ s.cellend[first]! + 1 ∧
        (state = first + 1 + cursor.prefix.length ∨
          s.hits[s.lab[state]!]! ≠ s.hits[s.lab[first]!]!)⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList,
      -Array.toList_setIfInBounds, -Array.toList_set!]
    try grind [List.Perm.refl, List.Perm.trans, List.Perm.length_eq,
      rotate_read, rotate_perm, exchange_perm, indirect_perm, perm_size,
      List.eq_of_range'_eq_append_cons, List.mem_of_range'_eq_append_cons, range_cursor]
  case vc5.step.isTrue =>
    rename_i r pref j suff hr b hne hscan hk hin
    have hj := range_cursor hscan.2.1 hr
    have hs := perm_size hin.1
    have hjb : j < b.2.2.2.2.size := by omega
    have hr := rotate_read b.2.2.2.2 j b.2.2.2.1 b.2.1 (by omega) (by omega) hjb
    simp only [Array.set!_eq_setIfInBounds] at hr
    rw [hr]
    refine ⟨(rotate_perm _ _ _ _ (by omega) (by omega) hjb).trans hin.1, by omega, by omega⟩
  case vc6.step.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hkey hk hin
    have hj := range_cursor hscan.2.1 hr
    have hs := perm_size hin.1
    refine ⟨(exchange_perm _ _ _ (by omega) (by omega)).trans hin.1, by omega, by omega⟩
  case vc7.step.isFalse.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hk hin
    have hj := range_cursor hscan.2.1 hr
    have hs := perm_size hin.1
    have hjb : j < b.2.2.2.2.size := by omega
    have hr := rotate_read b.2.2.2.2 j b.2.1 first (by omega) (by omega) hjb
    simp only [Array.set!_eq_setIfInBounds] at hr
    rw [hr]
    refine ⟨(rotate_perm _ _ _ _ (by omega) (by omega) hjb).trans hin.1, by omega, by omega⟩
  case vc8.step.isFalse.isFalse.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hlo hhi hin
    have hj := range_cursor hscan.2.1 hr
    have hs := perm_size hin.1
    refine ⟨(exchange_perm _ _ _ (by omega) (by omega)).trans hin.1, by omega⟩

end Hex.GraphIso.Nauty.Sparse
