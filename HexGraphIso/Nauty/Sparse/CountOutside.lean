/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Sparse.Rotate
public import HexGraphIso.Nauty.Sparse.SortStack
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- The actual count splitter changes labels only inside its original cell. -/
theorem splitCounts_outside (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size)
    (q : Nat) (hq : q < first ∨ s.cellend[first]! < q) :
    (splitCounts level first distance s).lab[q]! = s.lab[q]! := by
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => t.lab[q]! = s.lab[q]!)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜state.1.lab[q]! = s.lab[q]!⌝)
    | exact (⇓⟨cursor, state⟩ => ⌜state.2.2.2.2[q]! = s.lab[q]! ∧
        state.2.2.2.2.size = s.lab.size ∧
        first < state.2.1 ∧ state.2.1 ≤ state.2.2.2.1 ∧
        state.2.2.2.1 ≤ s.cellend[first]! + 1 - cursor.suffix.length⌝)
    | exact (⇓⟨cursor, state⟩ => ⌜first < state ∧ state ≤ s.cellend[first]! + 1 ∧
        (state = first + 1 + cursor.prefix.length ∨
          s.hits[s.lab[state]!]! ≠ s.hits[s.lab[first]!]!)⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList]
    try grind [Array.getElem!_set!_ne, Sort.indirect_outside, range_cursor]
  case vc5.step.isTrue =>
    rename_i r pref j suff hr b hne hscan hk hin
    have hj := range_cursor hscan.2.1 hr
    simp only [← Array.set!_eq_setIfInBounds]
    repeat rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    omega
  case vc6.step.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hkey hk hin
    have hj := range_cursor hscan.2.1 hr
    simp only [← Array.set!_eq_setIfInBounds]
    repeat rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    omega
  case vc7.step.isFalse.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hk hin
    have hj := range_cursor hscan.2.1 hr
    simp only [← Array.set!_eq_setIfInBounds]
    repeat rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    omega
  case vc8.step.isFalse.isFalse.isFalse.isTrue =>
    rename_i r pref j suff hr b hne hscan hn1 hn2 hlo hhi hin
    have hj := range_cursor hscan.2.1 hr
    simp only [← Array.set!_eq_setIfInBounds]
    repeat rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    omega

end Hex.GraphIso.Nauty.Sparse
