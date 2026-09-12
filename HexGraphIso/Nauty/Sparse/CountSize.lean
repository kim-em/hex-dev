/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine.CountSpec
public import HexGraphIso.Nauty.Sparse.MinimaBound
public import HexGraphIso.Nauty.Sparse.Cuts
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- Fragment installation charges exactly one new cell to every boundary
it closes, and retains all previously closed partition values. -/
theorem CountSort.finish_cuts (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat)
    (hs : s.ptn.size = n) (hb : last ≤ n)
    (hm : Minima.Bounded s.lab s.hits first last v2 v3 last w1 w2 (n + 2))
    (hopen : ∀ q, first ≤ q → q < last - 1 → level < s.ptn[q]!) :
    Cuts level n s.ptn (CountSort.finish level first last distance s w1 v2 w2 v3).ptn
      s.numcells (CountSort.finish level first last distance s w1 v2 w2 v3).numcells n := by
  have bounds := hm.positions
  have gap : v2 < last → v2 < v3 := hm.second_pos
  cases distance <;> unfold CountSort.finish
  all_goals simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
  all_goals apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    Cuts level n s.ptn t.ptn s.numcells t.numcells n)
  all_goals mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜first ≤ state.2.2.2 ∧ state.2.2.2 ≤ last - 1 ∧
          Cuts level n s.ptn state.1.ptn s.numcells state.1.numcells state.2.2.2⌝)
      | exact (⇓⟨cursor, state⟩ => ⌜first ≤ state.2 ∧ state.2 + cursor.suffix.length ≤ last - 1 ∧
          Cuts level n s.ptn state.1.ptn s.numcells state.1.numcells state.2⌝)
      | exact (⇓_ => ⌜True⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push]
    try omega
    try exact Cuts.refl _ _ _ _ _
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
  all_goals first
    | exact Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
        (hopen _ (by omega) (by omega))
    | exact ⟨by omega, by omega,
        Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
          (hopen _ (by omega) (by omega))⟩
    | exact ⟨by omega, Cuts.initial s.ptn s.numcells (by omega) (by omega) (by omega)
        (hopen _ (by omega) (by omega))⟩

/-- Count splitting closes one boundary for every new partition cell. -/
theorem splitCounts_cuts (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    Cuts level n s.ptn (splitCounts level first distance s).ptn
      s.numcells (splitCounts level first distance s).numcells n := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  apply splitCounts_induct level first distance s
    (fun t => Cuts level n s.ptn t.ptn s.numcells t.numcells n) hf (by omega) hk
  · intro _; exact Cuts.refl _ _ _ _ _
  · intro lab w1 v2 w2 v3 hm
    exact CountSort.finish_cuts level first (s.cellend[first]! + 1) distance
      { s.hash first with lab } w1 v2 w2 v3 hs (by omega) hm.toBounded
      (fun q hq he => hc.2.2.1 q hq (by omega))

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
