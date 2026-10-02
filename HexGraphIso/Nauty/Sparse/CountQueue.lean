/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine.CountSpec
public import HexGraphIso.Nauty.Sparse.MinimaBound
public import HexGraphIso.Nauty.Sparse.Cuts
public import HexGraphIso.Nauty.Sparse.CellQueue
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- Fragment installation preserves the ordered active queue, including
the replacement of the largest fragment. -/
theorem CountSort.finish_queue (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat) (hs : s.ptn.size = n) (hb : last ≤ n)
    (hc : IsCell s.ptn level first (last - first))
    (hm : Minima.Bounded s.lab s.hits first last v2 v3 last w1 w2 (n + 2))
    (hq : CellQueue s.ptn level s.active s.queue) :
    let t := CountSort.finish level first last distance s w1 v2 w2 v3
    CellQueue t.ptn level t.active t.queue := by
  have bounds := hm.positions
  have hopen (q : Nat) (hq : first ≤ q) (he : q < last - 1) :
      level < s.ptn[q]! := hc.2.2.1 q hq (by omega)
  cases distance <;> unfold CountSort.finish
  all_goals simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
  all_goals apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    CellQueue t.ptn level t.active t.queue)
  all_goals mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜first ≤ state.2.2.2 ∧ state.2.2.2 ≤ (last - 1) ∧
          Cuts level n s.ptn state.1.ptn s.numcells state.1.numcells state.2.2.2 ∧
          CellQueue state.1.ptn level state.1.active state.1.queue ∧
          0 < state.1.queue.size ∧ ∀ p, state.2.1 = some p → p < state.1.queue.size⌝)
      | exact (let r : RefineSt n × Option Nat × Nat × Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜first ≤ state.2 ∧
          state.2 + cursor.suffix.length ≤ (last - 1) ∧
          Cuts level n s.ptn state.1.ptn s.numcells state.1.numcells state.2 ∧
          CellQueue state.1.ptn level state.1.active state.1.queue ∧
          0 < state.1.queue.size ∧ ∀ p, r.2.1 = some p → p < state.1.queue.size⌝)
      | exact (⇓_ => ⌜True⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList]
    try omega
    try exact hq
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
    have bounds := hm.positions
    have gap := hm.second_pos (by omega)
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

/-- Count splitting preserves the exact active queue. -/
theorem splitCounts_queue (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hq : CellQueue s.ptn level s.active s.queue) :
    let t := splitCounts level first distance s
    CellQueue t.ptn level t.active t.queue := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  apply splitCounts_induct level first distance s
    (fun t => CellQueue t.ptn level t.active t.queue) hf (by omega) hk
  · intro _; exact hq
  · intro lab w1 v2 w2 v3 hm
    exact CountSort.finish_queue level first (s.cellend[first]! + 1) distance
      { s.hash first with lab } w1 v2 w2 v3 hs (by omega) hc hm.toBounded hq

end Hex.GraphIso.Nauty.Sparse
