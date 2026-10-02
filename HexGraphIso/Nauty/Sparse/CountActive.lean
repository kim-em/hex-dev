/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ActiveSpan
public import HexGraphIso.Nauty.Sparse.Refine.CountSpec
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- Fragment installation activates all fragments of an active cell and
at most omits one otherwise. Replacement retains exterior membership. -/
theorem CountSort.finish_active (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat) (hb : last ≤ n)
    (hc : IsCell s.ptn level first (last - first))
    (hm : Minima.Bounded s.lab s.hits first last v2 v3 last w1 w2 (n + 2)) :
    let t := CountSort.finish level first last distance s w1 v2 w2 v3
    CellActive level first last s.active t.active t.ptn ∧
      ∀ u, u < first ∨ last ≤ u → t.active.mem u = s.active.mem u := by
  have bounds := hm.positions
  have ha := ActiveSpan.initial (active := s.active) hc
  have hq := QueueSpan.initial (first := first) (last := last) s.queue
  cases distance <;> unfold CountSort.finish
  all_goals simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
  all_goals apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    CellActive level first last s.active t.active t.ptn ∧
      ∀ u, u < first ∨ last ≤ u → t.active.mem u = s.active.mem u)
  all_goals mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜first ≤ state.2.2.2 ∧ state.2.2.2 ≤ (last - 1) ∧
          ActiveSpan level first (last) s.active state.1.active state.1.ptn ∧
          QueueSpan first (last) s.queue.size state.1.queue ∧
          s.queue.size < state.1.queue.size ∧
          ∀ p, state.2.1 = some p → s.queue.size ≤ p ∧ p < state.1.queue.size⌝)
      | exact (let r : RefineSt n × Option Nat × Nat × Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜first ≤ state.2 ∧
          state.2 + cursor.suffix.length ≤ (last - 1) ∧
          ActiveSpan level first (last) s.active state.1.active state.1.ptn ∧
          QueueSpan first (last) s.queue.size state.1.queue ∧
          s.queue.size < state.1.queue.size ∧
          ∀ p, r.2.1 = some p → s.queue.size ≤ p ∧ p < state.1.queue.size⌝)
      | exact (⇓_ => ⌜True⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, Std.Legacy.Range.toList]
    try omega
    try exact ha.finish
    try exact ⟨ha.finish, ha.outside⟩
  all_goals try
    rename_i hin
    exact ⟨by omega, by omega, hin.2.2⟩
  all_goals try
    rename_i hin
    exact ⟨hin.2.2.1.finish, hin.2.2.1.outside⟩
  all_goals try
    rename_i hin
    exact hin.2.2.1.replace_get hin.2.2.2.1 hin.2.2.2.2.2.1 hin.2.2.2.2.2.2
      (by omega) (by simp_all)
  all_goals try
    rename_i hin
    obtain ⟨hfirst, hend, hactive, hqueue, hsize, hbig⟩ := hin
    refine ⟨by omega, by omega, hactive.cut_next (by omega) (by omega) (by omega),
      hqueue.push (by omega) (by omega), by omega, ?_⟩
    intro p hp
    have := hbig p hp
    omega
    done
  all_goals try
    have bounds := hm.positions
    have gap := hm.second_pos (by omega)
  all_goals try omega
  all_goals try
    refine ⟨?_, ?_⟩
    · first
      | exact CellActive.binary_left hc (by omega) (by omega) (by omega) (by simp_all)
      | simpa only [Nat.add_sub_cancel] using
          CellActive.binary_left (cut := first + 1) hc (by omega) (by omega) (by omega) (by simp_all)
      | exact (ha.cut_push (by omega) (by omega) (by omega)).finish
      | exact (ha.cut_next (by omega) (by omega) (by omega)).finish
    · exact ActiveSpan.insert_outside (by omega) (by omega)
    done
  all_goals try
    exact ⟨by omega, by omega,
      ha.cut_next (by omega) (by omega) (by omega), hq.push (by omega) (by omega)⟩
  all_goals try
    exact ⟨by omega,
      ha.cut_next (by omega) (by omega) (by omega), hq.push (by omega) (by omega)⟩
  all_goals try
    exact ⟨by omega, by omega,
      ha.cut_push (by omega) (by omega) (by omega), hq.push (by omega) (by omega)⟩
  all_goals try
    exact ⟨by omega,
      ha.cut_push (by omega) (by omega) (by omega), hq.push (by omega) (by omega)⟩

/-- Count splitting activates all fragments of an active cell and leaves
at most one inactive fragment otherwise, preserving exterior membership. -/
theorem splitCounts_active (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hb : s.cellend[first]! < n)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    let t := splitCounts level first distance s
    CellActive level first (s.cellend[first]! + 1) s.active t.active t.ptn ∧
      ∀ u, u < first ∨ s.cellend[first]! + 1 ≤ u → t.active.mem u = s.active.mem u := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  apply splitCounts_induct level first distance s
    (fun t => CellActive level first (s.cellend[first]! + 1) s.active t.active t.ptn ∧
      ∀ u, u < first ∨ s.cellend[first]! + 1 ≤ u → t.active.mem u = s.active.mem u)
    hf (by omega) hk
  · intro _
    have ha := ActiveSpan.initial (active := s.active) hc
    exact ⟨ha.finish, ha.outside⟩
  · intro lab w1 v2 w2 v3 hm
    exact CountSort.finish_active level first (s.cellend[first]! + 1) distance
      { s.hash first with lab } w1 v2 w2 v3 (by omega) hc hm.toBounded

end Hex.GraphIso.Nauty.Sparse
