/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineState
public import HexGraphIso.Nauty.Sparse.BfsRun
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 1600000

/-- Full refinement retains labels, original cell contents and boundaries,
exact cell accounting, a valid cache, and the active queue invariant. -/
theorem refineWith_state (G : Hex.SparseGraph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n scratch) :
    let t := refineWith (.ofGraph G) level lab ptn active numcells scratch
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Cuts level n ptn t.ptn numcells t.numcells n ∧ cellsPerm ptn level t.lab lab ∧
      CellQueue t.ptn level t.active t.queue ∧ Scratch.Valid n t.lab t.ptn level t.toScratch := by
  let R (t : RefineSt n) := RefineSt.Valid level t ∧
    Cuts level n ptn t.ptn numcells t.numcells n ∧ cellsPerm ptn level t.lab lab
  have finish (t : RefineSt n) (h : R t) :
      t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
        Cuts level n ptn t.ptn numcells t.numcells n ∧ cellsPerm ptn level t.lab lab ∧
        CellQueue t.ptn level t.active t.queue ∧ Scratch.Valid n t.lab t.ptn level t.toScratch :=
    ⟨h.1.lab, h.1.size, h.2.1, h.2.2, h.1.queue, h.1.scratch, fun _ => h.1.index⟩
  have compose {s t : RefineSt n} (h : R s) (ht : RefineSt.Valid level t)
      (hstep : RefineSt.Step level s t) : R t :=
    ⟨ht, h.2.1.trans hstep.cuts, cellsPerm_trans
      (h.2.1.perm hs (by simpa using h.1.lab.length_eq)
        (by simpa using ht.lab.length_eq) hend hstep.cells) h.2.2⟩
  have queue_done {queue : Array Nat} {next : Option Nat}
      (h : ActiveScan active queue next) (hl : next ≠ none → queue.size = n) :
      CellQueue ptn level active queue := by
    have hn : next = none := by
      by_cases hn : next = none
      · exact hn
      · exact h.exhausted (by rw [hl hn]; exact Nat.le_refl _)
    exact CellQueue.of_scan (hn ▸ h) ha
  have cached := indexCells_valid lab ptn scratch.cellstart scratch.cellend level hs hend
    (fun i hi => perm_bound hp hi) (fun i j hi hj he => perm_injective hp hi hj he)
    hb.starts_size hb.ends_size
  have initialized (queue : Array Nat) (hq : CellQueue ptn level active queue) :
      RefineSt.Valid level {
        lab, ptn, active, queue, numcells, longcode := numcells
        cellstart := (indexCells n lab ptn level scratch.cellstart scratch.cellend).1
        cellend := (indexCells n lab ptn level scratch.cellstart scratch.cellend).2
        indexed := true, hits := scratch.hits, marks := scratch.marks
        vmarks := scratch.vmarks, stamp := scratch.stamp } :=
    ⟨hp, hs, hend, cached,
      ⟨cached.starts_size, cached.ends_size, hb.hits_size, hb.marks_size, hb.vmarks_size,
        hb.marks_le, hb.vmarks_le⟩, hq⟩
  have single {s : RefineSt n} {pos : Nat} (h : R s) (hpos : pos < s.queue.size) :
      R (splitSingleton (.ofGraph G) level s.queue[pos]!
        (({ s with active := s.active.erase s.queue[pos]!
                   queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } : RefineSt n).hash
          s.queue[pos]!)) := by
    have hcell := h.1.queue_cell hpos
    have ht := (h.1.remove hpos).hash s.queue[pos]!
    have hr := ht.singleton G _ hcell.1
    exact compose ⟨ht, h.2⟩ hr.1 hr.2
  have multiple {s : RefineSt n} {pos : Nat} (h : R s) (hpos : pos < s.queue.size) :
      R (splitNontrivial (.ofGraph G) level s.queue[pos]!
        (({ s with active := s.active.erase s.queue[pos]!
                   queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } : RefineSt n).hash
          s.queue[pos]!)) := by
    have hcell := h.1.queue_cell hpos
    have ht := (h.1.remove hpos).hash s.queue[pos]!
    have hr := ht.nontrivial G _ _ hcell.2.1 (by omega)
    exact compose ⟨ht, h.2⟩ hr.1 hr.2
  have endpoint {s : RefineSt n} (h : RefineSt.Valid level s) {first : Nat}
      (hf : first < n) (ha : first = 0 ∨ s.ptn[first - 1]! ≤ level) :
      s.ptn[s.cellend[first]!]! ≤ level := by
    have hc := h.cell hf ha
    have he : first + (s.cellend[first]! + 1 - first) - 1 = s.cellend[first]! := by omega
    simpa only [he] using hc.1.2.2.2
  have distance {s : RefineSt n} {first : Nat} (h : R s) (hf : first < n)
      (ha : first = 0 ∨ s.ptn[first - 1]! ≤ level) (hv : ∀ v, v < n → s.hits[v]! ≤ n) :
      R (splitCounts level first true s) ∧ s.cellend[first]! + 1 ≤ n ∧
        (splitCounts level first true s).ptn[s.cellend[first]!]! ≤ level ∧
        ∀ v, v < n → (splitCounts level first true s).hits[v]! ≤ n := by
    have hc := h.1.cell hf ha
    have ht := h.1.counts first true hc.1 hc.2.2 (by
      intro q hq hu
      have := hv s.lab[q]! (perm_bound h.1.lab (i := q) (by omega))
      omega)
    refine ⟨compose h ht.1 ht.2, by omega, ?_, ?_⟩
    · rw [ht.2.cuts.closed _ (endpoint h.1 hf ha)]
      exact endpoint h.1 hf ha
    · rw [(splitCounts_frame level first true s).hits]
      exact hv
  unfold refineWith
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
      Cuts level n ptn t.ptn numcells t.numcells n ∧ cellsPerm ptn level t.lab lab ∧
      CellQueue t.ptn level t.active t.queue ∧ Scratch.Valid n t.lab t.ptn level t.toScratch)
  mvcgen
  all_goals try
    guard_target = Invariant _ _ _
    first
    | exact (⇓⟨cursor, state⟩ => ⌜ActiveScan active state.1 state.2 ∧
        (state.2 ≠ none → state.1.size = cursor.prefix.length)⌝)
    | exact (⇓⟨_, state⟩ => ⌜R state.1 ∧ state.2 ≤ n ∧
        (state.2 = 0 ∨ state.1.ptn[state.2 - 1]! ≤ level) ∧
        ∀ v, v < n → state.1.hits[v]! ≤ n⌝)
    | exact (⇓⟨_, state⟩ => ⌜R state⌝)
    | exact (let s : RefineSt n := by assumption
        ⇓⟨_, state⟩ => ⌜state < s.queue.size⌝)
  all_goals simp +zetaDelta [RefineSt.hash, RefineSt.toScratch, Std.Legacy.Range.toList] at *
  all_goals try assumption
  all_goals try grind only [ActiveScan.initial, ActiveScan.step, finish]
  all_goals try grind only [single, multiple]
  case vc2.step.h_2 =>
    rename_i next he hin hnone
    cases next <;> simp_all
  case vc4.post.success.isTrue =>
    rename_i hin
    exact ⟨hp, hs, Cuts.refl _ _ _ _ _, cellsPerm_refl _ _ _,
      queue_done hin.1 hin.2, hb.invalidate lab ptn level⟩
  case vc23.post.success.isFalse.isFalse.pre =>
    rename_i hin
    exact ⟨initialized _ (queue_done hin.1 hin.2), Cuts.refl _ _ _ _ _, cellsPerm_refl _ _ _⟩
  all_goals try
    rename_i hin
    have hpos := Array.size_pos_iff.mpr hin.1
    omega
  case vc10.step.isTrue | vc18.step.isTrue =>
    rename_i hr b hy hi hne hd hscan hgo
    have hj := range_cursor (by omega) hr
    omega
  case vc6.step.isFalse.isTrue =>
    rename_i hin hne hd hscan hf
    exact distance hin.1.1 hin.1.2.1 hin.1.2.2 hf hin.2.2.1 hin.2.2.2
  case vc8.post.success.isFalse.isTrue.pre =>
    rename_i hne hd hscan
    have hq := queue_done hscan.1 hscan.2
    have hsize := hd.1.1.2
    have hv := (initialized _ hq).queue_cell (pos := 0) (by dsimp; omega)
    have hroot := perm_bound hp hv.1
    have hdist := distvals_correct G ⟨_, hroot⟩
    have hqr := hq.remove (pos := 0) (by omega)
    have clear_queue {q : Array Nat} (he : q.size = 1) :
        (q.setIfInBounds 0 q[q.size - 1]!).pop = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      simp only [Array.size_pop, Array.size_setIfInBounds, he]
    rw [clear_queue hsize] at hqr
    refine ⟨⟨⟨hp, hs, hend, cached, ?_, hqr⟩, Cuts.refl _ _ _ _ _, cellsPerm_refl _ _ _⟩, ?_⟩
    · exact ⟨cached.starts_size, cached.ends_size, distvals_size _ _, hb.marks_size, hb.vmarks_size,
        hb.marks_le, hb.vmarks_le⟩
    · intro v hv
      exact hdist.bound ⟨v, hv⟩

end Hex.GraphIso.Nauty.Sparse
