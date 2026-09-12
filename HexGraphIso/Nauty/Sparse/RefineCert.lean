/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.DistanceCert
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

/-- The complete executed refinement preserves the equitability certificate,
including the distance branch, both splitter passes, and queue selection. -/
theorem refineWith_cert (G : Hex.SparseGraph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n scratch)
    (hinv : CertInv (Graph.context G) level
      { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }) :
    CertInv (Graph.context G) level
      (refineWith (.ofGraph G) level lab ptn active numcells scratch).toPartition := by
  let R (t : RefineSt n) := RefineSt.Valid level t ∧ CertInv (Graph.context G) level t.toPartition
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
  let start (queue : Array Nat) : RefineSt n := {
    lab, ptn, active, queue, numcells, longcode := numcells
    cellstart := (indexCells n lab ptn level scratch.cellstart scratch.cellend).1
    cellend := (indexCells n lab ptn level scratch.cellstart scratch.cellend).2
    indexed := true, hits := scratch.hits, marks := scratch.marks
    vmarks := scratch.vmarks, stamp := scratch.stamp }
  let distanceStart (queue : Array Nat) : RefineSt n := { start queue with
    queue := #[], active := active.erase queue[0]!
    hits := distvals (.ofGraph G) lab[queue[0]!]! }
  have initialized (queue : Array Nat) (hq : CellQueue ptn level active queue) :
      RefineSt.Valid level (start queue) :=
    ⟨hp, hs, hend, cached,
      ⟨cached.starts_size, cached.ends_size, hb.hits_size, hb.marks_size, hb.vmarks_size,
        hb.marks_le, hb.vmarks_le⟩, hq⟩
  have source (queue : Array Nat) : CertInv (Graph.context G) level (start queue).toPartition := hinv
  have single {s : RefineSt n} {pos : Nat} (h : R s) (hpos : pos < s.queue.size)
      (hsp : s.ptn[s.queue[pos]!]! ≤ level) :
      R (splitSingleton (.ofGraph G) level s.queue[pos]!
        (({ s with active := s.active.erase s.queue[pos]!
                   queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } : RefineSt n).hash
          s.queue[pos]!)) := by
    have hcell := h.1.queue_cell hpos
    exact ⟨(((h.1.remove hpos).hash s.queue[pos]!).singleton G _ hcell.1).1,
      h.1.singleton_cert G pos hpos hsp h.2⟩
  have multiple {s : RefineSt n} {pos : Nat} (h : R s) (hpos : pos < s.queue.size) :
      R (splitNontrivial (.ofGraph G) level s.queue[pos]!
        (({ s with active := s.active.erase s.queue[pos]!
                   queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } : RefineSt n).hash
          s.queue[pos]!)) := by
    have hcell := h.1.queue_cell hpos
    exact ⟨(((h.1.remove hpos).hash s.queue[pos]!).nontrivial G _ _ hcell.2.1 (by omega)).1,
      h.1.nontrivial_cert G pos hpos h.2⟩
  have finish_distance {queue : Array Nat} {next : Option Nat} {t : RefineSt n} {first : Nat}
      (hscan : ActiveScan active queue next) (hdone : next ≠ none → queue.size = n)
      (hq : queue.size = 1) (hsp : ptn[queue[0]!]! ≤ level)
      (hd : DistanceState level (distanceStart queue) t first) (hf : n ≤ first) : R t := by
    have he := Nat.le_antisymm hd.bound hf
    have hd' : DistanceState level (distanceStart queue) t n := by simpa only [he] using hd
    exact ⟨hd.valid, (initialized queue (queue_done hscan hdone)).distance_finish G hq hsp (source queue) hd'⟩
  have finish {s : RefineSt n} (hc : CertInv (Graph.context G) level s.toPartition) :
      CertInv (Graph.context G) level
        ({ s with longcode := cleanup (mash s.longcode s.numcells) } : RefineSt n).toPartition := hc
  unfold refineWith
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => CertInv (Graph.context G) level t.toPartition)
  mvcgen
  all_goals try
    guard_target = Invariant _ _ _
    first
    | exact (⇓⟨cursor, state⟩ => ⌜ActiveScan active state.1 state.2 ∧
        (state.2 ≠ none → state.1.size = cursor.prefix.length)⌝)
    | exact (let r : Array Nat × Option Nat := by assumption
        ⇓⟨cursor, state⟩ => ⌜DistanceState level (distanceStart r.1) state.1 state.2 ∧
          RefineSt.Valid level (distanceStart r.1) ∧
          (∀ v, v < n → (distanceStart r.1).hits[v]! ≤ n) ∧ cursor.prefix.length ≤ state.2⌝)
    | exact (⇓⟨_, state⟩ => ⌜R state⌝)
    | exact (let s : RefineSt n := by assumption
        ⇓⟨_, state⟩ => ⌜state < s.queue.size⌝)
  all_goals simp +zetaDelta [RefineSt.hash, Std.Legacy.Range.toList] at *
  all_goals try assumption
  all_goals try grind only [ActiveScan.initial, ActiveScan.step]
  all_goals try grind only [single, multiple, finish_distance]
  all_goals try grind only [finish]
  case vc2.step.h_2 =>
    rename_i next he hin hnone
    cases next <;> simp_all
  case vc6.step.isFalse.isTrue =>
    rename_i hin hne hd hscan hf
    have hc := hin.1.cell hf
    exact ⟨hin.1.counts hin.2.1 hin.2.2.1 hf, hin.2.1, hin.2.2.1, by omega⟩
  case vc7.step.isFalse.isFalse =>
    rename_i hin hne hd hscan hf hc
    have hcell := hin.1.cell hf
    have he := Nat.le_antisymm hc hcell.2.1
    simpa only [he] using And.intro (hin.1.singleton hf he) hin.2
  case vc8.post.success.isFalse.isTrue.pre =>
    rename_i hne hd hscan
    have hq := queue_done hscan.1 hscan.2
    have hsize := hd.1.1.2
    have hi := initialized _ hq
    have hr := hi.distance_start G hsize
    have hc := hi.queue_cell (pos := 0) (by dsimp; omega)
    have hroot := perm_bound hp hc.1
    have hdist := distvals_correct G ⟨_, hroot⟩
    exact ⟨DistanceState.initial hr, hr, fun v hv => hdist.bound ⟨v, hv⟩⟩
  case vc10.step.isTrue =>
    rename_i hr b hy hi hne hd hscan hdist hgo
    have hj := range_cursor (by omega) hr
    omega
  case vc18.step.isTrue =>
    rename_i hr b hy hi hne hd hscan hgo
    have hj := range_cursor (by omega) hr
    omega
  all_goals try
    rename_i hin
    have hpos := Array.size_pos_iff.mpr hin.1
    omega

end Hex.GraphIso.Nauty.Sparse
