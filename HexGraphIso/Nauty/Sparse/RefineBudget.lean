/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace RefineSt

/-- Each new queue entry is charged to a new partition cell. This potential
does not require an a priori bound on the number of refinement passes. -/
structure Budget (s t : RefineSt n) : Prop where
  cells : s.numcells ≤ t.numcells
  queue : t.queue.size + s.numcells ≤ s.queue.size + t.numcells

theorem Budget.refl (s : RefineSt n) : Budget s s := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem Budget.trans {s t u : RefineSt n} (h : Budget s t) (k : Budget t u) :
    Budget s u := by
  obtain ⟨hc, hq⟩ := h
  obtain ⟨kc, kq⟩ := k
  exact ⟨by omega, by omega⟩

end RefineSt

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

/-- Installing count fragments adds at most one activation per new cell,
including replacement of the largest inactive fragment. -/
theorem CountSort.finish_budget (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat) :
    RefineSt.Budget s (CountSort.finish level first last distance s w1 v2 w2 v3) := by
  unfold CountSort.finish
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => RefineSt.Budget s t)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜RefineSt.Budget s state.1⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push] <;>
      grind [RefineSt.Budget]

/-- The complete count splitter adds at most one activation per new cell. -/
theorem splitCounts_budget (level first : Nat) (distance : Bool) (s : RefineSt n) :
    RefineSt.Budget s (splitCounts level first distance s) := by
  unfold splitCounts
  simp only [Id.run, bind, pure]
  split
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · let m := CountSort.minima s.lab s.hits (n + 2) first (s.cellend[first]! + 1)
        (CountSort.firstRun s.lab s.hits first (s.cellend[first]! + 1))
    have h := CountSort.finish_budget level first (s.cellend[first]! + 1) distance
        { s.hash first with lab := m.2.2.2.2 } m.1 m.2.1 m.2.2.1 m.2.2.2.1
    exact ⟨h.cells, h.queue⟩

end Hex.GraphIso.Nauty.Sparse
