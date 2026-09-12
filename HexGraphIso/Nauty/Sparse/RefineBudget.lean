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
set_option maxHeartbeats 800000

/-- The executed count splitter adds at most one activation per new cell,
including the replacement of the largest inactive fragment. -/
theorem splitCounts_budget (level first : Nat) (distance : Bool) (s : RefineSt n) :
    RefineSt.Budget s (splitCounts level first distance s) := by
  unfold splitCounts
  simp only
  all_goals apply Id.of_wp_run_eq rfl (fun t : RefineSt n => RefineSt.Budget s t)
  all_goals mvcgen +jp
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜RefineSt.Budget s state.1⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push] <;>
      grind [RefineSt.Budget]

end Hex.GraphIso.Nauty.Sparse
