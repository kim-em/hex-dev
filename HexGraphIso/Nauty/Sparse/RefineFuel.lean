/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SplitBudget
public import HexGraphIso.Nauty.Sparse.ActiveScan
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- The production refinement loop reaches one of its stopping conditions
within its existing `n` iterations. Only the initial active-cell count bound
is needed for this operational exhaustion result. Partition validity will
identify the second alternative with a discrete partition. -/
theorem refineWith_saturated (g : Graph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (ha : active.card ≤ numcells) :
    let t := refineWith g level lab ptn active numcells scratch
    t.queue.isEmpty = true ∨ n ≤ t.numcells := by
  unfold refineWith
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => t.queue.isEmpty = true ∨ n ≤ t.numcells)
  mvcgen
  all_goals first
    | exact (⇓⟨cursor, state⟩ => ⌜ActiveScan active state.1 state.2 ∧
        (state.2 ≠ none → state.1.size = cursor.prefix.length)⌝)
    | exact (⇓⟨_, state⟩ => ⌜state.1.queue.size ≤ state.1.numcells⌝)
    | exact (⇓⟨cursor, state⟩ => ⌜state.queue.isEmpty = true ∨ n ≤ state.numcells ∨
        state.queue.size + cursor.prefix.length ≤ state.numcells⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash]
    try grind [RefineSt.Budget, splitCounts_budget, splitSingleton_budget,
      splitNontrivial_budget, ActiveScan.initial, ActiveScan.step, ActiveScan.size_le]
  case vc2.step.h_2 =>
    rename_i next hnone he hin
    cases next <;> simp_all
  case vc23.post.success.isFalse.isFalse.pre =>
    rename_i hne ht hin
    exact Or.inr (Nat.le_trans hin.1.size_le ha)

end Hex.GraphIso.Nauty.Sparse
