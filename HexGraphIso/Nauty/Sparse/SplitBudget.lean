/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineBudget
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- A singleton pass charges each activation to its binary cell split. -/
theorem splitSingleton_budget (g : Graph n) (level split : Nat) (s : RefineSt n) :
    RefineSt.Budget s (splitSingleton g level split s) := by
  unfold splitSingleton
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => RefineSt.Budget s t)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜RefineSt.Budget s state⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push] <;>
      grind [RefineSt.Budget]

/-- Accumulating neighbour counts adds no activations. The following count
splits compose the same queue potential, regardless of the touched-cell order. -/
theorem splitNontrivial_budget (g : Graph n) (level split : Nat) (s : RefineSt n) :
    RefineSt.Budget s (splitNontrivial g level split s) := by
  unfold splitNontrivial
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => RefineSt.Budget s t)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜RefineSt.Budget s state⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash] <;>
      grind [RefineSt.Budget, splitCounts_budget]

end Hex.GraphIso.Nauty.Sparse
