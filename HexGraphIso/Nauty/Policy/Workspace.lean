/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- Engine insertion obeys the bounded workspace invariant. -/
theorem workspace_push {st : Search n} (h : WorkspaceOk st.view)
    (pair : VSet n × VSet n) : WorkspaceOk (pushAuto st pair).view := by
  rw [view_pushAuto]
  exact h.push

/-- Explicit generator admission keeps the capacity and bounded pair array. -/
theorem workspace_admit {st : Search n} (h : WorkspaceOk st.view) :
    WorkspaceOk (admit st).view := by
  unfold admit
  simp only [Id.run_pure]
  apply workspace_push
  exact h

/-- Inserting the frozen implicit pair preserves workspace bounds. -/
theorem workspace_prune {st : Search n} (h : WorkspaceOk st.view) (level : Nat) :
    WorkspaceOk (pruneReturn level st).2.view := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · exact workspace_push h _
  · exact h

/-- Every leaf action preserves the bounded workspace, independently of
the automorphism and subtree proofs that justify its admitted pair. -/
theorem workspace_leaf {st : Search n} (h : WorkspaceOk st.view) (leaf : Leaf) (level : Nat) :
    WorkspaceOk (leafExit leaf level st).2.view := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | exact h
    | exact workspace_admit h
    | exact workspace_prune h level
    | apply workspace_prune; exact h

/-- Classification changes neither the workspace capacity nor its pair array. -/
theorem classify_capacity (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.wsCap = st.wsCap := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.wsCap, ite_self]

end Hex.GraphIso.Nauty.Engine
