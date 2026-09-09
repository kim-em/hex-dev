/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Engine insertion obeys the bounded workspace invariant. -/
theorem workspace_push {st : Search n} (h : WorkspaceOk st)
    (pair : VSet n × VSet n) : WorkspaceOk (pushAuto st pair) := by

  exact h.push

/-- Explicit generator admission keeps the capacity and bounded pair array. -/
theorem workspace_admit {st : Search n} (h : WorkspaceOk st) :
    WorkspaceOk (admit st) := by
  unfold admit
  simp only [Id.run_pure]
  apply workspace_push
  exact h

/-- Inserting the frozen implicit pair preserves workspace bounds. -/
theorem workspace_prune {st : Search n} (h : WorkspaceOk st) (level : Nat) :
    WorkspaceOk (pruneReturn level st).2 := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · exact workspace_push h _
  · exact h

/-- Every leaf action preserves the bounded workspace, independently of
the automorphism and subtree proofs that justify its admitted pair. -/
theorem workspace_leaf {st : Search n} (h : WorkspaceOk st) (leaf : Leaf) (level : Nat) :
    WorkspaceOk (leafExit leaf level st).2 := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | exact h
    | exact workspace_admit h
    | exact workspace_prune h level
    | apply workspace_prune; exact h

/-- Leaf emission retains the capacity used by its pair insertion. -/
theorem leafExit_capacity (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.wsCap = st.wsCap := by
  have hp : ∀ (s : Search n) pair, (pushAuto s pair).wsCap = s.wsCap := by
    intros
    unfold pushAuto
    split <;> rfl
  have ha : ∀ s : Search n, (admit s).wsCap = s.wsCap := by
    intro s
    unfold admit
    simp only [Id.run_pure, hp]
  have hr : ∀ s : Search n, (pruneReturn level s).2.wsCap = s.wsCap := by
    intro s
    unfold pruneReturn
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
      apply_ite Search.wsCap, hp, ite_self]
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | rfl
    | exact ha _
    | exact hr _

/-- Classification changes neither the workspace capacity nor its pair array. -/
theorem classify_capacity (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.wsCap = st.wsCap := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.wsCap, ite_self]

end Hex.GraphIso.Nauty
