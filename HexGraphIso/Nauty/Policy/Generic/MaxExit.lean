/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Partition
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ : Type} [Policy σ n]

/-- A node consumes every completed local action or sweep. Its own return
always unwinds or reports exhausted fuel. -/
theorem nodeStep_ne_done (ctx : Ctx n) (tcLevel : Nat) (next : SweepFn σ n)
    (first : Bool) (level numcells : Nat) (st : σ) :
    (nodeStep ctx tcLevel next first level numcells st).1 ≠ .done := by
  unfold nodeStep
  dsimp only
  repeat' split
  all_goals simp only [Id.run_pure]
  all_goals intro he
  all_goals first | cases he | contradiction

/-- No recursive node returns the sweep-completion exit. -/
theorem node_ne_done (first : Bool) (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat)
    (st : σ) : (node first ctx inf tcLevel fuel level numcells st).1 ≠ .done := by
  cases fuel with
  | zero => rw [node]; intro he; cases he
  | succ fuel => rw [node]; exact nodeStep_ne_done ctx tcLevel _ first level numcells st

end Hex.GraphIso.Nauty.Generic

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Adequate child fuel and the node's exit shape leave only an unwind. -/
theorem SweepInput.child_exit {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    ∃ target short out, Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st) = (.unwind target short, out) := by
  have hi := h.push hgsz hsymm hloop
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hf := node_noFuel (ctx := ctx) (tcLevel := tcLevel) (first && tv == tv1) hn0 hi.frame.positive hi.frame.partition hi.fuel
  dsimp only [Parent.child] at hf
  rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at hf
  have hd := Generic.node_ne_done (first && tv == tv1) ctx (n + 2) tcLevel fuel
    (level + 1) (numcells + 1) (Nauty.child first level tc tv st)
  rw [← node_eq_generic] at hd
  generalize he : Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
    (level + 1) (numcells + 1) (Nauty.child first level tc tv st) = result at hf hd ⊢
  obtain ⟨exit, out⟩ := result
  cases exit with
  | fuel => exact (hf rfl).elim
  | done => exact (hd rfl).elim
  | unwind target short => exact ⟨target, short, out, rfl⟩

end Hex.GraphIso.Nauty.Max
