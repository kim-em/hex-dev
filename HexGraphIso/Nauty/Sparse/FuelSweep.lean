/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FuelNode
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Recovery and pruning cannot introduce exhaustion after a completed
child. Every subsequent packed-set cursor advances strictly. -/
theorem fuel_advance (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    {fuel cfuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (fuelContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n)
    (st out : State n) (exit : Generic.Exit) (hl : 1 ≤ level) (h : Ready G level numcells st)
    (htarget : Generic.Target State.frame level tc cell st) (hx : FrameOut G level level st out)
    (hsafe : exit ≠ .fuel) (hf : n ≤ level + fuel) (hcursor : n ≤ tv + (cfuel + 1)) :
    (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit).1 ≠ .fuel := by
  have hr := h.recover hn hl hx
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
        (if first && Generic.Policy.orbit (n := n) ((policy (n := n)).recover (n + 2) level out) tv == tv1
          then index + 1 else index)
        ((policy (n := n)).recover (n + 2) level out)).1 ≠ .fuel := by
    intro smaller hsub
    have ht := (htarget.subset hsub).of_out hr.2.effect
    exact (hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller _ _
      ⟨hl, hr.1, ht, fun _ hv => VSet.nextElem_mem hv⟩).2 hf (Generic.CursorFuel.next hcursor)
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).1 ≠ .fuel := by
    intro smaller hsub
    unfold Generic.resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
    split
    · apply hcontinue
      intro v hv
      exact hsub v (Nauty.longprune_subset hv)
    · exact hcontinue smaller hsub
  cases exit with
  | fuel => exact (hsafe rfl).elim
  | done => exact hresume cell (fun _ hv => hv)
  | unwind target short =>
    unfold Generic.advance
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
    split
    · simp
    · split
      · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := out.frame) hv)
      · exact hresume cell (fun _ hv => hv)

/-- Individualization consumes a level, and each sibling consumes a cursor
position. The existing node and sweep bounds cover both recursive calls. -/
theorem fuel_sweep (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    {fuel cfuel : Nat} {descend : Generic.NodeFn (State n)} {next : Generic.SweepFn (State n) n}
    (hdescend : (fuelContract G).nodeValid fuel descend)
    (hnext : (fuelContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : State n)
    (hl : 1 ≤ level) (h : Ready G level numcells st)
    (htarget : Generic.Target State.frame level tc cell st) (htv : cell.mem tv = true)
    (hf : n ≤ level + fuel) (hcursor : n ≤ tv + (cfuel + 1)) :
    (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).1 ≠ .fuel := by
  have hchild := h.child hn hl first htarget htv
  have hd := hdescend (first && tv == tv1) (level + 1) (numcells + 1) _ ⟨by omega, hchild⟩
  have hsafe := hd.2 (by omega)
  have hout := hd.1
  unfold Generic.sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
  split
  · generalize he : descend (first && tv == tv1) (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st) = r at hout hsafe ⊢
    obtain ⟨exit, out⟩ := r
    have hparent : FrameOut G level level st out := h.child_frame hn hl first htarget htv hout
    split
    · exact fuel_advance G hn hnext first level numcells tc tv1 tv index cell st _ exit hl h htarget
        ((hparent.afterChild level tv1).leave tv) hsafe hf hcursor
    · exact fuel_advance G hn hnext first level numcells tc tv1 tv index cell st _ exit hl h htarget
        (hparent.leave tv) hsafe hf hcursor
  · exact (hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hl, h, htarget, fun _ hv => VSet.nextElem_mem hv⟩).2 hf (Generic.CursorFuel.next hcursor)

end Hex.GraphIso.Nauty.Sparse
