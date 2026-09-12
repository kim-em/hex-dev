/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.StoreNode
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Once a child returns a valid store, every recovery, filter and surviving
sibling retains it. The child's frame justifies the recovered parent. -/
theorem store_advance (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    {fuel cfuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (storeContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n)
    (st out : State n) (exit : Generic.Exit) (hl : 1 ≤ level) (h : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hx : FrameOut G level level st out)
    (hs : Store G.graph out) :
    Store G.graph (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit).2.2 := by
  have hr := h.recover hn hl hx
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
      Store G.graph (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index
        ((policy (n := n)).recover (n + 2) level out)).2.2 := by
    intro smaller hsub index
    exact (hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index _
      ⟨hl, hr.1, (ht.subset hsub).of_out hr.2.effect, fun _ hv => VSet.nextElem_mem hv⟩).2
      (hs.recover (n + 2) level)
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      Store G.graph (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).2.2 := by
    intro smaller hsub
    unfold Generic.resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · apply hcontinue
      intro v hv
      exact hsub v (Nauty.longprune_subset hv)
    · exact hcontinue smaller hsub _
  cases exit with
  | fuel => exact hs
  | done => exact hresume cell (fun _ hv => hv)
  | unwind target short =>
    unfold Generic.advance
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hs
    · split
      · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := out.frame) hv)
      · exact hresume cell (fun _ hv => hv)

/-- Each actual child and later sibling preserves the installed canonical
store, including orbit-skipped vertices and returns past this sweep. -/
theorem store_sweep (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    {fuel cfuel : Nat} {descend : Generic.NodeFn (State n)} {next : Generic.SweepFn (State n) n}
    (hd : (storeContract G).nodeValid fuel descend) (hnext : (storeContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : State n)
    (hl : 1 ≤ level) (h : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) (hs : Store G.graph st) :
    Store G.graph (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2 := by
  have hchild := h.child hn hl first ht hv
  have hdesc := hd (first && tv == tv1) (level + 1) (numcells + 1) _ ⟨by omega, hchild⟩
  have hstore := hdesc.2 (hs.child first level tc tv)
  unfold Generic.sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · generalize he : descend (first && tv == tv1) (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st) = r at hdesc hstore ⊢
    obtain ⟨exit, out⟩ := r
    have hp := h.child_frame hn hl first ht hv hdesc.1
    split
    · exact store_advance G hn hnext first level numcells tc tv1 tv index cell st _ exit hl h ht
        ((hp.afterChild level tv1).leave tv) ((hstore.afterChild level tv1).leave tv)
    · exact store_advance G hn hnext first level numcells tc tv1 tv index cell st _ exit hl h ht
        (hp.leave tv) (hstore.leave tv)
  · exact (hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hl, h, ht, fun _ hv => VSet.nextElem_mem hv⟩).2 hs

end Hex.GraphIso.Nauty.Sparse
