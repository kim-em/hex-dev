/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceFrameNode
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A returned child's frozen frame survives every native continuation:
both target filters, parent recovery, and a nonlocal return past the caller. -/
theorem traceFrame_advance (G : GraphIso.Sparse.Colored n k) {base cells : Nat} {root : State n}
    (hp : Ready G base cells root) (hn : 0 < n) (hb : 1 ≤ base)
    {fuel cfuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (traceFrameContract G base root).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n)
    (st out : State n) (exit : Exit) (hl : 1 ≤ level) (hi : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (he : FrameOut G level level st out)
    (hlevel : base ≤ level) (h : TraceFrame G base root out) :
    TraceFrame G base root
      (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit).2.2 := by
  have hr := hi.recover hn hl he
  have hbound : level ≤ n := Nat.le_trans hi.ok.bc (bcount_le _ _ _)
  have hframe := h.recover hp hn hb hlevel hbound
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
      TraceFrame G base root (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index
        ((policy (n := n)).recover (n + 2) level out)).2.2 := by
    intro smaller hs index
    exact (hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index _
      ⟨hl, hr.1, (ht.subset hs).of_out hr.2.effect, fun _ hv => VSet.nextElem_mem hv⟩).2 hlevel hframe
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      TraceFrame G base root
        (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).2.2 := by
    intro smaller hs
    unfold Generic.resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hcontinue _ (fun _ hv => hs _ (Nauty.longprune_subset hv)) _
    · exact hcontinue smaller hs _
  cases exit with
  | fuel => exact h
  | done => exact hresume cell (fun _ hv => hv)
  | unwind target short =>
    unfold Generic.advance
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact h
    · split
      · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := out.frame) hv)
      · exact hresume cell (fun _ hv => hv)

/-- The literal child call and the remaining sibling sweep preserve the
suspended first-path cells and all trace generators stabilizing them. -/
theorem traceFrame_sweep (G : GraphIso.Sparse.Colored n k) {base cells : Nat} {root : State n}
    (hp : Ready G base cells root) (hn : 0 < n) (hb : 1 ≤ base)
    {fuel cfuel : Nat} {descend : Generic.NodeFn (State n)} {next : Generic.SweepFn (State n) n}
    (hd : (traceFrameContract G base root).nodeValid fuel descend)
    (hnext : (traceFrameContract G base root).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : State n)
    (hl : 1 ≤ level) (hi : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hlevel : base ≤ level) (h : TraceFrame G base root st) :
    TraceFrame G base root
      (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2 := by
  have hch := hi.child hn hl first ht hv
  have hchild := h.child hp hi hn hb hlevel first ht hv
  have hout := hd (first && tv == tv1) (level + 1) (numcells + 1)
    ((policy (n := n)).child first level tc tv st) ⟨by omega, hch⟩
  have htf := hout.2 (by omega) hchild
  unfold Generic.sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · generalize he : descend (first && tv == tv1) (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st) = r at hout htf ⊢
    obtain ⟨exit, out⟩ := r
    have hframe := hi.child_frame hn hl first ht hv
      (by simpa only [Nat.add_sub_cancel] using hout.1)
    split
    · exact traceFrame_advance G hp hn hb hnext first level numcells tc tv1 tv index cell st _ exit hl hi ht
        ((hframe.afterChild level tv1).leave tv) hlevel ((htf.afterChild level tv1).leave tv)
    · exact traceFrame_advance G hp hn hb hnext first level numcells tc tv1 tv index cell st _ exit hl hi ht
        (hframe.leave tv) hlevel (htf.leave tv)
  · exact (hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hl, hi, ht, fun _ hv => VSet.nextElem_mem hv⟩).2 hlevel h

end Hex.GraphIso.Nauty.Sparse
