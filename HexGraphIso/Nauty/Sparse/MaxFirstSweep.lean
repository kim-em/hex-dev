/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstResume
public import HexGraphIso.Nauty.Sparse.MaxUpperNode
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The actual first-child bound extends through the complete native
sibling sweep, including local filters and nonlocal returns. -/
theorem FirstEntry.sweep_upper {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel tv last : Nat} {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstEntry G f) (hs : Scope G tcLevel f [] f.entry parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true f.level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.2).orbits[tv]! = tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel
        (p.child G.graph tcLevel).level (p.child G.graph tcLevel).numcells
        (p.child G.graph tcLevel).entry last leaf)
    (hf : n ≤ f.level + fuel)
    (hchild : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      Bounded (ch.key G.graph tcLevel) none
        (State.best G.graph (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel
          ch.level ch.numcells ch.entry).2)) :
    let p := f.firstParent G.graph tcLevel [] tv
    Bounded (f.key G.graph tcLevel) none
      (State.best G.graph (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        f.level (f.target G.graph tcLevel).numcells p.tc tv (some tv) p.cell 0 p.state).2.2) := by
  let p := f.firstParent G.graph tcLevel [] tv
  let ch := p.child G.graph tcLevel
  let raw := Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry
  let left := (policy (n := n)).leaveChild tv (afterChildFirst f.level tv raw.2)
  let back := p.firstBack G.graph tcLevel fuel
  let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
    Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel n level numcells tc tv1 cursor cell index st
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hm := VSet.nextElem_mem htv
  have hp : p.Valid G tcLevel := h.frame.first_parent h.shape hi hm []
  obtain ⟨bs, fs, hr, resumed⟩ := h.receive hs hi htv horbit path hf
  change Bounded (ch.key G.graph tcLevel) none (State.best G.graph raw.2) at hchild
  rw [hr.read] at hchild
  have hbound : Bounded (f.key G.graph tcLevel) none (State.key G.graph bs raw.2) :=
    hchild.absorb hp.child_bound
  have hleft : ReturnCodes G.graph ch.codes bs fs left := (hr.afterChild f.level tv).leave tv
  have hleftBound : Bounded (f.key G.graph tcLevel) none (State.best G.graph left) := by
    rw [hleft.read]
    exact hbound
  have hbackBound : Bounded (f.key G.graph tcLevel) none (State.key G.graph bs back) := by
    change Bounded _ _ (State.key G.graph bs ((policy (n := n)).recover (n + 2) f.level left))
    rw [recover_key]
    exact hbound
  have hpast : ∀ smaller : VSet n, Generic.Past true tv (smaller.nextElem (some tv)) := by
    intro smaller _ v hv
    have hb := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at hb
    omega
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → p.cell.mem v = true) → ∀ index,
      Bounded (f.key G.graph tcLevel) none
        (State.best G.graph (next true f.level (f.target G.graph tcLevel).numcells p.tc tv
          (smaller.nextElem (some tv)) smaller index back).2.2) := by
    intro smaller hsub index
    apply hbackBound.trans
    exact upper_sweep G hn tcLevel fuel (node_upper G tcLevel fuel) n true f bs fs p.tc tv index
      (smaller.nextElem (some tv)) smaller back parents h.frame resumed.codes
      (fun v hv => resumed.next smaller hsub v hv) resumed.scope
      (fun _ hv => VSet.nextElem_mem hv) (hpast smaller) resumed.recorded resumed.route hf
      (Generic.CursorFuel.next (by omega : n ≤ tv + (n + 1))) resumed.machine
      (Or.inl (recover_nonpos hleft.nonpos (n + 2) f.level))
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → p.cell.mem v = true) →
      Bounded (f.key G.graph tcLevel) none
        (State.best G.graph (Generic.resume (n + 2) next true f.level (f.target G.graph tcLevel).numcells
          p.tc tv tv smaller 0 left).2.2) := by
    intro smaller hsub
    unfold Generic.resume
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, Id.run_pure]
    exact hcontinue smaller hsub _
  have hadv : Bounded (f.key G.graph tcLevel) none
      (State.best G.graph (Generic.advance (n + 2) next true f.level (f.target G.graph tcLevel).numcells
        p.tc tv tv p.cell 0 left raw.1).2.2) := by
    cases raw.1 with
    | fuel => exact hleftBound
    | done => exact hresume p.cell (fun _ hv => hv)
    | unwind target short =>
      unfold Generic.advance
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split
      · exact hleftBound
      · split
        · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := left.frame) hv)
        · exact hresume p.cell (fun _ hv => hv)
  change (policy (n := n)).orbit p.state tv = tv at horbit
  change Bounded (f.key G.graph tcLevel) none
    (State.best G.graph (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
      f.level (f.target G.graph tcLevel).numcells p.tc tv (some tv) p.cell 0 p.state).2.2)
  rw [Generic.sweep]
  unfold Generic.sweepStep
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, ite_true, Id.run_pure]
  exact hadv

/-- Native first preparation enters the literal sibling continuation
when its refined partition remains nondiscrete. -/
theorem Frame.first_sweep_step {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    (next : Generic.SweepFn (State n) n)
    (hd : (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).1 ≠ n) :
    Generic.nodeStep (.ofGraph G) tcLevel next true f.level f.numcells f.entry =
      let r := Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry
      let s := next true f.level r.1 r.2.1.toNat ((r.2.2.1.nextElem none).getD 0)
        (r.2.2.1.nextElem none) r.2.2.1 0 (cheapCheck true f.level r.2.2.2.2)
      match s.1 with
      | .done => (.unwind (f.level - 1) false,
          (policy (n := n)).afterSweep true f.level r.2.2.2.1 s.2.1 s.2.2)
      | _ => (s.1, s.2.2) := by
  unfold Generic.prepareFirst at hd ⊢
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.chooseTarget, Generic.Policy.cheapCheck, Generic.Policy.afterSweep] at hd ⊢
  simp only [ite_true, beq_eq_false_iff_ne.mpr hd, Bool.false_eq_true, ite_false]
  rfl

end Hex.GraphIso.Nauty.Sparse.Max
