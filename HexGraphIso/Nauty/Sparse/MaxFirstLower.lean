/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstNext
public import HexGraphIso.Nauty.Sparse.MaxFirstFilter
import HexGraphIso.Nauty.Policy.Generic.MaxExit
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.CursorCover
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The first child's maximum result extends through the complete native
first sweep. Recovery establishes the proved later-sibling context, and
the actual short filter is justified by the first call's emitted pairs. -/
theorem FirstInput.sweep_lower {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel tv last : Nat} {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstInput G tcLevel f parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true f.level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.2).orbits[tv]! = tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel ch.level ch.numcells ch.entry last leaf)
    (hf : n ≤ f.level + fuel)
    (hchild : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      let raw := Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry
      MaxResult (ch.key G.graph tcLevel) none (State.best G.graph raw.2) f.level
        (Max.Witness G tcLevel (parents.push p).frames) raw.1) :
    let p := f.firstParent G.graph tcLevel [] tv
    let swept := Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
      f.level (f.target G.graph tcLevel).numcells p.tc tv (some tv) p.cell 0 p.state
    ExitCover (f.key G.graph tcLevel) (State.best G.graph swept.2.2) f.level
      (Max.Witness G tcLevel (parents.frames.insert f)) swept.1 := by
  let l : Loop n := ⟨f, true⟩
  let c := l.cell G.graph tcLevel
  let p := f.firstParent G.graph tcLevel [] tv
  let ch := p.child G.graph tcLevel
  let raw := Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry
  let left := (policy (n := n)).leaveChild tv (afterChildFirst f.level tv raw.2)
  let back := p.firstBack G.graph tcLevel fuel
  let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
    Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel n
      level numcells tc tv1 cursor cell index st
  let result : Exit × Nat × State n → Prop := fun out =>
    ExitCover (f.key G.graph tcLevel) (State.best G.graph out.2.2) f.level
      (Max.Witness G tcLevel (parents.frames.insert f)) out.1
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  have hm := VSet.nextElem_mem htv
  have hp : p.Valid G tcLevel := h.entry.frame.first_parent h.entry.shape hi hm []
  have hselected := l.selected (tcLevel := tcLevel) h.entry.frame hi (by intro he; cases he)
  have hcell : c.Valid G := hselected.1
  have hset : p.cell = c.vertices := hselected.2
  have hframe : FrameOut G f.level f.level c.entry p.state := (l.prepared h.entry.frame).2
  have hcover : c.Cover G.graph tcLevel (Remaining (some tv) p.cell) (State.key G.graph [] p.state) := by
    have hh := Cell.Cover.initial G.graph tcLevel c (State.key G.graph [] p.state)
    rw [← hset] at hh
    change c.Cover G.graph tcLevel (Remaining (p.cell.nextElem none) p.cell) _ at hh
    have ht : p.cell.nextElem none = some tv := htv
    rw [ht] at hh
    exact hh
  have hadv : result (Generic.advance (n + 2) next true f.level c.numcells p.tc tv tv p.cell 0 left raw.1) := by
    cases hx : raw.1 with
    | fuel => unfold Generic.advance; trivial
    | done => exact (Generic.node_ne_done true (.ofGraph G.graph) (n + 2) tcLevel fuel
        ch.level ch.numcells ch.entry hx).elim
    | unwind target short =>
      have hh := hchild.coverage
      change ExitCover _ _ f.level _ raw.1 at hh
      rw [hx] at hh
      have hbound : target ≤ f.level := hh.1
      by_cases he : target < f.level
      · unfold Generic.advance
        simp only [he, ite_true, Id.run_pure]
        have hw : Max.Witness G tcLevel (parents.push p).frames target (State.best G.graph raw.2) := by
          simpa only [ExitCover, ite_eq_right (by omega : target ≠ f.level)] using hh.2
        rw [Parents.push_frames hp.node.positive] at hw
        change Max.Witness G tcLevel (parents.frames.insert f) target (State.best G.graph left) at hw
        exact ⟨Nat.le_of_lt he, by simpa only [ite_eq_right (by omega : target ≠ f.level)] using hw⟩
      · have ht : target = f.level := by omega
        subst target
        have hd : Covers (ch.key G.graph tcLevel) (State.best G.graph raw.2) := by
          simpa only [ExitCover, ↓reduceIte] using hh.2
        obtain ⟨bs, fs, hr, resumed⟩ := h.entry.receive h.scope hi htv horbit path hf
        have hbackRead : State.best G.graph back = State.key G.graph bs back := by
          have he : State.best G.graph back = State.best G.graph raw.2 :=
            recover_best G.graph (n + 2) f.level left
          rw [he, hr.read]
          exact (recover_key G.graph bs (n + 2) f.level left).symm
        have hmax : MaxResult ((c.child true p.state tv).key G.graph tcLevel)
            (State.key G.graph [] (c.child true p.state tv).entry) (State.best G.graph raw.2)
            c.level (Max.Witness G tcLevel (parents.push p).frames) (.unwind f.level short) := by
          change MaxResult (ch.key G.graph tcLevel) none (State.best G.graph raw.2)
            f.level _ _
          rw [← hx]
          exact hchild
        have hvisit : c.Cover G.graph tcLevel (Remaining (p.cell.nextElem (some tv)) p.cell)
            (State.best G.graph left) := hcover.received hcell hframe hp.ready (hset ▸ hm) hmax
        have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → p.cell.mem v = true) → ∀ index,
            c.Cover G.graph tcLevel (Remaining (smaller.nextElem (some tv)) smaller) (State.best G.graph left) →
            result (next true f.level c.numcells p.tc tv (smaller.nextElem (some tv)) smaller index back) := by
          intro smaller hsub index hcov
          have he : State.best G.graph back = State.best G.graph left := recover_best G.graph (n + 2) f.level left
          rw [← he, hbackRead] at hcov
          have hs := h.recovered hi htv path hr resumed hd hsub hcov
          apply lower_sweep G tcLevel fuel (node_max G tcLevel fuel) n l bs fs tv index
            (smaller.nextElem (some tv)) smaller back parents hs hf
            (Generic.CursorFuel.next (by omega : n ≤ tv + (n + 1)))
          intro _ v hv
          have hb := (VSet.nextElem_eq_some_iff.mp hv).2.1
          change tv + 1 ≤ v at hb
          omega
        have hresume : ∀ smaller, (∀ v, smaller.mem v = true → p.cell.mem v = true) →
            c.Cover G.graph tcLevel (Remaining (smaller.nextElem (some tv)) smaller) (State.best G.graph left) →
            result (Generic.resume (n + 2) next true f.level c.numcells p.tc tv tv smaller 0 left) := by
          intro smaller hsub hcov
          unfold Generic.resume
          simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, Id.run_pure]
          exact hcontinue smaller hsub _ hcov
        unfold Generic.advance
        simp only [Nat.lt_irrefl, ite_false, Id.run_pure, apply_ite Id.run]
        cases short with
        | false => exact hresume p.cell (fun _ hv => hv) hvisit
        | true =>
          let filtered := (policy (n := n)).shortprune p.cell left
          have hsub : ∀ v, filtered.mem v = true → p.cell.mem v = true :=
            fun _ hv => Nauty.shortprune_subset (st := left.frame) hv
          have hshort : c.Cover G.graph tcLevel
              (fun v => Remaining (p.cell.nextElem (some tv)) p.cell v ∧ filtered.mem v = true)
              (State.best G.graph left) := by
            apply CellCover.pruned hvisit hcell.ready hn hcell.positive hcell.window hcell.size hcell.range hcell.fuel
              (fun v hv => by change c.vertices.mem v = true; rw [← hset]; exact hv.1)
            intro v hv hdrop
            obtain ⟨gamma, ha, hs, hlt⟩ := h.short_drop hi htv path hx v (VSet.mem_lt hv.1) hv.1 hdrop
            exact ⟨gamma, ha, hcell.stabilizes hframe hp.ready hs, hlt⟩
          exact hresume filtered hsub (hshort.filtered hsub)
  change (policy (n := n)).orbit p.state tv = tv at horbit
  change result (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
    f.level c.numcells p.tc tv (some tv) p.cell 0 p.state)
  rw [Generic.sweep]
  unfold Generic.sweepStep
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, ite_true, Id.run_pure]
  exact hadv

end Hex.GraphIso.Nauty.Sparse.Max
