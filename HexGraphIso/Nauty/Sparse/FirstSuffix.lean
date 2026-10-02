/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstComplete
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

/-- The actual guiding child establishes the complete suffix context,
its boundary values and the literal continuation equation. These are
derived from the executed child's maximum and normal-return theorems,
without any generation or orbit-count premise. -/
theorem FirstInput.suffix {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel tv last : Nat} {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstInput G tcLevel f parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true f.level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.2).orbits[tv]! = tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel ch.level ch.numcells ch.entry last leaf)
    (hf : n ≤ f.level + fuel) :
    let l : Loop n := ⟨f, true⟩
    let c := l.cell G.graph tcLevel
    let p := f.firstParent G.graph tcLevel [] tv
    let back := p.firstBack G.graph tcLevel fuel
    ∃ bs fs, SweepInput G tcLevel l bs fs (p.cell.nextElem (some tv)) p.cell back parents ∧
      back.eqlevFirst = f.level ∧ f.level < back.allsamelevel ∧
      Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        f.level c.numcells p.tc tv (some tv) p.cell 0 p.state =
      Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel n
        f.level c.numcells p.tc tv (p.cell.nextElem (some tv)) p.cell
        (if back.orbits[tv]! == tv then 1 else 0) back := by
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
  have hch := h.child hi htv
  have hbudget : n + 1 ≤ ch.level + fuel := by change n + 1 ≤ f.level + 1 + fuel; omega
  have hchild := hch.maximum path hbudget
  have hreturn : raw.1 = .unwind f.level false := hch.returns path hbudget
  have hd : Covers (ch.key G.graph tcLevel) (State.best G.graph raw.2) := by
    have hh := hchild.coverage
    change ExitCover _ _ f.level _ raw.1 at hh
    rw [hreturn] at hh
    simpa only [ExitCover, ↓reduceIte] using hh.2
  obtain ⟨bs, fs, hr, resumed⟩ := h.entry.receive h.scope hi htv horbit path hf
  have hbackRead : State.best G.graph back = State.key G.graph bs back := by
    have he : State.best G.graph back = State.best G.graph raw.2 :=
      recover_best G.graph (n + 2) f.level left
    rw [he, hr.read]
    exact (recover_key G.graph bs (n + 2) f.level left).symm
  have hmax : MaxResult ((c.child true p.state tv).key G.graph tcLevel)
      (State.key G.graph [] (c.child true p.state tv).entry) (State.best G.graph raw.2)
      c.level (Max.Witness G tcLevel (parents.push p).frames) (.unwind f.level false) := by
    change MaxResult (ch.key G.graph tcLevel) none (State.best G.graph raw.2) f.level _ _
    rw [← hreturn]
    exact hchild
  have hvisit : c.Cover G.graph tcLevel (Remaining (p.cell.nextElem (some tv)) p.cell)
      (State.best G.graph left) := hcover.received hcell hframe hp.ready (hset ▸ hm) hmax
  have hbRead : State.best G.graph back = State.best G.graph left := recover_best G.graph (n + 2) f.level left
  rw [← hbRead, hbackRead] at hvisit
  have hs := h.recovered hi htv path hr resumed hd (fun _ hv => hv) hvisit
  have hfloor := firstPath_floor (inf := n + 2) path
  change f.level + 1 ≤ raw.2.allsamelevel ∧ f.level + 1 ≤ raw.2.eqlevFirst at hfloor
  have hsame : f.level < back.allsamelevel := by
    have he := recover_same (n + 2) f.level left
    change back.allsamelevel = raw.2.allsamelevel at he
    rw [he]
    omega
  have heq : back.eqlevFirst = f.level := by
    have he := recover_eqlev (n + 2) f.level left
    change back.eqlevFirst = min raw.2.eqlevFirst f.level at he
    rw [he]
    exact Nat.min_eq_right (by omega)
  refine ⟨bs, fs, hs, heq, hsame, ?_⟩
  change (policy (n := n)).orbit p.state tv = tv at horbit
  change Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
    f.level c.numcells p.tc tv (some tv) p.cell 0 p.state = _
  rw [Generic.sweep]
  unfold Generic.sweepStep
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, ite_true, Id.run_pure]
  change Generic.advance (n + 2) next true f.level c.numcells p.tc tv tv p.cell 0 left raw.1 = _
  rw [hreturn]
  unfold Generic.advance Generic.resume
  simp only [Nat.lt_irrefl, ite_false, Bool.false_eq_true, Bool.not_true,
    Bool.false_and, Bool.true_and, Id.run_pure]
  rfl

end Hex.GraphIso.Nauty.Sparse.Max
