/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstTail
public import HexGraphIso.Nauty.Sparse.MaxFirstNode
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstLeaf
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxFirstSweep
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
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A normally returning guiding child initializes the full native
sibling sweep, which finishes after all surviving targets are processed. -/
theorem FirstInput.sweep_done {G : GraphIso.Sparse.Colored n k}
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
    (hreturn : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).1 =
        .unwind f.level false) :
    let p := f.firstParent G.graph tcLevel [] tv
    (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
      f.level (f.target G.graph tcLevel).numcells p.tc tv (some tv) p.cell 0 p.state).1 = .done := by
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
  have hchild := hch.maximum path (by change n + 1 ≤ f.level + 1 + fuel; omega)
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
  have hbRead : State.best G.graph back = State.best G.graph left :=
    recover_best G.graph (n + 2) f.level left
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
  have htail (index : Nat) : (next true f.level c.numcells p.tc tv
      (p.cell.nextElem (some tv)) p.cell index back).1 = .done := by
    apply hs.tail_done rfl heq hsame hf
      (Generic.CursorFuel.next (by omega : n ≤ tv + (n + 1)))
    intro _ v hv
    have hb := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at hb
    omega
  have hadv : (Generic.advance (n + 2) next true f.level c.numcells p.tc tv tv p.cell 0 left raw.1).1 = .done := by
    rw [hreturn]
    unfold Generic.advance Generic.resume
    simp only [Nat.lt_irrefl, ite_false, Bool.false_eq_true, Bool.not_true, Bool.false_and, Id.run_pure]
    exact htail _
  change (policy (n := n)).orbit p.state tv = tv at horbit
  change (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
    f.level c.numcells p.tc tv (some tv) p.cell 0 p.state).1 = .done
  rw [Generic.sweep]
  unfold Generic.sweepStep
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, ite_true, Id.run_pure]
  exact hadv

/-- Every actual first-path call returns normally to its immediate
parent. The proof derives the guiding child's return by induction and
then executes its entire remaining sibling sweep. -/
theorem FirstInput.returns {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstInput G tcLevel f parents)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf)
    (hf : n + 1 ≤ f.level + fuel) :
    (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).1 =
      .unwind (f.level - 1) false := by
  obtain ⟨level, numcells, codes, st⟩ := f
  induction fuel generalizing level numcells codes st last leaf parents with
  | zero => cases path
  | succ fuel ih =>
    let f : Frame n := ⟨level, numcells, codes, st⟩
    cases path with
    | leaf =>
      rename_i hd
      rw [Generic.node, Frame.first_step _ hd]
    | @step _ _ _ _ _ _ tv hopen htv horbit path =>
      have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
      have hi : (visit (.ofGraph G.graph) level numcells st).1 < n := by
        have hr := h.entry.frame.node.visit_ready hn h.entry.frame.positive
        have hc : (visit (.ofGraph G.graph) level numcells st).1 =
            bcount (visit (.ofGraph G.graph) level numcells st).2.2.ptn level n := hr.ok.count
        have hb := bcount_le (visit (.ofGraph G.graph) level numcells st).2.2.ptn level n
        change (visit (.ofGraph G.graph) level numcells st).1 ≠ n at hopen
        omega
      let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
      have hchild := ih (level := ch.level) (numcells := ch.numcells) (codes := ch.codes) (st := ch.entry)
        hch path (by change n + 1 ≤ (level + 1) + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega)
      have hsweep := h.sweep_done hi htv horbit path
        (by change n ≤ level + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega) hchild
      rw [Generic.node, Frame.first_sweep_step _ hopen]
      dsimp only
      rw [htv]
      simp only [Option.getD_some]
      let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      let swept := Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 (cheapCheck true level r.2.2.2.2)
      change swept.1 = .done at hsweep
      change (match swept.1 with
        | .done => (Generic.Exit.unwind (level - 1) false,
            (policy (n := n)).afterSweep true level r.2.2.2.1 swept.2.1 swept.2.2)
        | _ => (swept.1, swept.2.2)).1 = _
      rw [hsweep]

end Hex.GraphIso.Nauty.Sparse.Max
