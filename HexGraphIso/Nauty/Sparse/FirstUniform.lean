/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstDrop
public import HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.Preparation
import all HexGraphIso.Nauty.Sparse.FirstChoice
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The actual all-same boundary certifies every native leaf, including
its target sequence and all refinement codes. The induction follows the
guiding child and uses the actual sweep's counted checked carriers; it
does not assume automorphism-generation completeness. -/
theorem FirstInput.uniform {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstInput G tcLevel f parents)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf)
    (hf : n + 1 ≤ f.level + fuel)
    (hsame : (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2.allsamelevel ≤ f.level) :
    ∃ targets key, Generation.Uniform G.graph tcLevel f.level
      (State.refined (.ofGraph G.graph) f.level f.numcells f.entry) targets key := by
  obtain ⟨level, numcells, codes, st⟩ := f
  induction fuel generalizing level numcells codes st last leaf parents with
  | zero => cases path
  | succ fuel ih =>
    let f : Frame n := ⟨level, numcells, codes, st⟩
    let R := State.refined (.ofGraph G.graph) level numcells st
    have hr : RefineSt.Ready G.graph level R := h.entry.frame.node.refined
    have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
    cases path with
    | leaf =>
      rename_i hd
      have hp := prepareFirst_partition (.ofGraph G.graph) tcLevel level numcells st
      have hdisc : discreteAt R.ptn level n = true := by
        apply (discreteAt_iff_bcount hr.spec.node.ptnSize.symm hr.spec.node.ptnEnd).mpr
        change (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 = n at hd
        exact hr.spec.count.symm.trans (hp.2.2.symm.trans hd)
      obtain ⟨label, hlabel⟩ := Label.ofArray?_exists hr.spec.label
      exact ⟨[], _, Generation.Uniform.leaf hr hdisc hlabel⟩
    | @step _ _ _ _ _ _ tv hopen htv horbit path =>
      let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      let l : Loop n := ⟨f, true⟩
      let c := l.cell G.graph tcLevel
      let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      have hi : (visit (.ofGraph G.graph) level numcells st).1 < n := by
        have hc := hr.spec.count
        have hb := bcount_le R.ptn level n
        change R.numcells ≠ n at hopen
        change R.numcells < n
        omega
      have hdrop := first_drop (inf := n + 2) hopen htv horbit path hsame
      have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
      obtain ⟨targets, key, hu⟩ := ih (level := ch.level) (numcells := ch.numcells)
        (codes := ch.codes) (st := ch.entry) hch path
        (by change n + 1 ≤ (level + 1) + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega)
        (Nat.le_of_eq hdrop.2.2)
      have hselected := l.selected (tcLevel := tcLevel) h.entry.frame hi (by intro he; cases he)
      have hcell : c.Valid G := hselected.1
      have hm : c.vertices.mem tv = true := hselected.2 ▸ VSet.nextElem_mem htv
      obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp (mem_windowSet.mp hm).2
      change R.lab[c.tc + o]! = tv at hat
      have hwindow : IsCell R.ptn level c.tc c.len := hcell.window
      have htarget : c.tc = targetcell (.ofGraph G.graph) R.lab R.ptn level tcLevel (-1) := by
        change r.2.1.toNat = _
        rw [prepareFirst_choice h.entry.frame.node hn h.entry.frame.positive hopen]
        rfl
      have hguide : Generation.Uniform G.graph tcLevel (level + 1)
          (R.child (.ofGraph G.graph) level c.tc R.lab[c.tc + o]! ch.entry.canong.scratch) targets key := by
        change Generation.Uniform G.graph tcLevel (level + 1)
          (State.refined (.ofGraph G.graph) (level + 1) (r.1 + 1)
            ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))) targets key at hu
        rw [firstChild_refined] at hu
        rw [hat]
        exact hu
      obtain ⟨previous, hcount⟩ := h.counted hi htv horbit path
        (by change n ≤ level + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega)
      have hall := hcount.full (Nat.le_of_eq hdrop.2.1)
      refine ⟨c.tc :: targets, ⟨R.longcode :: key.codes, key.graph⟩,
        Generation.Uniform.carriers hr hwindow hcell.range hcell.size ho
          hch.entry.frame.node.scratch htarget ?_ hguide⟩
      intro a ha
      have hm : R.lab[c.tc + a]! ∈ segN c.entry.lab c.tc c.len :=
        mem_segN_iff.mpr ⟨a, ha, rfl⟩
      obtain ⟨gamma, hcheck, hstab, hmove⟩ := hall _ hm
      exact ⟨gamma, hcheck, hstab, hmove.trans hat.symm⟩

end Hex.GraphIso.Nauty.Sparse.Max
