/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstUniform
public import HexGraphIso.Nauty.Sparse.RefPath
public import HexGraphIso.Nauty.Sparse.Matching
import all HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.RefPath
import all HexGraphIso.Nauty.Sparse.Matching
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstLeaf
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

/-- The complete first call stores a selected native reference retaining
uniformity at exactly its returned all-same boundary. The witness agrees
with the literal saved codes, targets, sentinel and parsed first label. -/
theorem FirstInput.witness {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstInput G tcLevel f parents)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf)
    (hf : n + 1 ≤ f.level + fuel) :
    let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2
    ∃ targets key,
      Generation.RefPath G.graph tcLevel out.allsamelevel f.level
        (State.refined (.ofGraph G.graph) f.level f.numcells f.entry) targets key ∧
      Generation.Matches G.graph f.level out targets key := by
  obtain ⟨level, numcells, codes, st⟩ := f
  induction fuel generalizing level numcells codes st last leaf parents with
  | zero => cases path
  | succ fuel ih =>
    let f : Frame n := ⟨level, numcells, codes, st⟩
    let R := State.refined (.ofGraph G.graph) level numcells st
    let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel (fuel + 1) level numcells st).2
    have hr : RefineSt.Ready G.graph level R := h.entry.frame.node.refined
    have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
    have hpath := path
    obtain ⟨ref, hlast⟩ := firstRef_of_path (inf := n + 2) hn path h.entry.frame.positive
      h.entry.frame.node h.entry.targetSize (by rw [h.entry.firstSize]; omega)
    obtain ⟨rt, rk, hocc, hmatches⟩ := ref.occurs hr
    by_cases hb : out.allsamelevel ≤ level
    · obtain ⟨ut, uk, hu⟩ := h.uniform path hf hb
      obtain ⟨rfl, rfl⟩ := hu rt rk hocc
      exact ⟨_, _, hocc.uniformPath hr hu, hmatches⟩
    cases path with
    | @leaf _ _ _ _ hd =>
      have he : out.allsamelevel = level := by
        dsimp only [out]
        rw [Generic.node, Frame.first_step (f := f) _ hd]
        rfl
      exact (hb (Nat.le_of_eq he)).elim
    | @step _ _ _ _ _ _ tv hopen htv horbit path =>
      let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      let l : Loop n := ⟨f, true⟩
      let c := l.cell G.graph tcLevel
      let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      let childOut := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel
        ch.level ch.numcells ch.entry).2
      have hi : (visit (.ofGraph G.graph) level numcells st).1 < n := by
        have hc := hr.spec.count
        have hbc := bcount_le R.ptn level n
        change R.numcells ≠ n at hopen
        change R.numcells < n
        omega
      have hnd : discreteAt R.ptn level n ≠ true := by
        intro hd
        have hc := (discreteAt_iff_bcount hr.spec.node.ptnSize.symm hr.spec.node.ptnEnd).mp hd
        have he := hr.spec.count
        change R.numcells < n at hi
        omega
      have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
      obtain ⟨targets, key, href, hm⟩ := ih (level := ch.level) (numcells := ch.numcells)
        (codes := ch.codes) (st := ch.entry) hch path
        (by change n + 1 ≤ (level + 1) + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega)
      have hboundary : out.allsamelevel = childOut.allsamelevel :=
        (first_boundary (inf := n + 2) (fuel := fuel) hopen htv horbit).resolve_left
          (fun he => hb (Nat.le_of_eq he))
      have hreference : out.reference = childOut.reference :=
        (firstPath_reference (inf := n + 2) hpath).trans (firstPath_reference (inf := n + 2) path).symm
      have hselected := l.selected (tcLevel := tcLevel) h.entry.frame hi (by intro he; cases he)
      have hcell : c.Valid G := hselected.1
      have hmem : c.vertices.mem tv = true := hselected.2 ▸ VSet.nextElem_mem htv
      obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp (mem_windowSet.mp hmem).2
      change R.lab[c.tc + o]! = tv at hat
      have hwindow : IsCell R.ptn level c.tc c.len := hcell.window
      have htarget : c.tc = targetcell (.ofGraph G.graph) R.lab R.ptn level tcLevel (-1) := by
        change r.2.1.toNat = _
        rw [prepareFirst_choice h.entry.frame.node hn h.entry.frame.positive hopen]
        rfl
      have htail : Generation.RefPath G.graph tcLevel out.allsamelevel (level + 1)
          (R.child (.ofGraph G.graph) level c.tc R.lab[c.tc + o]! ch.entry.canong.scratch) targets key := by
        change Generation.RefPath G.graph tcLevel childOut.allsamelevel (level + 1)
          (State.refined (.ofGraph G.graph) (level + 1) (r.1 + 1)
            ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))) targets key at href
        rw [firstChild_refined] at href
        rw [hat, hboundary]
        exact href
      have hhead := hmatches.head hocc
      refine ⟨c.tc :: targets, ⟨R.longcode :: key.codes, key.graph⟩,
        .step hwindow hcell.range hcell.size ho hch.entry.frame.node.scratch htarget htail
          (fun he => (hb he).elim), ?_⟩
      exact (hm.congr hreference).cons hhead.1 (by rw [htarget]; exact hhead.2 hnd)

end Hex.GraphIso.Nauty.Sparse.Max
