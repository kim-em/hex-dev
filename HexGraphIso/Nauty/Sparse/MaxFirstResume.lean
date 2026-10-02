/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstCodes
public import HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstCodes
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The literal first-child return, including its first-ancestor update,
fixed-point cleanup and native parent recovery. -/
def Parent.firstBack (G : Hex.SparseGraph n) (tcLevel fuel : Nat) (p : Parent n) : State n :=
  let ch := p.child G tcLevel
  let raw := (Generic.node true (.ofGraph G) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  (policy (n := n)).recover (n + 2) p.node.level
    ((policy (n := n)).leaveChild p.chosen (afterChildFirst p.node.level p.chosen raw))

/-- The executed first child supplies every comparison, history and
ancestor fact needed by the later sibling loop. No code or maximum
contract for that child is assumed. -/
theorem FirstEntry.receive {G : GraphIso.Sparse.Colored n k} {tcLevel fuel tv last : Nat}
    {f : Frame n} {leaf : State n} {parents : Parents n} (h : FirstEntry G f)
    (hs : Scope G tcLevel f [] f.entry parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true f.level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.2).orbits[tv]! = tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel
        (p.child G.graph tcLevel).level (p.child G.graph tcLevel).numcells
        (p.child G.graph tcLevel).entry last leaf)
    (hf : n ≤ f.level + fuel) :
    let p := f.firstParent G.graph tcLevel [] tv
    let ch := p.child G.graph tcLevel
    let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
    ∃ bs fs, ReturnCodes G.graph ch.codes bs fs out ∧
      Resumed G tcLevel p bs fs (p.firstBack G.graph tcLevel fuel) parents := by
  let p := f.firstParent G.graph tcLevel [] tv
  let ch := p.child G.graph tcLevel
  let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild tv (afterChildFirst f.level tv out)
  let back := p.firstBack G.graph tcLevel fuel
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hm := VSet.nextElem_mem htv
  have hp : p.Valid G tcLevel := h.frame.first_parent h.shape hi hm []
  have hch : FirstEntry G ch := h.child hi hm
  have hlen : ch.codes.length = f.level := by
    change (f.codes ++ [_]).length = f.level
    simp only [List.length_append, List.length_singleton, h.frame.length]
  have hfchild : n + 1 ≤ ch.level + fuel := by change n + 1 ≤ (f.level + 1) + fuel; omega
  obtain ⟨bs, fs, hr⟩ := hch.returned path hfchild
  have hleft : ReturnCodes G.graph ch.codes bs fs left := (hr.afterChild f.level tv).leave tv
  have hmachine := hleft.recover (n + 2)
  rw [hlen] at hmachine
  have htrace := firstPath_trace hn path hch.frame.positive hch.frame.node hch.shape hch.targetSize
    (by rw [hch.firstSize]; omega) hch.blank hch.work hch.trace
  have hopen : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).1 ≠ n := by
    change (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 ≠ n
    omega
  have hreturned := firstChild_trace hn h.frame.positive h.frame.node h.shape h.targetSize
    (by rw [h.firstSize]; omega) h.blank h.work hopen htv horbit path htrace
  have hroute := firstChild_route hn h.frame.positive h.frame.node h.targetSize
    (by rw [h.firstSize]; omega) hopen htv horbit path
  have hrecord := firstChild_recorded hn h.frame.positive h.frame.node h.targetSize hopen path
  have hcodes : CodeReady G tcLevel f.level (f.target G.graph tcLevel).numcells back :=
    ⟨hreturned.1, hroute⟩
  have hframe := node_frame G hn true tcLevel fuel ch.level ch.numcells ch.entry hch.frame.positive hch.frame.node
  have hparent := hp.ready.child_frame hn h.frame.positive true hp.target hm
    (by simpa only [ch, p, Parent.child, Frame.firstParent, Nat.add_sub_cancel] using hframe)
  have hrecovered := hp.ready.recover hn h.frame.positive ((hparent.afterChild f.level tv).leave tv)
  have hg : Grows (State.key G.graph [] p.state) (State.key G.graph bs back) := by
    intro key he
    cases he
  have hbefore : Scope G tcLevel f [] p.state parents := hs.change
    (by intro key he; cases he) (f.firstParent_boundary G.graph tcLevel [] tv)
  have hboundary := p.first_boundary path
  refine ⟨bs, fs, hr, hmachine, hcodes, hreturned.2, hrecord,
    hbefore.change hg (hboundary.imp id (fun h => Nat.le_of_lt h)), hg, ?_⟩
  intro cell hsub v hv
  exact hp.next hrecovered.1 hrecovered.2 hg hboundary
    ((hp.target.of_out hrecovered.2.effect).subset hsub) hv

end Hex.GraphIso.Nauty.Sparse.Max
