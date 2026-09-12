/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstContext
public import HexGraphIso.Nauty.Sparse.FirstPairs
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- First-descent entry invariants supply valid pruning pairs throughout
the complete executed first call, including its later siblings. -/
theorem FirstInput.pairs_out {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {f : Frame n} {parents : Parents n} {leaf : State n}
    (h : FirstInput G tcLevel f parents)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf) :
    PairsOk G (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2 := by
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  exact firstPath_pairs hn path h.entry.frame.positive h.entry.frame.node h.entry.shape
    h.entry.targetSize (by rw [h.entry.firstSize]; omega) h.entry.blank h.entry.work h.entry.trace
    h.pairs h.path h.boundary h.bound

/-- Native first-child cleanup and recovery restore the complete pruning
workspace at its parent. The fixed-point set is restored literally, and
the implicit-pair boundary is inherited from the actual first call. -/
theorem FirstInput.pairs_back {G : GraphIso.Sparse.Colored n k} {tcLevel fuel tv last : Nat}
    {f : Frame n} {parents : Parents n} {leaf : State n} {bs fs : List Nat}
    (h : FirstInput G tcLevel f parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel
        (p.child G.graph tcLevel).level (p.child G.graph tcLevel).numcells
        (p.child G.graph tcLevel).entry last leaf)
    (resume : let p := f.firstParent G.graph tcLevel [] tv
      Resumed G tcLevel p bs fs (p.firstBack G.graph tcLevel fuel) parents) :
    let p := f.firstParent G.graph tcLevel [] tv
    PairsReady G tcLevel f.level (f.target G.graph tcLevel).numcells
      (p.firstBack G.graph tcLevel fuel) := by
  let p := f.firstParent G.graph tcLevel [] tv
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild tv (afterChildFirst f.level tv raw)
  let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  have hm := VSet.nextElem_mem htv
  have hp : p.Valid G tcLevel := h.entry.frame.first_parent h.entry.shape hi hm []
  have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
  have hpath : PathInv G f.level p.state :=
    (((h.path.visit h.entry.frame.node).record (f.code G.graph)).target true tcLevel r.1).cheap true
  have ho := node_frame G hn true tcLevel fuel ch.level ch.numcells ch.entry
    hch.entry.frame.positive hch.entry.frame.node
  have hframe := hp.ready.child_frame hn h.entry.frame.positive true hp.target hm
    (by simpa only [ch, p, Parent.child, Frame.firstParent, Nat.add_sub_cancel] using ho)
  have hfixed := node_fixed hn true tcLevel fuel ch.level ch.numcells ch.entry
    hch.entry.frame.positive hch.entry.frame.node hch.path.fixed
  have hleft : left.fixedpts = p.state.fixedpts := by
    apply fixed_restore (st := p.state) (out := raw) hfixed
    exact (fixed_child true hn hp.ready hpath.fixed hp.target hm).1
  have hpathBack := hpath.recover hn h.entry.frame.positive hp.ready
    ((hframe.afterChild f.level tv).leave tv) hleft
  have hboundary : CheapBoundary G (f.level + 1) left :=
    (hch.boundary.firstNode hn (by change 1 < f.level + 1; have := h.entry.frame.positive; omega)
      hch.entry.frame.node path).congr rfl rfl rfl
  refine ⟨resume.codes.toTraceReady, hpathBack,
    (((hch.pairs_out path).afterChild f.level tv).leave tv).recover (n + 2) f.level,
    hboundary.recover_child h.entry.frame.positive ?_, recover_bound f.level left⟩
  have hh := Nat.le_trans hp.ready.ok.bc (bcount_le _ _ _)
  change f.level ≤ n at hh
  have hl := h.entry.frame.positive
  omega

end Hex.GraphIso.Nauty.Sparse.Max
