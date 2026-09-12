/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstPairs
public import HexGraphIso.Nauty.Sparse.ShortPair
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A short pair returned by the actual first child is valid at its
parent. The first leaf supplies the saved labels and trace, while the
complete first call supplies pair soundness. First-child bookkeeping
does not change the pair read by the filter. -/
theorem FirstInput.short_drop {G : GraphIso.Sparse.Colored n k} {tcLevel fuel tv last : Nat}
    {f : Frame n} {parents : Parents n} {leaf : State n}
    (h : FirstInput G tcLevel f parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel ch.level ch.numcells ch.entry last leaf)
    (hexit : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).1 =
        .unwind f.level true) :
    let p := f.firstParent G.graph tcLevel [] tv
    let ch := p.child G.graph tcLevel
    let raw := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
    let left := (policy (n := n)).leaveChild tv (afterChildFirst f.level tv raw)
    ∀ v, v < n → p.cell.mem v = true → ((policy (n := n)).shortprune p.cell left).mem v = false →
      ∃ gamma, checkAutom (Graph.context G.graph).g gamma = true ∧
        CellStab p.state.ptn f.level p.state.lab gamma ∧ gamma[v]! < v := by
  intro p ch raw left v hv hm hd
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  have hmem := VSet.nextElem_mem htv
  have hp : p.Valid G tcLevel := h.entry.frame.first_parent h.entry.shape hi hmem []
  have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
  have hpath : PathInv G f.level p.state :=
    (((h.path.visit h.entry.frame.node).record (f.code G.graph)).target true tcLevel
      (visit (.ofGraph G.graph) f.level f.numcells f.entry).1).cheap true
  have hguid : p.Guided G.graph tcLevel :=
    f.firstParent_guided (by rw [h.first]; exact h.entry.frame.positive)
      (by rw [h.canon]; exact h.entry.frame.positive) [] tv
  have hcap : 0 < p.state.wsCap := by
    have he : p.state.wsCap = f.entry.wsCap :=
      (Loop.mk f true).preserve (capacityPolicy (.ofGraph G.graph) (n + 2) tcLevel f.entry.wsCap) rfl
    rw [he]
    exact h.capacity
  have hsaved := firstPath_saved hn hch.entry.frame.positive hch.entry.frame.node path hch.entry.blank hch.entry.work
  have htrace := firstPath_trace hn path hch.entry.frame.positive hch.entry.frame.node hch.entry.shape
    hch.entry.targetSize (by rw [hch.entry.firstSize]; omega) hch.entry.blank hch.entry.work hch.entry.trace
  apply shortprune_drop (st := left.frame) hv hm hd
  intro fix mcr hpair
  exact Sparse.return_pair hp.ready hn h.entry.frame.positive hpath hp.target hmem
    (by change f.level < f.level + 1; omega) hexit (Nat.le_refl _) hguid.canonical hcap hsaved htrace (hch.pairs_out path)
    (fix, mcr) hpair

end Hex.GraphIso.Nauty.Sparse.Max
