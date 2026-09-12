/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstSweep
import all HexGraphIso.Nauty.Sparse.MaxFirstSweep
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstLeaf
import all HexGraphIso.Nauty.Sparse.MaxDescent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The complete actual first-path call installs only keys below its
full frozen subtree. The induction discharges every first-child bound;
all later children use the proved native off-path recursion. -/
theorem FirstEntry.upper {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstEntry G f)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf)
    (hs : Scope G tcLevel f [] f.entry parents) (hf : n + 1 ≤ f.level + fuel) :
    Bounded (f.key G.graph tcLevel) none
      (State.best G.graph (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel
        f.level f.numcells f.entry).2) := by
  obtain ⟨level, numcells, codes, st⟩ := f
  induction fuel generalizing level numcells codes st last leaf parents with
  | zero => cases path
  | succ fuel ih =>
    let f : Frame n := ⟨level, numcells, codes, st⟩
    cases path with
    | leaf =>
      rename_i hd
      exact (h.frame.first_leaf h.stored (by rw [h.firstSize]; omega) h.canonSize
        h.codes_lt hd (fun _ _ => True)).bounded
    | @step _ _ _ _ _ _ tv hopen htv horbit path =>
      have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
      have hi : (visit (.ofGraph G.graph) level numcells st).1 < n := by
        have hr := h.frame.node.visit_ready hn h.frame.positive
        have hc : (visit (.ofGraph G.graph) level numcells st).1 =
            bcount (visit (.ofGraph G.graph) level numcells st).2.2.ptn level n := hr.ok.count
        have hb := bcount_le (visit (.ofGraph G.graph) level numcells st).2.2.ptn level n
        change (visit (.ofGraph G.graph) level numcells st).1 ≠ n at hopen
        omega
      have hm := VSet.nextElem_mem htv
      let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      have hch : FirstEntry G ch := h.child hi hm
      have hscope : Scope G tcLevel ch [] ch.entry (parents.push p) :=
        hs.first_child h.frame h.shape hi hm
      have hchild : Bounded (ch.key G.graph tcLevel) none
          (State.best G.graph (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel
            ch.level ch.numcells ch.entry).2) :=
        ih (level := ch.level) (numcells := ch.numcells) (codes := ch.codes) (st := ch.entry)
          hch path hscope
          (by change n + 1 ≤ (level + 1) + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega)
      have hupper := h.sweep_upper hs hi htv horbit path
        (by change n ≤ level + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega) hchild
      rw [Generic.node, Frame.first_sweep_step _ hopen]
      dsimp only
      rw [htv]
      simp only [Option.getD_some]
      let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      let swept := Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 (cheapCheck true level r.2.2.2.2)
      change Bounded (f.key G.graph tcLevel) none (State.best G.graph swept.2.2) at hupper
      change Bounded (f.key G.graph tcLevel) none
        (State.best G.graph (match swept.1 with
          | .done => (Generic.Exit.unwind (level - 1) false,
              (policy (n := n)).afterSweep true level r.2.2.2.1 swept.2.1 swept.2.2)
          | _ => (swept.1, swept.2.2)).2)
      generalize hx : swept = result at hupper ⊢
      obtain ⟨exit, index, out⟩ := result
      cases exit with
      | fuel => exact hupper
      | unwind => exact hupper
      | done =>
        change Bounded _ _ (State.best G.graph ((policy (n := n)).afterSweep true level r.2.2.2.1 index out))
        rw [afterSweep_best]
        exact hupper

end Hex.GraphIso.Nauty.Sparse.Max
