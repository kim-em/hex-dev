/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxGuideBack
public import HexGraphIso.Nauty.Sparse.FirstFrame
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxScatter
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Receiving the first child establishes both covered references for
the actual next sibling. The newly saved first label comes from the
executed first descent; only the completed child's coverage is inductive. -/
theorem Parent.Guided.first_back {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {p : Parent n} {ds fs : List Nat} {cell : VSet n} {tv : Nat} {leaf : State n}
    (h : p.Guided G.graph tcLevel) (hp : p.Valid G tcLevel)
    (hb : p.state.gcaCanon ≤ p.node.level)
    (path : let ch := p.child G.graph tcLevel
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel ch.level ch.numcells ch.entry last leaf)
    (hg : Grows (State.key G.graph p.bs p.state)
      (State.key G.graph ds (p.firstBack G.graph tcLevel fuel)))
    (hr : let ch := p.child G.graph tcLevel
      ReturnCodes G.graph ch.codes ds fs
        (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2)
    (hd : let ch := p.child G.graph tcLevel
      Covers (ch.key G.graph tcLevel) (State.best G.graph
        (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2)) :
    (p.next (p.firstBack G.graph tcLevel fuel) ds cell tv).Guided G.graph tcLevel := by
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild p.chosen (afterChildFirst p.node.level p.chosen raw)
  let out := p.firstBack G.graph tcLevel fuel
  have hn : 0 < n := by have := hp.node.positive; have := hp.node.depth; omega
  have hk : State.key G.graph ds out = State.best G.graph raw :=
    (recover_key G.graph ds (n + 2) p.node.level left).trans hr.read.symm
  have hdone : Covers (p.key G.graph tcLevel p.chosen) (State.key G.graph ds out) := by
    rw [hk, ← p.child_key]
    exact hd
  obtain ⟨hready, hframe⟩ := hp.returned_frame true
  apply hp.guide_frame hready hframe (h.canon_return hp true hb hg hdone)
  intro _
  have hstore := child_first_store hp.ready hn hp.node.positive p.first hp.target hp.chosen path
  have href : out.firstlab = raw.firstlab := congrArg (fun r => r.2.2)
    ((referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover p.node.level left)
  change Covers (p.key G.graph tcLevel out.firstlab[p.tc]!) (State.key G.graph ds out) ∧
    cellsPerm p.state.ptn p.node.level p.state.lab out.firstlab
  rw [href]
  exact ⟨hstore.2.2 ▸ hdone, hstore.2.1⟩

end Hex.GraphIso.Nauty.Sparse.Max
