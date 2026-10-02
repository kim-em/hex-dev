/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxGuideFrame
public import HexGraphIso.Nauty.Sparse.MaxGuideReturn
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxScatter
import all HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A completed native child supplies the canonical reference guide at
recovery. Its coverage is the local induction premise; the reference's
origin and containment follow from the executed child call. -/
theorem Parent.Guided.canon_return {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} {after : Option (Key n)} (h : p.Guided G.graph tcLevel)
    (hp : p.Valid G tcLevel) (first : Bool) (hb : p.state.gcaCanon ≤ p.node.level)
    (hg : Grows (State.key G.graph p.bs p.state) after)
    (hd : Covers (p.key G.graph tcLevel p.chosen) after) :
    let ch := p.child G.graph tcLevel
    let raw := (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
    let left := (policy (n := n)).leaveChild p.chosen
      (if first then afterChildFirst p.node.level p.chosen raw else raw)
    CanonGuide p.node.level p.tc p.state (p.key G.graph tcLevel) after
      ((policy (n := n)).recover (n + 2) p.node.level left) := by
  intro ch raw left
  have hn : 0 < n := by have := hp.node.positive; have := hp.node.depth; omega
  apply h.canonical.recover (G := G) hb hg hd
    ⟨SearchOut.refl _ _ _ hp.ready.ok.reach, hp.ready.scratch.toBounded⟩
  have hr := child_canon (tcLevel := tcLevel) (fuel := fuel)
    hp.ready hn hp.node.positive p.first first hp.target hp.chosen
  cases first <;> exact hr

/-- Returning from an actual off-path child establishes the covered
references for the next sibling in its recovered label ordering. -/
theorem Parent.Guided.back {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} {ds fs : List Nat} {cell : VSet n} {tv : Nat}
    (h : p.Guided G.graph tcLevel) (hp : p.Valid G tcLevel)
    (hb : p.state.gcaCanon ≤ p.node.level)
    (hg : Grows (State.key G.graph p.bs p.state)
      (State.key G.graph ds (p.back G.graph tcLevel fuel)))
    (hr : let ch := p.child G.graph tcLevel
      ReturnCodes G.graph ch.codes ds fs
        (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2)
    (hd : let ch := p.child G.graph tcLevel
      Covers (ch.key G.graph tcLevel) (State.best G.graph
        (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2)) :
    (p.next (p.back G.graph tcLevel fuel) ds cell tv).Guided G.graph tcLevel := by
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild p.chosen raw
  let out := p.back G.graph tcLevel fuel
  have hk : State.key G.graph ds out = State.best G.graph raw :=
    (recover_key G.graph ds (n + 2) p.node.level left).trans hr.read.symm
  have hdone : Covers (p.key G.graph tcLevel p.chosen) (State.key G.graph ds out) := by
    rw [hk, ← p.child_key]
    exact hd
  obtain ⟨hready, hframe⟩ := hp.returned_frame false
  apply hp.guide_frame hready hframe (h.canon_return hp false hb hg hdone)
  intro ht
  have hgc : out.gcaFirst = p.state.gcaFirst := by
    have he : out.gcaFirst = raw.gcaFirst :=
      (gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover p.node.level left
    rw [he, node_gca]
    dsimp only [ch, Parent.child]
    cases p.first <;> rfl
  have hfl : out.firstlab = p.state.firstlab := by
    have he : out.firstlab = raw.firstlab := congrArg (fun r => r.2.2)
      ((referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover p.node.level left)
    have hr := congrArg (fun r => r.2.2)
      (node_reference (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry)
    exact (he.trans hr).trans (by dsimp only [ch, Parent.child]; cases p.first <;> rfl)
  obtain ⟨hc, hp⟩ := h.first (hgc.symm.trans ht)
  change Covers (p.key G.graph tcLevel out.firstlab[p.tc]!) (State.key G.graph ds out) ∧
    cellsPerm p.state.ptn p.node.level p.state.lab out.firstlab
  rw [hfl]
  exact ⟨hc.grow hg, hp⟩

end Hex.GraphIso.Nauty.Sparse.Max
