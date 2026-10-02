/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxContext
public import HexGraphIso.Nauty.Sparse.ReceiveCover
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxRecover
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxGuideReturn
import all HexGraphIso.Nauty.Sparse.MaxGuideBack
import all HexGraphIso.Nauty.Sparse.MaxCosetState
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Once an actual off-path child is covered, recovery establishes the
complete next-sibling context for every filtered subset with proved ranked
coverage. Code histories and geometry come from the native receiving
theorem; no full-search correctness is required to restore them. -/
theorem SweepInput.recovered {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat} {l : Loop n}
    {bs fs ds : List Nat} {cursor : Option Nat} {cell smaller : VSet n} {st : State n}
    {parents : Parents n} {tv : Nat}
    (h : SweepInput G tcLevel l bs fs cursor cell st parents) (htv : cursor = some tv)
    (hr : let p := l.parent G.graph tcLevel st bs cell tv
      let ch := p.child G.graph tcLevel
      ReturnCodes G.graph ch.codes ds fs
        (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2)
    (resume : let p := l.parent G.graph tcLevel st bs cell tv
      Resumed G tcLevel p ds fs (p.back G.graph tcLevel fuel) parents)
    (hd : let p := l.parent G.graph tcLevel st bs cell tv
      let ch := p.child G.graph tcLevel
      Covers (ch.key G.graph tcLevel) (State.best G.graph
        (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2))
    (hsub : ∀ v, smaller.mem v = true → cell.mem v = true)
    (hc : let p := l.parent G.graph tcLevel st bs cell tv
      (l.cell G.graph tcLevel).Cover G.graph tcLevel (Remaining (smaller.nextElem (some tv)) smaller)
        (State.key G.graph ds (p.back G.graph tcLevel fuel))) :
    let p := l.parent G.graph tcLevel st bs cell tv
    SweepInput G tcLevel l ds fs (smaller.nextElem (some tv)) smaller
      (p.back G.graph tcLevel fuel) parents := by
  let p := l.parent G.graph tcLevel st bs cell tv
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild tv raw
  let back := p.back G.graph tcLevel fuel
  have hv := h.member tv htv
  have hp : p.Valid G tcLevel := h.parent hv
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hch := h.child htv
  have hframe := hp.returned_frame (fuel := fuel) false
  have htrace := hch.traces.node hch.scope hch.frame false fuel
  have hrest := htrace.recovered h.scope hp false
  have hcounter := hp.back_counters (fuel := fuel) h.counters.1
    (Nat.le_trans h.counters.2.1 h.counters.2.2) h.counters.2.1
  have hnext := resume.next cell (fun _ hv => hv) tv hv
  have hgc : back.gcaFirst = st.gcaFirst := by
    have hg : back.gcaFirst = raw.gcaFirst :=
      (gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover l.node.level left
    rw [hg, node_gca]
    dsimp only [ch, p, Parent.child, Loop.parent]
    cases l.first <;> rfl
  have hcap : back.wsCap = st.wsCap := by
    have he : back.wsCap = raw.wsCap :=
      (capacityPolicy (.ofGraph G.graph) (n + 2) tcLevel raw.wsCap).recover l.node.level left rfl
    rw [he, node_capacity]
    dsimp only [ch, p, Parent.child, Loop.parent]
    cases l.first <;> rfl
  have hpairs := node_pairs G hn tcLevel fuel ch.level ch.numcells ch.entry hch.frame.positive hch.pairs
  have hbackPairs := h.pairs.child_return hn h.frame.positive l.first fuel h.target hv h.recorded hpairs
  have horbits : OrbitTrace G back :=
    (orbitPolicy G (n + 2) tcLevel).recover l.node.level left
      ((orbitPolicy G (n + 2) tcLevel).leave tv raw
        (node_orbitTrace G false (n + 2) tcLevel fuel ch.level ch.numcells ch.entry hch.orbits))
  refine ⟨h.frame, h.internal, h.selected, resume.codes, hbackPairs.1, resume.machine,
    h.effect.trans hframe.2, (h.target.of_out hframe.2.effect).subset hsub,
    fun v hv => h.subset v (hsub v hv), fun _ hv => VSet.nextElem_mem hv,
    h.choice.grow resume.grows, hnext.small, resume.scope,
    h.guides.back h.scope hp, hch.cosets.back h.scope, h.ranked, hrest.pop h.scope,
    horbits, ?_, ?_, hcounter, ?_, ?_, ?_, resume.recorded, resume.route, hc, ?_⟩
  · intro hf
    have hs : (parents.push p) p.node.level = some p := by simp only [Parents.push, ↓reduceIte]
    have hh := hrest p.node.level p hs hf
    exact hh.rebase hp.ready hframe.1 hn h.frame.positive
  · intro v
    exact (h.guided tv).back hp h.counters.2.2 resume.grows hr hd
  · intro hf
    change back.gcaFirst = l.node.level
    rw [hgc]
    exact h.first hf
  · intro hf
    change back.gcaFirst < l.node.level
    rw [hgc]
    exact h.other hf
  · change 0 < back.wsCap
    rw [hcap]
    exact h.capacity
  · exact Or.inl (recover_nonpos (hr.leave tv).nonpos (n + 2) l.node.level)

end Hex.GraphIso.Nauty.Sparse.Max
