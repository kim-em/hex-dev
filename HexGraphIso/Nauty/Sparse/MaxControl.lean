/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxGuideFirst
public import HexGraphIso.Nauty.Sparse.AncestorOrder
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Actual first preparation retains both reference labels and their
ancestor counters through refinement, recording, target selection and
the cheap check. -/
theorem Frame.firstParent_refs (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    let out := (f.firstParent G tcLevel bs tv).state
    out.firstlab = f.entry.firstlab ∧ out.gcaFirst = f.entry.gcaFirst ∧
      out.canonlab = f.entry.canonlab ∧ out.gcaCanon = f.entry.gcaCanon := by
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  let r := recordFirst f.level v.2.1 v.2.2
  have hf := chooseTarget_frame true (.ofGraph G) tcLevel f.level v.1 r
  have hg := (chooseTarget_controls true (.ofGraph G) tcLevel f.level v.1 r).1
  have hc := chooseTarget_ancestor true (.ofGraph G) tcLevel f.level v.1 r
  dsimp only [Frame.firstParent]
  unfold cheapCheck
  split <;> exact ⟨hf.2.2.1, hg, hf.2.2.2, hc⟩

/-- The actual off-path preparation retains the same reference fields,
including the comparison and hinted-target branches. -/
theorem Frame.otherParent_refs (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    let out := (f.otherParent G tcLevel bs tv).state
    out.firstlab = f.entry.firstlab ∧ out.gcaFirst = f.entry.gcaFirst ∧
      out.canonlab = f.entry.canonlab ∧ out.gcaCanon = f.entry.gcaCanon := by
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  let r := compareCodes f.level v.2.1 v.2.2
  have hf := chooseTarget_frame false (.ofGraph G) tcLevel f.level v.1 r
  have hr := compareCodes_frame f.level v.2.1 v.2.2
  have hg := (chooseTarget_controls false (.ofGraph G) tcLevel f.level v.1 r).1
  have hrg := (gcaPolicy (.ofGraph G) 0 tcLevel).compare f.level v.2.1 v.2.2
  have hc := chooseTarget_ancestor false (.ofGraph G) tcLevel f.level v.1 r
  dsimp only [Frame.otherParent]
  unfold cheapCheck
  split <;> exact ⟨hf.2.2.1.trans hr.2.2.1, hg.trans hrg, hf.2.2.2.trans hr.2.2.2,
    hc.trans (compare_canon f.level v.2.1 v.2.2)⟩

theorem Guides.first_prepare {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    {parents : Parents n} (h : Guides G tcLevel f.entry parents) (bs : List Nat) (tv : Nat) :
    Guides G tcLevel (f.firstParent G tcLevel bs tv).state parents := by
  obtain ⟨hf, hg, hc, ha⟩ := f.firstParent_refs G tcLevel bs tv
  exact h.fields hf hg hc ha

theorem Guides.other_prepare {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    {parents : Parents n} (h : Guides G tcLevel f.entry parents) (bs : List Nat) (tv : Nat) :
    Guides G tcLevel (f.otherParent G tcLevel bs tv).state parents := by
  obtain ⟨hf, hg, hc, ha⟩ := f.otherParent_refs G tcLevel bs tv
  exact h.fields hf hg hc ha

/-- A newly prepared sweep has no reference pointing to an unvisited
child of its own level. Earlier covered references remain in the scope. -/
theorem Frame.firstParent_guided {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    (hf : f.entry.gcaFirst < f.level) (hc : f.entry.gcaCanon < f.level)
    (bs : List Nat) (tv : Nat) : (f.firstParent G tcLevel bs tv).Guided G tcLevel := by
  have hr := f.firstParent_refs G tcLevel bs tv
  exact Parent.Guided.vacuous (by rw [hr.2.1]; exact hf) (by rw [hr.2.2.2]; exact hc)

theorem Frame.otherParent_guided {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    (hf : f.entry.gcaFirst < f.level) (hc : f.entry.gcaCanon < f.level)
    (bs : List Nat) (tv : Nat) : (f.otherParent G tcLevel bs tv).Guided G tcLevel := by
  have hr := f.otherParent_refs G tcLevel bs tv
  exact Parent.Guided.vacuous (by rw [hr.2.1]; exact hf) (by rw [hr.2.2.2]; exact hc)

/-- First-child bookkeeping and recovery set both ancestors to the
receiving parent. The canonical lower bound comes from the literal
first-path call, including all of its later siblings. -/
theorem Parent.firstBack_counters {G : Hex.SparseGraph n} {tcLevel fuel last : Nat}
    {p : Parent n} {leaf : State n}
    (path : let ch := p.child G tcLevel
      Generic.FirstPath (.ofGraph G) tcLevel fuel ch.level ch.numcells ch.entry last leaf) :
    let out := p.firstBack G tcLevel fuel
    out.gcaFirst = p.node.level ∧ out.gcaCanon = p.node.level := by
  let ch := p.child G tcLevel
  let raw := (Generic.node true (.ofGraph G) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild p.chosen (afterChildFirst p.node.level p.chosen raw)
  have hf : p.node.level ≤ raw.gcaCanon := firstPath_canon path
    (by change p.node.level ≤ p.node.level + 1; omega)
  constructor
  · exact (gcaPolicy (.ofGraph G) (n + 2) tcLevel).recover p.node.level left
  · change (Nauty.recover (n + 2) p.node.level left).gcaCanon = _
    rw [recover_canon]
    change min p.node.level raw.gcaCanon = p.node.level
    exact Nat.min_eq_left hf

/-- Off-path child return preserves positivity and counter order, and
native recovery supplies the upper bound for the next child entry. -/
theorem Parent.Valid.back_counters {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} (h : p.Valid G tcLevel) (hf : 0 < p.state.gcaFirst)
    (hl : p.state.gcaFirst ≤ p.node.level) (ho : p.state.gcaFirst ≤ p.state.gcaCanon) :
    let out := p.back G.graph tcLevel fuel
    0 < out.gcaFirst ∧ out.gcaFirst ≤ out.gcaCanon ∧ out.gcaCanon ≤ p.node.level := by
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild p.chosen raw
  let out := p.back G.graph tcLevel fuel
  have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hfirst : ch.entry.gcaFirst = p.state.gcaFirst := by
    dsimp only [ch, Parent.child]; cases p.first <;> rfl
  have hcanon : ch.entry.gcaCanon = p.state.gcaCanon := by
    dsimp only [ch, Parent.child]; cases p.first <;> rfl
  obtain ⟨hkeep, horder⟩ := node_order (tcLevel := tcLevel) (fuel := fuel) hn h.child.positive h.child.node
    (by rw [hfirst]; change p.state.gcaFirst ≤ p.node.level + 1; omega)
    (by rw [hfirst, hcanon]; exact ho)
  have hg : out.gcaFirst = p.state.gcaFirst :=
    ((gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover p.node.level left).trans (hkeep.trans hfirst)
  have hc : out.gcaCanon = min p.node.level raw.gcaCanon := by
    change (Nauty.recover (n + 2) p.node.level left).gcaCanon = _
    exact recover_canon p.node.level left
  change raw.gcaFirst ≤ raw.gcaCanon at horder
  have hr : raw.gcaFirst = p.state.gcaFirst := hkeep.trans hfirst
  change 0 < out.gcaFirst ∧ out.gcaFirst ≤ out.gcaCanon ∧ out.gcaCanon ≤ p.node.level
  rw [hg, hc]
  omega

end Hex.GraphIso.Nauty.Sparse.Max
