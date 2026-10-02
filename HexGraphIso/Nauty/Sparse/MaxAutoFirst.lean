/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxGuideReturn
public import HexGraphIso.Nauty.Sparse.MaxEmitter
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The actual first-reference emission retains its native automorphism
scatter, including admission through the cheap guard. The saved-history
and workspace premises come from the production code entry. -/
theorem Frame.Valid.first_scatter {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} (h : f.Valid G) (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (ha : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .autoFirst) :
    let out := (f.emit G.graph tcLevel).2
    Automorphism G out.workperm ∧ out.firstlab.size = n ∧
      ∀ i, i < n → out.workperm[out.firstlab[i]!]! = out.lab[i]! := by
  intro out
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hr := hi.prepare hn h.positive
  have hc : c.1 = .autoFirst := ha
  have hauto := classify_auto hn hr.ready hr.history hr.saved.store hr.saved.canonical
    hr.saved.first hr.saved.work (Or.inl hc)
  have hscatter := congrArg SearchState.workperm (classify_first (Prod.ext hc rfl)).2.2.1
  have hw : out.workperm = c.2.workperm := leafExit_workperm c.1 f.level c.2
  have hf : out.firstlab = p.2.2.2.2.2.firstlab :=
    (leafExit_frame c.1 f.level c.2).2.2.1.trans
      (classify_frame (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).2.2.1
  have hl : out.lab = p.2.2.2.2.2.lab :=
    (leafExit_frame c.1 f.level c.2).1.trans
      (classify_frame (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1
  refine ⟨hw ▸ hauto, hf ▸ hr.saved.first.1, ?_⟩
  intro i hiN
  rw [hw, hf, hl, hscatter]
  exact scatter_map hr.saved.work hr.saved.first.1
    (isPerm_of_cellsReach hr.saved.first.1 hn hr.saved.first.2) i hiN

/-- First-reference admission returns exactly to its retained first
ancestor and does not request a short filter. -/
theorem first_exit (level : Nat) (st : State n) :
    (leafExit .autoFirst level st).1 = .unwind (leafExit .autoFirst level st).2.gcaFirst false := by
  unfold leafExit
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd]
  split <;> rfl

/-- The actual first-reference leaf satisfies the full native maximum
return contract. Nonlocal coverage comes from its retained covered first
child and the emitted automorphism, using the derived ancestor geometry. -/
theorem Frame.Valid.auto_first {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} (h : f.Valid G)
    (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hs : Scope G tcLevel f bs f.entry parents) (hg : Guides G.graph tcLevel f.entry parents)
    (hpos : 0 < f.entry.gcaFirst) (hlt : f.entry.gcaFirst < f.level)
    (ha : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .autoFirst) :
    MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2
  let out := (f.emit G.graph tcLevel).2
  have hclass : c.1 = .autoFirst := ha
  have hdisc : p.1 = n := (classify_first (Prod.ext hclass rfl)).1
  have hexit : (f.emit G.graph tcLevel).1 = .unwind out.gcaFirst false := by
    change (leafExit c.1 f.level c.2).1 = .unwind (leafExit c.1 f.level c.2).2.gcaFirst false
    rw [hclass]
    exact first_exit f.level c.2
  have hdone : (f.emit G.graph tcLevel).1 ≠ .done := by rw [hexit]; intro hh; cases hh
  have hfirst : out.gcaFirst = f.entry.gcaFirst := by
    have he := node_gca (.ofGraph G.graph) (n + 2) tcLevel 1 f.level f.numcells f.entry
    rw [Generic.node, f.emit_step _ hdone] at he
    exact he
  rw [hfirst] at hexit
  obtain ⟨_, _, hbound, hcover⟩ := h.leaf_bound hi hc hdisc
  refine ⟨hbound, ?_⟩
  rw [hexit]
  refine ⟨by omega, ?_⟩
  split
  · exact hcover
  · rename_i hne
    obtain ⟨parent, hp⟩ := hs.complete f.entry.gcaFirst hpos hlt
    obtain ⟨_, _, hlevel, _⟩ := hs.valid f.entry.gcaFirst parent hp
    have hreturned := hg.emit hs h hdone
    have hreference := hreturned.first f.entry.gcaFirst parent hp (Nat.le_of_eq hfirst)
    have he : parent.state.gcaFirst = parent.node.level :=
      hreference.1.symm.trans (hfirst.trans hlevel.symm)
    obtain ⟨hcovered, hcontained⟩ := (hg.saved _ parent hp).first he
    have hscatter := h.first_scatter hi ha
    have hchild : Covers ((parent.child G.graph tcLevel).key G.graph tcLevel) (State.best G.graph out) := by
      apply hs.emit_cover h hp hscatter.1 hscatter.2.1
      · rw [hreference.2]
        exact hcontained
      · exact hscatter.2.2
      · rw [hreference.2]
        exact hcovered.grow ((hs.grows _ parent hp).trans hbound.grows)
    exact hs.child_witness hp (by omega) hchild

end Hex.GraphIso.Nauty.Sparse.Max
