/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxAutoFirst
public import HexGraphIso.Nauty.Sparse.CanonScatter
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The native canonical automorphism verdict is necessarily discrete. -/
theorem canon_discrete {g : Graph n} {level numcells : Nat} {st : State n}
    (h : (classify g level numcells st).1 = .autoCanon) : numcells = n := by
  by_cases hn : numcells = n
  · exact hn
  rw [classify_eq] at h
  split at h
  · cases h
  · simp only [bne_iff_ne.mpr hn, ite_true] at h
    cases h

/-- The canonical verdict retains the reference and its ancestor through
the actual preparation, native classifier, orbit update and leaf action. -/
theorem Frame.emit_canon {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    (ha : let p := prepareOther (.ofGraph G) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G) f.level p.1 p.2.2.2.2.2).1 = .autoCanon) :
    (f.emit G tcLevel).2.canonlab = f.entry.canonlab ∧
      (f.emit G tcLevel).2.gcaCanon = f.entry.gcaCanon := by
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  let p := prepareOther (.ofGraph G) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G) f.level p.1 p.2.2.2.2.2
  have hc : c.1 = .autoCanon := ha
  change (leafExit c.1 f.level c.2).2.canonlab = f.entry.canonlab ∧
    (leafExit c.1 f.level c.2).2.gcaCanon = f.entry.gcaCanon
  rw [hc, autoCanon_ref, autoCanon_ancestor]
  constructor
  · exact (classify_frame (.ofGraph G) f.level p.1 p.2.2.2.2.2).2.2.2.trans
      ((chooseTarget_frame false (.ofGraph G) tcLevel f.level v.1
        (compareCodes f.level v.2.1 v.2.2)).2.2.2.trans (compareCodes_frame f.level v.2.1 v.2.2).2.2.2)
  · exact (classify_ancestor (.ofGraph G) f.level p.1 p.2.2.2.2.2).trans
      ((chooseTarget_ancestor false (.ofGraph G) tcLevel f.level v.1
        (compareCodes f.level v.2.1 v.2.2)).trans (compare_canon f.level v.2.1 v.2.2))

/-- The actual canonical-reference emission retains its native checked
scatter, including classification after a failed first-reference scan. -/
theorem Frame.Valid.canon_scatter {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} (h : f.Valid G) (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (ha : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .autoCanon) :
    let out := (f.emit G.graph tcLevel).2
    Automorphism G out.workperm ∧ out.canonlab.size = n ∧
      ∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]! := by
  intro out
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hr := hi.prepare hn h.positive
  have hc : c.1 = .autoCanon := ha
  have hauto := classify_auto hn hr.ready hr.history hr.saved.store hr.saved.canonical
    hr.saved.first hr.saved.work (Or.inr hc)
  have hw : out.workperm = c.2.workperm := leafExit_workperm c.1 f.level c.2
  have href : out.canonlab = p.2.2.2.2.2.canonlab := by
    change (leafExit c.1 f.level c.2).2.canonlab = _
    rw [hc, autoCanon_ref]
    exact (classify_frame (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).2.2.2
  have hl : out.lab = p.2.2.2.2.2.lab :=
    (leafExit_frame c.1 f.level c.2).1.trans
      (classify_frame (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1
  refine ⟨hw ▸ hauto, href ▸ hr.saved.canonical.1, ?_⟩
  intro i hiN
  rw [hw, href, hl]
  exact classify_canon_map hc hr.saved.work hr.saved.canonical.1
    (isPerm_of_cellsReach hr.saved.canonical.1 hn hr.saved.canonical.2) i hiN

/-- A canonical automorphism returning to its canonical ancestor satisfies
the full maximum contract for either short flag. The separate coset return
to an earlier first ancestor has a different coverage argument. -/
theorem Frame.Valid.auto_canon {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} {short : Bool} (h : f.Valid G)
    (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hs : Scope G tcLevel f bs f.entry parents) (hg : Guides G.graph tcLevel f.entry parents)
    (hpos : 0 < f.entry.gcaCanon) (hlt : f.entry.gcaCanon < f.level)
    (ha : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .autoCanon)
    (hexit : (f.emit G.graph tcLevel).1 = .unwind f.entry.gcaCanon short) :
    MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  let out := (f.emit G.graph tcLevel).2
  have hdone : (f.emit G.graph tcLevel).1 ≠ .done := by rw [hexit]; intro hh; cases hh
  obtain ⟨_, _, hbound, hcover⟩ := h.leaf_bound hi hc (canon_discrete ha)
  refine ⟨hbound, ?_⟩
  rw [hexit]
  refine ⟨by omega, ?_⟩
  split
  · exact hcover
  · rename_i hne
    obtain ⟨parent, hp⟩ := hs.complete f.entry.gcaCanon hpos hlt
    obtain ⟨_, _, hlevel, _⟩ := hs.valid f.entry.gcaCanon parent hp
    have hcanon : out.gcaCanon = f.entry.gcaCanon := (f.emit_canon ha).2
    have hreturned := hg.emit hs h hdone
    have hreference := hreturned.canonical f.entry.gcaCanon parent hp (Nat.le_of_eq hcanon)
    have he : parent.state.gcaCanon = parent.node.level :=
      hreference.1.symm.trans (hcanon.trans hlevel.symm)
    obtain ⟨v, hcovered, hat, hcontained⟩ := (hg.saved _ parent hp).canonical he
    have hscatter := h.canon_scatter hi ha
    have hchild : Covers ((parent.child G.graph tcLevel).key G.graph tcLevel) (State.best G.graph out) := by
      apply hs.emit_cover h hp hscatter.1 hscatter.2.1
      · rw [hreference.2]
        exact hcontained
      · exact hscatter.2.2
      · rw [hreference.2, hat]
        exact hcovered.grow ((hs.grows _ parent hp).trans hbound.grows)
    exact hs.child_witness hp (by omega) hchild

end Hex.GraphIso.Nauty.Sparse.Max
