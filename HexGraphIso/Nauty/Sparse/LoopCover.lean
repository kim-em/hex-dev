/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxLoop
public import HexGraphIso.Nauty.Sparse.MaxRank
public import HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxChoice
import all HexGraphIso.Nauty.Sparse.MaxScatter
import all HexGraphIso.Nauty.Sparse.MaxRank
import all HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A recovered window at the selected coordinate is the same complete
cell as the frozen selection, regardless of mutable filtering. -/
theorem Cell.Valid.member {G : GraphIso.Sparse.Colored n k} {c : Cell n}
    {st : State n} {len v : Nat} (h : c.Valid G)
    (he : FrameOut G c.level c.level c.entry st)
    (hw : IsCell st.ptn c.level c.tc len)
    (hv : (windowSet n st.lab c.tc len).mem v = true) : c.vertices.mem v = true := by
  have hc := isCell_of_low he.effect.low h.window
  have hlen : len = c.len := by
    have hh := isCell_disjoint_or_eq hc hw
    change c.tc + len ≤ c.tc ∨ c.tc + c.len ≤ c.tc ∨ c.tc = c.tc ∧ c.len = len at hh
    rcases hh with hh | hh | hh
    · exact False.elim ((Nat.not_le_of_gt (Nat.lt_add_of_pos_right hw.1)) hh)
    · exact False.elim ((Nat.not_le_of_gt (Nat.lt_add_of_pos_right hc.1)) hh)
    · exact hh.2.symm
  change (windowSet n c.entry.lab c.tc c.len).mem v = true
  have hwindow : windowSet n c.entry.lab c.tc c.len = windowSet n st.lab c.tc c.len :=
    he.effect.window_eq h.window
  rw [hwindow, ← hlen]
  exact hv

/-- Exhausting the actual target covers its native node. If the target
was hinted, the existing negative-prefix alternative covers the node. -/
theorem Loop.cover {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    {best : Option (Key n)} (h : l.node.Valid G)
    (hi : (visit (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry).1 < n)
    (hc : (l.cell G.graph tcLevel).Valid G)
    (ht : l.node.Choice G.graph tcLevel (l.cell G.graph tcLevel).tc best)
    (hd : ∀ v, (l.cell G.graph tcLevel).vertices.mem v = true →
      Covers ((l.cell G.graph tcLevel).key G.graph tcLevel v) best) :
    Covers (l.node.key G.graph tcLevel) best := by
  rcases ht with ht | ht
  · let c := l.cell G.graph tcLevel
    let d := l.node.target G.graph tcLevel
    have hv := h.target (tcLevel := tcLevel) hi
    have hw : IsCell c.entry.ptn c.level c.tc d.len := by
      rw [ht]
      exact hv.window
    have hlen : c.len = d.len := by
      have hh := isCell_disjoint_or_eq hc.window hw
      change c.tc + d.len ≤ c.tc ∨ c.tc + c.len ≤ c.tc ∨ c.tc = c.tc ∧ c.len = d.len at hh
      rcases hh with hh | hh | hh
      · exact False.elim ((Nat.not_le_of_gt (Nat.lt_add_of_pos_right hw.1)) hh)
      · exact False.elim ((Nat.not_le_of_gt (Nat.lt_add_of_pos_right hc.window.1)) hh)
      · exact hh.2
    have he : c = d := by
      change (⟨c.level, c.numcells, c.tc, c.len, c.codes, c.entry⟩ : Cell n) =
        ⟨c.level, c.numcells, d.tc, d.len, c.codes, c.entry⟩
      have htc : c.tc = d.tc := ht
      rw [htc, hlen]
    apply (h.target_cover hi).mpr
    change ∀ v, d.vertices.mem v = true → Covers (d.key G.graph tcLevel v) best
    rw [← he]
    exact hd
  · obtain ⟨tail, he⟩ := h.tail tcLevel
    rw [he]
    exact ht tail

/-- Ranked coverage of the actual selected cell supplies the suspended
parent's smaller-vertex invariant, for hinted and unhinted selections. -/
theorem Loop.ranked {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    {st : State n} {bs : List Nat} {cell : VSet n} {tv : Nat}
    (hc : (l.cell G.graph tcLevel).Valid G)
    (he : FrameOut G l.node.level l.node.level (l.cell G.graph tcLevel).entry st)
    (hs : Ready G l.node.level (l.cell G.graph tcLevel).numcells st)
    (hd : (l.cell G.graph tcLevel).Cover G.graph tcLevel (Remaining (some tv) cell)
      (State.key G.graph bs st)) :
    (l.parent G.graph tcLevel st bs cell tv).Ranked G.graph tcLevel := by
  intro len hw v hv hlt
  have hmem := hc.member he hw hv
  have hk := l.vertex_key (bs := bs) (cell := cell) (tv := tv) hc he hs hmem
  rw [hk]
  exact hd.earlier hmem hlt

/-- The receiving parent's canonical guide is also a guide for the
frozen actual cell used by both native pruning filters. -/
theorem Loop.canon_guide {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    {st : State n} {bs : List Nat} {cell : VSet n} {tv : Nat}
    (hc : (l.cell G.graph tcLevel).Valid G)
    (he : FrameOut G l.node.level l.node.level (l.cell G.graph tcLevel).entry st)
    (hs : Ready G l.node.level (l.cell G.graph tcLevel).numcells st)
    (hg : (l.parent G.graph tcLevel st bs cell tv).Guided G.graph tcLevel) :
    CanonGuide l.node.level (l.cell G.graph tcLevel).tc (l.cell G.graph tcLevel).entry
      ((l.cell G.graph tcLevel).key G.graph tcLevel) (State.key G.graph bs st) st := by
  let c := l.cell G.graph tcLevel
  intro hlevel
  obtain ⟨v, hv, hat, hp⟩ := hg.canonical hlevel
  change st.canonlab[c.tc]! = v at hat
  have hperm : cellsPerm c.entry.ptn c.level c.entry.lab st.canonlab := by
    apply cellsPerm_trans he.effect.perm
    intro a len ha
    exact hp a len (isCell_of_low he.effect.low ha)
  have hmem : c.vertices.mem v = true := by
    apply mem_windowSet.mpr
    have hm : v ∈ segN c.entry.lab c.tc c.len := by
      apply (hperm c.tc c.len hc.window).mem_iff.mpr
      rw [← hat]
      exact mem_segN_iff.mpr ⟨0, hc.window.1, by simp⟩
    refine ⟨?_, hm⟩
    obtain ⟨o, ho, ho'⟩ := mem_segN_iff.mp hm
    rw [← ho']
    have hsize : c.entry.lab.size = n := hc.ready.ok.labSize
    exact (labOk_of_reach hc.ready.ok.labSize hc.ready.ok.reach) _ (by
      change c.tc + o < c.entry.lab.size
      rw [hsize]
      have hrange : c.tc + c.len ≤ n := hc.range
      omega)
  have hk := l.vertex_key (bs := bs) (cell := cell) (tv := tv) hc he hs hmem
  rw [hk] at hv
  exact ⟨v, hv, hat, hperm⟩

end Hex.GraphIso.Nauty.Sparse.Max
