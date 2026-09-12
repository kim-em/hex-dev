/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxParent
public import HexGraphIso.Nauty.Sparse.FirstCheap
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxChoice
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.SmallCell.Transitive
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The parent suspended by an actual first-child call. -/
def Frame.firstParent (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) : Parent n :=
  let p := Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry
  ⟨f, true, cheapCheck true f.level p.2.2.2.2, p.2.1.toNat, p.2.2.1, tv, bs⟩

/-- The parent suspended by an actual off-path child call. -/
def Frame.otherParent (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) : Parent n :=
  let p := prepareOther (.ofGraph G) tcLevel f.level f.numcells f.entry
  ⟨f, false, cheapCheck false f.level p.2.2.2.2.2, p.2.2.1.toNat, p.2.2.2.1, tv, bs⟩

/-- Native first preparation and its inherited cheap shape establish every
suspended-parent field before descent. -/
theorem Frame.Valid.first_parent {G : GraphIso.Sparse.Colored n k} {tcLevel tv : Nat}
    {f : Frame n} (h : f.Valid G) (hs : FirstShape G.graph f.level f.numcells f.entry)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (hm : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.mem tv = true)
    (bs : List Nat) : (f.firstParent G.graph tcLevel bs tv).Valid G tcLevel := by
  let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
  let p := Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hr := (h.node.visit_ready hn h.positive).record v.2.1
  have ht := hr.ready.target_frame true tcLevel
  have hh := ht.ready.cheap true
  have hall := (hr.trans ht).trans hh
  have hp := (h.node.prepare (tcLevel := tcLevel) hn h.positive).2
  refine ⟨h, hi, hall.ready, hall.frame, hp.of_out hh.frame.effect, hm, ?_, ?_⟩
  · exact Or.inl (f.first_target hi)
  · intro hc
    have hshape := hs.prepare (tcLevel := tcLevel) h.node hc
    have he := (prepareFirst_partition (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.1
    change NodeShape n f.level (cheapCheck true f.level p.2.2.2.2).ptn
    unfold cheapCheck
    split <;> change NodeShape n f.level p.2.2.2.2.ptn <;> rw [he] <;> exact hshape

/-- Off-path preparation proves the complete parent invariant directly
from its native comparison and guard, including the hinted-target branch. -/
theorem Frame.Valid.other_parent {G : GraphIso.Sparse.Colored n k} {tcLevel tv : Nat}
    {f : Frame n} {bs fs : List Nat} (h : f.Valid G)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (hm : (prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.1.mem tv = true) :
    (f.otherParent G.graph tcLevel bs tv).Valid G tcLevel := by
  let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hr := (h.node.visit_ready hn h.positive).compare v.2.1
  have ht := hr.ready.target_frame false tcLevel
  have hh := ht.ready.cheap false
  have hall := (hr.trans ht).trans hh
  have hp := hr.ready.target hn h.positive false tcLevel
  refine ⟨h, hi, hall.ready, hall.frame, hp.of_out hh.frame.effect, hm, ?_, ?_⟩
  · have he : State.key G.graph bs (cheapCheck false f.level p.2.2.2.2.2) =
        State.key G.graph bs p.2.2.2.2.2 := by
      unfold cheapCheck
      split <;> rfl
    change f.Choice G.graph tcLevel p.2.2.1.toNat
      (State.key G.graph bs (cheapCheck false f.level p.2.2.2.2.2))
    rw [he]
    exact h.choice hc hi
  · intro hbound
    have hg : cheapautom p.2.2.2.2.2.ptn f.level n = true := by
      change (cheapCheck false f.level p.2.2.2.2.2).noncheaplevel ≤ f.level at hbound
      cases he : cheapautom p.2.2.2.2.2.ptn f.level n with
      | true => rfl
      | false =>
        simp only [cheapCheck, Bool.not_false, Bool.true_or, he, Bool.and_self, ite_true] at hbound
        omega
    have hshape := (ht.ready.small hn h.positive hg).shape
    change NodeShape n f.level (cheapCheck false f.level p.2.2.2.2.2).ptn
    unfold cheapCheck
    split <;> exact hshape

end Hex.GraphIso.Nauty.Sparse.Max
