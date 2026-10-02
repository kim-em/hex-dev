/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxScope
public import HexGraphIso.Nauty.Sparse.MaxPrepare
public import HexGraphIso.Nauty.Sparse.CodeNode
public import HexGraphIso.Nauty.Sparse.BoundaryControl
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.ReturnCodes
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- First preparation and its cheap check retain the incoming native key. -/
theorem Frame.firstParent_key (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    State.key G bs (f.firstParent G tcLevel bs tv).state = State.key G bs f.entry := by
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  have he : (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).2.2.2.2.canonlab =
      f.entry.canonlab := (chooseTarget_frame true (.ofGraph G) tcLevel f.level v.1
        (recordFirst f.level v.2.1 v.2.2)).2.2.2
  dsimp only [Frame.firstParent]
  unfold cheapCheck
  split <;> simp only [State.key, he]

theorem Frame.firstParent_boundary (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    (f.firstParent G tcLevel bs tv).state.noncheaplevel = f.entry.noncheaplevel ∨
      f.level ≤ (f.firstParent G tcLevel bs tv).state.noncheaplevel := by
  dsimp only [Frame.firstParent]
  unfold cheapCheck
  split
  · exact Or.inr (by change f.level ≤ f.level + 1; omega)
  · exact Or.inl (prepareFirst_noncheap _ _ _ _ _)

/-- Off-path preparation and its cheap check retain the incoming native key. -/
theorem Frame.otherParent_key (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    State.key G bs (f.otherParent G tcLevel bs tv).state = State.key G bs f.entry := by
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  have he : (prepareOther (.ofGraph G) tcLevel f.level f.numcells f.entry).2.2.2.2.2.canonlab =
      f.entry.canonlab := (chooseTarget_frame false (.ofGraph G) tcLevel f.level v.1
        (compareCodes f.level v.2.1 v.2.2)).2.2.2.trans (compareCodes_frame f.level v.2.1 v.2.2).2.2.2
  dsimp only [Frame.otherParent]
  unfold cheapCheck
  split <;> simp only [State.key, he]

theorem Frame.otherParent_boundary (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    (f.otherParent G tcLevel bs tv).state.noncheaplevel = f.entry.noncheaplevel ∨
      f.level ≤ (f.otherParent G tcLevel bs tv).state.noncheaplevel := by
  have he : (prepareOther (.ofGraph G) tcLevel f.level f.numcells f.entry).2.2.2.2.2.noncheaplevel =
      f.entry.noncheaplevel := by
    dsimp only [prepareOther]
    rw [(chooseTarget_controls false _ _ _ _ _).2]
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]
    rfl
  dsimp only [Frame.otherParent]
  unfold cheapCheck
  split
  · exact Or.inr (by change f.level ≤ f.level + 1; omega)
  · exact Or.inl he

/-- The ancestor invariant is established at the actual first child,
including its prepared target and inherited cheap shape. -/
theorem Scope.first_child {G : GraphIso.Sparse.Colored n k} {tcLevel tv : Nat}
    {f : Frame n} {bs : List Nat} {parents : Parents n}
    (h : Scope G tcLevel f bs f.entry parents) (hv : f.Valid G)
    (hs : FirstShape G.graph f.level f.numcells f.entry)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (hm : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.mem tv = true) :
    let p := f.firstParent G.graph tcLevel bs tv
    Scope G tcLevel (p.child G.graph tcLevel) bs (p.child G.graph tcLevel).entry (parents.push p) := by
  intro p
  have hg : Grows (State.key G.graph bs f.entry) (State.key G.graph bs p.state) := by
    rw [f.firstParent_key]
    exact Grows.refl _
  have hp : Scope G tcLevel f bs p.state parents :=
    h.change hg (f.firstParent_boundary _ _ _ _)
  exact hp.push (hv.first_parent hs hi hm bs)

/-- Native off-path preparation establishes the child scope from the
incoming comparison machines; all hinted-target obligations are discharged. -/
theorem Scope.other_child {G : GraphIso.Sparse.Colored n k} {tcLevel tv : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : Scope G tcLevel f bs f.entry parents) (hv : f.Valid G)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (hm : (prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.1.mem tv = true) :
    let p := f.otherParent G.graph tcLevel bs tv
    Scope G tcLevel (p.child G.graph tcLevel) bs (p.child G.graph tcLevel).entry (parents.push p) := by
  intro p
  have hg : Grows (State.key G.graph bs f.entry) (State.key G.graph bs p.state) := by
    rw [f.otherParent_key]
    exact Grows.refl _
  have hp : Scope G tcLevel f bs p.state parents :=
    h.change hg (f.otherParent_boundary _ _ _ _)
  exact hp.push (hv.other_parent hc hi hm)

/-- A complete actual off-path call preserves every suspended ancestor.
Both required effects come from the executed code and boundary proofs,
independently of the outstanding maximum theorem. -/
theorem Scope.node {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : Scope G tcLevel f bs f.entry parents) (hv : f.Valid G)
    (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (hc : Comparison G.graph f.codes bs fs f.entry) (hf : n ≤ f.codes.length + fuel) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2
    ∃ ds, ReturnCodes G.graph f.codes ds fs out ∧ Scope G tcLevel f ds out parents := by
  have hn : 0 < n := by have := hv.positive; have := hv.depth; omega
  have hlen := hv.length
  have he := node_codes G hn tcLevel fuel f.codes bs fs f.numcells f.entry
    (by simpa only [hlen] using hi) hf hc
  rw [hlen] at he
  obtain ⟨ds, hr, hg⟩ := he
  exact ⟨ds, hr, h.change hg
    (node_boundary (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry (by omega))⟩

end Hex.GraphIso.Nauty.Sparse.Max
