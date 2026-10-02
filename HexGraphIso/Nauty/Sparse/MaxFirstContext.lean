/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxNode
public import HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxDescent
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxRank
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- First-descent invariants before any leaf has been installed. Saved
ancestor ranks and guides are local facts about the selected first child;
reference containment is established only when that child's first leaf
exists. The executable workspace and path invariants are retained too. -/
structure FirstInput (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat)
    (f : Frame n) (parents : Parents n) : Prop where
  entry : FirstEntry G f
  scope : Scope G tcLevel f [] f.entry parents
  guides : Guides G.graph tcLevel f.entry parents
  ranked : ∀ t p, parents t = some p → p.Ranked G.graph tcLevel
  orbits : OrbitTrace G f.entry
  first : f.entry.gcaFirst = 0
  canon : f.entry.gcaCanon = 0
  empty : f.entry.genTrace = #[]
  capacity : 0 < f.entry.wsCap
  path : PathInv G f.level f.entry
  pairs : PairsOk G f.entry
  boundary : CheapBoundary G f.level f.entry
  bound : f.entry.noncheaplevel ≤ f.level

/-- Stable colour initialization establishes the complete first-descent
context directly from the native arrays and empty ancestor map. -/
theorem FirstInput.initial (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    FirstInput G tcLevel ⟨1, p.2.length, [], initial (.ofGraph G.graph) p.1 p.2⟩ (fun _ => none) := by
  refine ⟨FirstEntry.initial G hn, Scope.root G tcLevel _ _ _ [],
    Guides.root G.graph tcLevel _, ?_, OrbitTrace.initial G _ _, rfl, rfl, rfl,
    by change 0 < 500; decide, initial_pathInv G, initial_pairs G _ _, initial_boundary G hn, Nat.le_refl _⟩
  intro t p hp
  cases hp

/-- Taking the native first cursor preserves the first-descent context.
Its suspended rank follows from the complete selected window and the
literal minimum cursor; the first reference is still uninstalled. -/
theorem FirstInput.child {G : GraphIso.Sparse.Colored n k} {tcLevel tv : Nat}
    {f : Frame n} {parents : Parents n} (h : FirstInput G tcLevel f parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv) :
    let p := f.firstParent G.graph tcLevel [] tv
    FirstInput G tcLevel (p.child G.graph tcLevel) (parents.push p) := by
  let l : Loop n := ⟨f, true⟩
  let p := f.firstParent G.graph tcLevel [] tv
  let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let ready := cheapCheck true f.level r.2.2.2.2
  let c := l.cell G.graph tcLevel
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  have hm := VSet.nextElem_mem htv
  have hp : p.Valid G tcLevel := h.entry.frame.first_parent h.entry.shape hi hm []
  have hselected := l.selected (tcLevel := tcLevel) h.entry.frame hi (by intro he; cases he)
  have hcell : c.Valid G := hselected.1
  have hset : r.2.2.1 = c.vertices := hselected.2
  have hframe : FrameOut G f.level f.level c.entry ready := (l.prepared h.entry.frame).2
  have hcover : c.Cover G.graph tcLevel (Remaining (some tv) r.2.2.1) (State.key G.graph [] ready) := by
    have hc := Cell.Cover.initial G.graph tcLevel c (State.key G.graph [] ready)
    rw [← hset, htv] at hc
    exact hc
  have hrank : p.Ranked G.graph tcLevel := by
    have hh := l.ranked (bs := []) (cell := r.2.2.1) hcell hframe hp.ready hcover
    simpa only [l, p, ready, r, Loop.parent, Loop.prepare, Frame.firstParent, Generic.prepareFirst,
      policy, Generic.Policy.visit, Generic.Policy.recordFirst,
      Generic.Policy.chooseTarget, ite_true] using hh
  have hguid : p.Guided G.graph tcLevel :=
    f.firstParent_guided (by rw [h.first]; exact h.entry.frame.positive)
      (by rw [h.canon]; exact h.entry.frame.positive) [] tv
  have href := f.firstParent_refs G.graph tcLevel [] tv
  have hcap : ready.wsCap = f.entry.wsCap :=
    l.preserve (capacityPolicy (.ofGraph G.graph) (n + 2) tcLevel f.entry.wsCap) rfl
  have ho : OrbitTrace G ready := l.preserve (orbitPolicy G (n + 2) tcLevel) h.orbits
  have hpath : PathInv G f.level r.2.2.2.2 :=
    ((h.path.visit h.entry.frame.node).record (f.code G.graph)).target true tcLevel r.1
  have hb : CheapBoundary G f.level r.2.2.2.2 :=
    ((h.boundary.visit hn h.entry.frame.positive h.entry.frame.node).record (f.code G.graph)).target true tcLevel r.1
  have hready := (h.entry.frame.node.prepare (tcLevel := tcLevel) hn h.entry.frame.positive).1
  have hbound : ready.noncheaplevel ≤ f.level + 1 := by
    apply cheap_bound true
    rw [prepareFirst_noncheap]
    exact h.bound
  refine ⟨h.entry.child hi hm, h.scope.first_child h.entry.frame h.entry.shape hi hm,
    (h.guides.first_prepare [] tv).child hguid, ?_,
    (orbitPolicy G (n + 2) tcLevel).child true f.level r.2.1.toNat tv ready ho,
    ?_, ?_, ?_, ?_, (hpath.cheap true).child hn h.entry.frame.positive hp.ready true hp.target hm,
    (((((h.pairs.visit f.level f.numcells).record f.level (f.code G.graph)).target
      true tcLevel f.level r.1).cheap true f.level).child true f.level r.2.1.toNat tv),
    (hb.cheap hn h.entry.frame.positive hready true).child h.entry.frame.positive true hp.target hm, hbound⟩
  · intro t q hq
    by_cases he : t = f.level
    · change (parents.push p) t = some q at hq
      have hl : p.node.level = f.level := rfl
      simp only [Parents.push, hl, ite_eq_left he] at hq
      cases hq
      exact hrank
    · change (parents.push p) t = some q at hq
      have hl : p.node.level = f.level := rfl
      simp only [Parents.push, hl, ite_eq_right he] at hq
      exact h.ranked t q hq
  · change p.state.gcaFirst = 0
    rw [href.2.1]
    exact h.first
  · change p.state.gcaCanon = 0
    rw [href.2.2.2]
    exact h.canon
  · change ready.genTrace = #[]
    unfold ready cheapCheck
    split <;> exact (prepareFirst_trace (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).trans h.empty
  · change 0 < ready.wsCap
    rw [hcap]
    exact h.capacity

end Hex.GraphIso.Nauty.Sparse.Max
