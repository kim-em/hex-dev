/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SelectedCell
public import HexGraphIso.Nauty.Sparse.MaxPrepare
public import HexGraphIso.Nauty.Sparse.MaxScatter
public import HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxScatter
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A native sweep frozen at the node whose target it traverses. -/
structure Loop (n : Nat) where
  node : Frame n
  first : Bool

/-- The literal native preparation, including code comparison, target
hinting and the cheap guard. -/
def Loop.prepare (G : Hex.SparseGraph n) (tcLevel : Nat) (l : Loop n) :
    Nat × Int × VSet n × Nat × State n :=
  let f := l.node
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  let st := if l.first then recordFirst f.level v.2.1 v.2.2 else compareCodes f.level v.2.1 v.2.2
  let t := chooseTarget l.first (.ofGraph G) tcLevel f.level v.1 st
  (v.1, t.1, t.2.1, t.2.2.1, cheapCheck l.first f.level t.2.2.2)

/-- The complete selected cell, before any orbit skip or target filter.
Its coordinates come from the actual dispatch, including hinted targets;
its frozen ordering is the actual cached visit's ordering. -/
def Loop.cell (G : Hex.SparseGraph n) (tcLevel : Nat) (l : Loop n) : Cell n :=
  let p := l.prepare G tcLevel
  let v := visit (.ofGraph G) l.node.level l.node.numcells l.node.entry
  ⟨l.node.level, v.1, p.2.1.toNat, p.2.2.2.1, l.node.codes ++ [v.2.1], v.2.2⟩

/-- Suspending a selected child retains the actual sweep's target
coordinate while its state and remaining bitset may have changed. -/
def Loop.parent (G : Hex.SparseGraph n) (tcLevel : Nat) (l : Loop n)
    (st : State n) (bs : List Nat) (cell : VSet n) (tv : Nat) : Parent n :=
  ⟨l.node, l.first, st, (l.prepare G tcLevel).2.1.toNat, cell, tv, bs⟩

theorem Loop.first_parent (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    let l : Loop n := ⟨f, true⟩
    l.parent G tcLevel (l.prepare G tcLevel).2.2.2.2 bs (l.prepare G tcLevel).2.2.1 tv =
      f.firstParent G tcLevel bs tv := by
  simp only [Loop.parent, Loop.prepare, Frame.firstParent, Generic.prepareFirst,
    ite_true]
  rfl

theorem Loop.other_parent (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (bs : List Nat) (tv : Nat) :
    let l : Loop n := ⟨f, false⟩
    l.parent G tcLevel (l.prepare G tcLevel).2.2.2.2 bs (l.prepare G tcLevel).2.2.1 tv =
      f.otherParent G tcLevel bs tv := by
  simp only [Loop.parent, Loop.prepare, Frame.otherParent, prepareOther,
    Bool.false_eq_true, ite_false]

/-- Every prepared sweep retains the equitable visit and its exact
partition frame through recording, comparison, selection and the guard. -/
theorem Loop.prepared {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    (h : l.node.Valid G) :
    let c := l.cell G.graph tcLevel
    let st := (l.prepare G.graph tcLevel).2.2.2.2
    Ready G c.level c.numcells st ∧ FrameOut G c.level c.level c.entry st := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  let v := visit (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
  have hv := h.node.visit_ready hn h.positive
  have hr : Local G l.node.level v.1 v.2.2
      (if l.first then recordFirst l.node.level v.2.1 v.2.2
        else compareCodes l.node.level v.2.1 v.2.2) := by
    cases l.first with
    | true => exact hv.record v.2.1
    | false => exact hv.compare v.2.1
  have ht := hr.ready.target_frame l.first tcLevel
  have hh := ht.ready.cheap l.first
  exact ⟨hh.ready, ((hr.trans ht).trans hh).frame⟩

/-- Persistent native bookkeeping invariants pass through the literal
preparation sequence for either kind of sweep. -/
theorem Loop.preserve {G : Hex.SparseGraph n} {inf tcLevel : Nat} {l : Loop n}
    {P : State n → Prop} (h : Generic.Preserve (.ofGraph G) inf tcLevel P)
    (hi : P l.node.entry) : P (l.prepare G tcLevel).2.2.2.2 := by
  let v := visit (.ofGraph G) l.node.level l.node.numcells l.node.entry
  have hv : P v.2.2 := h.visit l.node.level l.node.numcells l.node.entry hi
  have hr : P (if l.first then recordFirst l.node.level v.2.1 v.2.2
      else compareCodes l.node.level v.2.1 v.2.2) := by
    cases l.first with
    | true => exact h.record _ _ _ hv
    | false => exact h.compare _ _ _ hv
  exact h.cheap _ _ _ (h.target _ _ _ _ hr)

/-- Internal native preparation selects the whole actual cell. Off-path
classification supplies the enabled target guard, without assuming an
unhinted target or any search-maximum theorem. -/
theorem Loop.selected {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    (h : l.node.Valid G)
    (hc : (visit (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry).1 < n)
    (hi : l.first = false →
      (classify (.ofGraph G.graph) l.node.level
        (prepareOther (.ofGraph G.graph) tcLevel l.node.level l.node.numcells l.node.entry).1
        (prepareOther (.ofGraph G.graph) tcLevel l.node.level l.node.numcells l.node.entry).2.2.2.2.2).1 =
          .internal) :
    (l.cell G.graph tcLevel).Valid G ∧
      (l.prepare G.graph tcLevel).2.2.1 = (l.cell G.graph tcLevel).vertices := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  let v := visit (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
  let before := if l.first then recordFirst l.node.level v.2.1 v.2.2
    else compareCodes l.node.level v.2.1 v.2.2
  have hv := h.node.visit_ready hn h.positive
  have hr : Ready G l.node.level v.1 before := by
    dsimp only [before]
    cases l.first with
    | true => exact (hv.record v.2.1).ready
    | false => exact (hv.compare v.2.1).ready
  have ho : l.first = true ∨ before.eqlevFirst = l.node.level ∨ 0 ≤ before.compCanon := by
    cases he : l.first with
    | true => exact Or.inl rfl
    | false =>
      right
      have hopen := chooseTarget_open (hi he)
      simpa only [before, he, Bool.false_eq_true, ite_false] using hopen
  have hs := hr.selected_cell (tcLevel := tcLevel) hn h.positive hc l.first ho
  have hlab : before.lab = v.2.2.lab := by
    dsimp only [before]
    cases l.first with
    | true => rfl
    | false => exact (compareCodes_frame _ _ _).1
  have hptn : before.ptn = v.2.2.ptn := by
    dsimp only [before]
    cases l.first with
    | true => rfl
    | false => exact (compareCodes_frame _ _ _).2.1
  rw [hlab, hptn] at hs
  refine ⟨⟨h.positive, ?_, hv, hs.1, hs.2.1, hs.2.2.1⟩, hs.2.2.2⟩
  change (l.node.codes ++ [_]).length = l.node.level
  simp only [List.length_append, List.length_singleton, h.length]

/-- The generic child entry is literally the individualization represented
by the complete selected cell, with the parent's current native state. -/
theorem Loop.child (G : Hex.SparseGraph n) (tcLevel : Nat) (l : Loop n)
    (st : State n) (bs : List Nat) (cell : VSet n) (tv : Nat) :
    (l.parent G tcLevel st bs cell tv).child G tcLevel =
      (l.cell G tcLevel).child l.first st tv := by
  simp only [Loop.parent, Parent.child, Frame.target, Loop.cell, Cell.child]

/-- Recovered sibling order changes neither the actual selected target's
vertex key nor the child subtree represented by that key. -/
theorem Loop.vertex_key {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    {st : State n} {bs : List Nat} {cell : VSet n} {tv v : Nat}
    (hc : (l.cell G.graph tcLevel).Valid G)
    (he : FrameOut G l.node.level l.node.level (l.cell G.graph tcLevel).entry st)
    (hs : Ready G l.node.level (l.cell G.graph tcLevel).numcells st)
    (hv : (l.cell G.graph tcLevel).vertices.mem v = true) :
    (l.parent G.graph tcLevel st bs cell tv).key G.graph tcLevel v =
      (l.cell G.graph tcLevel).key G.graph tcLevel v := by
  change (l.parent G.graph tcLevel st bs cell v).key G.graph tcLevel v = _
  have hk := Parent.child_key G.graph tcLevel (l.parent G.graph tcLevel st bs cell v)
  change ((l.parent G.graph tcLevel st bs cell v).child G.graph tcLevel).key G.graph tcLevel =
    (l.parent G.graph tcLevel st bs cell v).key G.graph tcLevel v at hk
  rw [← hk, Loop.child]
  exact hc.child_key he hs l.first hv tcLevel

end Hex.GraphIso.Nauty.Sparse.Max
