/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxChoice
public import HexGraphIso.Nauty.Sparse.CodeScope
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxChoice
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A suspended native parent records the actual child selection and
the incumbent codes at that selection. Its mutable target may be filtered. -/
structure Parent (n : Nat) where
  node : Frame n
  first : Bool
  state : State n
  tc : Nat
  cell : VSet n
  chosen : Nat
  bs : List Nat

def Parent.child (G : Hex.SparseGraph n) (tcLevel : Nat) (p : Parent n) : Frame n :=
  let c := p.node.target G tcLevel
  ⟨p.node.level + 1, c.numcells + 1, c.codes,
    (policy (n := n)).child p.first p.node.level p.tc p.chosen p.state⟩

/-- The suspended entry retains its native frame and cheap shape. A
hinted target is allowed when its negative comparison already covers the
parent; the positive branch retains the original target coordinate. -/
structure Parent.Valid (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat) (p : Parent n) : Prop where
  node : p.node.Valid G
  internal : (visit (.ofGraph G.graph) p.node.level p.node.numcells p.node.entry).1 < n
  ready : Ready G p.node.level (p.node.target G.graph tcLevel).numcells p.state
  effect : FrameOut G p.node.level p.node.level (p.node.target G.graph tcLevel).entry p.state
  target : Generic.Target State.frame p.node.level p.tc p.cell p.state
  chosen : p.cell.mem p.chosen = true
  choice : p.node.Choice G.graph tcLevel p.tc (State.key G.graph p.bs p.state)
  small : p.state.noncheaplevel ≤ p.node.level → NodeShape n p.node.level p.state.ptn

theorem Parent.Valid.child {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {p : Parent n}
    (h : p.Valid G tcLevel) : (p.child G.graph tcLevel).Valid G := by
  have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  refine ⟨by dsimp [Parent.child]; omega, ?_,
    h.ready.child hn h.node.positive p.first h.target h.chosen⟩
  change (p.node.codes ++ [_]).length + 1 = p.node.level + 1
  simp only [List.length_append, List.length_singleton, h.node.length]

/-- A selected vertex belongs to the original unfiltered window whenever
the actual target coordinate agrees with the unhinted native target. -/
theorem Parent.Valid.member {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {p : Parent n}
    (h : p.Valid G tcLevel) (ht : p.tc = (p.node.target G.graph tcLevel).tc) :
    (p.node.target G.graph tcLevel).vertices.mem p.chosen = true := by
  let c := p.node.target G.graph tcLevel
  have hv := h.node.target (tcLevel := tcLevel) h.internal
  have hcell : IsCell p.state.ptn p.node.level c.tc c.len := isCell_of_low h.effect.effect.low hv.window
  obtain ⟨len, hwindow, hmem⟩ := h.target
  obtain ⟨hw, hl, _⟩ := hwindow (mem_ne_empty h.chosen)
  have hs : len = c.len := by
    rw [ht] at hw
    change IsCell p.state.ptn p.node.level c.tc len at hw
    have hsize : 1 < c.len := hv.size
    rcases isCell_disjoint_or_eq hcell hw with he | he | he <;> omega
  have he : windowSet n c.entry.lab c.tc c.len = windowSet n p.state.lab c.tc c.len :=
    h.effect.effect.window_eq hv.window
  change (windowSet n c.entry.lab c.tc c.len).mem p.chosen = true
  rw [he]
  apply mem_windowSet.mpr
  refine ⟨VSet.mem_lt h.chosen, ?_⟩
  have hm := hmem p.chosen h.chosen
  change p.chosen ∈ segN p.state.lab p.tc len at hm
  rwa [ht, hs] at hm

/-- A cheap parent's full key is covered already or equals the key of
its actual chosen child. The two cases are the literal target-choice
alternatives; no whole-search correctness is assumed. -/
theorem Parent.Valid.collapse {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {p : Parent n}
    (h : p.Valid G tcLevel) (hc : p.state.noncheaplevel ≤ p.node.level) :
    Covers (p.node.key G.graph tcLevel) (State.key G.graph p.bs p.state) ∨
      p.node.key G.graph tcLevel = (p.child G.graph tcLevel).key G.graph tcLevel := by
  rcases h.choice with ht | hd
  · right
    have hv := h.node.target (tcLevel := tcLevel) h.internal
    have hp : p.state.ptn = (p.node.target G.graph tcLevel).entry.ptn :=
      h.effect.effect.ptnEq hv.ready.ok h.ready.ok
    have hshape := h.small hc
    rw [hp] at hshape
    have hk := h.node.small_key h.internal hshape (h.member ht)
    have hchild : p.child G.graph tcLevel =
        (p.node.target G.graph tcLevel).child p.first p.state p.chosen := by
      dsimp only [Parent.child, Cell.child]
      rw [ht]
      rfl
    rw [hchild]
    exact hk.trans (hv.child_key h.effect h.ready p.first (h.member ht) tcLevel).symm
  · obtain ⟨tail, he⟩ := h.node.tail tcLevel
    exact Or.inl (he ▸ hd tail)

/-- Every actual selected child stays below the parent's allowed upper
bound. A hinted child is bounded by its negative code prefix, even when
it does not belong to the unhinted specification target. -/
theorem Parent.Valid.child_bound {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {p : Parent n}
    (h : p.Valid G tcLevel) :
    Key.Le ((p.child G.graph tcLevel).key G.graph tcLevel)
      (incMax (State.key G.graph p.bs p.state) (p.node.key G.graph tcLevel)) := by
  have hc : Covers ((p.child G.graph tcLevel).key G.graph tcLevel)
      (some (incMax (State.key G.graph p.bs p.state) (p.node.key G.graph tcLevel))) := by
    rcases h.choice with ht | hd
    · have hv := h.node.target (tcLevel := tcLevel) h.internal
      have hm := h.member ht
      have hchild : p.child G.graph tcLevel =
          (p.node.target G.graph tcLevel).child p.first p.state p.chosen := by
        dsimp only [Parent.child, Cell.child]
        rw [ht]
        rfl
      rw [hchild, hv.child_key h.effect h.ready p.first hm tcLevel]
      exact (h.node.target_cover h.internal).mp (Covers.incMax _ _) p.chosen hm
    · have hh := hd (subtreeKey G.graph tcLevel (n + 1 - (p.node.level + 1))
        (p.node.level + 1) (p.child G.graph tcLevel).entry.lab
        (p.child G.graph tcLevel).entry.ptn (p.child G.graph tcLevel).entry.active
        (p.child G.graph tcLevel).numcells)
      exact hh.grow (Grows.incMax _ _)
  obtain ⟨key, he, hk⟩ := hc
  cases he
  exact hk

/-- Suspended native parents are indexed by their node level. -/
abbrev Parents (n : Nat) := Nat → Option (Parent n)

def Parents.push (parents : Parents n) (p : Parent n) : Parents n :=
  fun level => if level = p.node.level then some p else parents level

/-- Return target zero names the root entry; every later target names
the frozen entry at the next level. -/
def Parents.frames (parents : Parents n) : Frames n :=
  fun target => (parents (target + 1)).map Parent.node

theorem Parents.push_frames {parents : Parents n} {p : Parent n} (hp : 1 ≤ p.node.level) :
    (parents.push p).frames = parents.frames.insert p.node := by
  funext target
  by_cases he : target + 1 = p.node.level
  · simp only [Parents.frames, Parents.push, ite_eq_left he, Option.map_some,
      Frames.insert, ite_eq_left (by omega : target = p.node.level - 1)]
  · simp only [Parents.frames, Parents.push, ite_eq_right he,
      Frames.insert, ite_eq_right (by omega : target ≠ p.node.level - 1)]

end Hex.GraphIso.Nauty.Sparse.Max
