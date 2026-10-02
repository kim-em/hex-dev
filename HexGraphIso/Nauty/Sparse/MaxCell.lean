/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFrame
public import HexGraphIso.Nauty.Sparse.CoverFrame
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A prepared native target, frozen before sibling permutations and filters. -/
structure Cell (n : Nat) where
  level : Nat
  numcells : Nat
  tc : Nat
  len : Nat
  codes : List Nat
  entry : State n

def Cell.vertices (c : Cell n) : VSet n := windowSet n c.entry.lab c.tc c.len

def Cell.key (G : Hex.SparseGraph n) (tcLevel : Nat) (c : Cell n) (v : Nat) : Key n :=
  prefixKey c.codes (vertexKey G tcLevel (n - c.level) c.level
    c.entry.lab c.entry.ptn c.tc c.numcells v)

def Cell.Cover (G : Hex.SparseGraph n) (tcLevel : Nat) (c : Cell n)
    (live : Nat → Prop) (best : Option (Key n)) : Prop :=
  CellCover G tcLevel (n - c.level) c.level c.numcells c.tc c.len c.codes c.entry live best

/-- Frozen target facts are about the executed native partition and cache. -/
structure Cell.Valid (G : GraphIso.Sparse.Colored n k) (c : Cell n) : Prop where
  positive : 1 ≤ c.level
  length : c.codes.length = c.level
  ready : Ready G c.level c.numcells c.entry
  window : IsCell c.entry.ptn c.level c.tc c.len
  size : 1 < c.len
  range : c.tc + c.len ≤ n

theorem Cell.Valid.depth {G : GraphIso.Sparse.Colored n k} {c : Cell n}
    (h : c.Valid G) : c.level ≤ n :=
  Nat.le_trans h.ready.ok.bc (bcount_le _ _ _)

theorem Cell.Valid.fuel {G : GraphIso.Sparse.Colored n k} {c : Cell n}
    (h : c.Valid G) : n < (n - c.level) + (c.numcells + 1) := by
  have hd := h.depth
  have hc := h.ready.ok.bc
  have he := h.ready.ok.count
  omega

/-- Recovery retains the complete original window, including removed vertices. -/
theorem Cell.Valid.target {G : GraphIso.Sparse.Colored n k} {c : Cell n} {st : State n}
    (h : c.Valid G) (he : FrameOut G c.level c.level c.entry st) :
    Generic.Target State.frame c.level c.tc c.vertices st :=
  (h.ready.window_target h.window h.size h.range).of_out he.effect

/-- The actual individualized entry of a child visited in a reordered parent. -/
def Cell.child (c : Cell n) (first : Bool) (st : State n) (v : Nat) : Frame n :=
  ⟨c.level + 1, c.numcells + 1, c.codes,
    (policy (n := n)).child first c.level c.tc v st⟩

theorem Cell.Valid.child {G : GraphIso.Sparse.Colored n k} {c : Cell n} {st : State n}
    (h : c.Valid G) (he : FrameOut G c.level c.level c.entry st)
    (hs : Ready G c.level c.numcells st) (first : Bool) {v : Nat}
    (hv : c.vertices.mem v = true) : (c.child first st v).Valid G := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  exact ⟨by dsimp [Cell.child]; omega, by dsimp [Cell.child]; rw [h.length],
    hs.child hn h.positive first (h.target he) hv⟩

/-- The recursive child's frozen key is the original target's vertex key.
The equality includes the exact sparse individualization and every unpruned
descendant; parent recovery may reorder the labelling array. -/
theorem Cell.Valid.child_key {G : GraphIso.Sparse.Colored n k} {c : Cell n} {st : State n}
    (h : c.Valid G) (he : FrameOut G c.level c.level c.entry st)
    (hs : Ready G c.level c.numcells st) (first : Bool) {v : Nat}
    (hv : c.vertices.mem v = true) (tcLevel : Nat) :
    (c.child first st v).key G.graph tcLevel = c.key G.graph tcLevel v := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hk := he.vertex_key (tcLevel := tcLevel) h.ready hs hn h.positive
    h.window h.size h.range hv h.fuel
  have hd : n + 1 - (c.level + 1) = n - c.level := by omega
  have hc : (c.child first st v).key G.graph tcLevel =
      prefixKey c.codes (vertexKey G.graph tcLevel (n - c.level) c.level
        st.lab st.ptn c.tc c.numcells v) := by
    dsimp only [Cell.child, Frame.key]
    rw [hd]
    cases first <;> rfl
  rw [hc, ← hk]
  rfl

theorem Cell.Cover.grow {G : Hex.SparseGraph n} {tcLevel : Nat} {c : Cell n}
    {live : Nat → Prop} {before after : Option (Key n)}
    (h : c.Cover G tcLevel live before) (hg : Grows before after) :
    c.Cover G tcLevel live after := CellCover.grow h hg

theorem Cell.Cover.finish {G : Hex.SparseGraph n} {tcLevel : Nat} {c : Cell n}
    {live : Nat → Prop} {best : Option (Key n)} (h : c.Cover G tcLevel live best)
    (he : ∀ v, ¬ live v) : ∀ v, c.vertices.mem v = true → Covers (c.key G tcLevel v) best :=
  CellCover.finish h he

end Hex.GraphIso.Nauty.Sparse.Max
