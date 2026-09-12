/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.VertexKey
public import HexGraphIso.Nauty.Sparse.Coverage
public import HexGraphIso.Nauty.Sparse.PrefixKey
public import HexGraphIso.Nauty.Invariant.Coverage
import all HexGraphIso.Nauty.Sparse.Coverage

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Coverage of a frozen target cell, indexed by vertex labels. Live
vertices can include the cursor condition as well as mutable set membership. -/
@[expose] def CellCover (G : Hex.SparseGraph n) (tcLevel fuel level numcells tc len : Nat)
    (cs : List Nat) (st : State n) (live : Nat → Prop) (best : Option (Key n)) : Prop :=
  ChildCover (fun v => prefixKey cs (vertexKey G tcLevel fuel level st.lab st.ptn tc numcells v))
    id (fun v => (windowSet n st.lab tc len).mem v = true)
    (fun v => Covers
      (prefixKey cs (vertexKey G tcLevel fuel level st.lab st.ptn tc numcells v)) best) live

/-- Before visiting children, every target vertex represents itself. -/
theorem CellCover.init (G : Hex.SparseGraph n) (tcLevel fuel level numcells tc len : Nat)
    (cs : List Nat) (st : State n) (best : Option (Key n)) :
    CellCover G tcLevel fuel level numcells tc len cs st
      (fun v => (windowSet n st.lab tc len).mem v = true) best :=
  (ChildCover.init _ _ _).monoDone (fun _ h => h.elim)

/-- Growing the incumbent preserves all previously covered children. -/
theorem CellCover.grow {G : Hex.SparseGraph n} {tcLevel fuel level numcells tc len : Nat}
    {cs : List Nat} {st : State n} {live : Nat → Prop} {before after : Option (Key n)}
    (h : CellCover G tcLevel fuel level numcells tc len cs st live before)
    (hg : Grows before after) :
    CellCover G tcLevel fuel level numcells tc len cs st live after :=
  h.monoDone (fun _ hc => hc.grow hg)

/-- Visiting the least live vertex advances the cursor and absorbs every
original child represented by that vertex. -/
theorem CellCover.visit {G : Hex.SparseGraph n} {tcLevel fuel level numcells tc len tv : Nat}
    {cs : List Nat} {st : State n} {live : Nat → Prop} {best : Option (Key n)}
    (h : CellCover G tcLevel fuel level numcells tc len cs st live best)
    (hle : ∀ v, live v → tv ≤ v)
    (hc : Covers
      (prefixKey cs (vertexKey G tcLevel fuel level st.lab st.ptn tc numcells tv)) best) :
    CellCover G tcLevel fuel level numcells tc len cs st (fun v => live v ∧ tv < v) best := by
  apply h.step ?_ (fun _ hd => hd)
  intro v hv
  by_cases he : v = tv
  · subst v
    left
    intro z hz
    rwa [hz]
  · exact Or.inr ⟨v, ⟨hv, by have := hle v hv; omega⟩, rfl, Nat.le_refl _⟩

/-- A child repeating a smaller representative is already covered when
it reaches the cursor. Ranked coverage rules out a still-live carrier
below that cursor, including after earlier filters. -/
theorem CellCover.skip {G : Hex.SparseGraph n} {tcLevel fuel level numcells tc len tv rep : Nat}
    {cs : List Nat} {st : State n} {live : Nat → Prop} {best : Option (Key n)}
    (h : CellCover G tcLevel fuel level numcells tc len cs st live best)
    (hle : ∀ v, live v → tv ≤ v)
    (hr : (windowSet n st.lab tc len).mem rep = true) (hlt : rep < tv)
    (hkey : vertexKey G tcLevel fuel level st.lab st.ptn tc numcells tv =
      vertexKey G tcLevel fuel level st.lab st.ptn tc numcells rep) :
    CellCover G tcLevel fuel level numcells tc len cs st (fun v => live v ∧ tv < v) best := by
  apply h.visit hle
  rcases h rep hr with hd | ⟨w, hw, _, hrank⟩
  · rwa [hkey]
  · have := hle w hw
    change w ≤ rep at hrank
    omega

/-- Exhausting the live set covers the full original target cell. -/
theorem CellCover.finish {G : Hex.SparseGraph n} {tcLevel fuel level numcells tc len : Nat}
    {cs : List Nat} {st : State n} {live : Nat → Prop} {best : Option (Key n)}
    (h : CellCover G tcLevel fuel level numcells tc len cs st live best)
    (hempty : ∀ v, ¬ live v) :
    ∀ v, (windowSet n st.lab tc len).mem v = true → Covers
      (prefixKey cs (vertexKey G tcLevel fuel level st.lab st.ptn tc numcells v)) best :=
  ChildCover.finish h hempty

/-- The executable cursor terminator exhausts every live member at or
after its scan start, closing coverage of the original target cell. -/
theorem CellCover.finish_cursor {G : Hex.SparseGraph n} {tcLevel fuel level numcells tc len : Nat}
    {cs : List Nat} {st : State n} {live : Nat → Prop} {best : Option (Key n)}
    {cell : VSet n} {cursor : Option Nat}
    (h : CellCover G tcLevel fuel level numcells tc len cs st live best)
    (hmem : ∀ v, live v → cell.mem v = true)
    (hle : ∀ v, live v → VSet.scanStart cursor ≤ v)
    (hnone : cell.nextElem cursor = none) :
    ∀ v, (windowSet n st.lab tc len).mem v = true → Covers
      (prefixKey cs (vertexKey G tcLevel fuel level st.lab st.ptn tc numcells v)) best := by
  apply h.finish
  intro v hv
  have hf := VSet.nextElem_none hnone v (hle v hv)
  rw [hmem v hv] at hf
  cases hf

end Hex.GraphIso.Nauty.Sparse
