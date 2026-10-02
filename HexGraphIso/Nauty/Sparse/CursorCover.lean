/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxCell
public import HexGraphIso.Nauty.Sparse.TraceOrbit
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.VSet.Basic

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The executable cursor names the next vertex, including that vertex. -/
def Remaining (cursor : Option Nat) (cell : VSet n) (v : Nat) : Prop :=
  cell.mem v = true ∧ ∃ tv, cursor = some tv ∧ tv ≤ v

theorem Remaining.next {cell : VSet n} {tv v : Nat} :
    Remaining (cell.nextElem (some tv)) cell v ↔ cell.mem v = true ∧ tv < v := by
  constructor
  · rintro ⟨hv, w, hw, hwv⟩
    have hh := (VSet.nextElem_some hw).2.1
    change tv + 1 ≤ w at hh
    exact ⟨hv, by omega⟩
  · rintro ⟨hv, htv⟩
    cases he : cell.nextElem (some tv) with
    | none =>
      have hh := VSet.nextElem_none he v (by change tv + 1 ≤ v; omega)
      rw [hv] at hh
      cases hh
    | some w =>
      refine ⟨hv, w, rfl, ?_⟩
      by_cases hn : w ≤ v
      · exact hn
      · have hh := (VSet.nextElem_some he).2.2 v (by change tv + 1 ≤ v; omega) (by omega)
        rw [hv] at hh
        cases hh

theorem Remaining.first {cell : VSet n} {v : Nat} :
    Remaining (cell.nextElem none) cell v ↔ cell.mem v = true := by
  constructor
  · exact fun h => h.1
  · intro hv
    cases he : cell.nextElem none with
    | none =>
      have hh := VSet.nextElem_none he v (Nat.zero_le _)
      rw [hv] at hh
      cases hh
    | some w =>
      refine ⟨hv, w, rfl, ?_⟩
      by_cases hn : w ≤ v
      · exact hn
      · have hh := (VSet.nextElem_some he).2.2 v (Nat.zero_le _) (by omega)
        rw [hv] at hh
        cases hh

theorem Remaining.le {cell : VSet n} {tv v : Nat} (h : Remaining (some tv) cell v) : tv ≤ v := by
  obtain ⟨_, w, hw, hle⟩ := h
  cases hw
  exact hle

theorem Remaining.none {cell : VSet n} {v : Nat} : ¬ Remaining none cell v := by
  rintro ⟨_, w, hw, _⟩
  cases hw

/-- Changing only the description of live vertices preserves frozen coverage. -/
theorem Cell.Cover.live {G : Hex.SparseGraph n} {tcLevel : Nat} {c : Cell n}
    {before after : Nat → Prop} {best : Option (Key n)}
    (h : c.Cover G tcLevel before best) (he : ∀ v, before v ↔ after v) :
    c.Cover G tcLevel after best := by
  have heq : before = after := funext (fun v => propext (he v))
  rwa [← heq]

/-- The actual first cursor retains the complete original window. -/
theorem Cell.Cover.initial (G : Hex.SparseGraph n) (tcLevel : Nat) (c : Cell n)
    (best : Option (Key n)) :
    c.Cover G tcLevel (Remaining (c.vertices.nextElem none) c.vertices) best :=
  Cell.Cover.live (CellCover.init G tcLevel (n - c.level) c.level c.numcells c.tc c.len c.codes c.entry best)
    (fun _ => Remaining.first.symm)

/-- A received child result covers exactly that child's original vertex key.
The native frame theorem accounts for the parent's current label order. -/
theorem Cell.Cover.received {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {c : Cell n} {st out : State n} {cell : VSet n} {tv : Nat} {bs : List Nat}
    {first short : Bool} {witness : Nat → Option (Key n) → Prop}
    (h : c.Cover G.graph tcLevel (Remaining (some tv) cell) (State.key G.graph bs st))
    (hc : c.Valid G) (he : FrameOut G c.level c.level c.entry st)
    (hs : Ready G c.level c.numcells st) (hv : c.vertices.mem tv = true)
    (hr : MaxResult ((c.child first st tv).key G.graph tcLevel)
      (State.key G.graph bs (c.child first st tv).entry) (State.best G.graph out)
      c.level witness (.unwind c.level short)) :
    c.Cover G.graph tcLevel (Remaining (cell.nextElem (some tv)) cell) (State.best G.graph out) := by
  have hg := hr.bounded.grows
  have hbefore : State.key G.graph bs (c.child first st tv).entry = State.key G.graph bs st := by
    cases first <;> rfl
  rw [hbefore] at hg
  have hkey : Covers (c.key G.graph tcLevel tv) (State.best G.graph out) := by
    rw [← hc.child_key he hs first hv tcLevel]
    simpa only [ExitCover, ↓reduceIte] using hr.coverage.2
  have hvisit : c.Cover G.graph tcLevel
      (fun v => Remaining (some tv) cell v ∧ tv < v) (State.best G.graph out) :=
    CellCover.visit (h.grow hg) (fun _ hv => hv.le) hkey
  apply hvisit.live
  intro v
  rw [Remaining.next]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, tv, rfl, by omega⟩, h.2⟩

/-- Skipping the actual nonrepresentative advances coverage with the same
cursor used by the native sweep. Stabilization comes from `TraceFrame`. -/
theorem Cell.Cover.skipped {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {c : Cell n} {st : State n} {cell : VSet n} {tv : Nat} {best : Option (Key n)} {first : Bool}
    (h : c.Cover G.graph tcLevel (Remaining (some tv) cell) best)
    (hc : c.Valid G) (hf : TraceFrame G c.level c.entry st)
    (ho : OrbitTrace G st) (ht : TraceOk G st) (hv : c.vertices.mem tv = true)
    (hskip : (!first || st.orbits[tv]! == tv) = false) :
    c.Cover G.graph tcLevel (Remaining (cell.nextElem (some tv)) cell) best := by
  have hn : 0 < n := by have := hc.positive; have := hc.depth; omega
  have hskip' : c.Cover G.graph tcLevel
      (fun v => Remaining (some tv) cell v ∧ tv < v) best :=
    hf.skip_cover h hc.ready ho ht hn hc.positive hc.window hc.size hc.range hc.fuel hv
      (fun _ hv => hv.le) hskip
  apply hskip'.live
  intro v
  rw [Remaining.next]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, tv, rfl, by omega⟩, h.2⟩

/-- Sequential filters retain precisely their larger survivors at the next
cursor, even when an earlier filter has already removed a representative. -/
theorem Cell.Cover.filtered {G : Hex.SparseGraph n} {tcLevel : Nat} {c : Cell n}
    {cell filtered : VSet n} {tv : Nat} {best : Option (Key n)}
    (h : c.Cover G tcLevel
      (fun v => Remaining (cell.nextElem (some tv)) cell v ∧ filtered.mem v = true) best)
    (hs : ∀ v, filtered.mem v = true → cell.mem v = true) :
    c.Cover G tcLevel (Remaining (filtered.nextElem (some tv)) filtered) best := by
  apply h.live
  intro v
  rw [Remaining.next, Remaining.next]
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · exact fun h => ⟨⟨hs v h.1, h.2⟩, h.1⟩

end Hex.GraphIso.Nauty.Sparse.Max
