/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CursorCover
public import HexGraphIso.Nauty.Sparse.FilterPrune
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A pair interpreted in the current recovered partition also stabilizes
the original frozen cells; both share the actual parent frame. -/
theorem Cell.Valid.stabilizes {G : GraphIso.Sparse.Colored n k} {c : Cell n}
    {st : State n} {gamma : Array Nat} (h : c.Valid G)
    (he : FrameOut G c.level c.level c.entry st) (hs : Ready G c.level c.numcells st)
    (hg : CellStab st.ptn c.level st.lab gamma) :
    CellStab c.entry.ptn c.level c.entry.lab gamma := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  exact he.stab_below ⟨SearchOut.refl _ _ _ hs.ok.reach, hs.scratch.toBounded⟩
    h.ready hs hn h.positive h.positive (Nat.le_refl _) hg

/-- The literal native long filter preserves coverage in the original
window, even after recovery has reordered its vertices. -/
theorem Cell.Cover.long {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {c : Cell n} {st : State n} {cell : VSet n} {live : Nat → Prop} {best : Option (Key n)}
    (h : c.Cover G.graph tcLevel live best) (hc : c.Valid G)
    (he : FrameOut G c.level c.level c.entry st) (hp : PairsReady G tcLevel c.level c.numcells st)
    (hv : ∀ v, live v → c.vertices.mem v = true) (hm : ∀ v, live v → cell.mem v = true) :
    c.Cover G.graph tcLevel (fun v => live v ∧ ((policy (n := n)).longprune cell st).mem v = true) best := by
  have hn : 0 < n := by have := hc.positive; have := hc.depth; omega
  apply CellCover.pruned h hc.ready hn hc.positive hc.window hc.size hc.range hc.fuel hv
  intro v hv' hd
  obtain ⟨gamma, ha, hs, hlt⟩ := hp.long_drop (windowSet_lt (hv v hv')) (hm v hv') hd
  exact ⟨gamma, ha, hc.stabilizes he hp.ready hs, hlt⟩

/-- The actual received short pair preserves coverage in the original
window. Its checked carrier and strict descent come from the executed
child, not a premise about every vertex removed by the filter. -/
theorem Cell.Cover.short {G : GraphIso.Sparse.Colored n k} {tcLevel runFuel : Nat}
    {c : Cell n} {st : State n} {cell : VSet n} {tv target : Nat} {first : Bool}
    {live : Nat → Prop} {best guideBest : Option (Key n)}
    (h : c.Cover G.graph tcLevel live best) (hc : c.Valid G)
    (he : FrameOut G c.level c.level c.entry st) (hp : PairsReady G tcLevel c.level c.numcells st)
    (ht : Generic.Target State.frame c.level c.tc cell st) (htv : cell.mem tv = true)
    (hrecord : CheapRecorded c.level c.tc st) (hcanon : st.gcaCanon ≤ c.level) (hcap : 0 < st.wsCap)
    (hexit : (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel runFuel
      (c.level + 1) (c.numcells + 1) ((policy (n := n)).child first c.level c.tc tv st)).1 =
        .unwind target true)
    (hreceive : c.level ≤ target)
    (hguide : CanonGuide c.level c.tc c.entry (c.key G.graph tcLevel) guideBest st)
    (hv : ∀ v, live v → c.vertices.mem v = true) (hm : ∀ v, live v → cell.mem v = true) :
    let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel runFuel
      (c.level + 1) (c.numcells + 1) ((policy (n := n)).child first c.level c.tc tv st)).2
    c.Cover G.graph tcLevel
      (fun v => live v ∧ ((policy (n := n)).shortprune cell ((policy (n := n)).leaveChild tv raw)).mem v = true)
      best := by
  intro raw
  have hn : 0 < n := by have := hc.positive; have := hc.depth; omega
  apply CellCover.pruned h hc.ready hn hc.positive hc.window hc.size hc.range hc.fuel hv
  intro v hv' hd
  obtain ⟨gamma, ha, hs, hlt⟩ := hp.short_drop hn hc.positive ht htv hrecord hcanon hcap
    hexit hreceive (hguide.rebase he) v (windowSet_lt (hv v hv')) (hm v hv') hd
  exact ⟨gamma, ha, hc.stabilizes he hp.ready hs, hlt⟩

end Hex.GraphIso.Nauty.Sparse.Max
