/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxGuides
public import HexGraphIso.Nauty.Sparse.MaxAncestor
public import HexGraphIso.Nauty.Sparse.MaxRecover
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxRecover
import all HexGraphIso.Nauty.Sparse.MaxScatter
import all HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Coverage of a reference child transfers to the actual recovered
ordering together with reference containment in the parent cells. -/
theorem Parent.Valid.reference_frame {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {out : State n} {ref : Array Nat} {ds : List Nat} {cell : VSet n} {tv : Nat}
    {best : Option (Key n)} (h : p.Valid G tcLevel)
    (hr : Ready G p.node.level (p.node.target G.graph tcLevel).numcells out)
    (he : FrameOut G p.node.level p.node.level p.state out)
    (hc : Covers (p.key G.graph tcLevel ref[p.tc]!) best)
    (hp : cellsPerm p.state.ptn p.node.level p.state.lab ref) :
    Covers ((p.next out ds cell tv).key G.graph tcLevel ref[p.tc]!) best ∧
      cellsPerm out.ptn p.node.level out.lab ref := by
  have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  obtain ⟨len, hwindow, _⟩ := h.target
  obtain ⟨hw, hlen, hbound⟩ := hwindow (mem_ne_empty h.chosen)
  have hm : (windowSet n p.state.lab p.tc len).mem ref[p.tc]! = true := by
    have hm : ref[p.tc]! ∈ segN p.state.lab p.tc len :=
      (hp p.tc len hw).mem_iff.mpr (mem_segN_iff.mpr ⟨0, hw.1, by simp⟩)
    apply mem_windowSet.mpr
    refine ⟨?_, hm⟩
    obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp hm
    rw [← hv]
    exact (labOk_of_reach h.ready.ok.labSize h.ready.ok.reach) _ (by
      change p.tc + o < p.state.lab.size
      have hs : p.state.lab.size = n := h.ready.ok.labSize
      rw [hs]
      omega)
  have hf : n < (n - p.node.level) + ((p.node.target G.graph tcLevel).numcells + 1) := by
    have hd := h.node.depth
    have hc : (p.node.target G.graph tcLevel).numcells = bcount p.state.ptn p.node.level n := h.ready.ok.count
    have hb : p.node.level ≤ bcount p.state.ptn p.node.level n := h.ready.ok.bc
    omega
  have hk := he.vertex_key (tcLevel := tcLevel) h.ready hr hn h.node.positive hw (by omega) hbound hm hf
  constructor
  · change Covers (prefixKey (p.node.codes ++ [p.node.code G.graph])
      (vertexKey G.graph tcLevel (n - p.node.level) p.node.level out.lab out.ptn
        p.tc (p.node.target G.graph tcLevel).numcells ref[p.tc]!)) best
    rw [← hk]
    exact hc
  · have hptn : out.ptn = p.state.ptn := he.effect.ptnEq h.ready.ok hr.ok
    rw [hptn]
    exact cellsPerm_trans (cellsPerm_symm he.effect.perm) hp

/-- Recovered reference coverage in the frozen parent becomes the
complete guide for whichever surviving vertex is suspended next. -/
theorem Parent.Valid.guide_frame {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {out : State n} {ds : List Nat} {cell : VSet n} {tv : Nat}
    (h : p.Valid G tcLevel)
    (hr : Ready G p.node.level (p.node.target G.graph tcLevel).numcells out)
    (he : FrameOut G p.node.level p.node.level p.state out)
    (hc : CanonGuide p.node.level p.tc p.state (p.key G.graph tcLevel) (State.key G.graph ds out) out)
    (hf : out.gcaFirst = p.node.level →
      Covers (p.key G.graph tcLevel out.firstlab[p.tc]!) (State.key G.graph ds out) ∧
        cellsPerm p.state.ptn p.node.level p.state.lab out.firstlab) :
    (p.next out ds cell tv).Guided G.graph tcLevel := by
  have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  obtain ⟨len, hwindow, _⟩ := h.target
  obtain ⟨hw, hlen, hbound⟩ := hwindow (mem_ne_empty h.chosen)
  have hsize : n < (n - p.node.level) + ((p.node.target G.graph tcLevel).numcells + 1) := by
    have hd := h.node.depth
    have hc : (p.node.target G.graph tcLevel).numcells = bcount p.state.ptn p.node.level n := h.ready.ok.count
    have hb : p.node.level ≤ bcount p.state.ptn p.node.level n := h.ready.ok.bc
    omega
  refine ⟨hc.frame he h.ready hr hn h.node.positive hw (by omega) hbound hsize, ?_⟩
  intro ht
  obtain ⟨hcover, hperm⟩ := hf ht
  exact h.reference_frame hr he hcover hperm

/-- Either actual child call supplies a valid recovered parent and its
native frame effect, including first-child bookkeeping and cache invalidation. -/
theorem Parent.Valid.returned_frame {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} (h : p.Valid G tcLevel) (first : Bool) :
    let ch := p.child G.graph tcLevel
    let raw := (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
    let left := (policy (n := n)).leaveChild p.chosen
      (if first then afterChildFirst p.node.level p.chosen raw else raw)
    let out := (policy (n := n)).recover (n + 2) p.node.level left
    Ready G p.node.level (p.node.target G.graph tcLevel).numcells out ∧
      FrameOut G p.node.level p.node.level p.state out := by
  intro ch raw left out
  have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hc := h.child
  have hx := node_frame G hn first tcLevel fuel ch.level ch.numcells ch.entry hc.positive hc.node
  have hp := h.return_frame (by
    simpa only [ch, Parent.child, Nat.add_sub_cancel] using hx)
  apply h.ready.recover hn h.node.positive
  cases first with
  | false => exact hp.leave p.chosen
  | true => exact (hp.afterChild p.node.level p.chosen).leave p.chosen

end Hex.GraphIso.Nauty.Sparse.Max
