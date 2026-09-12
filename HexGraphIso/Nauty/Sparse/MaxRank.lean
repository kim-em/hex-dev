/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxScatter
public import HexGraphIso.Nauty.Sparse.CursorCover
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxScatter
import all HexGraphIso.Nauty.Sparse.CursorCover
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Every original child below the current cursor is covered. A removed
child's ranked carrier cannot still be live below that cursor. -/
theorem Cell.Cover.earlier {G : Hex.SparseGraph n} {tcLevel : Nat} {c : Cell n}
    {cell : VSet n} {tv v : Nat} {best : Option (Key n)}
    (h : c.Cover G tcLevel (Remaining (some tv) cell) best)
    (hv : c.vertices.mem v = true) (hlt : v < tv) : Covers (c.key G tcLevel v) best := by
  rcases h v hv with hd | ⟨w, hw, _, hrank⟩
  · exact hd
  · have hle := hw.le
    change w ≤ v at hrank
    omega

/-- A suspended cursor has already covered every smaller vertex of its
original target cell, including vertices removed by earlier filters. -/
def Parent.Ranked (G : Hex.SparseGraph n) (tcLevel : Nat) (p : Parent n) : Prop :=
  ∀ len, IsCell p.state.ptn p.node.level p.tc len →
    ∀ v, (windowSet n p.state.lab p.tc len).mem v = true → v < p.chosen →
      Covers (p.key G tcLevel v) (State.key G p.bs p.state)

/-- The native frozen-cell coverage invariant supplies the suspended
cursor's rank rule. A hinted target uses its already dominating code
prefix; an unhinted target transports the actual recovered cell order. -/
theorem Parent.Valid.ranked {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {p : Parent n}
    (h : p.Valid G tcLevel)
    (hc : (p.node.target G.graph tcLevel).Cover G.graph tcLevel (Remaining (some p.chosen) p.cell)
      (State.key G.graph p.bs p.state)) : p.Ranked G.graph tcLevel := by
  intro len hcell v hv hlt
  rcases h.choice with ht | hd
  · let c := p.node.target G.graph tcLevel
    have hvalid := h.node.target (tcLevel := tcLevel) h.internal
    have hw : IsCell p.state.ptn p.node.level c.tc c.len :=
      isCell_of_low h.effect.effect.low hvalid.window
    have he : len = c.len := by
      rw [ht] at hcell
      change IsCell p.state.ptn p.node.level c.tc len at hcell
      have hcases := isCell_disjoint_or_eq hw hcell
      change c.tc + len ≤ c.tc ∨ c.tc + c.len ≤ c.tc ∨ c.tc = c.tc ∧ c.len = len at hcases
      rcases hcases with he | he | he
      · exact False.elim ((Nat.not_le_of_gt (Nat.lt_add_of_pos_right hcell.1)) he)
      · exact False.elim ((Nat.not_le_of_gt (Nat.lt_add_of_pos_right hw.1)) he)
      · exact he.2.symm
    have hwindow : windowSet n c.entry.lab c.tc c.len = windowSet n p.state.lab c.tc c.len :=
      h.effect.effect.window_eq hvalid.window
    have hmem : c.vertices.mem v = true := by
      change (windowSet n c.entry.lab c.tc c.len).mem v = true
      rw [hwindow]
      rwa [ht, he] at hv
    have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
    have hk := h.effect.vertex_key (tcLevel := tcLevel) hvalid.ready h.ready hn hvalid.positive
      hvalid.window hvalid.size hvalid.range hmem hvalid.fuel
    change vertexKey G.graph tcLevel (n - c.level) c.level c.entry.lab c.entry.ptn c.tc c.numcells v =
      vertexKey G.graph tcLevel (n - c.level) c.level p.state.lab p.state.ptn c.tc c.numcells v at hk
    change Covers (prefixKey c.codes (vertexKey G.graph tcLevel (n - c.level) c.level
      p.state.lab p.state.ptn p.tc c.numcells v)) (State.key G.graph p.bs p.state)
    have htc : p.tc = c.tc := ht
    rw [htc, ← hk]
    exact hc.earlier hmem hlt
  · exact hd (vertexKey G.graph tcLevel (n - p.node.level) p.node.level p.state.lab p.state.ptn
      p.tc (p.node.target G.graph tcLevel).numcells v)

/-- A smaller orbit pointer covers the interrupted child of a suspended
cursor. The word in the executed generator trace stays in its frozen
target cell and transports the full native subtree key. -/
theorem Parent.Ranked.orbit_cover {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {out : State n} {best : Option (Key n)} (h : p.Ranked G.graph tcLevel)
    (hp : p.Valid G tcLevel) (ho : OrbitTrace G out) (ht : TraceOk G out)
    (hs : ∀ gamma ∈ out.genTrace, CellStab p.state.ptn p.node.level p.state.lab gamma)
    (hlt : out.orbits[p.chosen]! < p.chosen)
    (hg : Grows (State.key G.graph p.bs p.state) best) :
    Covers ((p.child G.graph tcLevel).key G.graph tcLevel) best := by
  have hn : 0 < n := by have := hp.node.positive; have := hp.node.depth; omega
  obtain ⟨len, hwindow, hmembers⟩ := hp.target
  obtain ⟨hc, hlen, hrange⟩ := hwindow (mem_ne_empty hp.chosen)
  have hv : (windowSet n p.state.lab p.tc len).mem p.chosen = true :=
    mem_windowSet.mpr ⟨VSet.mem_lt hp.chosen, hmembers p.chosen hp.chosen⟩
  obtain ⟨gamma, ha, hstab, hmap, _⟩ := ho.carrier ht hp.ready hn hp.node.positive
    (VSet.mem_lt hp.chosen) hs (by omega)
  have hsize : p.state.lab.size = n := hp.ready.ok.labSize
  have hm := windowSet_carry hstab hc (by rw [hsize]; exact hrange)
    (labOk_of_reach hp.ready.ok.labSize hp.ready.ok.reach) hv
  have hf : n < (n - p.node.level) + ((p.node.target G.graph tcLevel).numcells + 1) := by
    have hd := hp.node.depth
    have he : (p.node.target G.graph tcLevel).numcells = bcount p.state.ptn p.node.level n := hp.ready.ok.count
    have hb : p.node.level ≤ bcount p.state.ptn p.node.level n := hp.ready.ok.bc
    omega
  have hk := hp.ready.vertex_key hn hp.node.positive ha hstab hc (by omega) hrange hv hf tcLevel
  have hd := h len hc gamma[p.chosen]! hm (by rw [hmap]; exact hlt)
  rw [p.child_key]
  change Covers (prefixKey (p.node.codes ++ [p.node.code G.graph])
    (vertexKey G.graph tcLevel (n - p.node.level) p.node.level p.state.lab p.state.ptn
      p.tc (p.node.target G.graph tcLevel).numcells p.chosen)) best
  rw [hk]
  exact hd.grow hg

end Hex.GraphIso.Nauty.Sparse.Max
