/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxParent
public import HexGraphIso.Nauty.Sparse.Pairs
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.VertexKey
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Full child keys at the actual suspended target, retaining its native
arrays before the descendant call. The target may be hinted or filtered. -/
def Parent.key (G : Hex.SparseGraph n) (tcLevel : Nat) (p : Parent n) (v : Nat) : Key n :=
  prefixKey (p.node.codes ++ [p.node.code G])
    (vertexKey G tcLevel (n - p.node.level) p.node.level p.state.lab p.state.ptn
      p.tc (p.node.target G tcLevel).numcells v)

/-- The executed individualization has exactly the suspended selected
vertex's full key, including its actual code prefix. -/
theorem Parent.child_key (G : Hex.SparseGraph n) (tcLevel : Nat) (p : Parent n) :
    (p.child G tcLevel).key G tcLevel = p.key G tcLevel p.chosen := by
  dsimp only [Parent.child, Frame.key]
  rw [show n + 1 - (p.node.level + 1) = n - p.node.level by omega]
  cases p.first <;> rfl

/-- A native automorphism scattering a covered reference labelling to
the current descendant covers the suspended parent's entire chosen child.
This transports all unpruned leaves, regardless of the emitter's depth. -/
theorem Parent.Valid.scatter_cover {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G tcLevel) {ref lab gamma : Array Nat} {best : Option (Key n)}
    (ha : Automorphism G gamma) (href : ref.size = n)
    (hfr : cellsPerm p.state.ptn p.node.level p.state.lab ref)
    (hl : cellsPerm p.state.ptn p.node.level p.state.lab lab)
    (hmap : ∀ i, i < n → gamma[ref[i]!]! = lab[i]!)
    (hchosen : lab[p.tc]! = p.chosen)
    (hcover : Covers (p.key G.graph tcLevel ref[p.tc]!) best) :
    Covers ((p.child G.graph tcLevel).key G.graph tcLevel) best := by
  have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  obtain ⟨len, hwindow, _⟩ := h.target
  obtain ⟨hc, hlen, hr⟩ := hwindow (mem_ne_empty h.chosen)
  have hstab := cellStab_of_scatter h.ready.ok.ptnSize h.ready.ok.labSize href
    (searchOk_end hn h.ready.ok h.node.positive) hfr hl hmap
  have hmem : (windowSet n p.state.lab p.tc len).mem ref[p.tc]! = true := by
    have hm : ref[p.tc]! ∈ segN p.state.lab p.tc len :=
      (hfr p.tc len hc).mem_iff.mpr (mem_segN_iff.mpr ⟨0, hc.1, by simp⟩)
    apply mem_windowSet.mpr
    refine ⟨?_, hm⟩
    obtain ⟨o, ho, he⟩ := mem_segN_iff.mp hm
    rw [← he]
    exact (labOk_of_reach h.ready.ok.labSize h.ready.ok.reach) _
      (by
        change p.tc + o < p.state.lab.size
        have hs : p.state.lab.size = n := h.ready.ok.labSize
        rw [hs]
        omega)
  have hat : gamma[ref[p.tc]!]! = p.chosen := (hmap p.tc (by omega)).trans hchosen
  have hf : n < (n - p.node.level) + ((p.node.target G.graph tcLevel).numcells + 1) := by
    have hd := h.node.depth
    have hc : (p.node.target G.graph tcLevel).numcells = bcount p.state.ptn p.node.level n :=
      h.ready.ok.count
    have hb : p.node.level ≤ bcount p.state.ptn p.node.level n := h.ready.ok.bc
    omega
  have hk := h.ready.vertex_key hn h.node.positive ha.checked hstab hc (by omega) hr hmem hf tcLevel
  rw [hat] at hk
  rw [p.child_key, Parent.key, ← hk]
  exact hcover

end Hex.GraphIso.Nauty.Sparse.Max
