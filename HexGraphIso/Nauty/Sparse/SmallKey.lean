/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxCell
public import HexGraphIso.Nauty.Sparse.SmallCell
public import HexGraphIso.Nauty.SmallCell.Key
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- At a native equitable partition with the cheap shape, every member
of a target cell has the same complete unpruned sparse child key. -/
theorem Ready.small_key {G : GraphIso.Sparse.Colored n k}
    {level numcells tc len fuel v w : Nat} {st : State n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hshape : NodeShape n level st.ptn)
    (hc : IsCell st.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hv : (windowSet n st.lab tc len).mem v = true)
    (hw : (windowSet n st.lab tc len).mem w = true)
    (hf : n < fuel + (numcells + 1)) (tcLevel : Nat) :
    vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells v =
      vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells w := by
  by_cases he : v = w
  · rw [he]
  obtain ⟨a, ha, hav⟩ := mem_segN_iff.mp (mem_windowSet.mp hv).2
  obtain ⟨b, hb, hbw⟩ := mem_segN_iff.mp (mem_windowSet.mp hw).2
  have hab : a ≠ b := by intro heq; subst b; exact he (hav.symm.trans hbw)
  have hend : st.ptn[st.ptn.size - 1]! ≤ level := searchOk_end hn h.ok hl
  have hps : st.ptn.size = n := h.ok.ptnSize
  have hmem : (tc, tc + len - 1) ∈ cells st.ptn level n :=
    mem_cells_of_isCell (by change n ≤ st.ptn.size; rw [hps]; exact Nat.le_refl _) hend hc
      (by omega) (by change tc + len ≤ st.ptn.size; rw [hps]; exact hr)
  obtain ⟨sigma, hrows, hperm, hmap⟩ := h.transitive hn hl hshape hmem (by omega)
    (by omega : a ≤ tc + len - 1 - tc) (by omega : b ≤ tc + len - 1 - tc) hab
  let gamma := renamingArray sigma
  have hstab : CellStab st.ptn level st.lab gamma := by
    change cellsPerm st.ptn level st.lab (st.lab.map (fun v => gamma[v]!))
    have hmapLab : st.lab.map (fun v => gamma[v]!) = st.lab.map sigma.toFun :=
      map_congr_of_labOk (labOk_of_reach h.ok.labSize h.ok.reach)
        (fun v hv => renamingArray_get sigma hv)
    rw [hmapLab]
    exact hperm
  have hcarry : gamma[v]! = w := by
    rw [renamingArray_get sigma (windowSet_lt hv)]
    rw [hav, hbw] at hmap
    exact hmap.symm
  have hkey := h.vertex_key hn hl (checkAutom_renaming sigma hrows) hstab hc hlen hr hv hf tcLevel
  rw [hcarry] at hkey
  exact hkey

namespace Max

/-- Cheap-shape transitivity identifies the frozen keys of arbitrary
original target vertices, irrespective of later filtering. -/
theorem Cell.Valid.uniform {G : GraphIso.Sparse.Colored n k} {c : Cell n}
    (h : c.Valid G) (hshape : NodeShape n c.level c.entry.ptn) {v w : Nat}
    (hv : c.vertices.mem v = true) (hw : c.vertices.mem w = true) (tcLevel : Nat) :
    c.key G.graph tcLevel v = c.key G.graph tcLevel w := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  exact congrArg (prefixKey c.codes)
    (h.ready.small_key hn h.positive hshape h.window h.size h.range hv hw h.fuel tcLevel)

/-- Covering any one complete child of a cheap target covers every
original child, including those bypassed by a cheap-boundary return. -/
theorem Cell.Valid.cover {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {c : Cell n}
    {best : Option (Key n)} {v : Nat} (h : c.Valid G)
    (hshape : NodeShape n c.level c.entry.ptn) (hv : c.vertices.mem v = true)
    (hc : Covers (c.key G.graph tcLevel v) best) (live : Nat → Prop) :
    c.Cover G.graph tcLevel live best := by
  intro w hw
  left
  change Covers (c.key G.graph tcLevel w) best
  rw [h.uniform hshape hw hv tcLevel]
  exact hc

end Max
end Hex.GraphIso.Nauty.Sparse
