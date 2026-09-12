/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.VertexKey
public import HexGraphIso.Nauty.Invariant.Child
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual recovered parent frame preserves the full unpruned key of
every vertex-indexed child, despite changing its offset in the target cell. -/
theorem FrameOut.vertex_key {G : GraphIso.Sparse.Colored n k}
    {level numcells tc len v fuel tcLevel : Nat} {st out : State n}
    (h : FrameOut G level level st out) (hs : Ready G level numcells st)
    (ho : Ready G level numcells out) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : IsCell st.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hv : (windowSet n st.lab tc len).mem v = true) (hf : n < fuel + (numcells + 1)) :
    vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells v =
      vertexKey G.graph tcLevel fuel level out.lab out.ptn tc numcells v := by
  have hptn : out.ptn = st.ptn := h.effect.ptnEq hs.ok ho.ok
  have hwindow : windowSet n st.lab tc len = windowSet n out.lab tc len := h.effect.window_eq hc
  have hout : (windowSet n out.lab tc len).mem v = true := by rwa [← hwindow]
  have hco : IsCell out.ptn level tc len := by rw [hptn]; exact hc
  have hleft := (hs.child hn hl false (hs.window_target hc hlen hr) hv).spec
  have hright := (ho.child hn hl false (ho.window_target hco hlen hr) hout).spec
  obtain ⟨offset, hoffset, hat⟩ := mem_segN_iff.mp (mem_windowSet.mp hv).2
  obtain ⟨_, _, _, hchild⟩ := h.effect.breakoutPerm hs.ok ho.ok hn hl hc (by omega) hr hoffset
  change cellsPerm (st.ptn.set! tc (level + 1)) (level + 1)
    (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + offset]!).1
    (breakout n out.lab out.ptn (level + 1) tc st.lab[tc + offset]!).1 at hchild
  rw [hat] at hchild
  change SpecNode G.graph (level + 1) (breakout n out.lab out.ptn (level + 1) tc v).1
    (out.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1) at hright
  change subtreeKey G.graph tcLevel fuel (level + 1)
      (breakout n st.lab st.ptn (level + 1) tc v).1
      (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1) =
    subtreeKey G.graph tcLevel fuel (level + 1)
      (breakout n out.lab out.ptn (level + 1) tc v).1
      (out.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1)
  rw [hptn] at hright hchild ⊢
  exact subtreeKey_perm hleft hright (cellsPerm_symm hchild) hf

end Hex.GraphIso.Nauty.Sparse
