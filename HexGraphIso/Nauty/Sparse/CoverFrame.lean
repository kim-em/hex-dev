/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FilterCover
public import HexGraphIso.Nauty.Sparse.VertexFrame
public import HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Sparse.CanonGuide

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Parent recovery preserves the child coverage relation, including
previously covered and still-live representatives in the reordered frame. -/
theorem CellCover.frame {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc len : Nat} {cs : List Nat}
    {st out : State n} {live : Nat → Prop} {best : Option (Key n)}
    (h : CellCover G.graph tcLevel fuel level numcells tc len cs st live best)
    (hf : FrameOut G level level st out) (hs : Ready G level numcells st)
    (ho : Ready G level numcells out) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : IsCell st.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hfuel : n < fuel + (numcells + 1))
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true) :
    CellCover G.graph tcLevel fuel level numcells tc len cs out live best := by
  have hw : windowSet n st.lab tc len = windowSet n out.lab tc len := hf.effect.window_eq hc
  have hk : ∀ v, (windowSet n st.lab tc len).mem v = true →
      prefixKey cs (vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells v) =
        prefixKey cs (vertexKey G.graph tcLevel fuel level out.lab out.ptn tc numcells v) := by
    intro v hv
    exact congrArg (prefixKey cs) (hf.vertex_key hs ho hn hl hc hlen hr hv hfuel)
  intro v hv
  have hv' : (windowSet n st.lab tc len).mem v = true := by rwa [hw]
  rcases h v hv' with hd | ⟨w, hlive, he, hrank⟩
  · left
    dsimp only
    rwa [← hk v hv']
  · right
    refine ⟨w, hlive, ?_, hrank⟩
    dsimp only
    rw [← hk v hv', ← hk w (hsub w hlive)]
    exact he

/-- The reference and its native child key transfer together from the
frozen base to the current frame, even if filtering removed that reference
vertex from the mutable target set. -/
theorem CanonGuide.frame {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc len : Nat} {cs : List Nat}
    {base st : State n} {best : Option (Key n)}
    (h : CanonGuide level tc base
      (fun v => prefixKey cs (vertexKey G.graph tcLevel fuel level base.lab base.ptn tc numcells v)) best st)
    (hf : FrameOut G level level base st) (hbase : Ready G level numcells base)
    (hst : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : IsCell base.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hfuel : n < fuel + (numcells + 1)) :
    CanonGuide level tc st
      (fun v => prefixKey cs (vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells v)) best st := by
  intro he
  obtain ⟨v, hv, hat, hp⟩ := h.rebase hf he
  have hm : (windowSet n base.lab tc len).mem v = true := by
    obtain ⟨w, _, hw, hm⟩ := h.mem (labOk_of_reach hbase.ok.labSize hbase.ok.reach) hc
      (by change tc + len ≤ base.frame.lab.size; rw [hbase.ok.labSize]; exact hr) he
    have hwv : w = v := hw.symm.trans hat
    rwa [hwv] at hm
  refine ⟨v, ?_, hat, hp⟩
  have hk := hf.vertex_key (tcLevel := tcLevel) (fuel := fuel) hbase hst hn hl hc hlen hr hm hfuel
  dsimp only at hv ⊢
  rwa [← hk]

end Hex.GraphIso.Nauty.Sparse
