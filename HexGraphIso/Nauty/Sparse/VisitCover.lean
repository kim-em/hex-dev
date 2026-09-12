/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.VisitSplit
public import HexGraphIso.Nauty.Sparse.FilterCover

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Full coverage of an internal node is exactly coverage of all children
of its actual cached target, including the frozen ancestor code prefix. -/
theorem NodeInv.visit_cover {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells : Nat} {cs : List Nat} {st : State n}
    {best : Option (Key n)} (h : NodeInv G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (hf : n < (fuel + 1) + numcells) :
    let r := visit (.ofGraph G.graph) level numcells st
    let t := maketargetCached (.ofGraph G.graph) r.2.2.lab r.2.2.ptn level tcLevel (-1)
      r.2.2.canong.scratch
    r.1 < n →
      (Covers (prefixKey cs
        (subtreeKey G.graph tcLevel (fuel + 1) level st.lab st.ptn st.active numcells)) best ↔
        ∀ v, t.2.1.mem v = true → Covers (prefixKey (cs ++ [r.2.1])
          (vertexKey G.graph tcLevel fuel level r.2.2.lab r.2.2.ptn t.1 r.1 v)) best) := by
  intro r t hc
  constructor
  · intro hparent v hv
    have hb := (h.visit_bound hn hl hf hc).mp (Key.le_refl _) v hv
    have hp := hparent.mono (prefixKey_le cs hb)
    simpa only [prefixKey_append] using hp
  · intro hchildren
    obtain ⟨v, hv, he⟩ := h.visit_attains hn hl hf hc
    have hp := hchildren v hv
    rw [← prefixKey_append, he] at hp
    exact hp

/-- Exhausting the live representatives of an actual cached target covers
the original complete node. Earlier filter removals are accounted for by
the ranked child-coverage invariant. -/
theorem NodeInv.visit_finish {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells : Nat} {cs : List Nat} {st : State n}
    {best : Option (Key n)} {live : Nat → Prop} (h : NodeInv G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (hf : n < (fuel + 1) + numcells) :
    let r := visit (.ofGraph G.graph) level numcells st
    let t := maketargetCached (.ofGraph G.graph) r.2.2.lab r.2.2.ptn level tcLevel (-1)
      r.2.2.canong.scratch
    r.1 < n →
      CellCover G.graph tcLevel fuel level r.1 t.1 t.2.2.1 (cs ++ [r.2.1]) r.2.2 live best →
      (∀ v, ¬ live v) → Covers (prefixKey cs
        (subtreeKey G.graph tcLevel (fuel + 1) level st.lab st.ptn st.active numcells)) best := by
  intro r t hc hcover hempty
  apply (h.visit_cover hn hl hf hc).mpr
  intro v hv
  apply hcover.finish hempty v
  rw [← (h.visit_ready hn hl).target_window hn hl hc tcLevel (-1)]
  exact hv

end Hex.GraphIso.Nauty.Sparse
