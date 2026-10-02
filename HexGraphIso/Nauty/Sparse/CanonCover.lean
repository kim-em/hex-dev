/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CoverFrame
public import HexGraphIso.Nauty.Sparse.ShortPair
import all HexGraphIso.Nauty.Sparse.CanonGuide
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A canonical scatter returning from an actual child identifies its
whole unpruned maximum with the already covered reference child. The emitting
leaf may have returned through arbitrarily many intervening native sweeps. -/
theorem child_canon_cover {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel runFuel level numcells tc tv len : Nat} {first childFirst : Bool}
    {cell : VSet n} {st : State n} {cs : List Nat} {best : Option (Key n)}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hc : IsCell st.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hf : n < fuel + (numcells + 1))
    (hguide : CanonGuide level tc st
      (fun v => prefixKey cs (vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells v)) best st) :
    let out := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel runFuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    out.gcaCanon = level → out.canonlab.size = n → Automorphism G out.workperm →
      (∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]!) →
      Covers (prefixKey cs (vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells tv)) best := by
  intro out he hs ha hmap
  have hold := child_canon_old (tcLevel := tcLevel) (fuel := runFuel)
    h hn hl first childFirst ht hv (Nat.le_of_eq he)
  have hparent : st.gcaCanon = level := hold.1.symm.trans he
  obtain ⟨v, hvkey, hat, hm⟩ := hguide.mem (labOk_of_reach h.ok.labSize h.ok.reach) hc
    (by change tc + len ≤ st.frame.lab.size; rw [h.ok.labSize]; exact hr) hparent
  have hatout : out.canonlab[tc]! = v := by rw [hold.2]; exact hat
  have hstab := child_canon_stab h hn hl first childFirst ht hv h
    ⟨SearchOut.refl _ _ _ h.ok.reach, h.scratch.toBounded⟩ hguide he hs hmap
  have hi := h.child hn hl first ht hv
  have hx := node_frame G hn childFirst tcLevel runFuel (level + 1) (numcells + 1) _ (by omega) hi
  have hstore := h.child_store hn hl first ht hv ⟨hx.effect.labSize, hx.effect.perm⟩
  have hcarry : out.workperm[v]! = tv := by
    rw [← hatout]
    exact (hmap tc (by omega)).trans hstore.2.2
  have hkey := h.vertex_key hn hl ha.checked hstab hc hlen hr hm hf tcLevel
  rw [hcarry] at hkey
  rw [← hkey]
  exact hvkey

/-- An actually received short return either covers the entire current
child via its canonical automorphism, or retains the implicit cheap-boundary
limit. All child result validity is derived from the native entry invariants. -/
theorem PairsReady.short_witness {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel runFuel level numcells tc tv target len : Nat} {first : Bool}
    {cell : VSet n} {base st : State n} {cs : List Nat} {best : Option (Key n)}
    (h : PairsReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hrecord : CheapRecorded level tc st) (hcanon : st.gcaCanon ≤ level) (hcap : 0 < st.wsCap)
    (he : (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel runFuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).1 =
        .unwind target true)
    (hreceive : level ≤ target) (hbase : Ready G level numcells base)
    (hframe : FrameOut G level level base st)
    (hc : IsCell base.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hf : n < fuel + (numcells + 1))
    (hguide : CanonGuide level tc base
      (fun v => prefixKey cs (vertexKey G.graph tcLevel fuel level base.lab base.ptn tc numcells v)) best st) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel runFuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    Covers (prefixKey cs (vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells tv)) best ∨
      target ≤ out.noncheaplevel - 1 := by
  intro out
  have htarget := child_target h.ancestor hcanon h.bound he hreceive
  have hi := h.child hn hl first ht hv hrecord
  have hs := hi.saved.node hn tcLevel runFuel (level + 1) (numcells + 1) (by omega) hi.node
  have htrace := node_trace G hn tcLevel runFuel (level + 1) (numcells + 1) _ (by omega) hi.toTraceEntry
  have horigin := node_origin false (.ofGraph G.graph) (n + 2) tcLevel runFuel (level + 1) (numcells + 1)
    ((policy (n := n)).child first level tc tv st) he
  have hcapacity : 0 < out.wsCap := by
    dsimp only [out]
    rw [node_capacity]
    cases first <;> exact hcap
  rcases horigin.admission hcapacity with ⟨_, hg, hmem, hmap⟩ | ⟨_, hcheap⟩
  · left
    apply child_canon_cover h.ready hn hl ht hv (isCell_of_low hframe.effect.low hc) hlen hr hf
      (hguide.frame hframe hbase h.ready hn hl hc hlen hr hf)
      (hg.symm.trans htarget) hs.canonical.1 (htrace _ hmem)
    exact hmap hs.work hs.canonical.1 (isPerm_of_cellsReach hs.canonical.1 hn hs.canonical.2)
  · exact Or.inr hcheap

end Hex.GraphIso.Nauty.Sparse
