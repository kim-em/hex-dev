/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstTraceFrame
public import HexGraphIso.Nauty.Sparse.OrbitCover
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual first child initializes stabilization of its parent's
prepared target partition. Its successful first path supplies the first
reference; all subsequent child work is covered by the native recursion
theorem, without a premise about the returned generators. -/
theorem firstChild_stabilizes {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tv last : Nat} {st leaf : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (hi : NodeInv G level numcells st)
    (hw : st.workperm.size = n) (he : st.genTrace = #[])
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (path : let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf) :
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    TraceFrame G level r.2.2.2.2
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2 := by
  intro r
  let ready := cheapCheck true level r.2.2.2.2
  let child := (policy (n := n)).child true level r.2.1.toNat tv ready
  obtain ⟨hr, ht⟩ := hi.prepare (tcLevel := tcLevel) hn hl
  have hc := hr.cheap true
  have htarget := ht.of_out hc.frame.effect
  have hmem := VSet.nextElem_mem htv
  have hchild := hc.ready.child hn hl true htarget hmem
  have hframe := hc.frame.trans (hc.ready.child_frame hn hl true htarget hmem (FrameOut.refl hchild))
  have hwork : child.workperm.size = n := by
    change ready.workperm.size = n
    unfold ready cheapCheck
    split <;> exact (prepareFirst_workSize (.ofGraph G.graph) tcLevel level numcells st).trans hw
  have htrace : child.genTrace = #[] := by
    change ready.genTrace = #[]
    unfold ready cheapCheck
    split <;> exact (prepareFirst_trace (.ofGraph G.graph) tcLevel level numcells st).trans he
  exact firstPath_stabilizes hr hn hl path (by omega) hchild hframe hwork htrace

/-- The frozen trace invariant discharges stabilization at the literal
orbit guard. Its first-child initialization and complete-call preservation
are supplied by `firstChild_stabilizes` and `TraceFrame.sweep`. -/
theorem TraceFrame.skip_cover {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc len tv : Nat} {cs : List Nat}
    {root st : State n} {live : Nat → Prop} {best : Option (Key n)} {first : Bool}
    (h : TraceFrame G level root st)
    (hcover : CellCover G.graph tcLevel fuel level numcells tc len cs root live best)
    (hr : Ready G level numcells root) (ho : OrbitTrace G st) (ht : TraceOk G st)
    (hn : 0 < n) (hl : 1 ≤ level) (hc : IsCell root.ptn level tc len)
    (hlen : 1 < len) (hb : tc + len ≤ n) (hf : n < fuel + (numcells + 1))
    (hv : (windowSet n root.lab tc len).mem tv = true) (hle : ∀ v, live v → tv ≤ v)
    (hskip : (!first || st.orbits[tv]! == tv) = false) :
    CellCover G.graph tcLevel fuel level numcells tc len cs root (fun v => live v ∧ tv < v) best :=
  hcover.orbit_skip hr ho ht hn hl hc hlen hb hf hv hle h.trace hskip

end Hex.GraphIso.Nauty.Sparse
