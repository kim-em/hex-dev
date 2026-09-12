/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RouteHistory
public import HexGraphIso.Nauty.Sparse.FirstReturn
import all HexGraphIso.Nauty.Sparse.RouteHistory
import all HexGraphIso.Nauty.Sparse.RouteAt
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Completion of the actual first child initializes the general guided
history at its recovered parent. Both the selected reference and current
ancestor witness are derived from native execution, without a cheap guard. -/
theorem firstChild_route {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tv last : Nat} {st leaf : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (hok : NodeInv G level numcells st)
    (htsize : n < st.firsttc.size) (hcsize : n + 1 < st.firstcode.size)
    (hopen : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 ≠ n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.2.2).orbits[tv]! = tv)
    (hpath : let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf) :
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
      ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2
    let result := (policy (n := n)).recover (n + 2) level
      ((policy (n := n)).leaveChild tv (afterChildFirst level tv out))
    RouteHistory G.graph tcLevel level level r.1 result := by
  let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
  let R := State.refined (.ofGraph G.graph) level numcells st
  let ready := cheapCheck true level r.2.2.2.2
  let ch := (policy (n := n)).child true level r.2.1.toNat tv ready
  let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch).2
  let left := (policy (n := n)).leaveChild tv (afterChildFirst level tv out)
  let result := (policy (n := n)).recover (n + 2) level left
  have hp : Generic.FirstPath (.ofGraph G.graph) tcLevel (fuel + 1) level numcells st last leaf :=
    .step hopen htv horbit hpath
  obtain ⟨href, _⟩ := firstRef_of_path (inf := n + 2) hn hp hl hok htsize hcsize
  have hrout : out.reference =
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel (fuel + 1) level numcells st).2.reference :=
    (firstPath_reference hpath).trans (firstPath_reference hp).symm
  have hr : result.reference =
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel (fuel + 1) level numcells st).2.reference :=
    ((referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left).trans hrout
  have hg : result.gcaFirst = level := (gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left
  obtain ⟨hprep, htarg⟩ := hok.prepare (tcLevel := tcLevel) hn hl
  have hready := hprep.cheap true
  have htarget := htarg.of_out hready.frame.effect
  have hmem := VSet.nextElem_mem htv
  have hch := hready.ready.child hn hl true htarget hmem
  have ho := node_frame G hn true tcLevel fuel (level + 1) (r.1 + 1) ch (by omega) hch
  have hframe : FrameOut G level level ready out := hready.ready.child_frame hn hl true htarget hmem
    (by simpa only [Nat.add_sub_cancel] using ho)
  have hleft : FrameOut G level level ready left := (hframe.afterChild level tv).leave tv
  change RouteHistory G.graph tcLevel level level r.1 result
  rw [RouteHistory, hg]
  refine ⟨R, href.congr hr, hok.refined, ?_⟩
  refine ⟨?_, fun _ => ?_⟩
  · rw [recover_eqlev]
    omega
  · have hd : RouteAt G.graph tcLevel result.firsttc level R level r.1 ready := by
      have hp := prepareFirst_partition (.ofGraph G.graph) tcLevel level numcells st
      refine ⟨R, hok.refined, GuidedPerm.refl _ _ _ _ _, ?_, ?_, hp.2.2.symm⟩
      · unfold ready cheapCheck
        split <;> exact hp.1.symm
      · unfold ready cheapCheck
        split <;> exact hp.2.1.symm
    exact hd.recover hready.ready.ok hleft

/-- The first child's actual saved target supplies the guided choice for
the remaining siblings, after every inner return and parent recovery. -/
theorem firstChild_recorded {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tv last : Nat} {st leaf : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (hok : NodeInv G level numcells st)
    (htsize : n < st.firsttc.size)
    (hopen : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 ≠ n)
    (hpath : let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf) :
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
      ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2
    let result := (policy (n := n)).recover (n + 2) level
      ((policy (n := n)).leaveChild tv (afterChildFirst level tv out))
    RouteRecorded G.graph tcLevel level r.2.1.toNat result := by
  intro r out result _
  exact Or.inr (firstChild_target hn hl hok htsize hopen hpath)

end Hex.GraphIso.Nauty.Sparse
