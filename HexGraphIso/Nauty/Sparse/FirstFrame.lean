/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstPath
public import HexGraphIso.Nauty.Sparse.Reference
public import HexGraphIso.Nauty.Sparse.CanonSource
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The literal first descent retains the entry's cell contents and
ancestor boundaries, including the native refinement at each level. -/
theorem firstPath_frame {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hn : 0 < n) (hl : 1 ≤ level) (hi : NodeInv G level numcells st) :
    FrameOut G (level - 1) level st leaf := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    have hv := hi.visit_ready hn hl
    have hr := hv.record (visit (.ofGraph G.graph) level numcells st).2.1
    exact hi.visit_frame hl (hr.trans (hr.ready.target_frame true tcLevel)).frame
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    have hv := hi.visit_ready hn hl
    have hr := hv.record (visit (.ofGraph G.graph) level numcells st).2.1
    have ht := hr.ready.target_frame true tcLevel
    have htarget := hr.ready.target hn hl true tcLevel
    have hc := ht.ready.cheap true
    have hchild := hc.ready.child hn hl true (htarget.of_out hc.frame.effect) (VSet.nextElem_mem htv)
    have hout := ih (by omega) hchild
    have hreturn := hc.ready.child_frame hn hl true (htarget.of_out hc.frame.effect)
      (VSet.nextElem_mem htv) (by
        simpa only [Nat.add_sub_cancel, Generic.prepareFirst, policy, Generic.Policy.cheapCheck,
          Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.chooseTarget] using hout)
    exact hi.visit_frame hl (hr.frame.trans (ht.frame.trans (hc.frame.trans hreturn)))

/-- The reference saved by a first-child call comes from that child's
actual first descent. It respects the parent's cells and retains the
selected vertex at the target position, even after later siblings return. -/
theorem child_first_store {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv last : Nat} {cell : VSet n} {st leaf : State n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) (first : Bool)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st) last leaf) :
    let raw := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st)).2
    raw.firstlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab raw.firstlab ∧
      raw.firstlab[tc]! = tv := by
  intro raw
  have hchild := h.child hn hl first ht hv
  have he := firstPath_frame path hn (by omega) hchild
  have href := congrArg (fun r => r.2.2) (firstPath_reference (inf := n + 2) path)
  change raw.firstlab = leaf.lab at href
  rw [href]
  exact h.child_store hn hl first ht hv ⟨he.effect.labSize, he.effect.perm⟩

end Hex.GraphIso.Nauty.Sparse
