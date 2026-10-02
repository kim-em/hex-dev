/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstFields
public import HexGraphIso.Nauty.Sparse.RefinedNode
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The literal cached refinement performed by a production node. -/
@[expose] def State.refined (g : Graph n) (level numcells : Nat) (st : State n) : RefineSt n :=
  refineWith g level st.lab st.ptn st.active numcells st.canong.scratch

theorem NodeInv.refined {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}
    (h : NodeInv G level numcells st) :
    RefineSt.Ready G.graph level (State.refined (.ofGraph G.graph) level numcells st) :=
  h.spec.refineWith st.canong.scratch h.scratch

/-- First preparation retains exactly the partition and count returned by
its cached visit while recording the reference code and target. -/
theorem prepareFirst_partition (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    let r := Generic.prepareFirst g tcLevel level numcells st
    r.2.2.2.2.lab = (State.refined g level numcells st).lab ∧
      r.2.2.2.2.ptn = (State.refined g level numcells st).ptn ∧
      r.1 = (State.refined g level numcells st).numcells := by
  have hf := chooseTarget_frame true g tcLevel level (visit g level numcells st).1
    (recordFirst level (visit g level numcells st).2.1 (visit g level numcells st).2.2)
  exact ⟨hf.1, hf.2.1, rfl⟩

/-- The first child's production visit is a step of the native descent
relation with precisely the scratch stored by that child transition. -/
theorem firstChild_refined (g : Graph n) (tcLevel level numcells tv : Nat) (st : State n) :
    let r := Generic.prepareFirst g tcLevel level numcells st
    let child := (policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)
    State.refined g (level + 1) (r.1 + 1) child =
      (State.refined g level numcells st).child g level r.2.1.toNat tv child.canong.scratch := by
  let r := Generic.prepareFirst g tcLevel level numcells st
  have hf := child_fields true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)
  have hp := prepareFirst_partition g tcLevel level numcells st
  have hc : (cheapCheck true level r.2.2.2.2).lab = r.2.2.2.2.lab ∧
      (cheapCheck true level r.2.2.2.2).ptn = r.2.2.2.2.ptn := by
    unfold cheapCheck
    split <;> exact ⟨rfl, rfl⟩
  dsimp only
  change State.refined g (level + 1) (r.1 + 1) _ = _
  unfold State.refined RefineSt.child
  rw [hf.1, hf.2.1, hf.2.2, hc.1, hc.2, hp.1, hp.2.1, hp.2.2]
  rfl

end Hex.GraphIso.Nauty.Sparse
