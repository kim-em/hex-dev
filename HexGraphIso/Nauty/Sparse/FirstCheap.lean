/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CheapHistory
public import HexGraphIso.Nauty.Sparse.SmallStep
public import HexGraphIso.Nauty.Policy.Generic.FirstBounded
import all HexGraphIso.Nauty.Policy.Generic.FirstBounded
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.SmallCell.Transitive
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem prepareFirst_noncheap (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2.noncheaplevel = st.noncheaplevel := by
  exact (chooseTarget_controls true g tcLevel level (visit g level numcells st).1
    (recordFirst level (visit g level numcells st).2.1 (visit g level numcells st).2.2)).2

/-- Descending the actual first branch cannot enable a failed guard above it. -/
theorem firstLeaf_noncheap {g : Graph n} {tcLevel fuel level numcells last bound : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf)
    (hl : bound < level) (h : bound < st.noncheaplevel) : bound < leaf.noncheaplevel := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    rw [prepareFirst_noncheap]
    exact h
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    apply ih (by omega)
    change bound < (cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).noncheaplevel
    unfold cheapCheck
    split
    · change bound < level + 1; omega
    · rw [prepareFirst_noncheap]; exact h

/-- The complete first-path search retains every failed ancestor guard,
including all later siblings and returns past intervening frames. -/
theorem firstPath_noncheap {g : Graph n} {inf tcLevel fuel level numcells last bound : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf)
    (hl : bound < level) (h : bound < st.noncheaplevel) :
    bound < (Generic.node true g inf tcLevel fuel level numcells st).2.noncheaplevel := by
  apply path.bounded (noncheapPolicy g inf tcLevel bound) (fun _ _ _ h => h) (Nat.le_of_lt hl)
  change bound < leaf.noncheaplevel
  exact firstLeaf_noncheap path hl h

/-- A skipped cheap test on the first branch inherits the earlier passing
guard's shape for the literal cached refinement at this entry. -/
def FirstShape (G : Hex.SparseGraph n) (level numcells : Nat) (st : State n) : Prop :=
  st.noncheaplevel < level → NodeShape n level (State.refined (.ofGraph G) level numcells st).ptn

theorem FirstShape.initial (G : Hex.SparseGraph n) (lab : Array Nat) (ends : List Nat) :
    FirstShape G 1 ends.length (initial (.ofGraph G) lab ends) := by
  intro h
  change 1 < 1 at h
  omega

/-- The guard supplies the shape at a first node, either from a preceding
guard or from the actual cheapautom call performed at this level. -/
theorem FirstShape.prepare {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat} {st : State n}
    (h : FirstShape G.graph level numcells st) (hok : NodeInv G level numcells st)
    (hcheap : (cheapCheck true level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.2.2).noncheaplevel ≤ level) :
    NodeShape n level (State.refined (.ofGraph G.graph) level numcells st).ptn := by
  by_cases hbefore : st.noncheaplevel < level
  · exact h hbefore
  have hp := (prepareFirst_partition (.ofGraph G.graph) tcLevel level numcells st).2.1
  have hc : cheapautom (State.refined (.ofGraph G.graph) level numcells st).ptn level n = true := by
    unfold cheapCheck at hcheap
    rw [prepareFirst_noncheap, hp] at hcheap
    have hb : st.noncheaplevel ≥ level := by omega
    cases hguard : cheapautom (State.refined (.ofGraph G.graph) level numcells st).ptn level n with
    | true => rfl
    | false =>
      simp only [Bool.not_true, hb, decide_true, Bool.or_true, hguard, Bool.not_false,
        Bool.and_self, ite_true] at hcheap
      omega
  exact cheapautom_shape_or_exotic hok.refined.spec.node.ptnSize hok.refined.spec.node.ptnEnd hc

/-- The inherited shape extends to each actual first child; its refinement
retains the shape while using the child's real invalidated scratch. -/
theorem FirstShape.child {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells tv : Nat} {st : State n}
    (h : FirstShape G.graph level numcells st) (hok : NodeInv G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level)
    (hv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.1.mem tv = true) :
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    FirstShape G.graph (level + 1) (r.1 + 1)
      ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) := by
  intro r hcheap
  let ready := cheapCheck true level r.2.2.2.2
  have hc : ready.noncheaplevel ≤ level := by
    change ready.noncheaplevel < level + 1 at hcheap
    omega
  have hshape := h.prepare hok hc
  obtain ⟨hr, ht⟩ := hok.prepare (tcLevel := tcLevel) hn hl
  have hready := hr.cheap true
  have htarget := ht.of_out hready.frame.effect
  have hp : ready.ptn = (State.refined (.ofGraph G.graph) level numcells st).ptn := by
    unfold ready cheapCheck
    split <;> exact (prepareFirst_partition (.ofGraph G.graph) tcLevel level numcells st).2.1
  have hchild := hready.ready.child_small hn hl (by rw [hp]; exact hshape) true htarget hv
  exact hchild.2

end Hex.GraphIso.Nauty.Sparse
