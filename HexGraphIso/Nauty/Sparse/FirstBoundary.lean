/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CheapBoundary
public import HexGraphIso.Nauty.Sparse.FirstCheap
import all HexGraphIso.Nauty.Policy.Generic.FirstBounded
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Boundary
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual first descent retains an older boundary or replaces it
strictly below a fixed ancestor. -/
theorem firstLeaf_boundary {g : Graph n} {tcLevel fuel level numcells last bound saved : Nat}
    {st leaf : State n} (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf)
    (hl : bound < level) (h : st.noncheaplevel = saved ∨ bound < st.noncheaplevel) :
    leaf.noncheaplevel = saved ∨ bound < leaf.noncheaplevel := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    rw [prepareFirst_noncheap]
    exact h
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    apply ih (by omega)
    change (cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).noncheaplevel = saved ∨
      bound < (cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).noncheaplevel
    unfold cheapCheck
    split
    · exact Or.inr (by change bound < level + 1; omega)
    · rw [prepareFirst_noncheap]; exact h

/-- Completing the first node, including later siblings, cannot replace
its incoming boundary strictly above that node. -/
theorem firstPath_boundary {g : Graph n} {inf tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf) (hl : 0 < level) :
    (Generic.node true g inf tcLevel fuel level numcells st).2.noncheaplevel = st.noncheaplevel ∨
      level ≤ (Generic.node true g inf tcLevel fuel level numcells st).2.noncheaplevel := by
  have hh : (Generic.node true g inf tcLevel fuel level numcells st).2.noncheaplevel = st.noncheaplevel ∨
      level - 1 < (Generic.node true g inf tcLevel fuel level numcells st).2.noncheaplevel := by
    apply path.bounded (boundaryPolicy g inf tcLevel (level - 1) st.noncheaplevel)
      (fun _ _ _ h => h) (by omega)
    change leaf.noncheaplevel = st.noncheaplevel ∨ level - 1 < leaf.noncheaplevel
    exact firstLeaf_boundary path (by omega) (Or.inl rfl)
  exact hh.imp id (by omega)

/-- The complete first-child call preserves its still-active older pairs.
This uses actual first-path existence and native frame preservation. -/
theorem CheapBoundary.firstNode {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (h : CheapBoundary G level st) (hn : 0 < n) (hl : 1 < level) (hi : NodeInv G level numcells st)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf) :
    CheapBoundary G level (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 :=
  Nauty.Boundary.of_out h hl (node_frame G hn true tcLevel fuel level numcells st (by omega) hi).effect
    (firstPath_noncheap path (by omega) h.positive) (firstPath_boundary path (by omega))

end Hex.GraphIso.Nauty.Sparse
