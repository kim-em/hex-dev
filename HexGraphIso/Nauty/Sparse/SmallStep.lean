/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SmallCell
public import HexGraphIso.Nauty.Sparse.ChildFrame
public import HexGraphIso.Nauty.Sparse.VisitFrame
public import HexGraphIso.Nauty.Sparse.RefineBoundary

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The full native refinement preserves every cheap-guard shape. Only
its proved boundary writes matter; cache state and splitter order do not. -/
theorem visit_shape (g : Graph n) (level numcells : Nat) (st : State n)
    (hs : st.ptn.size = n) (hend : st.ptn[n - 1]! ≤ level)
    (h : NodeShape n level st.ptn) :
    NodeShape n level (visit g level numcells st).2.2.ptn := by
  have hb := refineWith_boundary g level st.lab st.ptn st.active numcells st.canong.scratch
  exact h.mono hs (hb.size.trans hs) hend (fun _ hq => hb.closed hq)

/-- The actual child transition preserves the cheap shape by adding its
singleton boundary. Refinement of that child preserves it again. -/
theorem child_shape (first : Bool) (level tc tv : Nat) (st : State n)
    (hs : st.ptn.size = n) (hend : st.ptn[n - 1]! ≤ level)
    (h : NodeShape n level st.ptn) :
    NodeShape n (level + 1) ((policy (n := n)).child first level tc tv st).ptn := by
  have hb := (Boundary.refl (level + 1) st.ptn).set tc
  rw [(child_fields first level tc tv st).2.1]
  exact h.mono hs (hb.size.trans hs) hend (fun _ hq => hb.closed (by omega))

namespace Ready

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}

/-- Every selected native child below a cheap-shaped equitable parent
returns an equitable partition of the same shape after its actual visit. -/
theorem child_small (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hshape : NodeShape n level st.ptn) (first : Bool) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    let child := (policy (n := n)).child first level tc tv st
    let r := visit (.ofGraph G.graph) (level + 1) (numcells + 1) child
    Ready G (level + 1) r.1 r.2.2 ∧ NodeShape n (level + 1) r.2.2.ptn := by
  let child := (policy (n := n)).child first level tc tv st
  have he := h.child hn hl first ht hv
  have hp := h.partition hn hl
  have hc := child_shape first level tc tv st hp.ptnSize
    (by simpa only [hp.ptnSize] using hp.ptnEnd) hshape
  refine ⟨he.visit_ready hn (by omega), ?_⟩
  exact visit_shape (.ofGraph G.graph) (level + 1) (numcells + 1) child he.spec.node.ptnSize
    (by simpa only [he.spec.node.ptnSize] using he.spec.node.ptnEnd) hc

end Ready
end Hex.GraphIso.Nauty.Sparse
