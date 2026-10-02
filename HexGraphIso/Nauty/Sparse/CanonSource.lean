/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonCalls
import all HexGraphIso.Nauty.Policy.Canon.Frame
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A label stored inside an actual individualized child retains the
chosen vertex at its target position and respects the parent's cells. -/
theorem Ready.child_store {G : GraphIso.Sparse.Colored n k} {level numcells tc tv : Nat}
    {st : State n} {lab : Array Nat} {cell : VSet n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) (first : Bool)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hs : let ch := (policy (n := n)).child first level tc tv st
      lab.size = ch.lab.size ∧ cellsPerm ch.ptn (level + 1) ch.lab lab) :
    lab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab lab ∧ lab[tc]! = tv := by
  apply Nauty.child_store (ctx := Graph.context G.graph) first hn hl h.ok ht hv
  cases first <;> exact hs

/-- A complete native child either retains the old canonical reference
without deepening its ancestor, or installs a reference through its chosen
vertex. This is independent of pruning correctness or generator completeness. -/
theorem child_canon {G : GraphIso.Sparse.Colored n k} {tcLevel fuel level numcells tc tv : Nat}
    {st : State n} {cell : VSet n} (h : Ready G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (first childFirst : Bool)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    let out := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    (out.gcaCanon ≤ st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab ∧
        out.canonlab[tc]! = tv) := by
  let ch := (policy (n := n)).child first level tc tv st
  have hc := h.child hn hl first ht hv
  have hr := node_canon G hn childFirst tcLevel fuel (level + 1) (numcells + 1) ch (by omega) hc
  rcases hr.source with hr | hr
  · left
    cases first <;> exact hr
  · exact Or.inr (h.child_store hn hl first ht hv hr.2)

/-- A returned canonical ancestor above the child identifies exactly the
parent's incoming reference and ancestor, even if that same label is reachable
again inside the child's subtree. -/
theorem child_canon_old {G : GraphIso.Sparse.Colored n k} {tcLevel fuel level numcells tc tv : Nat}
    {st : State n} {cell : VSet n} (h : Ready G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (first childFirst : Bool)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    let out := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    out.gcaCanon ≤ level → out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab := by
  intro out he
  let ch := (policy (n := n)).child first level tc tv st
  have hc := h.child hn hl first ht hv
  have hr := node_canon G hn childFirst tcLevel fuel (level + 1) (numcells + 1) ch (by omega) hc
  have hs := hr.old (by change out.gcaCanon < level + 1; omega)
  cases first <;> exact hs

end Hex.GraphIso.Nauty.Sparse
