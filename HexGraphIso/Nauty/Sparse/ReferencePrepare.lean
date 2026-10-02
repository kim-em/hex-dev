/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MatchingTarget
public import HexGraphIso.Nauty.Sparse.Matching
public import HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Sparse.Matching
import all HexGraphIso.Nauty.Sparse.LeafPath
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A matching selected occurrence keeps the production comparison on
the first reference and selects its stored target through the actual
cached dispatch. The node need not be cheap or uniform. -/
theorem matching_prepare {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st : State n} {targets : List Nat} {key : Key n}
    (hn : 0 < n) (hl : 1 ≤ level) (hnode : NodeInv G level numcells st)
    (hocc : Generation.HasLeaf G.graph tcLevel level
      (State.refined (.ofGraph G.graph) level numcells st) targets key)
    (hm : Generation.Matches G.graph level st targets key)
    (heq : st.eqlevFirst = level - 1)
    (hnc : (State.refined (.ofGraph G.graph) level numcells st).numcells < n) :
    let p := prepareOther (.ofGraph G.graph) tcLevel level numcells st
    classify (.ofGraph G.graph) level p.1 p.2.2.2.2.2 = (.internal, p.2.2.2.2.2) ∧
      p.2.2.1 = st.firsttc[level]! ∧ (cheapCheck false level p.2.2.2.2.2).eqlevFirst = level := by
  let g := Graph.ofGraph G.graph
  let rs := State.refined g level numcells st
  let visited := (visit g level numcells st).2.2
  let compared := compareCodes level rs.longcode visited
  let t := chooseTarget false g tcLevel level rs.numcells compared
  change rs.numcells < n at hnc
  have hr : RefineSt.Ready G.graph level rs := hnode.refined
  have hhead := hm.head hocc
  have hopen : discreteAt rs.ptn level n ≠ true := by
    intro hd
    have hc := (discreteAt_iff_bcount hr.spec.node.ptnSize.symm hr.spec.node.ptnEnd).mp hd
    have he := hr.spec.count
    omega
  have hcomp : Local G level rs.numcells visited compared := (hnode.visit_ready hn hl).compare rs.longcode
  have hclab : compared.lab = rs.lab := (compareCodes_frame level rs.longcode visited).1
  have hcptn : compared.ptn = rs.ptn := (compareCodes_frame level rs.longcode visited).2.1
  have hc : compared.eqlevFirst = level := by
    rw [compareCodes_eqlev]
    exact ite_eq_left ⟨heq, hhead.1.symm⟩
  have href : compared.reference = st.reference :=
    (referencePolicy g 0 tcLevel).compare level rs.longcode visited
  have htc : compared.firsttc = st.firsttc :=
    congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) href
  have hpos : t.1 = compared.firsttc[level]! := hcomp.ready.match_target hn hl hnc hc (by
    rw [htc, hclab, hcptn]
    exact hhead.2 hopen)
  have htEq : t.2.2.2.eqlevFirst = level := chooseTarget_match g tcLevel level rs.numcells compared hc hpos
  have hclass : classify g level rs.numcells t.2.2.2 = (.internal, t.2.2.2) := by
    rw [classify_eq]
    simp only [htEq, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false,
      bne_iff_ne.mpr (by omega : rs.numcells ≠ n), ite_true]
  refine ⟨hclass, hpos.trans (by rw [htc]), ?_⟩
  change (cheapCheck false level t.2.2.2).eqlevFirst = level
  unfold cheapCheck
  split <;> exact htEq

end Hex.GraphIso.Nauty.Sparse
