/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.UniformStep
import all HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.LeafPath
import all HexGraphIso.Nauty.Sparse.Matching
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A uniform matching native subtree follows its executed minimum
cursors until it emits a checked first-reference carrier. This is a proof
of the real recursion and scatter, without assumed generation or returns. -/
theorem uniform_reference {G : GraphIso.Sparse.Colored n k} (inf tcLevel : Nat) (hn : 0 < n) :
    ∀ fuel level numcells (st : State n) targets key,
      1 ≤ level → NodeInv G level numcells st →
      Generation.Uniform G.graph tcLevel level
        (State.refined (.ofGraph G.graph) level numcells st) targets key →
      st.workperm.size = n → CellsReach G.toDense st.firstlab →
      Generation.Matches G.graph level st targets key →
      st.eqlevFirst = level - 1 → st.gcaFirst < level → n < level + fuel →
      let out := Generic.node false (.ofGraph G.graph) inf tcLevel fuel level numcells st
      out.1 = .unwind st.gcaFirst false ∧
        LabelCarrier (Graph.context G.graph) st.firstlab out.2.lab out.2.genTrace := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st targets key hlevel hnode hu hw hrf hm heq hg hbudget
    have hd := hnode.ok.bc
    have hb := bcount_le st.ptn level n
    change level ≤ bcount st.ptn level n at hd
    omega
  | succ fuel ih =>
    intro level numcells st targets key hlevel hnode hu hw hrf hm heq hg hbudget
    let g := Graph.ofGraph G.graph
    let rs := State.refined g level numcells st
    have hr : RefineSt.Ready G.graph level rs := hnode.refined
    by_cases hd : rs.numcells = n
    · obtain ⟨label, hparse⟩ := Label.ofArray?_exists hr.spec.label
      have hdisc : discreteAt rs.ptn level n = true := by
        apply (discreteAt_iff_bcount hr.spec.node.ptnSize.symm hr.spec.node.ptnEnd).mpr
        rw [← hr.spec.count, hd]
      have hleaf := Generation.HasLeaf.leaf (G := G.graph) (tcLevel := tcLevel) hdisc hparse
      obtain ⟨htargets, hkey⟩ := hu _ _ hleaf
      have hocc : Generation.HasLeaf G.graph tcLevel level rs targets key := by
        rw [← htargets, ← hkey]
        exact hleaf
      have hcode := (hm.head hocc).1.symm
      obtain ⟨first, hfirst, hgraph⟩ := hm.graph
      have hrows : G.graph.relabel label.perm = G.graph.relabel first.perm :=
        (congrArg Key.graph hkey).trans hgraph
      exact matching_leaf hn hlevel hnode hw hfirst hrf hparse hd hcode hrows heq
    have hnc : rs.numcells < n := by
      have hc := hr.spec.count
      have hb := bcount_le rs.ptn level n
      omega
    let p := prepareOther g tcLevel level numcells st
    obtain ⟨hclass, tv, hnext, hchild, hchGca, hchWork, hchFirst, hchEq,
      rest, tail, huc, hmc⟩ := uniform_step hn hlevel hnode hu hm heq hnc
    let ready := cheapCheck false level p.2.2.2.2.2
    let ch := (policy (n := n)).child false level p.2.2.1.toNat tv ready
    have hresult := ih (level + 1) (p.1 + 1) ch rest tail (by omega) hchild huc
      (hchWork.trans hw) (by rw [hchFirst]; exact hrf) hmc
      (by simpa only [Nat.add_sub_cancel] using hchEq)
      (by rw [hchGca]; omega) (by omega)
    let raw := Generic.node false g inf tcLevel fuel (level + 1) (p.1 + 1) ch
    have hret : raw.1 = .unwind st.gcaFirst false := hresult.1.trans (by rw [hchGca])
    have hsweep : Generic.sweep false g inf tcLevel fuel (n + 1) level p.1 p.2.2.1.toNat tv
        (some tv) p.2.2.2.1 0 ready =
        (.unwind st.gcaFirst false, 0, { raw.2 with fixedpts := raw.2.fixedpts.erase tv }) := by
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [Bool.not_false, Bool.true_or, Bool.false_and, Bool.false_eq_true, ite_true, ite_false]
      change Generic.advance inf _ false level p.1 p.2.2.1.toNat tv tv p.2.2.2.1 0
        { raw.2 with fixedpts := raw.2.fixedpts.erase tv } raw.1 = _
      rw [hret]
      simp only [Generic.advance, hg, ite_true, Id.run_pure]
    have hcall : Generic.node false g inf tcLevel (fuel + 1) level numcells st =
        (.unwind st.gcaFirst false, { raw.2 with fixedpts := raw.2.fixedpts.erase tv }) := by
      rw [Generic.node]
      simp only [Generic.nodeStep, Bool.false_eq_true, ite_false]
      change (Id.run do
        let c := classify g level p.1 p.2.2.2.2.2
        let result := leafExit c.1 level c.2
        match result.1 with
        | .done =>
          let s := Generic.sweep false g inf tcLevel fuel (n + 1) level p.1 p.2.2.1.toNat
            ((p.2.2.2.1.nextElem none).getD 0) (p.2.2.2.1.nextElem none) p.2.2.2.1 0
            (cheapCheck false level result.2)
          match s.1 with
          | .done => pure (.unwind (level - 1) false,
              (policy (n := n)).afterSweep false level p.2.2.2.2.1 s.2.1 s.2.2)
          | _ => pure (s.1, s.2.2)
        | _ => pure result) = _
      have hcl : classify g level p.1 p.2.2.2.2.2 = (.internal, p.2.2.2.2.2) := hclass
      rw [hcl]
      simp only [show leafExit .internal level p.2.2.2.2.2 = (.done, p.2.2.2.2.2) from rfl]
      change (match (Generic.sweep false g inf tcLevel fuel (n + 1) level p.1 p.2.2.1.toNat
        ((p.2.2.2.1.nextElem none).getD 0) (p.2.2.2.1.nextElem none) p.2.2.2.1 0 ready).1 with
        | .done => _
        | _ => _) = _
      have hnxt : p.2.2.2.1.nextElem none = some tv := hnext
      rw [hnxt]
      simp only [Option.getD_some]
      rw [hsweep]
      rfl
    dsimp only
    rw [hcall]
    exact ⟨rfl, hchFirst ▸ hresult.2⟩

end Hex.GraphIso.Nauty.Sparse
