/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Uniform
public import HexGraphIso.Nauty.Sparse.MatchingTarget
public import HexGraphIso.Nauty.Sparse.ReferenceStep
import all HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.LeafPath
import all HexGraphIso.Nauty.Sparse.Matching
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A matching uniform native node continues through its actual minimum
cursor. Its cached child retains the uniform suffix and the literal stored
reference, without a cheap-shape or generation-completeness premise. -/
theorem uniform_step {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st : State n} {targets : List Nat} {key : Key n}
    (hn : 0 < n) (hlevel : 1 ≤ level) (hnode : NodeInv G level numcells st)
    (hu : Generation.Uniform G.graph tcLevel level
      (State.refined (.ofGraph G.graph) level numcells st) targets key)
    (hm : Generation.Matches G.graph level st targets key)
    (heq : st.eqlevFirst = level - 1)
    (hnc : (State.refined (.ofGraph G.graph) level numcells st).numcells < n) :
    let p := prepareOther (.ofGraph G.graph) tcLevel level numcells st
    classify (.ofGraph G.graph) level p.1 p.2.2.2.2.2 = (.internal, p.2.2.2.2.2) ∧
      ∃ tv, p.2.2.2.1.nextElem none = some tv ∧
        let ch := (policy (n := n)).child false level p.2.2.1.toNat tv
          (cheapCheck false level p.2.2.2.2.2)
        NodeInv G (level + 1) (p.1 + 1) ch ∧
          ch.gcaFirst = st.gcaFirst ∧ ch.workperm.size = st.workperm.size ∧
          ch.firstlab = st.firstlab ∧ ch.eqlevFirst = level ∧
          ∃ rest tail, Generation.Uniform G.graph tcLevel (level + 1)
            (State.refined (.ofGraph G.graph) (level + 1) (p.1 + 1) ch) rest tail ∧
            Generation.Matches G.graph (level + 1) ch rest tail := by
  let g := Graph.ofGraph G.graph
  let rs := State.refined g level numcells st
  let visited := (visit g level numcells st).2.2
  let compared := compareCodes level rs.longcode visited
  let t := chooseTarget false g tcLevel level rs.numcells compared
  let ready := cheapCheck false level t.2.2.2
  change rs.numcells < n at hnc
  have hr : RefineSt.Ready G.graph level rs := hnode.refined
  obtain ⟨rt, rk, hocc⟩ := Generation.HasLeaf.nonempty (tcLevel := tcLevel) hr
  have he := hu rt rk hocc
  rw [he.1, he.2] at hocc
  have hhead := hm.head hocc
  have hopen : discreteAt rs.ptn level n ≠ true := by
    intro hd
    have hc := (discreteAt_iff_bcount hr.spec.node.ptnSize.symm hr.spec.node.ptnEnd).mp hd
    have he := hr.spec.count
    change rs.numcells < n at hnc
    omega
  have hvisit := hnode.visit_ready hn hlevel
  have hcomp : Local G level rs.numcells visited compared := hvisit.compare rs.longcode
  have htarg : Local G level rs.numcells compared t.2.2.2 := hcomp.ready.target_frame false tcLevel
  have hready : Local G level rs.numcells t.2.2.2 ready := htarg.ready.cheap false
  have hclab : compared.lab = rs.lab := (compareCodes_frame level rs.longcode visited).1
  have hcptn : compared.ptn = rs.ptn := (compareCodes_frame level rs.longcode visited).2.1
  have hc : compared.eqlevFirst = level := by
    rw [compareCodes_eqlev]
    exact ite_eq_left ⟨heq, hhead.1.symm⟩
  have hcRef : compared.reference = st.reference :=
    (referencePolicy g 0 tcLevel).compare level rs.longcode visited
  have htRef : ready.reference = compared.reference :=
    ((referencePolicy g 0 tcLevel).cheap false level t.2.2.2).trans
      (chooseTarget_reference g tcLevel level rs.numcells compared)
  have hrRef : ready.reference = st.reference := htRef.trans hcRef
  have hcTc : compared.firsttc = st.firsttc :=
    congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) hcRef
  have hpos : t.1 = compared.firsttc[level]! := hcomp.ready.match_target hn hlevel hnc hc (by
    rw [hcTc, hclab, hcptn]
    exact hhead.2 hopen)
  have htargetEq : t.2.2.2.eqlevFirst = level := chooseTarget_match g tcLevel level rs.numcells compared hc hpos
  have hreadyEq : ready.eqlevFirst = level := by
    dsimp only [ready]
    unfold cheapCheck
    split <;> exact htargetEq
  have hclass : classify g level rs.numcells t.2.2.2 = (.internal, t.2.2.2) := by
    rw [classify_eq]
    simp only [htargetEq, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false,
      bne_iff_ne.mpr (by omega : rs.numcells ≠ n), ite_true]
  have hselected := hcomp.ready.selected_cell (tcLevel := tcLevel) hn hlevel hnc false (Or.inr (Or.inl hc))
  change IsCell compared.ptn level t.1.toNat t.2.2.1 ∧ 1 < t.2.2.1 ∧ t.1.toNat + t.2.2.1 ≤ n ∧
    t.2.1 = windowSet n compared.lab t.1.toNat t.2.2.1 at hselected
  obtain ⟨tv, hnext⟩ := nextElem_windowSet_some (lab := compared.lab) (by omega : 1 ≤ t.2.2.1)
    (cellsReach_lt hcomp.ready.ok.reach t.1.toNat (by omega))
  rw [← hselected.2.2.2] at hnext
  have hv := VSet.nextElem_mem hnext
  have htarget : Generic.Target State.frame level t.1.toNat t.2.1 ready :=
    (hcomp.ready.target hn hlevel false tcLevel).of_out hready.frame.effect
  have hchild := hready.ready.child hn hlevel false htarget hv
  have hrlab : ready.lab = rs.lab := by
    dsimp only [ready]
    unfold cheapCheck
    split <;> exact (chooseTarget_frame false g tcLevel level rs.numcells compared).1.trans hclab
  have hrptn : ready.ptn = rs.ptn := by
    dsimp only [ready]
    unfold cheapCheck
    split <;> exact (chooseTarget_frame false g tcLevel level rs.numcells compared).2.1.trans hcptn
  obtain ⟨o', ho', hat⟩ := mem_segN_iff.mp (mem_windowSet.mp (hselected.2.2.2 ▸ hv)).2
  rw [hclab] at hat
  rcases hocc.cases with ⟨label, hd, _⟩ |
    ⟨tc, len, o, scratch, rest, tail, hcell, hb, hlen, ho, hs, htargetSpec, hleaf, rfl, rfl⟩
  · exact (hopen hd).elim
  · have htc : t.1.toNat = tc := by
      rw [hpos, hcTc]
      have hh := hm.targets 0 (by simp)
      simpa using congrArg Int.toNat hh
    have hlen' : t.2.2.1 = len := by
      have hcell' := hselected.1
      rw [hcptn, htc] at hcell'
      rcases isCell_disjoint_or_eq hcell' hcell with hh | hh | hh
      · omega
      · omega
      · exact hh.2
    let ch := (policy (n := n)).child false level t.1.toNat tv ready
    have hchRef : ch.reference = st.reference := hrRef
    have hchFirst : ch.firstlab = st.firstlab :=
      congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.2) hchRef
    have hchGca : ch.gcaFirst = st.gcaFirst :=
      ((gcaPolicy g 0 tcLevel).cheap false level t.2.2.2).trans
        ((chooseTarget_controls false g tcLevel level rs.numcells compared).1.trans
          ((gcaPolicy g 0 tcLevel).compare level rs.longcode visited))
    have hchWork : ch.workperm.size = st.workperm.size :=
      (workSizePolicy g 0 tcLevel st.workperm.size).child false level t.1.toNat tv ready
        ((workSizePolicy g 0 tcLevel st.workperm.size).cheap false level t.2.2.2
          ((workSizePolicy g 0 tcLevel st.workperm.size).target false level rs.numcells compared
            ((workSizePolicy g 0 tcLevel st.workperm.size).compare level rs.longcode visited rfl)))
    have hvisit : State.refined g (level + 1) (rs.numcells + 1) ch =
        rs.child g level tc rs.lab[tc + o']! ch.canong.scratch := by
      rw [← htc, hat]
      unfold State.refined RefineSt.child
      rw [(child_fields false level t.1.toNat tv ready).1,
        (child_fields false level t.1.toNat tv ready).2.1,
        (child_fields false level t.1.toNat tv ready).2.2, hrlab, hrptn]
      rfl
    have huc := hu.child hcell hb hlen (show o' < len by omega) hchild.scratch htargetSpec
    refine ⟨hclass, tv, hnext, hchild, hchGca, hchWork, hchFirst, hreadyEq, rest, tail, ?_,
      hm.tail.congr hchRef⟩
    change Generation.Uniform G.graph tcLevel (level + 1)
      (State.refined g (level + 1) (rs.numcells + 1) ch) rest tail
    rw [hvisit]
    exact huc

end Hex.GraphIso.Nauty.Sparse
