/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceEmit
public import HexGraphIso.Nauty.Sparse.SelectedCell
import all HexGraphIso.Nauty.Sparse.FirstRef
import all HexGraphIso.Nauty.Sparse.DescentAt
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A matching open node takes its actual minimum target vertex and
retains the saved reference and matching code at the resulting cached
child visit. All inputs describe native entry states and saved histories. -/
theorem reference_step {G : GraphIso.Sparse.Colored n k} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : State n} (hn : 0 < n) (hlevel : 1 ≤ level)
    (hnode : NodeInv G level numcells st) (href : FirstRef G.graph tcLevel base root st)
    (hr : RefineSt.Ready G.graph base root) (hshape : NodeShape n base root.ptn)
    (hdepth : level ≤ href.last)
    (hfollow : FollowsPerm G.graph st.firsttc base root level
      (State.refined (.ofGraph G.graph) level numcells st))
    (hcode : (State.refined (.ofGraph G.graph) level numcells st).longcode = st.firstcode[level]!)
    (heq : st.eqlevFirst = level - 1)
    (hnc : (State.refined (.ofGraph G.graph) level numcells st).numcells < n) :
    let p := prepareOther (.ofGraph G.graph) tcLevel level numcells st
    classify (.ofGraph G.graph) level p.1 p.2.2.2.2.2 = (.internal, p.2.2.2.2.2) ∧
      ∃ tv, p.2.2.2.1.nextElem none = some tv ∧
        let ch := (policy (n := n)).child false level p.2.2.1.toNat tv
          (cheapCheck false level p.2.2.2.2.2)
        level + 1 ≤ href.last ∧ ch.reference = st.reference ∧
          NodeInv G (level + 1) (p.1 + 1) ch ∧
          ch.gcaFirst = st.gcaFirst ∧ ch.workperm.size = st.workperm.size ∧
          ch.firstlab = st.firstlab ∧ ch.eqlevFirst = level ∧
          FollowsPerm G.graph ch.firsttc base root (level + 1)
            (State.refined (.ofGraph G.graph) (level + 1) (p.1 + 1) ch) ∧
          (State.refined (.ofGraph G.graph) (level + 1) (p.1 + 1) ch).longcode = ch.firstcode[level + 1]! := by
  let g := Graph.ofGraph G.graph
  let rs := State.refined g level numcells st
  let visited := (visit g level numcells st).2.2
  let compared := compareCodes level rs.longcode visited
  let t := chooseTarget false g tcLevel level rs.numcells compared
  let ready := cheapCheck false level t.2.2.2
  change rs.numcells < n at hnc
  have hcurrent : RefineSt.Ready G.graph level rs := hnode.refined
  have hvisit := hnode.visit_ready hn hlevel
  have hcomp : Local G level rs.numcells visited compared := hvisit.compare rs.longcode
  have htarg : Local G level rs.numcells compared t.2.2.2 := hcomp.ready.target_frame false tcLevel
  have hready : Local G level rs.numcells t.2.2.2 ready := htarg.ready.cheap false
  have hc : compared.eqlevFirst = level := by
    rw [compareCodes_eqlev]
    exact ite_eq_left ⟨heq, hcode⟩
  have hcRef : compared.reference = st.reference :=
    (referencePolicy g 0 tcLevel).compare level rs.longcode visited
  have htRef : ready.reference = compared.reference :=
    ((referencePolicy g 0 tcLevel).cheap false level t.2.2.2).trans
      (chooseTarget_reference g tcLevel level rs.numcells compared)
  have hrRef : ready.reference = st.reference := htRef.trans hcRef
  have hcTc : compared.firsttc = st.firsttc :=
    congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) hcRef
  have hrTc : ready.firsttc = compared.firsttc :=
    congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) htRef
  have hdesc : DescentAt G.graph st.firsttc base root level rs.numcells visited :=
    ⟨rs, hcurrent, hfollow, rfl, rfl, rfl⟩
  have hcompDesc : DescentAt G.graph compared.firsttc base root level rs.numcells compared := by
    rw [hcTc]
    exact hdesc.congr (compareCodes_frame level rs.longcode visited).1
      (compareCodes_frame level rs.longcode visited).2.1
  let compRef := href.congr hcRef
  have hcompDepth : Depth compRef.last compared :=
    ⟨by rw [hc]; exact hdepth, compRef.sentinel⟩
  have hpos : t.1 = compared.firsttc[level]! :=
    hcompDesc.target compRef hcompDepth hc hnc hr hshape hcomp.ready.scratch
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
  obtain ⟨len, ht, hm⟩ := htarget
  obtain ⟨hcell, hlen, hb⟩ := ht (mem_ne_empty hv)
  obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp (hm tv hv)
  change ready.lab[t.1.toNat + o]! = tv at hat
  have hslot : ready.firsttc[level]! = Int.ofNat t.1.toNat := by
    rw [hrTc, ← hpos]
    exact (chooseTarget_cast hnc hc).symm
  have hreadyDesc : DescentAt G.graph ready.firsttc base root level rs.numcells ready := by
    rw [hrTc]
    apply hcompDesc.congr
    · dsimp only [ready]
      unfold cheapCheck
      split <;> exact (chooseTarget_frame false g tcLevel level rs.numcells compared).1
    · dsimp only [ready]
      unfold cheapCheck
      split <;> exact (chooseTarget_frame false g tcLevel level rs.numcells compared).2.1
  have hopen : discreteAt rs.ptn level n ≠ true := by
    intro hd
    have hh := (discreteAt_iff_bcount hcurrent.spec.node.ptnSize.symm hcurrent.spec.node.ptnEnd).mp hd
    have hh' := hcurrent.spec.count
    change rs.numcells < n at hnc
    omega
  have hlast : level + 1 ≤ href.last := by
    have hh := href.next_depth hdepth hr hshape hfollow hopen
    omega
  let readyRef := href.congr hrRef
  have hstep := readyRef.child_visit hlast hr hshape hreadyDesc false hcell hb
    (by omega) ho hslot hready.ready.scratch.toBounded
  rw [hat] at hstep
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
  refine ⟨hclass, tv, hnext, hlast, hchRef, hchild,
    hchGca, hchWork, hchFirst, hreadyEq, hstep⟩

end Hex.GraphIso.Nauty.Sparse
