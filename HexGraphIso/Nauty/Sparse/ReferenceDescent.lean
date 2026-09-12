/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceStep
import all HexGraphIso.Nauty.Sparse.FirstRef
import all HexGraphIso.Nauty.Sparse.DescentAt
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native node matching a saved cheap descent follows its executed
minimum cursors until it emits an automorphism carrying the saved label
to the returned label. The proof follows the actual recursion bound and
does not assume a return, a generated carrier, or a search maximum. -/
theorem cheap_reference {G : GraphIso.Sparse.Colored n k} {base : Nat} {root : RefineSt n}
    (inf tcLevel : Nat) (hn : 0 < n) (hr : RefineSt.Ready G.graph base root)
    (hshape : NodeShape n base root.ptn) :
    ∀ fuel level numcells (st : State n) (href : FirstRef G.graph tcLevel base root st) (f : Label n),
      1 ≤ level → NodeInv G level numcells st → st.workperm.size = n →
      Label.ofArray? n st.firstlab = some f → CellsReach G.toDense st.firstlab →
      level ≤ href.last →
      FollowsPerm G.graph st.firsttc base root level (State.refined (.ofGraph G.graph) level numcells st) →
      (State.refined (.ofGraph G.graph) level numcells st).longcode = st.firstcode[level]! →
      st.eqlevFirst = level - 1 → st.gcaFirst < level → n < level + fuel →
      let out := Generic.node false (.ofGraph G.graph) inf tcLevel fuel level numcells st
      out.1 = .unwind st.gcaFirst false ∧
        LabelCarrier (Graph.context G.graph) st.firstlab out.2.lab out.2.genTrace := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st href f hlevel hnode hw hf hrf hdepth hfollow hcode heq hg hbudget
    have hd := hnode.ok.bc
    have hb := bcount_le st.ptn level n
    change level ≤ bcount st.ptn level n at hd
    omega
  | succ fuel ih =>
    intro level numcells st href f hlevel hnode hw hf hrf hdepth hfollow hcode heq hg hbudget
    let g := Graph.ofGraph G.graph
    let rs := State.refined g level numcells st
    have hcurrent : RefineSt.Ready G.graph level rs := hnode.refined
    by_cases hd : rs.numcells = n
    · obtain ⟨l, hl⟩ := Label.ofArray?_exists hcurrent.spec.label
      have hdisc : discreteAt rs.ptn level n = true := by
        apply (discreteAt_iff_bcount hcurrent.spec.node.ptnSize.symm hcurrent.spec.node.ptnEnd).mpr
        rw [← hcurrent.spec.count, hd]
      have hrows := (href.leaf_follows hdepth hr hcurrent hshape hfollow hdisc hf hl).2
      exact matching_leaf hn hlevel hnode hw hf hrf hl hd hcode hrows heq
    have hnc : rs.numcells < n := by
      have hc := hcurrent.spec.count
      have hb := bcount_le rs.ptn level n
      omega
    let p := prepareOther g tcLevel level numcells st
    obtain ⟨hclass, tv, hnext, hlast, hchRef, hchild, hchGca, hchWork, hchFirst,
      hchEq, hchFollow, hchCode⟩ := reference_step hn hlevel hnode href hr hshape hdepth hfollow hcode heq hnc
    let ready := cheapCheck false level p.2.2.2.2.2
    let ch := (policy (n := n)).child false level p.2.2.1.toNat tv ready
    have hcRef : ch.reference = st.reference := hchRef
    let nextRef := href.congr hcRef
    have hresult := ih (level + 1) (p.1 + 1) ch nextRef f (by omega) hchild
      (hchWork.trans hw) (by rw [hchFirst]; exact hf) (by rw [hchFirst]; exact hrf)
      hlast hchFollow hchCode (by simpa only [Nat.add_sub_cancel] using hchEq)
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

/-- A recovered cheap parent reaches its saved reference through every
surviving target child. The conclusion includes the carrier in the actual
emitted trace, and permits either native child-entry mode. -/
theorem DescentAt.child_returns {G : GraphIso.Sparse.Colored n k}
    {tcLevel base level numcells tc tv : Nat} {root : RefineSt n} {st : State n}
    {cell : VSet n} {f : Label n}
    (hd : DescentAt G.graph st.firsttc base root level numcells st)
    (href : FirstRef G.graph tcLevel base root st) (hdepth : level ≤ href.last)
    (hr : RefineSt.Ready G.graph base root) (hshape : NodeShape n base root.ptn)
    (hready : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hnc : numcells < n) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (htc : st.firsttc[level]! = Int.ofNat tc)
    (hw : st.workperm.size = n) (hf : Label.ofArray? n st.firstlab = some f)
    (hrf : CellsReach G.toDense st.firstlab) (heq : st.eqlevFirst = level)
    (hg : st.gcaFirst ≤ level) (first : Bool) (inf fuel : Nat) (hbudget : n < level + 1 + fuel) :
    let ch := (policy (n := n)).child first level tc tv st
    let out := Generic.node false (.ofGraph G.graph) inf tcLevel fuel (level + 1) (numcells + 1) ch
    out.1 = .unwind st.gcaFirst false ∧
      LabelCarrier (Graph.context G.graph) st.firstlab out.2.lab out.2.genTrace := by
  have hdesc := hd
  obtain ⟨current, hc, hh, _, _, hcount⟩ := hdesc
  have hopen : discreteAt current.ptn level n ≠ true := by
    intro hdisc
    have hb := (discreteAt_iff_bcount hc.spec.node.ptnSize.symm hc.spec.node.ptnEnd).mp hdisc
    have hn' := hc.spec.count
    omega
  have hlast : level + 1 ≤ href.last := by
    have := href.next_depth hdepth hr hshape hh hopen
    omega
  have hchild := hready.child hn hl first ht hv
  obtain ⟨len, ht, hm⟩ := ht
  obtain ⟨hcell, hlen, hb⟩ := ht (mem_ne_empty hv)
  obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp (hm tv hv)
  change st.lab[tc + o]! = tv at hat
  have hvisit := href.child_visit hlast hr hshape hd first hcell hb (by omega) ho htc
    hready.scratch.toBounded
  rw [hat] at hvisit
  let ch := (policy (n := n)).child first level tc tv st
  have hreference : ch.reference = st.reference := by cases first <;> rfl
  have hfields : ch.firsttc = st.firsttc ∧ ch.firstcode = st.firstcode ∧
      ch.firstlab = st.firstlab ∧ ch.workperm.size = st.workperm.size ∧
      ch.eqlevFirst = st.eqlevFirst ∧ ch.gcaFirst = st.gcaFirst := by cases first <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  let nextRef := href.congr hreference
  have hresult := cheap_reference inf tcLevel hn hr hshape fuel (level + 1) (numcells + 1)
    ch nextRef f (by omega) hchild (hfields.2.2.2.1.trans hw)
    (by rw [hfields.2.2.1]; exact hf) (by rw [hfields.2.2.1]; exact hrf)
    hlast (by rw [hfields.1]; exact hvisit.1)
    (by rw [hfields.2.1]; exact hvisit.2)
    (by rw [hfields.2.2.2.2.1, heq, Nat.add_sub_cancel])
    (by rw [hfields.2.2.2.2.2]; omega) hbudget
  dsimp only
  rw [hfields.2.2.2.2.2, hfields.2.2.1] at hresult
  exact hresult

end Hex.GraphIso.Nauty.Sparse
