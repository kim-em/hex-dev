/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstChoice
public import HexGraphIso.Nauty.Sparse.PathCodes
public import HexGraphIso.Nauty.Policy.First.History
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual first descent stores its selected native target path and
every executed refinement code. Its mathematical leaf has the literal
label and partition of the prepared production leaf. -/
theorem firstPath_history {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (hn : 0 < n)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st)
    (htsize : n < st.firsttc.size) (hcsize : n < st.firstcode.size) :
    ∃ xs U codes, ∃ trace : CodePath G.graph level (State.refined (.ofGraph G.graph) level numcells st)
        xs last U codes,
      trace.Selects tcLevel ∧ Targets leaf.firsttc level (xs.map Prod.fst) ∧
      StoredCodes leaf.firstcode level codes ∧ U.lab = leaf.lab ∧ U.ptn = leaf.ptn ∧
      discreteAt U.ptn last n = true := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    let R := State.refined (.ofGraph G.graph) level numcells st
    have hp := prepareFirst_partition (.ofGraph G.graph) tcLevel level numcells st
    have hr := h.refined
    have hlevel : level ≤ n := Nat.le_trans h.spec.depth (by rw [h.spec.count]; exact bcount_le _ _ _)
    refine ⟨[], R, [R.longcode], .refl level R, trivial, ?_, ?_, hp.1.symm, hp.2.1.symm, ?_⟩
    · intro i hi
      simp at hi
    · intro i hi
      have hi0 : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst i
      simp only [Nat.add_zero, List.getElem!_cons_zero]
      rw [(prepareFirst_store (.ofGraph G.graph) tcLevel level numcells st).1,
        Array.getElem!_set!_self _ _ _ (by omega)]
      rfl
    · apply (discreteAt_iff_bcount hr.spec.node.ptnSize.symm hr.spec.node.ptnEnd).mpr
      have hc := hr.spec.count
      have hp' := hp.2.2
      change (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 = n at hdisc
      omega
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let R := State.refined (.ofGraph G.graph) level numcells st
    have hp := prepareFirst_partition (.ofGraph G.graph) tcLevel level numcells st
    obtain ⟨hr, ht⟩ := h.prepare (tcLevel := tcLevel) hn hl
    have hcheap := hr.cheap true
    have htarget := ht.of_out hcheap.frame.effect
    have hmem := VSet.nextElem_mem htv
    have hchild := hcheap.ready.child hn hl true htarget hmem
    let child := (policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)
    have hsize : (child.firstcode.size, child.firsttc.size) = (st.firstcode.size, st.firsttc.size) :=
      (firstPath_storeSize tail).symm.trans (firstPath_storeSize (.step hopen htv horbit tail))
    have hcs : n < child.firstcode.size := by rw [(Prod.mk.inj hsize).1]; exact hcsize
    have hts : n < child.firsttc.size := by rw [(Prod.mk.inj hsize).2]; exact htsize
    obtain ⟨len, hcell, hseg⟩ := ht
    obtain ⟨hc, hlen, hb⟩ := hcell (mem_ne_empty hmem)
    obtain ⟨o, ho, hlabel⟩ := mem_segN_iff.mp (hseg tv hmem)
    change r.2.2.2.2.lab[r.2.1.toNat + o]! = tv at hlabel
    rw [hp.1] at hlabel
    have hcR : IsCell R.ptn level r.2.1.toNat len := by
      change IsCell r.2.2.2.2.ptn level r.2.1.toNat len at hc
      rw [hp.2.1] at hc
      exact hc
    have hstep : State.refined (.ofGraph G.graph) (level + 1) (r.1 + 1) child =
        R.child (.ofGraph G.graph) level r.2.1.toNat R.lab[r.2.1.toNat + o]! child.canong.scratch := by
      rw [firstChild_refined, hlabel]
    have htail := ih (by omega) hchild hts hcs
    change ∃ xs U codes, ∃ trace : CodePath G.graph (level + 1)
        (State.refined (.ofGraph G.graph) (level + 1) (r.1 + 1) child) xs last U codes,
      trace.Selects tcLevel ∧ Targets leaf.firsttc (level + 1) (xs.map Prod.fst) ∧
      StoredCodes leaf.firstcode (level + 1) codes ∧ U.lab = leaf.lab ∧ U.ptn = leaf.ptn ∧
      discreteAt U.ptn last n = true at htail
    rw [hstep] at htail
    obtain ⟨xs, U, codes, trace, hsel, htargets, hcodes, hUL, hUP, hd⟩ := htail
    have hchoice := prepareFirst_choice h hn hl hopen
    have htarget : r.2.1.toNat = targetcell (.ofGraph G.graph) R.lab R.ptn level tcLevel (-1) := by
      rw [hchoice]
      rfl
    have hlevel : level ≤ n := Nat.le_trans h.spec.depth (by rw [h.spec.count]; exact bcount_le _ _ _)
    have hcode : leaf.firstcode[level]! = R.longcode := by
      rw [(Prod.mk.inj (firstPath_before tail (slot := level) (by omega))).1]
      change (cheapCheck true level r.2.2.2.2).firstcode[level]! = _
      unfold cheapCheck
      split <;> rw [(prepareFirst_store (.ofGraph G.graph) tcLevel level numcells st).1,
        Array.getElem!_set!_self _ _ _ (by omega)]
      all_goals rfl
    have htc : leaf.firsttc[level]! = Int.ofNat r.2.1.toNat := by
      rw [(Prod.mk.inj (firstPath_before tail (slot := level) (by omega))).2]
      change (cheapCheck true level r.2.2.2.2).firsttc[level]! = _
      unfold cheapCheck
      split <;> rw [(prepareFirst_store (.ofGraph G.graph) tcLevel level numcells st).2,
        Array.getElem!_set!_self _ _ _ (by omega)]
      all_goals rw [hchoice]; rfl
    refine ⟨(r.2.1.toNat, o) :: xs, U, R.longcode :: codes,
      .step _ len o child.canong.scratch hcR hb (by omega) ho hchild.scratch trace,
      (by simpa only [CodePath.Selects] using And.intro htarget hsel),
      Targets.cons htc htargets, StoredCodes.cons hcode hcodes, hUL, hUP, hd⟩

end Hex.GraphIso.Nauty.Sparse
