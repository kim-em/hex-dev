/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Matching
public import HexGraphIso.Nauty.Correct.Base
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Invariant.Codes

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- The first discrete descent installs the exact reference occurrence
used by subsequent matching searches. -/
theorem first_leaf {inf tcLevel fuel level numcells : Nat} {st : SearchSt n}
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells = n)
    (hsize : st.firstcode.size = n + 2) (hlevel : level ≤ n)
    (hdisc : ∀ q, q < n → (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! ≤ level) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let out := (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
    let key : Key n := ⟨[rs.longcode, codeSentinel], leafRows ctx rs.lab⟩
    HasLeaf ctx tcLevel level rs [] key ∧ Matches ctx level out [] key ∧ out.firstlab = rs.lab := by
  dsimp only
  rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
  have hfl : (firstterminal level (firstLeafSt ctx level numcells st)).firstlab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    rw [firstterminal_firstlab]
    rfl
  have hfc : (firstterminal level (firstLeafSt ctx level numcells st)).firstcode =
      (st.firstcode.set! level (refine ctx level st.lab st.ptn st.active numcells).longcode).set!
        (level + 1) codeSentinel := by
    rw [ftF_firstcode]
    rfl
  refine ⟨HasLeaf.leaf hdisc, ⟨?_, ?_, ?_⟩, hfl⟩
  · intro i hi
    dsimp only at hi ⊢
    have hi' : i = 0 ∨ i = 1 := by simp only [List.length_cons, List.length_nil] at hi; omega
    rcases hi' with rfl | rfl
    · simp only [List.getElem!_cons_zero, Nat.add_zero, hfc]
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega), Array.getElem!_set!_self _ _ _ (by omega)]
    · simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, hfc]
      rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_set!, hsize]; omega)]
  · intro i hi
    simp at hi
  · dsimp only
    rw [hfl]

/-- Both ways of returning from a discrete off-path node retain precisely
the trace produced by its leaf event. -/
theorem other_leaf_trace {inf tcLevel fuel level numcells : Nat} {st : SearchSt n}
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells = n) :
    (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.genTrace =
      (processnode ctx level n (otherLeafSt ctx level numcells st)).2.genTrace := by
  by_cases he : (processnode ctx level n (otherLeafSt ctx level numcells st)).1 < Int.ofNat level
  · rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum he]
  · rw [otherNode_leaf_done_state ctx inf tcLevel fuel level numcells st hnum he]
    dsimp only
    unfold leafFinish
    split <;> dsimp only <;> split <;> rfl

/-- A discrete off-path return retains the refined leaf labelling through
both the immediate return and the empty-sweep cleanup. -/
theorem other_leaf_lab {inf tcLevel fuel level numcells : Nat} {st : SearchSt n}
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells = n) :
    (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
  have hp : (processnode ctx level n (otherLeafSt ctx level numcells st)).2.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    rw [processnode_lab]
    exact prepF_lab _ _ _
  by_cases he : (processnode ctx level n (otherLeafSt ctx level numcells st)).1 < Int.ofNat level
  · rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum he]
    exact hp
  · rw [otherNode_leaf_done_state ctx inf tcLevel fuel level numcells st hnum he]
    dsimp only
    unfold leafFinish
    split <;> dsimp only <;> split <;> exact hp

/-- A discrete off-path node containing the matching first-reference leaf
returns an emitted carrier. This is stated for the actual recursive search
call, including its comparison preparation and leaf cleanup. -/
theorem other_leaf {inf tcLevel fuel level numcells : Nat} {st : SearchSt n}
    {targets : List Nat} {key : Key n}
    (hgsz : ctx.g.size = n)
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells = n)
    (hok : IterOk ctx level (refine ctx level st.lab st.ptn st.active numcells))
    (hdisc : ∀ q, q < n → (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! ≤ level)
    (hfirstSize : st.firstlab.size = n) (hfirst : st.firstlab.toList.Perm (List.range n))
    (hperm : (refine ctx level st.lab st.ptn st.active numcells).lab.toList.Perm (List.range n))
    (hm : Matches ctx level st targets key)
    (hleaf : HasLeaf ctx tcLevel level (refine ctx level st.lab st.ptn st.active numcells) targets key)
    (hlevel : st.eqlevFirst = level - 1) :
    LabelCarrier ctx st.firstlab (refine ctx level st.lab st.ptn st.active numcells).lab
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.genTrace ∧
      (st.gcaFirst < level →
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 = Int.ofNat st.gcaFirst) := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let pre := otherLeafSt ctx level numcells st
  have hfl : pre.firstlab = st.firstlab := by
    exact prepF_firstlab _ _ _
  have hlab : pre.lab = rs.lab := by
    exact prepF_lab _ _ _
  have hfc : pre.firstcode = st.firstcode := by
    exact otherNodePrep_firstcode _ _ _
  have hp : pre.eqlevFirst = level := by
    have hc : rs.longcode = st.firstcode[level]! := by
      obtain ⟨tail, ht⟩ := hleaf.head
      have hc := hm.codes 0 (by rw [ht]; simp)
      rw [ht] at hc
      simpa only [List.getElem!_cons_zero, Nat.add_zero] using hc
    change (otherNodePrep level rs.longcode
      { st with lab := rs.lab, ptn := rs.ptn, active := rs.active, numnodes := st.numnodes + 1 }).eqlevFirst = level
    exact match_prep (st :=
      { st with lab := rs.lab, ptn := rs.ptn, active := rs.active, numnodes := st.numnodes + 1 }) hlevel hc
  obtain ⟨hsent, hrows⟩ := hm.discrete hleaf hok hdisc
  have hevent := (rows_emit hgsz (hfl ▸ hfirstSize) (hfl ▸ hfirst)
    (hlab ▸ hok.ok.labSize) (hlab ▸ hperm) (by rw [hfl, hlab]; exact hrows)
    hp (by rw [hfc]; exact hsent)).2
  have hcarrier := hevent.1
  rw [hfl, hlab] at hcarrier
  refine ⟨?_, ?_⟩
  · rw [other_leaf_trace hnum]
    exact hcarrier
  · intro hguide
    have hr := hevent.2
    have hg : pre.gcaFirst = st.gcaFirst := prepF_gcaFirst _ _ _
    rw [hg] at hr
    rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum
      (by rw [hr]; exact Int.ofNat_lt.mpr hguide)]
    exact hr

end Hex.GraphIso.Nauty.Generation
