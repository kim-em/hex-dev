/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Internal
import all HexGraphIso.Nauty.Invariant.Refine
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Correct.Base

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- If a matching reference can be continued through every target child,
the executable's first descent emits its carrier and returns to the first
guide. This common induction serves both cheap and uniform subtrees. -/
theorem descent_reference (inf tcLevel : Nat)
    (hgsz : ctx.g.size = n)
    (P : Nat → RefineSt n → List Nat → Key n → Prop)
    (hvalid : ∀ {level rs targets key}, P level rs targets key →
      IterOk ctx level rs ∧ Equitable ctx level rs.lab rs.ptn ∧
        bcount rs.ptn level n = rs.numcells)
    (hchildren : ∀ {level rs tc e o targets key},
      P level rs (tc :: targets) ⟨rs.longcode :: key.codes, key.rows⟩ →
      level < n → (tc, e) ∈ cells rs.ptn level n → tc < e →
      tc = specTargetcell ctx rs.lab rs.ptn level tcLevel → o ≤ e - tc →
      HasLeaf ctx tcLevel (level + 1) (childSt ctx level rs tc rs.lab[tc + o]!) targets key →
      ∀ o', o' ≤ e - tc →
        P (level + 1) (childSt ctx level rs tc rs.lab[tc + o']!) targets key ∧
        HasLeaf ctx tcLevel (level + 1) (childSt ctx level rs tc rs.lab[tc + o']!) targets key) :
    ∀ fuel level numcells (st : SearchSt n) targets key,
      P level (refine ctx level st.lab st.ptn st.active numcells) targets key →
      st.firstlab.size = n → st.firstlab.toList.Perm (List.range n) →
      Matches ctx level st targets key →
      HasLeaf ctx tcLevel level (refine ctx level st.lab st.ptn st.active numcells) targets key →
      st.eqlevFirst = level - 1 → st.needshortprune = false →
      st.gcaFirst < level → level ≤ n → n < level + fuel →
      let result := otherNode ctx inf tcLevel fuel level numcells st
      result.1 = Int.ofNat st.gcaFirst ∧
        LabelCarrier ctx st.firstlab result.2.lab result.2.genTrace := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st targets key hS hsize hperm hm hleaf hlevel hclear hguide hbound hfuel
    omega
  | succ fuel ih =>
    intro level numcells st targets key hS hsize hperm hm hleaf hlevel hclear hguide hbound hfuel
    let rs := refine ctx level st.lab st.ptn st.active numcells
    change P level rs targets key at hS
    obtain ⟨hit, heqt, hcount⟩ := hvalid hS
    change HasLeaf ctx tcLevel level rs targets key at hleaf
    by_cases hnum : rs.numcells = n
    · have hdisc : ∀ q, q < n → rs.ptn[q]! ≤ level := by
        have hc : List.countP (fun q => decide (rs.ptn[q]! ≤ level)) (List.range n) =
            (List.range n).length := by
          rw [List.length_range]
          exact hcount.trans hnum
        intro q hq
        simpa using List.countP_eq_length.mp hc q (List.mem_range.mpr hq)
      obtain ⟨hc, hr⟩ := other_leaf (inf := inf) (fuel := fuel) hgsz hnum hit hdisc
        hsize hperm (labInj_perm_range hit.ok.labSize hit.ok.labOk hit.inj) hm hleaf hlevel
      refine ⟨hr hguide, ?_⟩
      rw [other_leaf_lab hnum]
      exact hc
    · have hbc : bcount rs.ptn level n < n := by
        rw [hcount]
        have hle : rs.numcells ≤ n := hcount ▸ bcount_le rs.ptn level n
        omega
      rcases hleaf.cases with ⟨hdisc, _, _⟩ | ⟨tc, e, o, rest, tail, hlvl, hcell, hne, ho, htarget, hchildLeaf, rfl, rfl⟩
      · obtain ⟨q, hq, hopen⟩ := exists_open_of_bcount_lt hbc
        have := hdisc q hq
        omega
      have he := target_end_lt hit.ok.ptnSize hit.ok.ptnEnd hcell
      let len := e + 1 - tc
      have hic : IsCell rs.ptn level tc len :=
        cells_isCell (by rw [hit.ok.ptnSize]; exact Nat.le_refl _) hit.ok.ptnEnd _ hcell
      have hce : cellEnd rs.ptn level (tc + 1) = tc + len - 1 :=
        cellEnd_of_isCell hic (by dsimp only [len]; omega) (by rw [hit.ok.ptnSize]; dsimp only [len]; omega)
      have hmt : specMaketargetcell ctx rs.lab rs.ptn level tcLevel =
          (tc, windowSet n rs.lab tc len, len) := by
        rw [specMaketargetcell, ← htarget, hce,
          worksetOf_eq_windowSet _ tc len (by dsimp only [len]; omega)]
        congr 2
        have hlen : 2 ≤ len := by dsimp only [len]; omega
        omega
      obtain ⟨tv, hnext⟩ := nextElem_windowSet_some (lab := rs.lab) (tc := tc) (len := len)
        (by dsimp only [len]; omega) (hit.ok.labOk _ (by rw [hit.ok.labSize]; omega))
      obtain ⟨o', ho', hat⟩ := mem_segN_iff.mp (mem_windowSet.mp (VSet.nextElem_mem hnext)).2
      obtain ⟨hsmall, hocc⟩ := hchildren hS hlvl hcell hne htarget ho hchildLeaf o'
        (by dsimp only [len] at ho'; omega)
      rw [hat] at hocc hsmall
      let pre := otherLeafSt ctx level numcells st
      let target := { pre with tctotal := pre.tctotal + len }
      let ready := if ¬ cheapautom target.ptn level n then
        { target with noncheaplevel := level + 1 } else target
      have hrlab : ready.lab = rs.lab := by
        dsimp only [ready]; split <;> exact prepF_lab _ _ _
      have hrptn : ready.ptn = rs.ptn := by
        dsimp only [ready]; split <;> exact prepF_ptn _ _ _
      have hrfirst : ready.firstlab = st.firstlab := by
        dsimp only [ready]; split <;> exact prepF_firstlab _ _ _
      have hrcode : ready.firstcode = st.firstcode := by
        dsimp only [ready]; split <;> exact otherNodePrep_firstcode _ _ _
      have hrtc : ready.firsttc = st.firsttc := by
        dsimp only [ready]; split <;> exact prepF_firsttc _ _ _
      have hrguide : ready.gcaFirst = st.gcaFirst := by
        dsimp only [ready]; split <;> exact prepF_gcaFirst _ _ _
      have hrclear : ready.needshortprune = false := by
        dsimp only [ready]; split <;> exact (otherLeafSt_short ctx level numcells st).trans hclear
      have hrlevel : ready.eqlevFirst = level := by
        have hp : pre.eqlevFirst = level := by
          apply (hm.stateEq (out := { st with
            lab := rs.lab, ptn := rs.ptn, active := rs.active, numnodes := st.numnodes + 1 }) rfl rfl rfl).prep hleaf
          exact hlevel
        dsimp only [ready]; split <;> exact hp
      let child : SearchSt n := { ready with
        lab := (breakout n ready.lab ready.ptn (level + 1) tc tv).1
        ptn := (breakout n ready.lab ready.ptn (level + 1) tc tv).2.1
        active := (breakout n ready.lab ready.ptn (level + 1) tc tv).2.2
        fixedpts := ready.fixedpts.insert tv }
      have hcrefine : refine ctx (level + 1) child.lab child.ptn child.active (rs.numcells + 1) =
          childSt ctx level rs tc tv := by
        change refine ctx (level + 1) (breakout n ready.lab ready.ptn (level + 1) tc tv).1
          (breakout n ready.lab ready.ptn (level + 1) tc tv).2.1
          (breakout n ready.lab ready.ptn (level + 1) tc tv).2.2 (rs.numcells + 1) = _
        rw [hrlab, hrptn, breakout_ptn]
        rfl
      have hcm : Matches ctx (level + 1) child rest tail :=
        hm.tail.stateEq hrcode hrtc hrfirst
      have hchild := ih (level + 1) (rs.numcells + 1) child rest tail
        (hcrefine ▸ hsmall) (hrfirst ▸ hsize) (hrfirst ▸ hperm) hcm (hcrefine ▸ hocc)
        (by simpa only [Nat.add_sub_cancel] using hrlevel) hrclear
        (by change ready.gcaFirst < level + 1; rw [hrguide]; omega) (by omega) (by omega)
      obtain ⟨r, out, hcall⟩ : ∃ r out,
          otherNode ctx inf tcLevel fuel (level + 1) (rs.numcells + 1) child = (r, out) := ⟨_, _, rfl⟩
      rw [hcall] at hchild
      change r = Int.ofNat ready.gcaFirst ∧ LabelCarrier ctx ready.firstlab out.lab out.genTrace at hchild
      rw [hrguide, hrfirst] at hchild
      have hstate := other_internal (inf := inf) (fuel := fuel) (hcount ▸ hbc) hit heqt hm hleaf hlevel hclear
      rw [hstate]
      dsimp only
      rw [hmt]
      let result := otherChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells tc
        (((windowSet n rs.lab tc len).nextElem none).getD 0)
        ((windowSet n rs.lab tc len).nextElem none) (windowSet n rs.lab tc len) ready
      let result' := match result.1 with
        | some r => (r, result.2)
        | none => (Int.ofNat level - 1, result.2)
      change result'.1 = Int.ofNat st.gcaFirst ∧ LabelCarrier ctx st.firstlab result'.2.lab result'.2.genTrace
      dsimp only [result', result]
      rw [hnext]
      rw [otherChildLoop_early ctx inf tcLevel fuel n level rs.numcells tc ((some tv).getD 0) tv
        (windowSet n rs.lab tc len) ready r out hcall (by rw [hchild.1]; exact Int.ofNat_lt.mpr hguide)]
      exact hchild

end Hex.GraphIso.Nauty.Generation
