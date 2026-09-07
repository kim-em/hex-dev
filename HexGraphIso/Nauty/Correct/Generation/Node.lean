/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.NodeFrame
public import HexGraphIso.Nauty.Correct.Generation.UniformVisit
public import HexGraphIso.Nauty.Correct.Generation.Cheap
import all HexGraphIso.Nauty.Correct.Generation.Control
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- Every valid off-path visit containing the stored first reference
returns automorphism evidence. Uniform and cheap subtrees use their first
descent; the remaining nodes use verified coverage of the actual sweep. -/
theorem other_reference {inf tcLevel : Nat} (hg : ctx.g = rowsOf G) (hinf : inf = n + 2) :
    ∀ fuel level numcells codes bs fs (st : SearchSt n) best trail boundary targets key,
      2 ≤ level → level = codes.length + 1 → n + 2 < level + fuel →
      NodeInv G ctx tcLevel level codes bs fs numcells st best trail →
      Live ctx level st trail →
      PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 level st →
      st.noncheaplevel ≤ level →
      CheapDesc ctx level st.noncheaplevel (refine ctx level st.lab st.ptn st.active numcells) →
      OrbSound (OrbConn st.genTrace.toList n) st.orbits n → st.cosetindex < n →
      (∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b) →
      RefPath ctx tcLevel boundary level (refine ctx level st.lab st.ptn st.active numcells) targets key →
      Matches ctx level st targets key → st.eqlevFirst = level - 1 → boundary ≤ st.allsamelevel →
      RefReturn ctx (otherNode ctx inf tcLevel fuel level numcells st).2
        (otherNode ctx inf tcLevel fuel level numcells st).1 := by
  have hgsz : ctx.g.size = n := by rw [hg]; exact size_rowsOf G
  have hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
    rw [hg]; exact rowsOf_symm G
  have hloopless : ∀ v, v < n → (ctx.g[v]!).mem v = false := by
    rw [hg]; exact rowsOf_loopless G
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells codes bs fs st best trail boundary targets key hl hpath hfuel hnode
    have hb := hnode.run.searchOk.bc
    have hn := bcount_le st.ptn level n
    omega
  | succ fuel ih =>
    intro level numcells codes bs fs st best trail boundary targets key hl hpath hfuel
      hnode hlive hpathOk hcheap hdesc horb hcoset hdom hp hm heq hsame
    have hbound : level ≤ n := Nat.le_trans hnode.run.searchOk.bc (bcount_le _ _ _)
    have hn0 : 0 < n := by omega
    let rs := refine ctx level st.lab st.ptn st.active numcells
    have ht := hnode.tree hg hn0 (by omega)
    have hsize := hnode.run.leafRefs.firstSize
    have hperm : st.firstlab.toList.Perm (List.range n) :=
      labInj_perm_range hsize (labOk_of_reach hsize hnode.run.leafRefs.firstReach)
        (labInj_of_reach hsize hn0 hnode.run.leafRefs.firstReach)
    have hfields := other_fields ctx inf tcLevel (fuel + 1) level numcells st
    have hcontrol := (node_control ctx inf tcLevel (fuel + 1) level numcells st hnode.shortClear).1
    have firstReturn :
        ((otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 = Int.ofNat st.gcaFirst ∧
          LabelCarrier ctx st.firstlab (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.lab
            (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2.genTrace) →
        RefReturn ctx (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
      intro h
      apply RefReturn.first
      · rw [hcontrol]; exact h.1
      · rw [hfields.lab]; exact h.2
    have emit : Uniform ctx tcLevel level rs targets key →
        RefReturn ctx (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
      intro hu
      exact firstReturn (uniform_reference hgsz hsymm ht hu hsize hperm hm heq
        hnode.shortClear hnode.firstBelow (by omega))
    by_cases hb : boundary ≤ level
    · exact emit (hp.uniform ht.it hb)
    have hleaf := hp.occurs
    cases hp with
    | leaf hd => exact emit (Uniform.leaf ht.it hd)
    | @step _ tc endPos o _ rest tail hlvl hcell hne ho htarget hchild hu =>
      by_cases hc : cheapautom rs.ptn level n = true
      · exact firstReturn (cheap_reference inf tcLevel hgsz hsymm hloopless (fuel + 1)
          level numcells st _ _ (hdesc.atLevel ht.it ht.eqt ht.acc hcheap (fun _ => hc))
          hsize hperm hm hleaf heq hnode.shortClear hnode.firstBelow hbound (by omega))
      have hcFalse : cheapautom rs.ptn level n = false := Bool.eq_false_iff.mpr hc
      have hend := target_end_lt ht.it.ok.ptnSize ht.it.ok.ptnEnd hcell
      have hic : IsCell rs.ptn level tc (endPos + 1 - tc) :=
        cells_isCell (by rw [ht.it.ok.ptnSize]; exact Nat.le_refl _) ht.it.ok.ptnEnd _ hcell
      have hnum : rs.numcells < n := by
        have hle : rs.numcells ≤ n := ht.acc ▸ bcount_le rs.ptn level n
        by_cases he : rs.numcells = n
        · have hcount : List.countP (fun q => decide (rs.ptn[q]! ≤ level)) (List.range n) =
              (List.range n).length := by rw [List.length_range]; exact ht.acc.trans he
          have hclosed := List.countP_eq_length.mp hcount tc (List.mem_range.mpr (by omega))
          have hopen := hic.2.2.1 tc (Nat.le_refl _) (by omega)
          simp only [decide_eq_true_eq] at hclosed
          omega
        · omega
      have heqPre : (otherLeafSt ctx level numcells st).eqlevFirst = level := by
        apply (hm.stateEq (out := { st with
          lab := rs.lab, ptn := rs.ptn, active := rs.active, numnodes := st.numnodes + 1 }) rfl rfl rfl).prep hleaf
        exact heq
      obtain ⟨tc', len, hmt, htrace⟩ := hnode.referenceSweep (specFuel := n - level) (runFuel := fuel)
        hg hinf hn0 hl hpath (by omega) (by omega) hcheap hdesc hlive hpathOk horb hcoset hdom hnum heqPre
      have htc : tc' = tc := by
        have hm := congrArg Prod.fst hmt
        change specTargetcell ctx rs.lab rs.ptn level tcLevel = tc' at hm
        exact hm.symm.trans htarget.symm
      subst tc'
      let cell := worksetOf n rs.lab tc (tc + len - 1)
      let start := sweepStart ctx level numcells len st
      let full := codes ++ [rs.longcode]
      change OtherSweep G ctx inf tcLevel (n - level) fuel level rs.numcells tc len
        ((cell.nextElem none).getD 0) st.noncheaplevel full fs rs.lab rs.ptn start
        (n + 1) none cell start best trail at htrace
      obtain ⟨_, hh⟩ := htrace.hyp
      have hlen2 := hh.inv.lenTwo
      have hrange := hh.inv.range
      have hlen : len = endPos + 1 - tc := by
        rcases isCell_disjoint_or_eq hic hh.inv.cell with h | h | h
        · omega
        · omega
        · exact h.2.symm
      have hfull : level = full.length := by
        simp only [full, List.length_append, List.length_singleton]
        omega
      have hs := sweepStart_fields ctx level numcells len st
      obtain ⟨_, _, _, _, hsFirst, hsCanon, _, _, _, _, _, _, _, hsPark, _⟩ :=
        sweepStart_frames ctx level numcells len st
      have hstartEq : start.eqlevFirst = level := by
        unfold start sweepStart
        dsimp only
        split <;> exact heqPre
      have hloop :
          let result := otherChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells tc
            ((cell.nextElem none).getD 0) (cell.nextElem none) cell start
          ∃ r, result.1 = some r ∧ r < Int.ofNat level ∧ RefReturn ctx result.2 r := by
        apply htrace.reference (boundary := boundary) (targets := rest) (key := tail) hg hinf hfull (by omega) (by omega)
        · intro bsC stC bestC trailC tv oC cellC cursorC hhC hnC hoC hatC hmC heqC hsC hgC hpC
          obtain ⟨off, cur, hoff, hcur, hatF, hatCur, hnChild⟩ :=
            hhC.inv.child (coset := stC.cosetindex) hnC (hhC.cheapOk hg)
          rw [hatCur] at hnChild
          let child : SearchSt n := { stC with
            lab := (breakout n stC.lab stC.ptn (level + 1) tc tv).1
            ptn := (breakout n stC.lab stC.ptn (level + 1) tc tv).2.1
            active := (breakout n stC.lab stC.ptn (level + 1) tc tv).2.2
            fixedpts := stC.fixedpts.insert tv }
          let childTrail := trailC.push level ⟨sweepFrame (n - level) full rs.lab rs.ptn tc rs.numcells, off⟩
          have hlChild : Live ctx (level + 1) child childTrail := by
            have h := hhC.inv.otherChildLive hhC.live off cur
            rw [hatCur] at h
            exact h
          have hpChild : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
              (initialPartition G).1 (level + 1) child := by
            have h := hhC.path.breakout hhC.inv hcur
            rw [hatCur] at h
            exact h
          have hdChild := hhC.inv.childDesc hg hhC.desc hhC.park hcur hatCur
          have hrChild := hhC.inv.childPath hgsz hoC hcur (hatCur.trans hatC.symm) hpC
          rw [hatCur] at hrChild
          have hrefChild : RefPath ctx tcLevel boundary (level + 1)
              (refine ctx (level + 1) child.lab child.ptn child.active (rs.numcells + 1)) rest tail := by
            change RefPath ctx tcLevel boundary (level + 1)
              (refine ctx (level + 1) (breakout n stC.lab stC.ptn (level + 1) tc tv).1
                (breakout n stC.lab stC.ptn (level + 1) tc tv).2.1
                (breakout n stC.lab stC.ptn (level + 1) tc tv).2.2 (rs.numcells + 1)) rest tail
            rw [breakout_ptn]
            exact hrChild
          exact ih (level + 1) (rs.numcells + 1) full bsC fs child bestC childTrail boundary rest tail
            (by omega) (by omega) (by omega) hnChild hlChild hpChild hhC.bnd hdChild
            hhC.orbits hhC.coset hhC.firstDom hrefChild (hmC.stateEq rfl rfl rfl)
            (by simpa only [Nat.add_sub_cancel] using heqC) hsC
        · change PathCover ctx tcLevel boundary level (LoopInv.frame rs.lab rs.ptn rs.numcells)
            tc len rest tail (worksetOf n rs.lab tc (tc + len - 1)) none
          rw [worksetOf_eq_windowSet _ tc len (by omega)]
          apply PathCover.start
          intro j hj
          exact hh.inv.frozenLabOk _ (by rw [hh.inv.frozenLabSize]; omega)
        · exact ⟨o, by omega, hchild⟩
        · apply CanonPast.start
          rw [hsCanon]
          exact hnode.canonBelow
        · exact hs.matching hm.tail
        · exact hstartEq
        · rw [hs.same]
          exact hsame
        · rw [hsFirst]
          exact hnode.firstBelow
        · rw [hsPark hcFalse]
          omega
      obtain ⟨r, hr, _, hreceipt⟩ := hloop
      rw [other_internal_sweep hnum ht.it ht.eqt hm hleaf heq hnode.shortClear]
      rw [hmt]
      change RefReturn ctx
        (match (otherChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells tc
          ((cell.nextElem none).getD 0) (cell.nextElem none) cell start).1 with
          | some r => (r, (otherChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells tc
              ((cell.nextElem none).getD 0) (cell.nextElem none) cell start).2)
          | none => (Int.ofNat level - 1, (otherChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells tc
              ((cell.nextElem none).getD 0) (cell.nextElem none) cell start).2)).2 _
      rw [hr]
      exact hreceipt

end Hex.GraphIso.Nauty.Generation
