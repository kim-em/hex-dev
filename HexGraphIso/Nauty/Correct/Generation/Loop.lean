/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.VisitReceipt
public import HexGraphIso.Nauty.Correct.Generation.Agreement
public import HexGraphIso.Nauty.Correct.Generation.History
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- Above both saved pruning boundaries, a sweep containing the sought
reference returns automorphism evidence. The child premise is the
recursive generation obligation; the sweep proof follows the recorded
visits and their actual short- and long-prune filters. -/
theorem _root_.Hex.GraphIso.Nauty.OtherSweep.reference
    {inf tcLevel specFuel runFuel level numcells tc len tv1 e boundary : Nat}
    {codes fs targets : List Nat} {rsLab rsPtn : Array Nat} {base : SearchSt n} {key : Key n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hpath : level = codes.length) (hrun : n + 2 < level + 1 + runFuel)
    (hboundary : level < boundary)
    (hvisit : ∀ {bs st best trail tv o tcell cursor},
      OtherLoopHyp G ctx tcLevel specFuel level codes bs fs numcells
        rsLab rsPtn tc len tcell cursor e base st best trail →
      tcell.nextElem cursor = some tv → o < len → rsLab[tc + o]! = tv →
      Matches ctx (level + 1) st targets key → st.eqlevFirst = level →
      boundary ≤ st.allsamelevel → st.gcaFirst < level →
      ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key o →
      let child : SearchSt n := { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      RefReturn ctx (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1) child).2
        (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1) child).1)
    {loopFuel : Nat} {cursor : Option Nat} {tcell : VSet n} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (sweep : OtherSweep G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
      codes fs rsLab rsPtn base loopFuel cursor tcell st best trail)
    (hcover : PathCover ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells)
      tc len targets key tcell cursor)
    (hocc : ∃ o, o < len ∧
      ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key o)
    (hpast : CanonPast level tc cursor st)
    (hm : Matches ctx (level + 1) st targets key) (heq : st.eqlevFirst = level)
    (hsame : boundary ≤ st.allsamelevel) (hguide : st.gcaFirst < level)
    (hcheap : level < st.noncheaplevel) :
    let result := otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
      (tcell.nextElem cursor) tcell st
    ∃ r, result.1 = some r ∧ r < Int.ofNat level ∧ RefReturn ctx result.2 r := by
  have hgsz : ctx.g.size = n := by rw [hg]; exact size_rowsOf G
  induction sweep with
  | done hh hnext =>
    obtain ⟨o, ho, hp⟩ := hocc
    exact (hcover.finish hnext o ho hp).elim
  | @visit loopFuel cursor tcell st best trail bs tv offset child out r childBest eventTrail
      hh hnext hoffset hatFrozen hchild hcall hchildRun hkeep continuation ih =>
    have hlevelLt := hh.inv.levelLt
    have hfuel : runFuel ≠ 0 := by omega
    have hfields : FirstFields st out := by
      have hf := other_fields ctx inf tcLevel runFuel (level + 1) (numcells + 1) child
      rw [hcall, hchild] at hf
      exact ⟨hf.codes, hf.targets, hf.lab, hf.same⟩
    have hfirst : out.gcaFirst = st.gcaFirst := by rw [hchildRun.firstGuide, hchild]
    have hcheapOut : level < out.noncheaplevel := by
      by_cases hb : level < out.noncheaplevel
      · exact hb
      · have he := hkeep.boundary (by omega)
        rw [hchild] at he
        dsimp only at he
        omega
    have hearlyReceipt : r < Int.ofNat level → RefReturn ctx out r := by
      intro hr
      apply RefReturn.ofEarly hchildRun.node.exit hfuel hr hcheapOut _ hchildRun.order
      rw [hfields.same]
      omega
    have hcall' : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv } = (r, out) := by
      rw [← hchild]
      exact hcall
    by_cases hstay : r < Int.ofNat level
    · dsimp only
      rw [hnext, otherChildLoop_early ctx inf tcLevel runFuel loopFuel level numcells tc tv1 tv
        tcell st r out hcall' hstay]
      exact ⟨r, rfl, hstay, (hearlyReceipt hstay).setFixed _⟩
    · let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
      let cleared := clearShortIf cleaned.needshortprune cleaned
      let cell := if cleaned.needshortprune then shortprune tcell cleared else tcell
      let cell' := if tv == tv1 then longprune cell cleared.fixedpts cleared.autos else cell
      let recSt := recover n inf level cleared
      have htail := continuation hstay
      change OtherSweep G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
        codes fs rsLab rsPtn base loopFuel (some tv) cell' recSt childBest eventTrail at htail
      obtain ⟨bsNext, hhNext⟩ := htail.hyp
      obtain ⟨o, current, ho, hc, hatF, hatC, hnode⟩ :=
        hh.inv.child (coset := st.cosetindex) hnext (hh.cheapOk hg)
      rw [hatC, ← hchild] at hnode
      have hout : SearchOut G level (level + 1) child out := by
        have hs := otherNode_ok G ctx inf hinf tcLevel hh.inv.nonempty runFuel
          (level + 1) (numcells + 1) child hnode.run.searchOk (by omega) (by omega)
        rw [hcall, Nat.add_sub_cancel] at hs
        exact hs
      have hadv : PathCover ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells)
          tc len targets key tcell (some tv) := by
        apply hcover.visit hh.inv hgsz hnext hpast hc hatC hchild hchildRun hout hguide hstay
        intro o ho hat hp
        have hv := hvisit hh hnext ho hat hm heq hsame hguide hp
        rw [← hchild] at hv
        dsimp only at hv
        rw [hcall] at hv
        exact hv
      have hlen := hh.inv.lenTwo
      have hrange := hh.inv.range
      have hcell : (tc, tc + len - 1) ∈ cells rsPtn level n :=
        isCell_mem_cells hh.inv.cell (by rw [hh.inv.frozenPtnSize]; exact Nat.le_refl _)
          hh.inv.frozenEnd (by omega)
      have hshort : PathCover ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells)
          tc len targets key cell (some tv) := by
        dsimp only [cell]
        split
        · next hs =>
          apply hadv.shortprune hh.inv.tree.it hlevelLt hgsz hcell (by omega) (by omega)
          intro fix mcr hback
          apply LoopInv.ShortSource.atReceiver hpath hh.inv hh.path hchildRun.node.exit
            hchildRun.node.event hchildRun.node.preserved (hchildRun.node.short hs) hstay
          cases hs : out.needshortprune <;>
            simpa only [cleared, cleaned, clearShortIf, hs, Bool.false_eq_true, ite_false, ite_true] using hback
        · exact hadv
      have hfiltered : PathCover ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells)
          tc len targets key cell' (some tv) := by
        dsimp only [cell']
        split
        · apply hshort.longprune hh.inv.tree.it hlevelLt hgsz hcell (by omega) (by omega)
          have hpairs := hhNext.inv.localPairs hhNext.path
          intro p hp hf
          apply hpairs p
          · simpa only [recSt, recover_store] using hp
          · simpa only [recSt, recover_fixedpts] using hf
        · exact hshort
      obtain ⟨hsingle, hpicked⟩ := hh.inv.picked hc hatC hchild
      have hclearedGuide : GuideRel (level + 1) child cleared := by
        apply hchildRun.guide.stateEq
        all_goals dsimp only [cleared, cleaned, clearShortIf]; split <;> rfl
      have hpastRec : CanonPast level tc (some tv) recSt :=
        hpast.recover (nextElem_after hnext) (by rw [hchild]) (by rw [hchild])
          hclearedGuide hsingle hpicked
      have hrecFields : FirstFields st recSt := by
        apply hfields.trans
        apply FirstFields.trans _ (FirstFields.recover inf level cleared)
        dsimp only [cleared, cleaned, clearShortIf]
        split <;> exact ⟨rfl, rfl, rfl, rfl⟩
      have heqOut : level ≤ out.eqlevFirst := by
        have ha := other_agreement ctx inf tcLevel level runFuel (level + 1) (numcells + 1)
          child (by omega) (by rw [hchild]; exact Nat.le_of_eq heq.symm)
        rw [hcall] at ha
        exact ha
      have heqRec : recSt.eqlevFirst = level := by
        apply match_recover
        dsimp only [cleared, cleaned, clearShortIf]
        split <;> exact heqOut
      have hguideRec : recSt.gcaFirst < level := by
        change (recover n inf level cleared).gcaFirst < level
        rw [recF_gcaFirst]
        have he : cleared.gcaFirst = out.gcaFirst := by
          dsimp only [cleared, cleaned, clearShortIf]
          split <;> rfl
        rw [he, hfirst]
        exact hguide
      have hcheapRec : level < recSt.noncheaplevel := by
        change level < (recover n inf level cleared).noncheaplevel
        rw [recover_noncheaplevel]
        have he : cleared.noncheaplevel = out.noncheaplevel := by
          dsimp only [cleared, cleaned, clearShortIf]
          split <;> rfl
        rw [he, ite_eq_left hcheapOut]
        omega
      have hresult := ih hstay hfiltered hpastRec (hrecFields.matching hm) heqRec
        (by rw [hrecFields.same]; exact hsame) hguideRec hcheapRec
      dsimp only
      rw [hnext, otherChildLoop_stay ctx inf tcLevel runFuel loopFuel level numcells tc tv1 tv
        tcell st r out hcall' hstay]
      exact hresult

end Hex.GraphIso.Nauty.Generation
