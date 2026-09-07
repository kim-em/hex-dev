/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.FirstReturn
public import HexGraphIso.Nauty.Correct.Generation.FirstCoverage
public import HexGraphIso.Nauty.Correct.Generation.HeadPrune
import all HexGraphIso.Nauty.Correct.Generation.Trace
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.Refine
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Invariant.Codes

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k}

/-- A complete first-path sweep generates the full orbit of its guiding
vertex, assuming generation in the next point stabilizer. The guiding
short-prune filter and all later visits use the actual search trace. -/
theorem FirstHead.cover
    {tcLevel specFuel runFuel level numcells tc len e : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {tcell : VSet n}
    {pre : SearchSt n} {trail : FrameTrail} {base : List (Fin n)} {guide : Fin n}
    (hpath : level = codes.length) (hrun : n + 2 < level + 1 + runFuel)
    (htcsize : pre.firsttc.size = n + 2)
    (hwindow : tcell = windowSet n rsLab tc len)
    (hbase : ∀ b : Fin n, pre.fixedpts.mem b.val = true ↔ b ∈ base)
    (hdeep : ∀ p, IsIso G G p → Perm.Fixes (guide :: base) p → Perm.Generated (Aut.gens G) p)
    (head : FirstHead G { g := rowsOf G } (n + 2) tcLevel specFuel runFuel level numcells tc len guide.val e
      codes rsLab rsPtn tcell pre trail)
    (htrace : ∀ γ ∈ (firstChildLoop { g := rowsOf G } (n + 2) tcLevel runFuel (n + 1)
      level numcells tc guide.val (tcell.nextElem none) tcell 0 pre).2.2.genTrace, γ ∈ Aut.trace G) :
    ∀ v, Aut.Orbit G base guide v → Aut.Carries G base guide v := by
  let ctx : Ctx n := { g := rowsOf G }
  cases head with
  | @intro offset child out r fs best eventTrail hnext horbit hlab hptn hpathPre hoff hat
      hchild hfirst hpathChild hcheap hdesc horbits hcall hchildRun hkeep tail =>
    have htcChild : child.firsttc.size = n + 2 := by rw [hchild]; exact htcsize
    have hlevel : level + 1 = codes.length + 1 := by omega
    have hr := first_return (ctx := ctx) tcLevel rfl runFuel (level + 1) (numcells + 1) codes child _
      hfirst hpathChild hcheap hdesc horbits (by omega) hlevel htcChild hrun
    rw [hcall] at hr
    have hreturn : r = Int.ofNat level := by
      dsimp only at hr
      exact hr.trans (by simp only [Int.ofNat_eq_natCast]; omega)
    have hstay : ¬ r < Int.ofNat level := by rw [hreturn]; exact Int.lt_irrefl _
    let cleaned : SearchSt n := { out with
      gcaFirst := level, stabvertex := guide.val, fixedpts := out.fixedpts.erase guide.val }
    let cleared := clearShortIf out.needshortprune cleaned
    let cell := if out.needshortprune then shortprune tcell cleared else tcell
    let recSt := recover n (n + 2) level cleared
    let index := if recSt.orbits[guide.val]! == guide.val then 0 + 1 else 0
    have htail := tail hstay
    change FirstTail G ctx (n + 2) tcLevel specFuel runFuel level numcells tc len guide.val e
      codes fs rsLab rsPtn pre n (some guide.val) cell recSt best eventTrail at htail
    obtain ⟨bs, hh⟩ := htail.hyp
    have hlen := hh.inv.lenTwo
    have hrange := hh.inv.range
    have hpos : tc < n := by omega
    have hsize : pre.lab.size = n := hh.inv.baseOk.labSize
    have hlabOk : LabOk pre.lab n := labOk_of_reach hsize hh.inv.baseOk.reach
    have hinj : LabInj pre.lab n := labInj_of_reach hsize hh.inv.nonempty hh.inv.baseOk.reach
    have hcellPre : IsCell pre.ptn level tc len := by rw [hptn]; exact hh.inv.cell
    have hfresh : pre.fixedpts.mem guide.val = false := by
      have h := hpathPre.fixed.fresh hlabOk hinj hsize hcellPre hlen hrange hoff
      rw [hlab, hat] at h
      exact h
    have hfixed : recSt.fixedpts = pre.fixedpts := by
      dsimp only [recSt]
      rw [recover_fixedpts, (clearShortIf_fields _ _).1]
      change out.fixedpts.erase guide.val = pre.fixedpts
      rw [hchildRun.proof.node.fixed, hchild]
      exact erase_insert_of_miss hfresh
    have hgen : recSt.genTrace = out.genTrace := by
      dsimp only [recSt]
      rw [recover_genTrace]
      dsimp only [cleared, cleaned, clearShortIf]
      split <;> rfl
    have hstate := firstChildLoop_stayGuide ctx (n + 2) tcLevel runFuel n level numcells tc
      guide.val guide.val tcell 0 pre r out horbit (by simp)
      (by rw [← hchild]; exact hcall) hstay
    rw [hnext, hstate] at htrace
    have htraceRec : ∀ γ ∈ (firstChildLoop ctx (n + 2) tcLevel runFuel n level numcells tc guide.val
        (cell.nextElem (some guide.val)) cell index recSt).2.2.genTrace, γ ∈ Aut.trace G := htrace
    have htraceOut : ∀ γ ∈ out.genTrace, γ ∈ Aut.trace G := by
      intro γ hγ
      apply htraceRec
      apply firstLoop_retains (first_retains ctx (n + 2) tcLevel runFuel)
      rwa [hgen]
    have hfixFrame : ∀ γ, CellStab rsPtn level rsLab γ → ∀ b ∈ base, γ[b.val]! = b.val := by
      intro γ hγ
      apply frame_fixes hpathPre.fixed hsize (fun b hb => (hbase b).mpr hb)
      rwa [hptn, hlab]
    have hfixOut : ∀ γ ∈ out.genTrace, ∀ b ∈ base, γ[b.val]! = b.val := by
      intro γ hγ
      apply hfixFrame γ
      apply hh.live.frameStab
      change γ ∈ recSt.genTrace.toList
      simpa only [hgen, Array.mem_toList_iff] using hγ
    have hentry := hchildRun.proof.node.outcome.preserved.pushAt
    obtain ⟨_, _, _, hfirstAt⟩ := hchildRun.proof.trail.picked level _ (by omega) hentry
    obtain ⟨_, _, _, hcanonAt⟩ := hchildRun.proof.canonTrail.picked level _ (by omega) hentry
    change out.firstlab[tc]! = rsLab[tc + offset]! at hfirstAt
    change out.canonlab[tc]! = rsLab[tc + offset]! at hcanonAt
    rw [hat] at hfirstAt hcanonAt
    have hf : FirstFields out recSt := by
      apply FirstFields.trans _ (FirstFields.recover (n + 2) level cleared)
      dsimp only [cleared, cleaned, clearShortIf]
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    have hpast : CanonPast level tc (some guide.val) recSt := by
      constructor
      · dsimp only [recSt]
        rw [recover_gcaCanon]
        split <;> omega
      · intro _
        change ¬ guide.val < recSt.canonlab[tc]!
        have he : recSt.canonlab = out.canonlab := by
          dsimp only [recSt]
          rw [(recover_frames n (n + 2) level cleared).1]
          dsimp only [cleared, cleaned, clearShortIf]
          split <;> rfl
        rw [he, hcanonAt]
        omega
    have hcover : Cover G base guide tcell (some guide.val) := by
      have hstart := Cover.window (G := G) hpathPre.stab hlabOk hcellPre
        (by rw [hsize]; exact hrange) (fun b hb => (hbase b).mp hb)
        (guide := guide) (by rw [hlab, ← hwindow]; exact VSet.nextElem_mem hnext)
      rw [hlab, ← hwindow] at hstart
      exact hstart.advance hnext (fun _ => Aut.Carries.refl G base guide)
    have hfiltered : Cover G base guide cell (some guide.val) := by
      dsimp only [cell]
      split
      · next hshort =>
        have hpreserved : TrailExt (level + 1)
            (eventTrail.push level ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
            eventTrail := by
          intro target htarget
          by_cases heq : target = level
          · subst target
            rw [FrameTrail.push_self]
            exact hentry
          · rw [FrameTrail.push_of_ne _ _ heq]
        have hsource := hchildRun.short hshort
        have hevent := hchildRun.proof.node.outcome.event
        rw [hreturn] at hsource hevent
        have hc := hcover.shortSource rfl hpath hh.inv hh.path hevent hpreserved hsource hat
          (fun b hb => by rw [hfixed]; exact (hbase b).mpr hb) htraceOut hfixOut hdeep
        dsimp only [cleared, cleaned, clearShortIf]
        split <;> exact hc
      · exact hcover
    obtain ⟨targets, key, hp, hm⟩ := first_path (ctx := ctx) tcLevel rfl runFuel (level + 1) (numcells + 1)
      codes child _ hfirst hpathChild hcheap hdesc horbits (by omega) hlevel htcChild hrun
    obtain ⟨_, _, _, _, hboundary⟩ := first_reference (ctx := ctx) (n + 2) tcLevel rfl runFuel (level + 1)
      (numcells + 1) codes child _ hfirst (by omega) hlevel htcChild (by omega)
    have ha := first_agreement (ctx := ctx) (n + 2) tcLevel rfl runFuel (level + 1) (numcells + 1)
      codes child _ hfirst (by omega) hlevel htcChild (by omega)
    rw [hcall] at hp hm hboundary ha
    dsimp only at hp hm hboundary ha
    have hpFrozen : ChildPath ctx tcLevel out.allsamelevel level
        (LoopInv.frame rsLab rsPtn numcells) tc targets key offset := by
      rw [hchild, hlab, hptn, breakout_ptn] at hp
      rw [show (breakout n rsLab rsPtn (level + 1) tc guide.val).2.2 = VSet.empty.insert tc from rfl] at hp
      simpa only [ChildPath, childSt, LoopInv.frame, hat] using hp
    have heq : recSt.eqlevFirst = level := by
      apply match_recover
      dsimp only [cleared, cleaned, clearShortIf]
      split <;> change level ≤ out.eqlevFirst <;> omega
    apply htail.cover rfl rfl hpath hrun (by omega) hoff hpFrozen ?_ hfixFrame
      (hf.matching hm) heq (by rw [hf.same]; exact Nat.le_refl _)
      (by simp only [cursorRank]; omega) (by rw [hf.lab]; exact hfirstAt)
      hpast hfiltered index htraceRec
    intro v hv o ho hatV
    have hcell : (tc, tc + len - 1) ∈ cells rsPtn level n :=
      isCell_mem_cells hh.inv.cell (by rw [hh.inv.frozenPtnSize]; exact Nat.le_refl _)
        hh.inv.frozenEnd (by omega)
    exact hpFrozen.orbit hh.inv.tree.it hh.inv.levelLt hpathPre.stab hlab hptn
      (fun b hb => (hbase b).mp hb) hcell (by omega) (by omega) (by omega) hat hatV hv

end Hex.GraphIso.Nauty.Generation
