/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.FirstFrame
public import HexGraphIso.Nauty.Correct.Generation.Tail
public import HexGraphIso.Nauty.Correct.Generation.FirstPath
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.Refine
import all HexGraphIso.Nauty.Invariant.Codes

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- A guiding child that returns to its parent installs all reference
premises needed to exhaust the actual first-path tail. -/
theorem FirstHead.complete
    {inf tcLevel specFuel runFuel level numcells tc len tv1 e : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {tcell : VSet n}
    {pre : SearchSt n} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hpath : level = codes.length) (hrun : n + 2 < level + 1 + runFuel)
    (htcsize : pre.firsttc.size = n + 2)
    (hreturn : ∀ child childTrail,
      FirstInv G ctx (level + 1) codes (numcells + 1) child childTrail →
      PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 (level + 1) child →
      child.noncheaplevel ≤ level + 1 →
      CheapDesc ctx (level + 1) child.noncheaplevel
        (refine ctx (level + 1) child.lab child.ptn child.active (numcells + 1)) →
      OrbSound (OrbConn child.genTrace.toList n) child.orbits n →
      child.firsttc.size = n + 2 →
      (firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1) child).1 = Int.ofNat level)
    (head : FirstHead G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
      codes rsLab rsPtn tcell pre trail) :
    (firstChildLoop ctx inf tcLevel runFuel (n + 1) level numcells tc tv1
      (tcell.nextElem none) tcell 0 pre).1 = none := by
  subst inf
  cases head with
  | @intro offset child out r fs best eventTrail hnext horbit hlab hptn hpathPre hoff hat
      hchild hfirst hpathChild hcheap hdesc horbits hcall hchildRun hkeep tail =>
    have htcChild : child.firsttc.size = n + 2 := by rw [hchild]; exact htcsize
    have hlevel : level + 1 = codes.length + 1 := by omega
    have hr := hreturn child _ hfirst hpathChild hcheap hdesc horbits htcChild
    rw [hcall] at hr
    dsimp only at hr
    have hstay : ¬ r < Int.ofNat level := by rw [hr]; exact Int.lt_irrefl _
    obtain ⟨targets, key, hp, hm⟩ := first_path tcLevel hg runFuel (level + 1) (numcells + 1)
      codes child _ hfirst hpathChild hcheap hdesc horbits (by omega) hlevel htcChild hrun
    obtain ⟨_, _, _, _, hboundary⟩ := first_reference (n + 2) tcLevel hg runFuel (level + 1)
      (numcells + 1) codes child _ hfirst (by omega) hlevel htcChild (by omega)
    have ha := first_agreement (n + 2) tcLevel hg runFuel (level + 1) (numcells + 1)
      codes child _ hfirst (by omega) hlevel htcChild (by omega)
    rw [hcall] at hp hm hboundary ha
    dsimp only at hp hm hboundary ha
    have hpFrozen : ChildPath ctx tcLevel out.allsamelevel level
        (LoopInv.frame rsLab rsPtn numcells) tc targets key offset := by
      change RefPath ctx tcLevel out.allsamelevel (level + 1)
        (refine ctx (level + 1) child.lab child.ptn child.active (numcells + 1)) targets key at hp
      rw [hchild, hlab, hptn, breakout_ptn] at hp
      rw [show (breakout n rsLab rsPtn (level + 1) tc tv1).2.2 = VSet.empty.insert tc from rfl] at hp
      simpa only [ChildPath, childSt, LoopInv.frame, hat] using hp
    let cleaned : SearchSt n := { out with
      gcaFirst := level, stabvertex := tv1, fixedpts := out.fixedpts.erase tv1 }
    let cleared := clearShortIf out.needshortprune cleaned
    let cell := if out.needshortprune then shortprune tcell cleared else tcell
    let recSt := recover n (n + 2) level cleared
    have hf : FirstFields out recSt := by
      apply FirstFields.trans _ (FirstFields.recover (n + 2) level cleared)
      dsimp only [cleared, cleaned, clearShortIf]
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    have heq : recSt.eqlevFirst = level := by
      apply match_recover
      dsimp only [cleared, cleaned, clearShortIf]
      split <;> change level ≤ out.eqlevFirst <;> omega
    have ht := (tail hstay).complete (boundary := out.allsamelevel) hg rfl hpath hrun
      (by omega) hoff hpFrozen (hf.matching hm) heq
      (by rw [hf.same]; exact Nat.le_refl _) (by simp only [cursorRank]; omega)
    rw [hnext, firstChildLoop_stayGuide ctx (n + 2) tcLevel runFuel n level numcells tc tv1 tv1
      tcell 0 pre r out horbit (by simp) (by rw [← hchild]; exact hcall) hstay]
    exact ht _

end Hex.GraphIso.Nauty.Generation
