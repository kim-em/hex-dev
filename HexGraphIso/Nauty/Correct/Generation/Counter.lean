/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Counted
public import HexGraphIso.Nauty.Correct.Generation.Control
public import HexGraphIso.Nauty.Correct.Generation.Head
import all HexGraphIso.Nauty.Correct.Generation.Counted
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Correct.Outcome

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

set_option maxHeartbeats 1600000 in
/-- The actual first-path sibling loop counts distinct original vertices
with checked carriers to its guide. Early returns retain the old count;
a successful visit or orbit skip performs the same Boolean increment as
the executable. -/
theorem firstTail_counted {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tv1 e : Nat}
    {codes fs : List Nat} {rsLab rsPtn : Array Nat} {base : SearchSt n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2) (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hrun : n + 2 < level + 1 + runFuel) (hspec : level + 1 + specFuel = n + 1)
    (hpath : level = codes.length) :
    ∀ loopFuel cursor (tcell : VSet n) (st : SearchSt n) best trail bs index,
      FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn tc len
        tcell cursor e tv1 base st best trail →
      Counted (segN rsLab tc len)
        (fun v => ∃ γ, checkAutom ctx.g γ = true ∧ CellStab rsPtn level rsLab γ ∧ γ[v]! = tv1)
        cursor index →
      ∃ last, Counted (segN rsLab tc len)
        (fun v => ∃ γ, checkAutom ctx.g γ = true ∧ CellStab rsPtn level rsLab γ ∧ γ[v]! = tv1)
        last (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
          (tcell.nextElem cursor) tcell index st).2.1 ∧
        FirstTail G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
          codes fs rsLab rsPtn base loopFuel cursor tcell st best trail := by
  intro loopFuel
  induction loopFuel with
  | zero =>
    intro cursor tcell st best trail bs index hh hc
    refine ⟨cursor, ?_, .zero hh⟩
    simpa only [firstChildLoop] using hc
  | succ loopFuel ihLoop =>
    intro cursor tcell st best trail bs index hh hc
    have hgsz : ctx.g.size = n := by rw [hg]; exact size_rowsOf G
    have hlevelLt : level < n := hh.inv.levelLt
    have hpositive : 1 ≤ level := hh.inv.positive
    have hfuelNe : runFuel ≠ 0 := by omega
    have hcodesLen : codes.length = level := hpath.symm
    cases hnext : tcell.nextElem cursor with
    | none =>
      refine ⟨cursor, ?_, .done hh hnext⟩
      simpa only [firstChildLoop] using hc
    | some tv =>
      have htvLt : tv < n := hh.inv.nextLt hnext
      have hafter : tv1 < tv := by
        obtain ⟨v, hv, hle⟩ := hh.after
        have ha := nextElem_after hnext
        rw [hv] at ha
        simp only [After] at ha
        omega
      have hother : (tv == tv1) = false := by simp only [beq_eq_false_iff_ne]; omega
      obtain ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen, hat⟩ := hh.inv.nextOffsets hnext
      have hm : tv ∈ segN rsLab tc len := mem_segN_iff.mpr ⟨offset, hoffset, hatFrozen⟩
      cases horb : st.orbits[tv]! == tv with
      | false =>
        have hinj : LabInj rsLab rsLab.size := by
          rw [← hh.inv.baseLab, hh.inv.baseOk.labSize]
          exact labInj_of_reach hh.inv.baseOk.labSize hh.inv.nonempty hh.inv.baseOk.reach
        have hcover := hh.inv.cover.orbitSkip hnext hoffset hatFrozen hgsz
          (fun γ hγ => hh.inv.run.genTraceOk.check hγ) hh.live.frameStab
          hh.inv.frozenLabSize hinj hh.inv.frozenLabOk hh.inv.frozenPtnSize
          hh.inv.frozenEnd hh.inv.frozenVals hh.inv.cell hh.inv.range hh.inv.fuelBound
          hh.orbits (by intro heq; rw [heq] at horb; simp at horb)
        have hhSkip : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
            tc len tcell (some tv) e tv1 base st best trail :=
          ⟨{ hh.inv with cover := hcover }, hh.live, hh.path, ⟨tv, rfl, Nat.le_of_lt hafter⟩,
            fun v hv => by cases hv; exact htvLt, hh.sign, hh.guide, hh.firstTrail,
            hh.canonTrail, hh.orbits, hh.coset, hh.firstDom, hh.desc, hh.bnd, hh.park, hh.keep⟩
        have hcNext := hc.cellStep (nextElem_after hnext) hm htvLt hh.inv.frozenLabOk
          hh.inv.frozenPtnSize hh.inv.frozenLabSize hh.inv.frozenEnd hh.orbits
          (fun γ hγ => hh.inv.run.genTraceOk.check hγ) hh.live.frameStab
        obtain ⟨last, htail, htrace⟩ := ihLoop (some tv) tcell st best trail bs _ hhSkip hcNext
        refine ⟨last, ?_, .skip hh hnext horb htrace⟩
        rw [firstChildLoop_skip ctx inf tcLevel runFuel loopFuel level numcells tc tv1 tv tcell index st horb]
        exact htail
      | true =>
        have hcheapOk := hh.cheapOk hg
        obtain ⟨offset', currentOffset', hoffset', hcurrent', hatFrozen', hat', hnodeChild⟩ :=
          hh.inv.child (coset := tv) hnext hcheapOk
        rw [hat'] at hnodeChild
        let child : SearchSt n := { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
          cosetindex := tv }
        let childTrail := trail.push level ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset'⟩
        have hdescChild := hh.inv.childDescWeak hg hh.desc hh.bnd hh.park hcurrent hat
        have hliveChild : Live ctx (level + 1) child childTrail := by
          have h := hh.inv.firstChildLive (coset := tv) hh.live offset' currentOffset'
          rw [hat'] at h
          exact h
        have hpathChild : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
            (initialPartition G).1 (level + 1) child := by
          have h := hh.path.breakout hh.inv hcurrent
          rw [hat] at h
          exact h.stateEq rfl rfl rfl
        obtain ⟨childBest, eventTrail, hrunChild, hkeepChild⟩ := ih specFuel (level + 1)
          (numcells + 1) codes bs fs child best childTrail hg hinf hn0 (by omega) (by omega)
          (by omega) (by omega) hh.bnd hdescChild hnodeChild hliveChild hpathChild hh.orbits htvLt hh.firstDom
        obtain ⟨value, out, hcall⟩ : ∃ value out,
            otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1) child = (value, out) := ⟨_, _, rfl⟩
        have hout : SearchOut G level (level + 1) child out := by
          have h := otherNode_ok G ctx inf hinf tcLevel hn0 runFuel (level + 1)
            (numcells + 1) child hnodeChild.run.searchOk (by omega) (by omega)
          rw [Nat.add_sub_cancel, hcall] at h
          exact h
        rw [hcall] at hrunChild hkeepChild
        dsimp only at hrunChild hkeepChild
        by_cases hearly : value < Int.ofNat level
        · refine ⟨cursor, ?_, .visit hh hnext horb hoffset' hatFrozen' rfl hcall hrunChild hkeepChild
            (fun hn => (hn hearly).elim) (fun hn => (hn hearly).elim)⟩
          rw [firstChildLoop_earlyOther ctx inf tcLevel runFuel loopFuel level numcells tc tv1 tv
            tcell index st value out horb hother hcall hearly]
          exact hc
        · let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
          let cleared := clearShortIf out.needshortprune cleaned
          let recSt := recover n inf level cleared
          have hreturn : value = Int.ofNat level := hrunChild.node.toOutcome.parentEq hfuelNe hearly
          have hshort : out.needshortprune = false := by
            have h := clear_at_guide (ctx := ctx) (inf := inf) (tcLevel := tcLevel)
              (fuel := runFuel) (level := level + 1) (numcells := numcells + 1) (st := child)
              hh.inv.shortClear (by rw [hcall]; change value = Int.ofNat st.gcaFirst; rw [hh.guide]; exact hreturn)
            rwa [hcall] at h
          have hshortRec : cleared.needshortprune = false := clearShortIf_self cleaned
          obtain ⟨bs', hhRec⟩ := hh.next hg hinf hcodesLen hfuelNe hnext hoffset' hcurrent'
            hatFrozen' hat' hrunChild hkeepChild hearly hout out.needshortprune hshortRec
          have hcNext := hc.cellStep (nextElem_after hnext) hm htvLt hhRec.inv.frozenLabOk
            hhRec.inv.frozenPtnSize hhRec.inv.frozenLabSize hhRec.inv.frozenEnd hhRec.orbits
            (fun γ hγ => hhRec.inv.run.genTraceOk.check hγ) hhRec.live.frameStab
          obtain ⟨last, htail, htrace⟩ := ihLoop (some tv) tcell recSt childBest eventTrail bs' _ hhRec hcNext
          refine ⟨last, ?_, .visit hh hnext horb hoffset' hatFrozen' rfl hcall hrunChild hkeepChild
            (fun _ => hshort) (fun _ => htrace)⟩
          rw [firstChildLoop_stayOther ctx inf tcLevel runFuel loopFuel level numcells tc tv1 tv
            tcell index st value out horb hother hcall hearly]
          dsimp only
          simpa only [recSt, cleared, cleaned, hshort, Bool.false_eq_true, ite_false] using htail

/-- The counter proof also records the executed tail independently of
its initial counter value. -/
theorem firstTail_trace {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tv1 e loopFuel : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat} {base st : SearchSt n}
    {cursor : Option Nat} {tcell : VSet n} {best : Option (Key n)} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2) (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hrun : n + 2 < level + 1 + runFuel) (hspec : level + 1 + specFuel = n + 1)
    (hpath : level = codes.length)
    (hh : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn tc len
      tcell cursor e tv1 base st best trail) :
    FirstTail G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
      codes fs rsLab rsPtn base loopFuel cursor tcell st best trail := by
  have hc : Counted (segN rsLab tc len)
      (fun v => ∃ γ, checkAutom ctx.g γ = true ∧ CellStab rsPtn level rsLab γ ∧ γ[v]! = tv1)
      cursor 0 := ⟨[], by simp, rfl, by simp⟩
  obtain ⟨_, _, ht⟩ := firstTail_counted hg hinf hn0 ih hrun hspec hpath loopFuel cursor
    tcell st best trail bs 0 hh hc
  exact ht

/-- Every recorded first-path tail exposes its current loop invariant. -/
theorem FirstTail.hyp {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tv1 e loopFuel : Nat}
    {codes fs : List Nat} {rsLab rsPtn : Array Nat} {base st : SearchSt n}
    {cursor : Option Nat} {tcell : VSet n} {best : Option (Key n)} {trail : FrameTrail}
    (h : FirstTail G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
      codes fs rsLab rsPtn base loopFuel cursor tcell st best trail) :
    ∃ bs, FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn tc len
      tcell cursor e tv1 base st best trail := by
  cases h with
  | zero hyp => exact ⟨_, hyp⟩
  | done hyp next => exact ⟨_, hyp⟩
  | skip hyp next orbit tail => exact ⟨_, hyp⟩
  | visit hyp next orbit offsetLt atOffset childEq call run keep clear continuation => exact ⟨_, hyp⟩

end Hex.GraphIso.Nauty.Generation
