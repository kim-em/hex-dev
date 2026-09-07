/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Node
public import HexGraphIso.Nauty.Correct.Generation.FirstReceipt

public section

namespace Hex.GraphIso.Nauty

open Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tv1 e boundary : Nat}
    {codes bs fs targets : List Nat} {rsLab rsPtn : Array Nat} {base st : SearchSt n}
    {key : Key n} {cursor : Option Nat} {tcell : VSet n} {best : Option (Key n)} {trail : FrameTrail}

/-- A matching child of a first-path sweep invokes the general off-path
reference theorem with its individualized vertex as the coset index. -/
theorem FirstSweepHyp.reference
    (hh : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn tc len
      tcell cursor e tv1 base st best trail)
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hpath : level = codes.length) (hfuel : n + 2 < level + 1 + runFuel)
    {tv o : Nat} (hnext : tcell.nextElem cursor = some tv)
    (ho : o < len) (hat : rsLab[tc + o]! = tv)
    (hm : Matches ctx (level + 1) st targets key) (heq : st.eqlevFirst = level)
    (hsame : boundary ≤ st.allsamelevel)
    (hp : ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key o) :
    let child : SearchSt n := { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv
      cosetindex := tv }
    RefReturn ctx (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1) child).2
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1) child).1 := by
  intro child
  have hgsz : ctx.g.size = n := by rw [hg]; exact size_rowsOf G
  obtain ⟨off, cur, hoff, hcur, hatF, hatCur, hnode⟩ :=
    hh.inv.child (coset := tv) hnext (hh.cheapOk hg)
  rw [hatCur] at hnode
  let childTrail := trail.push level ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, off⟩
  have hlive : Live ctx (level + 1) child childTrail := by
    have h := hh.inv.firstChildLive (coset := tv) hh.live off cur
    rw [hatCur] at h
    exact h
  have hpathChild : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 (level + 1) child := by
    have h := hh.path.breakout hh.inv hcur
    rw [hatCur] at h
    exact h.stateEq rfl rfl rfl
  have hdesc := hh.inv.childDescWeak hg hh.desc hh.bnd hh.park hcur hatCur
  have hrChild := hh.inv.childPath hgsz ho hcur (hatCur.trans hat.symm) hp
  rw [hatCur] at hrChild
  have href : RefPath ctx tcLevel boundary (level + 1)
      (refine ctx (level + 1) child.lab child.ptn child.active (numcells + 1)) targets key := by
    change RefPath ctx tcLevel boundary (level + 1)
      (refine ctx (level + 1) (breakout n st.lab st.ptn (level + 1) tc tv).1
        (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        (breakout n st.lab st.ptn (level + 1) tc tv).2.2 (numcells + 1)) targets key
    rw [breakout_ptn]
    exact hrChild
  have hpositive := hh.inv.positive
  exact other_reference hg hinf runFuel (level + 1) (numcells + 1) codes bs fs child best childTrail
    boundary targets key (by omega) (by omega) (by omega) hnode hlive hpathChild hh.bnd hdesc
    hh.orbits (hh.inv.nextLt hnext) hh.firstDom href (hm.stateEq rfl rfl rfl)
    (by simpa only [Nat.add_sub_cancel] using heq) hsame

/-- No off-path visit in this first-path sweep can cross its receiver.
Above both boundaries this follows from return classification. At a cheap
boundary every child contains the saved reference, so the reference
return theorem rules out an early non-generator return there as well. -/
theorem FirstSweepHyp.visitLevel
    (hh : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn tc len
      tcell cursor e tv1 base st best trail)
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hpath : level = codes.length) (hfuel : n + 2 < level + 1 + runFuel)
    {tv oRef offset : Nat} {child out : SearchSt n} {r : Int}
    {outBest : Option (Key n)} {eventTrail : FrameTrail}
    (hnext : tcell.nextElem cursor = some tv)
    (hm : Matches ctx (level + 1) st targets key) (heq : st.eqlevFirst = level)
    (hsame : boundary ≤ st.allsamelevel) (hboundary : level < boundary)
    (href : oRef < len)
    (hp : ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key oRef)
    (hchild : child = { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv
      cosetindex := tv })
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1) child = (r, out))
    (hrun : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs child out
      (numcells + 1) best outBest
      (trail.push level ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) eventTrail r)
    (hkeep : OtherKeep ctx (level + 1) child out) : r = Int.ofNat level := by
  have hlevelLt := hh.inv.levelLt
  have hfuelNe : runFuel ≠ 0 := by omega
  have hguide : out.gcaFirst = level := by rw [hrun.firstGuide, hchild]; exact hh.guide
  have hbelow := hrun.node.exit.below (by omega)
  by_cases hc : st.noncheaplevel ≤ level
  · have hgsz : ctx.g.size = n := by rw [hg]; exact size_rowsOf G
    have hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
      rw [hg]; exact rowsOf_symm G
    have hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false := by rw [hg]; exact rowsOf_loopless G
    have hS : SubtreeOk ctx level (LoopInv.frame rsLab rsPtn numcells) :=
      (hh.inv.subtreeAtWeak hh.desc hh.park hc).ofFrames rfl rfl rfl
    obtain ⟨o, cur, ho, _, hat, _⟩ := hh.inv.nextOffsets hnext
    have hlen := hh.inv.lenTwo
    have hrange := hh.inv.range
    have hcell : (tc, tc + len - 1) ∈ cells rsPtn level n :=
      isCell_mem_cells hh.inv.cell (by rw [hh.inv.frozenPtnSize]; exact Nat.le_refl _)
        hh.inv.frozenEnd (by omega)
    have hpCur := hp.smallChild hS hlevelLt hgsz hsymm hloop hcell (by omega) (by omega) (by omega : o ≤ tc + len - 1 - tc)
    have hret := hh.reference hg hinf hpath hfuel hnext ho hat hm heq hsame hpCur
    rw [← hchild] at hret
    dsimp only at hret
    rw [hcall] at hret
    exact hret.atGuide hguide hrun.order hbelow
  · by_cases hearly : r < Int.ofNat level
    · have hcheapOut := hkeep.above (by rw [hchild]; dsimp only; omega)
      have hfields := other_fields ctx inf tcLevel runFuel (level + 1) (numcells + 1) child
      rw [hcall] at hfields
      have hsameOut : level < out.allsamelevel := by
        rw [hfields.same, hchild]
        dsimp only
        omega
      have hret := RefReturn.ofEarly hrun.node.exit hfuelNe hearly hcheapOut hsameOut hrun.order
      have he := hret.atGuide hguide hrun.order hbelow
      rw [he] at hearly
      exact (Int.lt_irrefl _ hearly).elim
    · exact hrun.node.toOutcome.parentEq hfuelNe hearly

end Hex.GraphIso.Nauty
