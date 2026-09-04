/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeOtherNode
public import HexGraphIso.Nauty.SearchOutcomeLeaf
public import HexGraphIso.Nauty.SearchOutcomeGateFail

public section

/-!
The off-path node step of the totality induction: every off-path node
at executable fuel `runFuel + 1` is total once every node at fuel
`runFuel` is.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- An off-path leaf at any executable fuel is total. -/
theorem NodeInv.leafTotal {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells =
      ctx.n)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList ctx.n) st.orbits ctx.n)
    (hcoset : st.cosetindex < ctx.n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b) :
    ∃ outBest,
      OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
          numcells best outBest trail trail
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  have hlevel1 : 1 ≤ level := by omega
  rcases heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level)
    with _ | _
  · exact hnode.leafOther hn hg hn0 hlevel1 hpath hcheap hnum
      (by rw [heq]; decide) hlive hsound hcoset
  · by_cases hadmit :
      (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
          codeSentinel ∧
        isautom ctx (firstScatter ctx.n
          (otherLeafSt ctx level numcells st).firstlab
          (otherLeafSt ctx level numcells st).lab) = true
    · exact ⟨best, hnode.leafFirstOther hn hg hn0 hlevel1 hpath hnum heq
        hadmit.1 hadmit.2 hlive hsound hdom⟩
    · have hfail : (otherLeafSt ctx level numcells st).firstcode[level + 1]! ≠
          codeSentinel ∨
          isautom ctx (firstScatter ctx.n
            (otherLeafSt ctx level numcells st).firstlab
            (otherLeafSt ctx level numcells st).lab) = false := by
        by_cases hs : (otherLeafSt ctx level numcells st).firstcode[level + 1]!
            = codeSentinel
        · right
          rcases hp : isautom ctx (firstScatter ctx.n
            (otherLeafSt ctx level numcells st).firstlab
            (otherLeafSt ctx level numcells st).lab) with _ | _
          · rfl
          · exact (hadmit ⟨hs, hp⟩).elim
        · exact Or.inl hs
      have hnode' := hnode.setEqlevFirst (e := 0) (Nat.zero_le _)
      have hlive' : Live ctx level { st with eqlevFirst := 0 } trail :=
        hlive.stateEq rfl rfl rfl rfl rfl
      have hef' : ¬(((otherLeafSt ctx level numcells
          { st with eqlevFirst := 0 }).eqlevFirst == level) = true) := by
        rw [otherLeafSt_setEqlev ctx level numcells st hlevel]
        simp only [beq_iff_eq]
        omega
      obtain ⟨outBest, hrun', hkeep'⟩ :=
        NodeInv.leafOther (st := { st with eqlevFirst := 0 }) hn hg hn0 hlevel1
          hpath hcheap hnum hef' hnode' hlive' hsound hcoset
      exact ⟨outBest, OtherRun.ofGateFail hn hg hn0 hlevel hpath hcheap hnum
        heq hfail hnode hlive hrun' hkeep'⟩

/-- Every off-path node at the next executable fuel is total once every
node at the current fuel is. -/
theorem OtherTotal.succ (G : Colored n k) (ctx : Ctx)
    (inf tcLevel runFuel : Nat) (ih : OtherTotal G ctx inf tcLevel runFuel) :
    OtherTotal G ctx inf tcLevel (runFuel + 1) := by
  intro specFuel level numcells codes bs fs st best trail hn hg hinf hn0
    hlevel hpath hspec hfuel hcheap hdesc hnode hlive hpathOk horb hcoset hdom
  have hle : level ≤ n := hnode.run.searchOk.levelLe
  rcases Nat.lt_or_ge (refine ctx level st.lab st.ptn st.active
    numcells).numcells ctx.n with hnum | hnum
  · exact hnode.internalOther hn hg hinf hn0 ih hlevel hpath hspec hfuel
      hcheap hdesc hlive hpathOk horb hcoset hdom hnum
  · have hnum' : (refine ctx level st.lab st.ptn st.active
        numcells).numcells = ctx.n := by
      apply Nat.le_antisymm _ hnum
      rw [← (hnode.refined hn hg hn0 (by omega)).2.2]
      exact bcount_le _ _ _
    obtain ⟨sf, rfl⟩ : ∃ sf, specFuel = sf + 1 := ⟨specFuel - 1, by omega⟩
    obtain ⟨outBest, hrun, hkeep⟩ := hnode.leafTotal hn hg hn0 hlevel hpath
      hcheap hnum' hlive horb hcoset hdom
    exact ⟨outBest, trail, hrun, hkeep⟩

end Hex.GraphIso.Nauty
