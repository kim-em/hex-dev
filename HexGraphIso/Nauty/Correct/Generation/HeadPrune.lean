/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Frame
public import HexGraphIso.Nauty.Correct.FirstPath.Hyp
import all HexGraphIso.Generated

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- The guiding child's short-prune filter uses recorded generators for
explicit pairs and the deeper stabilizer for implicit pairs. The saved
cheap boundary fixes the guiding vertex in addition to the parent base. -/
theorem Cover.shortSource
    {base : List (Fin n)} {guide : Fin n} {cell : VSet n} {cursor : Option Nat}
    {tcLevel specFuel level numcells tc len offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {receiverCell : VSet n} {receiverCursor : Option Nat} {entry st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail}
    (h : Cover G base guide cell cursor)
    (hg : ctx.g = rowsOf G) (hpathCodes : level = codes.length)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn tc len
      receiverCell receiverCursor entry st best trail)
    (hpath : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hevent : EventOut G ctx tcLevel codes fs out outBest eventTrail (Int.ofNat level))
    (hpreserved : TrailExt (level + 1)
      (trail.push level ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) eventTrail)
    (hsource : ShortSource G ctx out eventTrail (Int.ofNat level))
    (hat : rsLab[tc + offset]! = guide.val)
    (hbase : ∀ b ∈ base, st.fixedpts.mem b.val = true)
    (htrace : ∀ γ ∈ out.genTrace, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ out.genTrace, ∀ b ∈ base, γ[b.val]! = b.val)
    (hdeep : ∀ p, IsIso G G p → Perm.Fixes (guide :: base) p → Perm.Generated (Aut.gens G) p) :
    Cover G base guide (Nauty.shortprune cell out) cursor := by
  apply h.shortCarriers
  intro fix mcr hback v hv
  cases hsource with
  | explicit target sourceFix sourceMcr returned back valid source =>
    have he : (sourceFix, sourceMcr) = (fix, mcr) := Option.some.inj (back.symm.trans hback)
    cases he
    obtain ⟨γ, hγ, hp⟩ := source
    have hdrop : (fmperm γ n).2.mem v.val = false := by rw [hp]; exact hv
    exact carries_fmperm (htrace γ hγ) (hfix γ hγ) hdrop
  | implicit target returned below back root =>
    have ht : level = target := Int.ofNat_inj.mp returned
    have hbelow : level < out.noncheaplevel := by omega
    have hbaseFix : ∀ b ∈ base,
        (fmptn out.lab out.ptn out.noncheaplevel n).1.mem b.val = true := by
      intro b hb
      exact hinv.fmptnFix hpathCodes hpath hevent hpreserved (Nat.le_of_lt hbelow)
        b.val b.isLt (hbase b hb)
    have hguideFix : (fmptn out.lab out.ptn out.noncheaplevel n).1.mem guide.val = true := by
      cases hevent with
      | intro current eventCodes bestCodes event depth stemEq past returned stable history =>
        have hcurrent : level < current := by rw [hpathCodes]; exact past
        have hentry := hpreserved.pushAt
        have hlen := hinv.lenTwo
        have hrange := hinv.range
        have htc : tc < n := by omega
        obtain ⟨_, _, _, _, _, hval⟩ := event.trailOk.picked level _ hcurrent hentry
        change out.lab[tc]! = rsLab[tc + offset]! at hval
        have hbit := picked_fix event.trailOk hcurrent hentry hbelow event.cheap.ptnSize
          (Nat.le_trans event.cheap.rootEnd (by have := event.cheap.positive; omega)) htc
          (by change out.lab[tc]! < n; rw [hval, hat]; exact guide.isLt)
        change (fmptn out.lab out.ptn out.noncheaplevel n).1.mem rsLab[tc + offset]! = true at hbit
        rwa [hat] at hbit
    have hpair := pair_implicit (G := G) (base := guide :: base) (by rw [← hg]; exact root)
      (fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hguideFix
        · exact hbaseFix b hb) hdeep
    have he : fmptn out.lab out.ptn out.noncheaplevel n = (fix, mcr) :=
      Option.some.inj (back.symm.trans hback)
    rw [he] at hpair hbaseFix
    exact hpair.carries hbaseFix hv

end Hex.GraphIso.Nauty.Generation
