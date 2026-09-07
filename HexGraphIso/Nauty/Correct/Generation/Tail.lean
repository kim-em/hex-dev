/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.FirstVisit
public import HexGraphIso.Nauty.Correct.Generation.Counter
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- Once the guiding child has installed its reference, the first-path
tail finishes its sweep. This rules out premature returns both above and
below an inherited cheap-cell boundary. -/
theorem FirstTail.complete
    {inf tcLevel specFuel runFuel level numcells tc len tv1 e boundary oRef : Nat}
    {codes fs targets : List Nat} {rsLab rsPtn : Array Nat} {base : SearchSt n} {key : Key n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hpath : level = codes.length) (hrun : n + 2 < level + 1 + runFuel)
    (hboundary : level < boundary) (href : oRef < len)
    (hp : ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key oRef)
    {loopFuel : Nat} {cursor : Option Nat} {tcell : VSet n} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (sweep : FirstTail G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
      codes fs rsLab rsPtn base loopFuel cursor tcell st best trail)
    (hm : Matches ctx (level + 1) st targets key) (heq : st.eqlevFirst = level)
    (hsame : boundary ≤ st.allsamelevel) (hfuel : n < cursorRank cursor + loopFuel) :
    ∀ index, (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
      (tcell.nextElem cursor) tcell index st).1 = none := by
  induction sweep with
  | zero hh =>
    have hcap := cursorRank_le hh.cursorLt
    omega
  | done hh hnext =>
    intro index
    rw [hnext, firstChildLoop]
    omega
  | skip hh hnext horbit tail ih =>
    intro index
    rw [hnext, firstChildLoop_skip ctx inf tcLevel runFuel _ level numcells tc tv1 _ _ index _ horbit]
    exact ih hm heq hsame (cursorFuel_step (nextElem_after hnext) hfuel) _
  | @visit loopFuel cursor tcell st best trail bs tv offset child out r childBest eventTrail
      hh hnext horbit hoff hat hchild hcall hchildRun hkeep hclear continuation ih =>
    intro index
    have hr := hh.visitLevel hg hinf hpath hrun hnext hm heq hsame hboundary href hp
      hchild hcall hchildRun hkeep
    have hstay : ¬ r < Int.ofNat level := by rw [hr]; exact Int.lt_irrefl _
    have hc := hclear hstay
    have hother : (tv == tv1) = false := by
      obtain ⟨v, hv, hle⟩ := hh.after
      have ha := nextElem_after hnext
      rw [hv] at ha
      change v < tv at ha
      simp only [beq_eq_false_iff_ne]
      omega
    let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
    let cleared := clearShortIf out.needshortprune cleaned
    let recSt := recover n inf level cleared
    have hf0 := other_fields ctx inf tcLevel runFuel (level + 1) (numcells + 1) child
    rw [hcall, hchild] at hf0
    have hf : FirstFields st recSt := by
      have hfo : FirstFields st out := ⟨hf0.codes, hf0.targets, hf0.lab, hf0.same⟩
      apply hfo.trans
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
    have hresult := ih hstay (hf.matching hm) heqRec (by rw [hf.same]; exact hsame)
      (cursorFuel_step (nextElem_after hnext) hfuel)
    have hcall' := hcall
    rw [hchild] at hcall'
    rw [hnext, firstChildLoop_stayOther ctx inf tcLevel runFuel loopFuel level numcells tc tv1 tv
      tcell index st r out horbit hother hcall' hstay]
    dsimp only
    simpa only [recSt, cleared, cleaned, hc, Bool.false_eq_true, ite_false] using hresult
      (if ((recover n inf level (clearShortIf false cleaned)).orbits[tv]! == tv1) = true
        then index + 1 else index)

end Hex.GraphIso.Nauty.Generation
