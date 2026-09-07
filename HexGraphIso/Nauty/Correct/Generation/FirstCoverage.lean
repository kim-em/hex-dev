/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Tail
public import HexGraphIso.Nauty.Correct.Generation.FirstReceipt
import all HexGraphIso.Nauty.Correct.Generation.Trace
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- The first-path tail covers the entire true orbit of its guiding child
by words in the final emitted generators. Reference transport uses the
true path stabilizer; only recorded return carriers require generation. -/
theorem FirstTail.cover
    {inf tcLevel specFuel runFuel level numcells tc len tv1 e boundary oRef : Nat}
    {codes fs targets : List Nat} {rsLab rsPtn : Array Nat} {entry : SearchSt n} {key : Key n}
    {base : List (Fin n)} {guide : Fin n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hpath : level = codes.length) (hrun : n + 2 < level + 1 + runFuel)
    (hboundary : level < boundary) (href : oRef < len)
    (hp : ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key oRef)
    (hmove : ∀ v : Fin n, Aut.Orbit G base guide v → ∀ o, o < len → rsLab[tc + o]! = v.val →
      ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key o)
    (hfixFrame : ∀ γ, CellStab rsPtn level rsLab γ → ∀ b ∈ base, γ[b.val]! = b.val)
    {loopFuel : Nat} {cursor : Option Nat} {tcell : VSet n} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (sweep : FirstTail G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
      codes fs rsLab rsPtn entry loopFuel cursor tcell st best trail)
    (hm : Matches ctx (level + 1) st targets key) (heq : st.eqlevFirst = level)
    (hsame : boundary ≤ st.allsamelevel) (hfuel : n < cursorRank cursor + loopFuel)
    (hfirst : st.firstlab[tc]! = guide.val) (hpast : CanonPast level tc cursor st)
    (hcover : Cover G base guide tcell cursor) (index : Nat)
    (htrace : ∀ γ ∈ (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
      (tcell.nextElem cursor) tcell index st).2.2.genTrace, γ ∈ Aut.trace G) :
    ∀ v, Aut.Orbit G base guide v → Aut.Carries G base guide v := by
  induction sweep generalizing index with
  | zero hh =>
    have hcap := cursorRank_le hh.cursorLt
    omega
  | done hh hnext => exact hcover.finish hnext
  | @skip loopFuel cursor tcell st best trail bs tv hh hnext horbit tail ih =>
    have hstate := firstChildLoop_skip ctx inf tcLevel runFuel loopFuel level numcells tc tv1 tv
      tcell index st horbit
    rw [hnext, hstate] at htrace
    let nextIndex := if st.orbits[tv]! == tv1 then index + 1 else index
    let v : Fin n := ⟨tv, hh.inv.nextLt hnext⟩
    have htraceSt : ∀ γ ∈ st.genTrace.toList, γ ∈ Aut.trace G := by
      intro γ hγ
      exact htrace γ (firstLoop_retains (first_retains ctx inf tcLevel runFuel)
        loopFuel level numcells tc tv1 _ tcell nextIndex st (by simpa using hγ))
    have hadv := hcover.orbitSkip (tv := v) hnext hh.orbits htraceSt
      (fun γ hγ => hfixFrame γ (hh.live.frameStab γ hγ))
      (by simpa only [beq_eq_false_iff_ne] using horbit)
    exact ih hm heq hsame (cursorFuel_step (nextElem_after hnext) hfuel) hfirst
      (hpast.advance (nextElem_after hnext)) hadv nextIndex htrace
  | @visit loopFuel cursor tcell st best trail bs tv offset child out r childBest eventTrail
      hh hnext horbit hoff hat hchild hcall hchildRun hkeep hclear continuation ih =>
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
    let nextIndex := if recSt.orbits[tv]! == tv1 then index + 1 else index
    have hcall' := hcall
    rw [hchild] at hcall'
    have hstate := firstChildLoop_stayOther ctx inf tcLevel runFuel loopFuel level numcells tc tv1 tv
      tcell index st r out horbit hother hcall' hstay
    rw [hnext, hstate] at htrace
    have htraceRec : ∀ γ ∈ (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (tcell.nextElem (some tv)) tcell nextIndex recSt).2.2.genTrace, γ ∈ Aut.trace G := by
      simpa only [recSt, cleared, cleaned, nextIndex, hc, Bool.false_eq_true, ite_false] using htrace
    have hgen : recSt.genTrace = out.genTrace := by
      dsimp only [recSt]
      rw [recover_genTrace]
      dsimp only [cleared, cleaned, clearShortIf]
      split <;> rfl
    have htraceOut : ∀ γ ∈ out.genTrace, γ ∈ Aut.trace G := by
      intro γ hγ
      apply htraceRec
      apply firstLoop_retains (first_retains ctx inf tcLevel runFuel)
      rwa [hgen]
    obtain ⟨bsNext, hhNext⟩ := (continuation hstay).hyp
    have hfixOut : ∀ γ ∈ out.genTrace, ∀ b ∈ base, γ[b.val]! = b.val := by
      intro γ hγ
      apply hfixFrame γ
      apply hhNext.live.frameStab
      change γ ∈ recSt.genTrace.toList
      simpa only [hgen, Array.mem_toList_iff] using hγ
    have hf0 := other_fields ctx inf tcLevel runFuel (level + 1) (numcells + 1) child
    rw [hcall, hchild] at hf0
    have hfo : FirstFields st out := ⟨hf0.codes, hf0.targets, hf0.lab, hf0.same⟩
    have hf : FirstFields st recSt := by
      apply hfo.trans
      apply FirstFields.trans _ (FirstFields.recover inf level cleared)
      dsimp only [cleared, cleaned, clearShortIf]
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨o, current, ho, hcur, hatF, hatC, hnode⟩ :=
      hh.inv.child (coset := tv) hnext (hh.cheapOk hg)
    rw [hatC, ← hchild] at hnode
    have hout : SearchOut G level (level + 1) child out := by
      have hs := otherNode_ok G ctx inf hinf tcLevel hh.inv.nonempty runFuel
        (level + 1) (numcells + 1) child hnode.run.searchOk (by omega) (by omega)
      rw [hcall, Nat.add_sub_cancel] at hs
      exact hs
    have hfake : { child with cosetindex := st.cosetindex } = { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } := by rw [hchild]
    have hpicked := hh.inv.picked hcur hatC hfake
    have hreturned := hh.inv.returned hcur hatC hfake (hout.inputEq rfl rfl rfl rfl)
    let v : Fin n := ⟨tv, hh.inv.nextLt hnext⟩
    have hadv : Cover G base guide tcell (some tv) := by
      by_cases hv : Aut.Orbit G base guide v
      · have hreceipt := hh.reference hg hinf hpath hrun hnext hoff hat hm heq hsame
          (hmove v hv offset hoff hat)
        dsimp only at hreceipt
        rw [← hchild, hcall] at hreceipt
        rw [hr] at hreceipt
        exact hcover.receipt (tv := v) hh.inv hnext hpast (by rw [hchild]) (by rw [hchild])
          hchildRun.guide hreceipt htraceOut hfixOut (by rw [hfo.lab]; exact hfirst)
          hreturned.2 (by rw [hchildRun.coset, hchild])
      · exact hcover.advance (tv := v) hnext (fun ho => (hv ho).elim)
    have hclearedGuide : GuideRel (level + 1) child cleared := by
      apply hchildRun.guide.stateEq
      all_goals dsimp only [cleared, cleaned, clearShortIf]; split <;> rfl
    have hpastRec : CanonPast level tc (some tv) recSt :=
      hpast.recover (nextElem_after hnext) (by rw [hchild]) (by rw [hchild])
        hclearedGuide hpicked.1 hpicked.2
    have heqOut : level ≤ out.eqlevFirst := by
      have ha := other_agreement ctx inf tcLevel level runFuel (level + 1) (numcells + 1)
        child (by omega) (by rw [hchild]; exact Nat.le_of_eq heq.symm)
      rw [hcall] at ha
      exact ha
    have heqRec : recSt.eqlevFirst = level := by
      apply match_recover
      dsimp only [cleared, cleaned, clearShortIf]
      split <;> exact heqOut
    exact ih hstay (hf.matching hm) heqRec (by rw [hf.same]; exact hsame)
      (cursorFuel_step (nextElem_after hnext) hfuel) (by rw [hf.lab]; exact hfirst)
      hpastRec hadv nextIndex htraceRec

end Hex.GraphIso.Nauty.Generation
