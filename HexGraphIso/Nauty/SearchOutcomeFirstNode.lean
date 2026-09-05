/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeFirstSweep
import all HexGraphIso.Nauty.Search

public section

/-!
The first-path node step of the totality induction: the discrete arm
installs the first leaf, and the internal arm runs the first-path sibling
sweep, each carrying the facts the enclosing sweep needs.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Installing the first leaf leaves the orbit ledger, the coset cursor
and the cheap-cell boundary alone. -/
theorem firstterminal_ledger (level : Nat) (st : SearchSt) :
    (firstterminal level st).orbits = st.orbits ∧
    (firstterminal level st).cosetindex = st.cosetindex ∧
    (firstterminal level st).noncheaplevel = st.noncheaplevel := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]
  simp

/-- The discrete first-path arm is total and carries the sweep facts. -/
theorem FirstInv.leafTotal {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hpath : level = codes.length + 1)
    (h : FirstInv G ctx level codes numcells st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList ctx.n) st.orbits ctx.n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
          numcells outBest trail eventTrail
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
        FirstKeep ctx level st
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2 fs
          outBest := by
  have hrun := h.terminalRun (inf := inf) (tcLevel := tcLevel)
    (specFuel := specFuel) (fuel := fuel) hn hn0 hpath hnum
  dsimp only at hrun
  refine ⟨_, _, trail, hrun, ?_⟩
  rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
  obtain ⟨horb, hcoset, hncl⟩ :=
    firstterminal_ledger level (firstLeafSt ctx level numcells st)
  have hgen := (firstterminal_store level
    (firstLeafSt ctx level numcells st)).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    cases hb
    rw [firstterminal_firstlab]
    exact keyLe_refl _
  · rw [horb, hgen]
    exact hsound
  · intro hc
    rw [hcoset]
    exact hc
  · intro _
    exact hncl
  · rw [(firstterminal_state level _).2.2.1]
    exact Nat.le_refl _

/-- The final first-path counter adjustment leaves the sweep facts alone. -/
theorem firstFinish_ledger (level size index : Nat) (st : SearchSt) :
    (firstFinish level size index st).orbits = st.orbits ∧
    (firstFinish level size index st).genTrace = st.genTrace ∧
    (firstFinish level size index st).cosetindex = st.cosetindex ∧
    (firstFinish level size index st).noncheaplevel = st.noncheaplevel ∧
    (firstFinish level size index st).gcaFirst = st.gcaFirst := by
  rw [firstFinish]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The internal first-path arm is total once every node at the current
fuel is. -/
theorem FirstInv.internalTotal {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (ihFirst : FirstTotal G ctx inf tcLevel runFuel)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + (specFuel + 1) = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (horb : OrbSound (OrbConn st.genTrace.toList ctx.n) st.orbits ctx.n)
    (hfirst : FirstInv G ctx level codes numcells st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ ctx.n) :
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel (specFuel + 1) (runFuel + 1) level codes fs st
          (firstPathNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells outBest trail eventTrail
          (firstPathNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        FirstKeep ctx level st
          (firstPathNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          fs outBest := by
  have href := hfirst.refined hn hg hn0 hlevel
  have hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff hn hn0 hfirst.searchOk
      hlevel]
    exact hnum
  have hpsz := href.1.ok.ptnSize
  have hend := href.1.ok.ptnEnd
  have hcount := href.2.2
  have hbc : bcount (refine ctx level st.lab st.ptn st.active numcells).ptn
      level ctx.n < ctx.n := by
    rw [hcount]
    exact Nat.lt_of_le_of_ne (hcount ▸ bcount_le _ _ _) hnum
  obtain ⟨tc, len, hmk, hcell, hlen2, hrange⟩ :=
    maketargetcell_open (ctx := ctx) (tcLevel := tcLevel) (hint := -1)
      (lab := (refine ctx level st.lab st.ptn st.active numcells).lab)
      hlevel hpsz hend hbc
  have hspecEq := maketargetcell_eq_spec (tcLevel := tcLevel) href.2.1
    href.1.ok.labOk href.1.ok.labSize hpsz hend
  rw [hspecEq] at hmk
  have hchildren := nodeKey_children (ctx := ctx) (tcLevel := tcLevel)
    (fuel := specFuel) (level := level) (numcells := numcells)
    (len := len - 1) (cs := codes) (st := st) hdisc
    (by rw [hmk]; simp only; omega)
  rw [hmk] at hchildren
  dsimp only at hchildren
  have hlt : level < n := by
    have hok := refine_searchOk hn hn0 hfirst.searchOk hlevel
      (st2 := firstLeafSt ctx level numcells st) rfl rfl (Or.inl rfl)
    have hle := hok.bc
    have hptn : (firstLeafSt ctx level numcells st).ptn =
      (refine ctx level st.lab st.ptn st.active numcells).ptn := rfl
    rw [hptn, ← hn] at hle
    rw [← hn]
    omega
  have hL := firstLoopTotal (tail := len - 1) (level := level)
    (specFuel := specFuel) (runFuel := runFuel) (cs := codes) (st := st)
    (numcells := numcells) (tc := tc) (len := len) (inf := inf)
    (tcLevel := tcLevel) (trail := trail) hn hg hinf hn0 ih ihFirst
    (by omega) (by omega) hlevel hpath hlt hfirst hpathOk hcheap hdesc horb
    hcell hlen2 hrange rfl (by omega)
  dsimp only at hL
  obtain ⟨fs, outBest, eventTrail, hrunL, hout⟩ := hL
  rw [firstPath_internal_state ctx inf tcLevel runFuel level numcells st hnum]
  dsimp only
  rw [hspecEq, hmk]
  dsimp only
  rw [worksetOf_eq_windowSet _ tc len (by omega)]
  have hprefix : (codes ++ [(refine ctx level st.lab st.ptn st.active
      numcells).longcode]).take codes.length = codes := by
    simp only [List.take_left']
  generalize hL : firstChildLoop ctx inf tcLevel runFuel (ctx.n + 1) level
    (refine ctx level st.lab st.ptn st.active numcells).numcells tc
    ((nextElem (windowSet (refine ctx level st.lab st.ptn st.active
      numcells).lab tc len) none).getD 0)
    (nextElem (windowSet (refine ctx level st.lab st.ptn st.active
      numcells).lab tc len) none)
    (windowSet (refine ctx level st.lab st.ptn st.active numcells).lab tc
      len) 0 _ = L at hrunL hout ⊢
  rcases L with ⟨rr, index, out⟩
  cases rr with
  | none =>
      dsimp only
      refine ⟨fs, outBest, eventTrail, ?_, ?_⟩
      · exact (hrunL.toNodeNone (nodeRunFuel := runFuel + 1)
          (tail := len - 1) hchildren.symm hchildren
          (show len = len - 1 + 1 by omega)
          (show ctx.n < cursorRank none + (ctx.n + 1) by
            simp only [cursorRank]; omega)
          (by split <;> rfl)).firstFinish (show runFuel + 1 ≠ 0 by omega)
      · obtain ⟨h1, h2, h3, h4, h5⟩ := firstFinish_ledger level len index out
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro b hb
          rw [firstFinish_firstlab]
          exact hout.dom b hb
        · rw [h1, h2]
          exact hout.orbits
        · intro _
          rw [h3]
          exact hout.coset
        · rw [h4]
          exact hout.boundary
        · rw [h5]
          exact hrunL.guideLevel
  | some r =>
      dsimp only
      exact ⟨fs, outBest, eventTrail,
        hrunL.toNodeSome (nodeRunFuel := runFuel + 1) hchildren.symm hprefix
          (by split <;> rfl),
        ⟨hout.dom, hout.orbits, fun _ => hout.coset, hout.boundary,
          hrunL.guideLevel⟩⟩

/-- Every first-path node at the next executable fuel is total once every
node at the current fuel is. -/
theorem FirstTotal.succ (G : Colored n k) (ctx : Ctx)
    (inf tcLevel runFuel : Nat) (ih : OtherTotal G ctx inf tcLevel runFuel)
    (ihFirst : FirstTotal G ctx inf tcLevel runFuel) :
    FirstTotal G ctx inf tcLevel (runFuel + 1) := by
  intro specFuel level numcells codes st trail hn hg hinf hn0 hlevel hpath
    hspec hfuel hcheap hdesc horb hfirst hpathOk
  have hle : level ≤ n := hfirst.searchOk.levelLe
  obtain ⟨sf, rfl⟩ : ∃ sf, specFuel = sf + 1 := ⟨specFuel - 1, by omega⟩
  by_cases hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n
  · exact hfirst.leafTotal hn hn0 hpath horb hnum
  · exact hfirst.internalTotal hn hg hinf hn0 ih ihFirst hlevel hpath hspec
      hfuel hcheap hdesc horb hpathOk hnum

end Hex.GraphIso.Nauty
