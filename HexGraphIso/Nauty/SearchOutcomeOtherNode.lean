/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeOtherLoop
import all HexGraphIso.Nauty.Search

public section

/-!
Totality of one off-path internal node, assembled from the totality of
its sibling sweep.

An off-path internal node either exits at once (the frozen gate and the
hinted target-cell mismatch), sweeps the specification's target cell, or,
when the path is frozen below the incumbent but still agrees with the
first path, sweeps the first path's hinted target cell.  The hinted sweep
does not compute the node key, so its loop bound is converted through the
common incumbent that dominates both.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Loop exits as node exits, through a common incumbent -/

namespace LoopExit

/-- An early integer-valued loop exit becomes a node exit whenever the
loop bound and the node key produce the same incumbent maximum. -/
theorem toNodeSomeInc {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail} {value : Int}
    (hinc : incMax best bound =
      incMax best (nodeKey ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
        nodeNumcells))
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail (some value)) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail value := by
  cases h with
  | done returned => cases returned
  | unwind target returned below sound payload located control =>
      refine NodeExit.unwind (target := target)
        (returned := Option.some.inj returned) (below := below)
        (sound := ?_) (payload := payload) located control
      constructor
      · intro b hb
        rw [← hinc]
        exact sound.upper b hb
      · exact sound.grows
  | frozen value returned below exact freeze =>
      cases Option.some.inj returned
      apply NodeExit.frozen
      · exact below
      · rw [← hinc]
        exact exact
      · exact freeze.shrink hprefix
  | cheap boundary returned positive below saved exact =>
      apply NodeExit.cheap boundary (Option.some.inj returned) positive below
      · exact saved
      rw [← hinc]
      exact exact
  | exhausted returned => cases returned

/-- A sufficiently fuelled `none` loop exit becomes the node's ordinary
return whenever the loop bound and the node key produce the same incumbent
maximum. -/
theorem toNodeNoneInc {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {trail : FrameTrail}
    (hinc : incMax best bound =
      incMax best (nodeKey ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
        nodeNumcells))
    (hfuel : n < cursorRank cursor + loopFuel)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail none) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail (Int.ofNat level - 1) := by
  cases h with
  | done _ exact =>
      apply NodeExit.done rfl
      rw [← hinc]
      exact exact
  | unwind _ returned => cases returned
  | frozen _ returned => cases returned
  | cheap _ returned => cases returned
  | exhausted _ finalCursor progress bounded =>
      exact (LoopResult.exhaustion_false hfuel progress bounded).elim

end LoopExit

namespace OtherLoopRun

/-- An early integer-valued off-path sweep becomes its enclosing off-path
node, given the guide relation between the node entry and the sweep
result. -/
theorem toNodeSomeInc {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (hinc : incMax best bound =
      incMax best (nodeKey ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
        nodeNumcells))
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (hcoset : loopSt.cosetindex = nodeSt.cosetindex)
    (hguide : GuideRel level nodeSt out)
    (h : OtherLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out best outBest receiptTrail eventTrail (some r)) :
    OtherRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells best outBest receiptTrail eventTrail r where
  node := {
    exit := h.exit.toNodeSomeInc hinc hprefix
    event := h.proof.loop.outcome.event
    preserved := h.proof.loop.outcome.preserved
    fixed := h.proof.loop.fixed.trans hfixed
    short := by
      intro hshort
      obtain ⟨value, hreturned, hsource⟩ := h.short hshort
      cases Option.some.inj hreturned
      exact hsource }
  firstGuide := hguide.first
  order := hguide.order
  canonGuide := hguide.canon
  coset := h.proof.coset.trans hcoset

/-- A sufficiently fuelled `none` off-path sweep is genuine completion and
becomes its enclosing off-path node's ordinary return. -/
theorem toNodeNoneInc {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    (hinc : incMax best bound =
      incMax best (nodeKey ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
        nodeNumcells))
    (hfuel : n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (hcoset : loopSt.cosetindex = nodeSt.cosetindex)
    (hguide : GuideRel level nodeSt out)
    (h : OtherLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out best outBest receiptTrail eventTrail none) :
    OtherRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells best outBest receiptTrail eventTrail
      (Int.ofNat level - 1) where
  node := {
    exit := h.exit.toNodeNoneInc hinc hfuel
    event := h.proof.loop.outcome.event
    preserved := h.proof.loop.outcome.preserved
    fixed := h.proof.loop.fixed.trans hfixed
    short := by
      intro hshort
      obtain ⟨value, hreturned, _⟩ := h.short hshort
      cases hreturned }
  firstGuide := hguide.first
  order := hguide.order
  canonGuide := hguide.canon
  coset := h.proof.coset.trans hcoset

/-- The ordinary case: the loop bound is the node key itself. -/
theorem toNodeSome {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (hcoset : loopSt.cosetindex = nodeSt.cosetindex)
    (hguide : GuideRel level nodeSt out)
    (h : OtherLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out best outBest receiptTrail eventTrail (some r)) :
    OtherRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells best outBest receiptTrail eventTrail r :=
  h.toNodeSomeInc (by rw [hbound]) hprefix hfixed hcoset hguide

/-- The ordinary case: the loop bound is the node key itself. -/
theorem toNodeNone {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hfuel : n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (hcoset : loopSt.cosetindex = nodeSt.cosetindex)
    (hguide : GuideRel level nodeSt out)
    (h : OtherLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out best outBest receiptTrail eventTrail none) :
    OtherRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells best outBest receiptTrail eventTrail
      (Int.ofNat level - 1) :=
  h.toNodeNoneInc (by rw [hbound]) hfuel hfixed hcoset hguide

end OtherLoopRun

/-! # The prepared node frame -/

/-- The node preparation leaves the active set alone. -/
theorem otherNodePrep_active (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).active = st.active := by
  rw [otherNodePrep]
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchSt.active,
    ite_self]

/-- The refined off-path frame before its target cell is chosen. -/
theorem otherLeafSt_active (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).active =
      (refine ctx level st.lab st.ptn st.active numcells).active := by
  unfold otherLeafSt
  rw [otherNodePrep_active]

theorem otherLeafSt_lab (ctx : Ctx n) (level numcells : Nat) (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
  unfold otherLeafSt
  exact (otherNodePrep_frames _ _ _).2.2.2.2.2.2.2.2.2.2.2.1

theorem otherLeafSt_ptn (ctx : Ctx n) (level numcells : Nat) (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).ptn =
      (refine ctx level st.lab st.ptn st.active numcells).ptn := by
  unfold otherLeafSt
  exact (otherNodePrep_frames _ _ _).2.2.2.2.2.2.2.2.2.2.2.2

/-- The sweep entry state: the prepared frame charged with the target
cell size and, when the cheap-automorphism test fails, parked one level
below. -/
@[expose] def sweepStart (ctx : Ctx n) (level numcells len : Nat)
    (st : SearchSt n) : SearchSt n :=
  let pre := otherLeafSt ctx level numcells st
  let base : SearchSt n := { pre with tctotal := pre.tctotal + len }
  if cheapautom base.ptn level n then base
  else { base with noncheaplevel := level + 1 }

/-- Every logical field of the sweep entry state is inherited from the
node entry or the refinement. -/
theorem sweepStart_frames (ctx : Ctx n) (level numcells len : Nat)
    (st : SearchSt n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let start := sweepStart ctx level numcells len st
    start.lab = rs.lab ∧ start.ptn = rs.ptn ∧ start.active = rs.active ∧
    start.fixedpts = st.fixedpts ∧ start.gcaFirst = st.gcaFirst ∧
    start.gcaCanon = st.gcaCanon ∧ start.canonlab = st.canonlab ∧
    start.genTrace = st.genTrace ∧ start.orbits = st.orbits ∧
    start.cosetindex = st.cosetindex ∧ start.firstlab = st.firstlab ∧
    start.needshortprune = st.needshortprune ∧
    (start.noncheaplevel = st.noncheaplevel ∨
      start.noncheaplevel = level + 1) ∧
    (cheapautom rs.ptn level n = false →
      start.noncheaplevel = level + 1) ∧
    (cheapautom rs.ptn level n = true →
      start.noncheaplevel = st.noncheaplevel) := by
  dsimp only
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hlab := otherLeafSt_lab ctx level numcells st
  have hptn := otherLeafSt_ptn ctx level numcells st
  have hact := otherLeafSt_active ctx level numcells st
  unfold sweepStart
  dsimp only
  split
  · rename_i hc
    rw [hptn] at hc
    exact ⟨hlab, hptn, hact, hf5, hf1, hf2, hf3, hf7, hf8, hf4, hf6, hf10,
      Or.inl hf9, fun h => (by rw [hc] at h; cases h), fun _ => hf9⟩
  · rename_i hc
    rw [hptn] at hc
    exact ⟨hlab, hptn, hact, hf5, hf1, hf2, hf3, hf7, hf8, hf4, hf6, hf10,
      Or.inr rfl, fun _ => rfl, fun h => absurd h hc⟩

/-! # A sweep at the node -/

/-- An off-path internal node whose child sweep starts at `sweepStart`
with a loop invariant, given the two state equations of the executable
node and a common incumbent maximum for the loop bound and the node key.
-/
theorem NodeInv.sweepNode {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel sf runFuel level numcells tc len : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {bound : Key n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + (sf + 1) = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hlen2 : 2 ≤ len) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := codes ++ [rs.longcode]
    let tcell := worksetOf n rs.lab tc (tc + len - 1)
    let start := sweepStart ctx level numcells len st
    let L := otherChildLoop ctx inf tcLevel runFuel (n + 1) level
      rs.numcells tc ((tcell.nextElem none).getD 0) (tcell.nextElem none)
      tcell start
    LoopInv G ctx tcLevel sf level full bs fs rs.numcells rs.lab rs.ptn tc
      len tcell none start start best trail →
    incMax best bound =
      incMax best (nodeKey ctx tcLevel (sf + 1) level codes st numcells) →
    bound = keysMax
      (sweepKey ctx tcLevel sf level full rs.lab rs.ptn tc rs.numcells 0)
      ((List.range (len - 1)).map fun o =>
        sweepKey ctx tcLevel sf level full rs.lab rs.ptn tc rs.numcells
          (o + 1)) →
    (∀ r out, L = (some r, out) →
      otherNode ctx inf tcLevel (runFuel + 1) level numcells st = (r, out)) →
    (∀ out, L = (none, out) →
      otherNode ctx inf tcLevel (runFuel + 1) level numcells st =
        (Int.ofNat level - 1, out)) →
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel (sf + 1) (runFuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells best outBest trail eventTrail
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2 := by
  intro rs full tcell start L hloop hinc hbound hsome hnone
  have hgsz : ctx.g.size = n := by
    rw [hg]
    exact size_rowsOf G
  have href := hnode.refined hg hn0 (by omega)
  obtain ⟨hsLab, hsPtn, hsActive, hsFixed, hsFirst, hsCanon, hsCanonlab,
    hsGen, hsOrb, hsCoset, hsFirstlab, hsShort, hsNcl, hsPark, hsKeep⟩ :=
    sweepStart_frames ctx level numcells len st
  have hpathFull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstemFull : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hpastFull : codes.length < level := by omega
  have hend : st.ptn[st.ptn.size - 1]! ≤ level :=
    searchOk_end hn0 hnode.run.searchOk (by omega)
  have hrefInv := refine_refInv (ctx := ctx) (level := level)
    (active := st.active) (numcells := numcells)
    (by rw [hnode.run.searchOk.ptnSize]; exact Nat.le_refl n)
    (hnode.run.searchOk.labSize.trans hnode.run.searchOk.ptnSize.symm)
    hend
  have hlive' : OtherLive ctx level start trail := by
    have := hnode.otherLive (len := len) hlive
    exact this
  have hpathStart : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level start := by
    have h1 := hpathOk.refine hn0 (by omega) hgsz hnode.run.searchOk
      hnode.activeStarts
    exact h1.stateEq hsLab hsPtn hsFixed
  have hh : OtherLoopHyp G ctx tcLevel sf level full bs fs rs.numcells
      rs.lab rs.ptn tc len tcell none st.noncheaplevel start start best
      trail := {
    inv := hloop
    live := hlive'
    path := hpathStart
    cursorLt := fun _ h => nomatch h
    sign := Or.inr rfl
    start := fun _ => worksetOf_eq_windowSet rs.lab tc len (by omega)
    guide := GuideRel.refl (by rw [hsFirst, hsCanon]; exact hlive.order)
    baseCanon := by
      rw [hsCanon]
      exact Nat.le_of_lt hnode.canonBelow
    orbits := by
      rw [hsGen, hsOrb]
      exact horb
    coset := by
      rw [hsCoset]
      exact hcoset
    firstDom := by
      rw [hsFirstlab]
      exact hdom
    desc := by
      intro hlt
      rcases hsNcl with hncl | hncl
      · rw [hncl] at hlt
        have hsub := hdesc hlt
        exact (hsub.setActive (a := VSet.empty)).ofFrames
          rfl rfl rfl
      · rw [hncl] at hlt
        exfalso
        omega
    bnd := by
      rcases hsNcl with hncl | hncl <;> rw [hncl] <;> omega
    park := hsPark
    keep := by
      intro hlt
      rcases hsNcl with hncl | hncl
      · exact hncl
      · rw [hncl] at hlt
        omega }
  obtain ⟨outBest, eventTrail, hrunL, hguideL, hkeepL⟩ :=
    otherLoopTotal (tv1 := (tcell.nextElem none).getD 0) (tail := len - 1)
      hg hinf hn0 ih (by omega) (by omega) hpathFull hstemFull hpastFull
      hbound (by omega) (n + 1) none tcell start best trail bs hh
      (by simp only [cursorRank]; omega)
  generalize hLdef : otherChildLoop ctx inf tcLevel runFuel (n + 1) level
    rs.numcells tc ((tcell.nextElem none).getD 0) (tcell.nextElem none) tcell
    start = L' at hrunL hguideL hkeepL
  have hguide : GuideRel level st L'.2 := by
    have hab : GuideRel level st start :=
      ⟨hsFirst, by rw [hsFirst, hsCanon]; exact hlive.order,
        Or.inl ⟨hsCanon, hsCanonlab⟩⟩
    refine GuideRel.transRefine hab hguideL ?_ ?_ ?_ ?_ hend ?_ ?_
    · rw [hsPtn, hnode.run.searchOk.ptnSize, href.1.ok.ptnSize]
    · rw [hsLab, hsPtn, href.1.ok.ptnSize, href.1.ok.labSize]
    · rw [hsPtn, href.1.ok.ptnSize]
      exact hrunL.proof.loop.outcome.event.canonSize
    · rw [hsPtn]
      exact href.1.ok.ptnEnd
    · rw [hsPtn]
      exact hrefInv.grow
    · rw [hsLab]
      exact hrefInv.perm
  have hkeep : OtherKeep ctx level st L'.2 :=
    ⟨hkeepL.firstlab.trans hsFirstlab, hkeepL.orbits, hkeepL.boundary⟩
  rcases L' with ⟨_ | r, out⟩
  · rw [hnone out hLdef]
    exact ⟨outBest, eventTrail,
      hrunL.toNodeNoneInc hinc (by simp only [cursorRank]; omega) hsFixed
        hsCoset hguide, hkeep⟩
  · rw [hsome r out hLdef]
    exact ⟨outBest, eventTrail,
      hrunL.toNodeSomeInc hinc hstemFull hsFixed hsCoset hguide, hkeep⟩

/-! # The specification's target cell -/

/-- An off-path internal node with a nonnegative comparison sweeps the
specification's target cell. -/
theorem NodeInv.plainSweep {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel sf runFuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + (sf + 1) = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hnonneg : (otherLeafSt ctx level numcells st).compCanon ≥ 0) :
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel (sf + 1) (runFuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells best outBest trail eventTrail
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2 := by
  obtain ⟨tc, len, hmk, hprocess, hchildren, hloop⟩ :=
    LoopInv.NodeInv.otherSweep (specFuel := sf) hg hn0 (by omega) hpath hnode
      (Nat.ne_of_lt hnum) hnonneg (by omega)
  have hlab := otherLeafSt_lab ctx level numcells st
  have hptn := otherLeafSt_ptn ctx level numcells st
  obtain ⟨-, -, -, -, -, -, -, -, -, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hmk' : maketargetcell ctx (otherLeafSt ctx level numcells st).lab
      (otherLeafSt ctx level numcells st).ptn level tcLevel (-1) =
      (tc, worksetOf n (refine ctx level st.lab st.ptn st.active
        numcells).lab tc (tc + len - 1), len) := by
    rw [hlab, hptn]
    exact hmk
  have hmkU := hmk'
  have hprocessU := hprocess
  simp only [otherLeafSt] at hmkU hprocessU
  have hshortBase : ({ otherLeafSt ctx level numcells st with
      tctotal := (otherLeafSt ctx level numcells st).tctotal + len } :
        SearchSt n).needshortprune = false :=
    hf10.trans hnode.shortClear
  have hshortU := hshortBase
  simp only [otherLeafSt] at hshortU
  have hhalf : ¬ (Int.ofNat level < Int.ofNat level) := Int.lt_irrefl _
  rcases hc : cheapautom (otherLeafSt ctx level numcells st).ptn level
      n with _ | _
  · -- the cheap-automorphism test fails: the sweep starts parked
    have hcU := hc
    simp only [otherLeafSt] at hcU
    have hstate := LoopInv.otherNode_park_state ctx inf tcLevel runFuel level numcells
      st hnum hnonneg
      (by
        dsimp only
        rw [hmkU]
        dsimp only
        rw [hprocessU]
        exact hshortU)
      (by
        dsimp only
        rw [hmkU]
        dsimp only
        rw [hprocessU]
        exact hcU)
    dsimp only at hstate
    rw [hmkU] at hstate
    dsimp only at hstate
    rw [hprocessU] at hstate
    dsimp only at hstate
    rw [ite_eq_right hhalf] at hstate
    have hsw : sweepStart ctx level numcells len st =
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len
          noncheaplevel := level + 1 } := by
      unfold sweepStart
      dsimp only
      rw [ite_eq_right (by rw [hc]; exact Bool.false_ne_true)]
    refine hnode.sweepNode hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
      hdesc hlive hpathOk horb hcoset hdom hloop.lenTwo hloop
      (by rw [hchildren]) rfl ?_ ?_
    · intro r out hL
      rw [hstate]
      rw [hsw] at hL
      simp only [otherLeafSt] at hL
      rw [hL]
    · intro out hL
      rw [hstate]
      rw [hsw] at hL
      simp only [otherLeafSt] at hL
      rw [hL]
  · -- the cheap-automorphism test passes
    have hcU := hc
    simp only [otherLeafSt] at hcU
    have hstate := otherNode_plain_state ctx inf tcLevel runFuel level numcells
      st hnum hnonneg
      (by
        dsimp only
        rw [hmkU]
        dsimp only
        rw [hprocessU]
        exact hshortU)
      (by
        dsimp only
        rw [hmkU]
        dsimp only
        rw [hprocessU]
        exact hcU)
    dsimp only at hstate
    rw [hmkU] at hstate
    dsimp only at hstate
    rw [hprocessU] at hstate
    dsimp only at hstate
    rw [ite_eq_right hhalf] at hstate
    have hsw : sweepStart ctx level numcells len st =
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len } := by
      unfold sweepStart
      dsimp only
      rw [ite_eq_left hc]
    refine hnode.sweepNode hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
      hdesc hlive hpathOk horb hcoset hdom hloop.lenTwo hloop
      (by rw [hchildren]) rfl ?_ ?_
    · intro r out hL
      rw [hstate]
      rw [hsw] at hL
      simp only [otherLeafSt] at hL
      rw [hL]
    · intro out hL
      rw [hstate]
      rw [hsw] at hL
      simp only [otherLeafSt] at hL
      rw [hL]

/-! # The first path's hinted target cell -/

/-- A frozen off-path internal node that still agrees with the first path
sweeps the first path's target cell when the stored hint is confirmed.
The sweep bound is not the node key, but both are dominated by the
incumbent. -/
theorem NodeInv.hintSweep {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel sf runFuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + (sf + 1) = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmatch : Int.ofNat (maketargetcell ctx
        (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 =
      (otherLeafSt ctx level numcells st).firsttc[level]!) :
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel (sf + 1) (runFuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells best outBest trail eventTrail
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2 := by
  have href := hnode.refined hg hn0 (by omega)
  have hlab := otherLeafSt_lab ctx level numcells st
  have hptn := otherLeafSt_ptn ctx level numcells st
  obtain ⟨-, -, -, -, -, -, -, -, -, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hnc : ¬ (((refine ctx level st.lab st.ptn st.active
      numcells).numcells == n) = true) := by
    intro h
    exact Nat.ne_of_lt hnum (beq_iff_eq.mp h)
  have hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff hn0
      hnode.run.searchOk (by omega)]
    exact Nat.ne_of_lt hnum
  obtain ⟨tc, len, hmk, hcell, hlen2, hrange⟩ :=
    maketargetcell_open (ctx := ctx)
      (lab := (refine ctx level st.lab st.ptn st.active numcells).lab)
      (ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn)
      (level := level) (tcLevel := tcLevel)
      (hint := (otherLeafSt ctx level numcells st).firsttc[level]!)
      (by omega) href.1.ok.ptnSize href.1.ok.ptnEnd
      (by rw [href.2.2]; exact hnum)
  have hmk' : maketargetcell ctx (otherLeafSt ctx level numcells st).lab
      (otherLeafSt ctx level numcells st).ptn level tcLevel
      (otherLeafSt ctx level numcells st).firsttc[level]! =
      (tc, worksetOf n (refine ctx level st.lab st.ptn st.active
        numcells).lab tc (tc + len - 1), len) := by
    rw [hlab, hptn]
    exact hmk
  have hprep : RunPrep G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (otherLeafSt ctx level numcells st) best trail :=
    hnode.run.otherLeaf hn0 (by omega) hpath
  have hbase : RunPrep G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal + len }
      best trail :=
    hprep.setTctotal
  have hprocess : processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal + len } =
      (Int.ofNat level,
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len }) := by
    apply processnode_internal
    · intro h
      exact h.1 (beq_iff_eq.mp heq)
    · exact hnc
  obtain ⟨hsLab, hsPtn, -, -, hsFirst, hsCanon, -, -, -, -, -, hsShort, -, -,
    -⟩ := sweepStart_frames ctx level numcells len st
  have hrun : RunInv G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (sweepStart ctx level numcells len st) best trail := by
    unfold sweepStart
    dsimp only
    rcases hc : cheapautom (otherLeafSt ctx level numcells st).ptn level
        n with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      exact hbase.run.park (hbase.cheap.park (by omega) (by omega))
    · simp only [ite_true]
      exact hbase.run
  have hvals : ∀ q : Nat,
      (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! ≤ level ∨
      (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! =
        n + 2 := by
    intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · exact href.1.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [href.1.ok.ptnSize]; omega)]
      exact Nat.zero_le _
  have hloop0 := LoopInv.start (specFuel := sf) hn0 (by omega) hrun
    (by rw [hsFirst]; exact hnode.firstBelow)
    (by rw [hsCanon]; exact hnode.canonBelow)
    (by rw [hsLab, hsPtn]; exact href.2.1)
    (by rw [hsPtn]; exact hcell) hlen2 hrange
    (by rw [hsPtn]; exact hvals)
    (by rw [hsShort]; exact hnode.shortClear) (by omega)
  have hloop : LoopInv G ctx tcLevel sf level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn tc len
      (worksetOf n (refine ctx level st.lab st.ptn st.active numcells).lab tc
        (tc + len - 1))
      none (sweepStart ctx level numcells len st)
      (sweepStart ctx level numcells len st) best trail := by
    rw [worksetOf_eq_windowSet _ tc len (by omega)]
    simpa only [hsLab, hsPtn] using hloop0
  -- both the sweep bound and the node key are dominated by the incumbent
  obtain ⟨tc', len', -, hspec', -, hlen2', -⟩ :=
    hnode.target hg hn0 (by omega) (Nat.ne_of_lt hnum)
  have hlenSpec : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn level
      tcLevel).2.2 = (len' - 1) + 1 := by
    rw [hspec']
    dsimp only
    omega
  have hnodeLe : keyLe (nodeKey ctx tcLevel (sf + 1) level codes st numcells)
      (incKey ctx bs st.canonlab) :=
    nodeKey_le_of_frozen hprep.codeInv hneg hdisc hlenSpec
  have hboundLe : keyLe (keysMax
      (sweepKey ctx tcLevel sf level
        (codes ++ [(refine ctx level st.lab st.ptn st.active
          numcells).longcode])
        (refine ctx level st.lab st.ptn st.active numcells).lab
        (refine ctx level st.lab st.ptn st.active numcells).ptn tc
        (refine ctx level st.lab st.ptn st.active numcells).numcells 0)
      ((List.range (len - 1)).map fun o =>
        sweepKey ctx tcLevel sf level
          (codes ++ [(refine ctx level st.lab st.ptn st.active
            numcells).longcode])
          (refine ctx level st.lab st.ptn st.active numcells).lab
          (refine ctx level st.lab st.ptn st.active numcells).ptn tc
          (refine ctx level st.lab st.ptn st.active numcells).numcells
          (o + 1)))
      (incKey ctx bs st.canonlab) := by
    apply keysMax_le
    · exact hprep.codeInv.frozenBound hneg _
    · intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨o, -, rfl⟩ := hy
      exact hprep.codeInv.frozenBound hneg _
  -- the executable node
  have hshort' : SearchSt.needshortprune (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal +
          (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
            (otherLeafSt ctx level numcells st).ptn level tcLevel
            (otherLeafSt ctx level numcells st).firsttc[level]!).2.2 }).2 =
      false := by
    rw [hmk']
    dsimp only
    rw [hprocess]
    exact hf10.trans hnode.shortClear
  have hstate := otherNode_hint_state ctx inf tcLevel runFuel level numcells
    st hnum heq hneg hmatch hshort'
  dsimp only at hstate
  rw [hmk'] at hstate
  dsimp only at hstate
  rw [hprocess] at hstate
  dsimp only at hstate
  rw [ite_eq_right (Int.lt_irrefl _)] at hstate
  have hflip : (if ¬ cheapautom
        ({ otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len } :
            SearchSt n).ptn level n = true then
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len
          noncheaplevel := level + 1 }
      else
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal + len }) =
      sweepStart ctx level numcells len st := by
    unfold sweepStart
    dsimp only
    rcases hc : cheapautom (otherLeafSt ctx level numcells st).ptn level
        n with _ | _
    · simp only [Bool.false_eq_true, not_false_eq_true, ite_true, ite_false]
    · simp only [not_true_eq_false, ite_false, ite_true]
  rw [hflip] at hstate
  refine hnode.sweepNode hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
    hdesc hlive hpathOk horb hcoset hdom hlen2 hloop
    (by
      rw [hnode.run.incumbent]
      exact (incMax_of_frozen hboundLe).trans (incMax_of_frozen hnodeLe).symm)
    rfl ?_ ?_
  · intro r out hL
    rw [hstate, hL]
  · intro out hL
    rw [hstate, hL]

/-! # Every off-path internal node -/

/-- Totality of an off-path internal node at the next executable fuel,
given totality of every off-path node at the current fuel. -/
theorem NodeInv.internalOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + specFuel = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n) :
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel specFuel (runFuel + 1) level codes fs st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells best outBest trail eventTrail
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel (runFuel + 1) level numcells st).2 := by
  have hle : level ≤ n := hnode.run.searchOk.levelLe
  obtain ⟨sf, rfl⟩ : ∃ sf, specFuel = sf + 1 := ⟨specFuel - 1, by omega⟩
  by_cases hgate : (otherLeafSt ctx level numcells st).eqlevFirst ≠ level ∧
      (otherLeafSt ctx level numcells st).compCanon < 0
  · obtain ⟨hrun, hkeep⟩ := hnode.gateRun (inf := inf) (specFuel := sf)
      (fuel := runFuel) hg hn0 (by omega) hpath hcheap hnum hgate hlive
      horb
    exact ⟨best, trail, hrun, hkeep⟩
  by_cases hnonneg : (otherLeafSt ctx level numcells st).compCanon ≥ 0
  · exact hnode.plainSweep hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
      hdesc hlive hpathOk horb hcoset hdom hnum hnonneg
  have hneg : (otherLeafSt ctx level numcells st).compCanon < 0 := by
    omega
  have heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true := by
    rcases Decidable.em ((otherLeafSt ctx level numcells st).eqlevFirst =
        level) with h | h
    · exact beq_iff_eq.mpr h
    · exact absurd ⟨h, hneg⟩ hgate
  by_cases hmatch : Int.ofNat (maketargetcell ctx
      (otherLeafSt ctx level numcells st).lab
      (otherLeafSt ctx level numcells st).ptn level tcLevel
      (otherLeafSt ctx level numcells st).firsttc[level]!).1 =
      (otherLeafSt ctx level numcells st).firsttc[level]!
  · exact hnode.hintSweep hg hinf hn0 ih hlevel hpath hspec hfuel hcheap
      hdesc hlive hpathOk horb hcoset hdom hnum heq hneg hmatch
  · obtain ⟨hrun, hkeep⟩ := hnode.hintFailRun (inf := inf) (specFuel := sf)
      (fuel := runFuel) hg hn0 (by omega) hpath hcheap hnum heq hneg
      hmatch hlive horb
    exact ⟨best, trail, hrun, hkeep⟩

end Hex.GraphIso.Nauty
