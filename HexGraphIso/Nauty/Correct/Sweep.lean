/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Exit
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.OrbJoin

public section

/-!
The sibling-sweep induction and the fuel-separated totality statements
it feeds.

Base cases and transport for one sweep, the assembly of the first
descent, the facts carried alongside the induction that no other package
records, the negative-comparison arms of an internal off-path node,
per-child transport, and the node statements whose logical, recursion and
cursor fuels are kept distinct.
-/

/-!
Base cases and transport for the corrected sibling-sweep induction.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The executable bookkeeping that precedes an off-path sibling sweep
preserves its entry guide relation. -/
theorem NodeInv.otherGuide {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells len : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    let pre := otherLeafSt ctx level numcells st
    let base : SearchSt n := { pre with tctotal := pre.tctotal + len }
    let start := if cheapautom base.ptn level n then base
      else { base with noncheaplevel := level + 1 }
    GuideRel level st start := by
  dsimp only
  let pre := otherLeafSt ctx level numcells st
  let base : SearchSt n := { pre with tctotal := pre.tctotal + len }
  let start := if cheapautom base.ptn level n then base
    else { base with noncheaplevel := level + 1 }
  have hfirst : pre.gcaFirst = st.gcaFirst := by
    simpa only [pre] using
      (RefTrail.otherLeaf_gcaFirst ctx level numcells st)
  have hcanon : pre.gcaCanon = st.gcaCanon := by
    simpa only [pre] using
      (RefTrail.otherLeaf_gcaCanon ctx level numcells st)
  have hcanonLab : pre.canonlab = st.canonlab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let raw : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    simpa only [pre, otherLeafSt, rs, raw] using
      (otherNodePrep_frames level rs.longcode raw).1
  have horder : start.gcaFirst ≤ start.gcaCanon := by
    simpa only [pre, base, start] using
      (hnode.otherLive (len := len) hlive).order
  refine ⟨?_, horder, Or.inl ⟨?_, ?_⟩⟩
  · split <;> exact hfirst
  · split <;> exact hcanon
  · split <;> exact hcanonLab

namespace OtherOutcome

/-- Resolving an ordinary off-path child after clearing a pending
short-prune request rebuilds the parent invariant.  This is the uniform
recovery form used by both filtered and unfiltered executable branches. -/
theorem nextClear {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len tv offset currentOffset inf : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail)
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out)
    (hinf : inf = n + 2) (hpath : codes.length = level)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (hnext : tcell.nextElem cursor = some tv)
    (hoffset : offset < len) (hcurrent : currentOffset < len)
    (htv : rsLab[tc + offset]! = tv)
    (hat : st.lab[tc + currentOffset]! = tv)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.2
            fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
          (numcells + 1)) :
    let cleaned : SearchSt n :=
      { out with
        fixedpts := out.fixedpts.erase tv
        needshortprune := false }
    let recovered := Nauty.recover n inf level cleaned
    ∃ bs',
      LoopInv G ctx tcLevel specFuel level codes bs' fs numcells rsLab rsPtn
          tc len tcell (some tv) base recovered outBest eventTrail ∧
        OtherLive ctx level recovered eventTrail := by
  dsimp only
  let child : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
  let oldCleaned : SearchSt n :=
    { out with fixedpts := out.fixedpts.erase tv }
  let cleaned : SearchSt n :=
    { oldCleaned with needshortprune := false }
  let oldRecovered := Nauty.recover n inf level oldCleaned
  let recovered := Nauty.recover n inf level cleaned
  have hreturn : r = Int.ofNat level := h.node.parentEq hfuel hstay
  have hfirst : child.gcaFirst < level := by
    change st.gcaFirst < level
    exact hlive.firstBelow
  have hfirstOut : out.gcaFirst < level := by
    rw [h.firstGuide]
    exact hfirst
  have hcoverage := h.cover hinv hfuel hstay hnext hoffset htv hfirst heq
  have hrecOld : SearchOut G level level base oldRecovered ∧
      SearchOk G level numcells oldRecovered := by
    simpa only [oldRecovered, oldCleaned, hat] using
      hinv.recoverChild hinf hcurrent hout
  have hrecovered : recovered =
      { oldRecovered with needshortprune := false } := by
    unfold recovered cleaned oldRecovered
    exact recover_clearShort n inf level oldCleaned
  have heffect : SearchOut G level level base recovered := by
    apply hrecOld.1.congr
    all_goals rw [hrecovered]
  have hok : SearchOk G level numcells recovered := by
    rw [hrecovered]
    exact {
      labSize := hrecOld.2.labSize
      ptnSize := hrecOld.2.ptnSize
      reach := hrecOld.2.reach
      init1 := hrecOld.2.init1
      vals := hrecOld.2.vals
      count := hrecOld.2.count
      bc := hrecOld.2.bc
      canon := hrecOld.2.canon }
  have hinfLevel : level < inf := by
    rw [hinf]
    have hle : level ≤ n := Nat.le_trans hinv.run.searchOk.bc
      (bcount_le st.ptn level n)
    omega
  have hfirstClean : cleaned.gcaFirst ≤ level := by
    exact Nat.le_of_lt hfirstOut
  obtain ⟨bs', hrun, hstable, hhistory⟩ :=
    (h.node.event.clearShort.setFixed (out.fixedpts.erase tv)).recoverRun
      hreturn hpath hinv.positive hinfLevel hfirstClean hok
  have hlive' : OtherLive ctx level recovered eventTrail := by
    constructor
    · constructor
      · exact hhistory
      · exact RefTrail.recover_order h.order hfirstClean
      · exact hstable
    · rw [(recover_frames n inf level cleaned).2.2.2.2.2.2.1]
      exact hfirstOut
  have hrefsOld := h.refs hinv hlive hcoverage hfuel hnext hoffset hcurrent
    htv hat (inf := inf) (fixedpts := out.fixedpts.erase tv)
  have hrefs : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells recovered outBest := by
    rw [hrecovered]
    exact ⟨hrefsOld.first, hrefsOld.canon⟩
  refine ⟨bs', ?_, hlive'⟩
  exact {
    nonempty := hinv.nonempty
    positive := hinv.positive
    baseOk := hinv.baseOk
    run := hrun
    effect := heffect
    baseLab := hinv.baseLab
    basePtn := hinv.basePtn
    equitable := hinv.equitable
    cell := hinv.cell
    lenTwo := hinv.lenTwo
    range := hinv.range
    values := hinv.values
    members := hinv.members
    cover := hcoverage
    refs := hrefs
    shortClear := by
      rw [recover_needshortprune]
    fuelBound := hinv.fuelBound }

end OtherOutcome

namespace EventOut

/-- Expose any shorter ancestor prefix of an existing search event. -/
theorem ancestor {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem codes fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel codes fs out best trail r)
    (hprefix : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length) :
    EventOut G ctx tcLevel stem fs out best trail r := by
  cases h with
  | intro current deep bestCodes event depth codesEq past returned stable
      history =>
      apply EventOut.intro current deep bestCodes event depth
      · calc
          deep.take stem.length =
              (deep.take codes.length).take stem.length := by
                rw [List.take_take, Nat.min_eq_left
                  (Nat.le_of_lt hshorter)]
          _ = stem := by rw [codesEq, hprefix]
      · omega
      · exact returned
      · exact stable
      · exact history

end EventOut

namespace LoopInv

/-- Replacing the mutable sweep set by a subset preserves the loop
invariant once transitive coverage has been re-established for that set. -/
theorem restrict {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell tcell' : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true)
    (hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell' cursor best) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
      tc len tcell' cursor base st best trail := by
  exact {
    nonempty := h.nonempty
    positive := h.positive
    baseOk := h.baseOk
    run := h.run
    effect := h.effect
    baseLab := h.baseLab
    basePtn := h.basePtn
    equitable := h.equitable
    cell := h.cell
    lenTwo := h.lenTwo
    range := h.range
    values := h.values
    members := fun v hv => h.members v (hsub v hv)
    cover := hcover
    refs := h.refs
    shortClear := h.shortClear
    fuelBound := h.fuelBound }

/-- Every fixed vertex of the receiving parent lies in the `fix` set of
an implicit pair frozen at a deeper cheap-cell boundary.  The result trail
identifies the parent's frozen frame; its two closed singleton boundaries
are unchanged in the deeper event partition. -/
theorem fmptnFix {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hpathCodes : level = codes.length)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hevent : EventOut G ctx tcLevel codes fs out outBest eventTrail r)
    (hpreserved : TrailExt (level + 1)
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail)
    (hsaved : level ≤ out.noncheaplevel) :
    ∀ v, v < n → st.fixedpts.mem v = true →
      (fmptn out.lab out.ptn out.noncheaplevel n).1.mem v = true := by
  intro v hv hfixed
  obtain ⟨q, hq, hqv, hsingle⟩ := hpath.fixed v hv hfixed
  have hsingleFrozen : IsCell rsPtn level q 1 := by
    rw [← h.ptnEq]
    exact hsingle
  have hparentLab : rsLab[q]! = st.lab[q]! :=
    cellsPerm_singleton h.labPerm hsingleFrozen
  let entry : TrailEntry :=
    ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
  have hentry : eventTrail level = some entry := by
    exact hpreserved.pushAt
  cases hevent with
  | intro current eventCodes bestCodes event depth stemEq past returned
      stable history =>
    have hcurrent : level < current := by
      rw [hpathCodes]
      exact past
    have hreach := event.trailOk.reach level entry hcurrent hentry
    change cellsPerm rsPtn level rsLab out.lab at hreach
    have houtLab : out.lab[q]! = v := by
      have heq := cellsPerm_singleton hreach hsingleFrozen
      rw [← heq, hparentLab, hqv]
    have hcellOut : IsCell out.ptn level q 1 := by
      apply isCell_of_agree hsingleFrozen
      intro x hxlo hxhi
      apply event.trailOk.frozen level entry hcurrent hentry
      change rsPtn[x]! ≤ level
      rcases Nat.eq_zero_or_pos q with rfl | hqpos
      · have hx : x = 0 := by omega
        subst x
        exact hsingleFrozen.2.2.2
      · rcases hsingleFrozen.2.1 with hzero | hstart
        · omega
        · rcases Decidable.em (x = q - 1) with hx | hx
          · rw [hx]
            exact hstart
          · have hxq : x = q := by omega
            rw [hxq]
            exact hsingleFrozen.2.2.2
    have hcellSaved := isCell_one_mono hcellOut hsaved
    have hend : out.ptn[out.ptn.size - 1]! ≤ out.noncheaplevel :=
      Nat.le_trans event.cheap.rootEnd (by
        exact Nat.succ_le_iff.mp event.cheap.positive)
    have hmem : (q, q) ∈ cells out.ptn out.noncheaplevel n := by
      have hmem' := isCell_mem_cells hcellSaved
        (by
          rw [event.cheap.ptnSize]
          exact Nat.le_refl _)
        hend hq
      have heq : q + 1 - 1 = q := by omega
      rw [heq] at hmem'
      exact hmem'
    have hbit := fmptn_singleton (lab := out.lab) hmem
      (by rw [houtLab]; assumption)
    rw [houtLab] at hbit
    exact hbit

/-- Root validity of the implicit pair and containment of the parent path
localize that pair to the exact frozen frame consumed by `shortprune`. -/
theorem fmptnPair {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hpathCodes : level = codes.length)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hevent : EventOut G ctx tcLevel codes fs out outBest eventTrail r)
    (hpreserved : TrailExt (level + 1)
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail)
    (hsaved : level ≤ out.noncheaplevel)
    (hroot : PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmptn out.lab out.ptn out.noncheaplevel n).1
      (fmptn out.lab out.ptn out.noncheaplevel n).2) :
    PairOk ctx.g rsPtn rsLab level
      (fmptn out.lab out.ptn out.noncheaplevel n).1
      (fmptn out.lab out.ptn out.noncheaplevel n).2 := by
  have hfix := h.fmptnFix hpathCodes hpath hevent hpreserved hsaved
  have hpair := hpath.pair hroot hfix
  rw [h.ptnEq] at hpair
  have hstSize : st.lab.size = n := h.run.searchOk.labSize
  exact LocalAutos.reindexPair hpair (cellsPerm_symm h.labPerm)
    h.frozenPtnSize hstSize h.frozenLabSize h.frozenEnd

namespace ShortSource

/-- A live short-prune source that reaches a receiving loop without a
lower return is valid in that loop's frozen frame.  The child exit bound
identifies the recorded target with the receiver; explicit pairs then use
their stored frame, while implicit pairs are localized from the root. -/
theorem atReceiver {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st child out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    {fix mcr : VSet n}
    (hpathCodes : level = codes.length)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hexit : NodeExit ctx tcLevel specFuel runFuel (level + 1) codes child
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) r)
    (hevent : EventOut G ctx tcLevel codes fs out outBest eventTrail r)
    (hpreserved : TrailExt (level + 1)
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail)
    (hsource : ShortSource G ctx out eventTrail r)
    (hstay : ¬ r < Int.ofNat level)
    (hback : out.autos.back? = some (fix, mcr)) :
    PairOk ctx.g rsPtn rsLab level fix mcr := by
  have hrBelow : r < Int.ofNat (level + 1) :=
    hexit.below (by omega)
  cases hsource with
  | explicit target sourceFix sourceMcr returned back valid =>
      have htargetBelow : target < level + 1 := by
        rw [returned] at hrBelow
        exact Int.ofNat_lt.mp hrBelow
      have hlevelLe : level ≤ target := by
        rw [returned] at hstay
        exact Int.ofNat_le.mp (Int.le_of_not_gt hstay)
      have htarget : target = level := by omega
      subst target
      have hp := valid
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
        hpreserved.pushAt
      have heq : (sourceFix, sourceMcr) = (fix, mcr) := by
        apply Option.some.inj
        rw [← back, ← hback]
      cases heq
      simpa only [sweepFrame] using hp
  | implicit target returned below back root =>
      have htargetBelow : target < level + 1 := by
        rw [returned] at hrBelow
        exact Int.ofNat_lt.mp hrBelow
      have hlevelLe : level ≤ target := by
        rw [returned] at hstay
        exact Int.ofNat_le.mp (Int.le_of_not_gt hstay)
      have htarget : target = level := by omega
      subst target
      have hp := hinv.fmptnPair hpathCodes hpath hevent hpreserved
        (Nat.le_of_lt below) root
      have heq :
          (fmptn out.lab out.ptn out.noncheaplevel n) = (fix, mcr) := by
        apply Option.some.inj
        rw [← back, ← hback]
      rw [heq] at hp
      exact hp

end ShortSource

/-- The long-prune filter preserves the full mutable sweep invariant.
The root ledger supplies valid pairs at the current ordering, and the
frozen-frame permutation transports their cell stabilization back to the
specification ordering. -/
theorem longprune {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hgsz : ctx.g.size = n)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
      tc len (Nauty.longprune tcell st.fixedpts st.autos) cursor base st
      best trail := by
  have hlocal : LocalAutos ctx level st := hpath.autos h.run
  have hstSize : st.lab.size = n := h.run.searchOk.labSize
  have haut : ∀ p ∈ st.autos.toList,
      st.fixedpts.subset p.1 = true →
      PairOk ctx.g rsPtn rsLab level p.1 p.2 := by
    intro p hp hfix
    have hpair := hlocal p hp hfix
    rw [h.ptnEq] at hpair
    exact LocalAutos.reindexPair hpair (cellsPerm_symm h.labPerm)
      h.frozenPtnSize hstSize h.frozenLabSize h.frozenEnd
  apply h.restrict (fun _ hm => longprune_subset hm)
  exact h.cover.longprune hgsz h.frozenLabSize h.frozenLabOk
    h.frozenPtnSize h.frozenEnd h.values h.cell h.range h.fuelBound haut

/-- The short-prune filter may read the newest pair from a descendant
state; validity at the frozen parent frame is the only fact needed to
preserve the mutable sweep invariant. -/
theorem shortpruneWith {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hgsz : ctx.g.size = n)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlast : ∀ fix mcr : VSet n, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g rsPtn rsLab level fix mcr) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
      tc len (Nauty.shortprune tcell out) cursor base st best trail := by
  apply h.restrict (fun _ hm => shortprune_subset hm)
  exact h.cover.shortprune hgsz h.frozenLabSize h.frozenLabOk
    h.frozenPtnSize h.frozenEnd h.values h.cell h.range h.fuelBound hlast

/-- The common case reads the newest pair from the current loop state. -/
theorem shortprune {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hgsz : ctx.g.size = n)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlast : ∀ fix mcr : VSet n, st.autos.back? = some (fix, mcr) →
      PairOk ctx.g rsPtn rsLab level fix mcr) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
      tc len (Nauty.shortprune tcell st) cursor base st best trail :=
  h.shortpruneWith hgsz hlast

/-- A child result carrying a live request supplies exactly the local
newest-pair premise required to filter its receiving parent sweep. -/
theorem shortpruneChild {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n}
    {offset : Nat} {fixedpts : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st childSt child : SearchSt n}
    {best childBest : Option (Key n)} {trail eventTrail : FrameTrail}
    {value : Int}
    (hgsz : ctx.g.size = n)
    (hpathCodes : level = codes.length)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      childSt child (numcells + 1) best childBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail value)
    (hstay : ¬ value < Int.ofNat level)
    (hshort : child.needshortprune = true) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
      tc len (Nauty.shortprune tcell
        { child with fixedpts := fixedpts, needshortprune := false })
      cursor base st best trail := by
  apply h.shortpruneWith hgsz
  intro fix mcr hback
  apply ShortSource.atReceiver hpathCodes h hpath hchild.node.exit
    hchild.node.event hchild.node.preserved (hchild.node.short hshort) hstay
  simpa only using hback

/-- The mutable child selected for a frozen offset has exactly that
offset's specification key. -/
theorem childKey {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len tv offset currentOffset coset : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hoffset : offset < len)
    (hfrozen : rsLab[tc + offset]! = tv)
    (hcurrentAt : st.lab[tc + currentOffset]! = tv) :
    sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells
        offset =
      nodeKey ctx tcLevel specFuel (level + 1) codes
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).2.2
          fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]!
          cosetindex := coset }
        (numcells + 1) := by
  let child : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]!
      cosetindex := coset }
  rw [← h.baseLab, ← h.basePtn]
  apply SearchOut.breakoutKey h.effect h.baseOk h.run.searchOk
    h.nonempty h.positive
  · rw [h.basePtn]
    exact h.cell
  · exact h.lenTwo
  · exact h.range
  · exact hoffset
  · change child.lab = (breakout n st.lab st.ptn (level + 1) tc
      base.lab[tc + offset]!).1
    rw [h.baseLab, hfrozen, ← hcurrentAt]
  · change child.ptn = (breakout n st.lab st.ptn (level + 1) tc
      base.lab[tc + offset]!).2.1
    rw [h.baseLab, hfrozen, ← hcurrentAt]
  · change child.active = (breakout n st.lab st.ptn (level + 1) tc
      base.lab[tc + offset]!).2.2
    rw [h.baseLab, hfrozen, ← hcurrentAt]
  · rfl
  · exact h.fuelBound

/-- Every original target-cell child key is below the fixed sweep bound. -/
theorem keyLeBound {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells tail offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {bound : Key n}
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells 0)
      ((List.range tail).map fun o =>
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells (o + 1)))
    (hlen : len = tail + 1) (hoffset : offset < len) :
    keyLe (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells offset) bound := by
  rw [hbound]
  rcases offset with _ | offset
  · exact keyLe_keysMax (Or.inl rfl)
  · apply keyLe_keysMax
    right
    exact List.mem_map.mpr ⟨offset, List.mem_range.mpr (by omega), rfl⟩

/-- In a verified small-cell subtree, the fixed sibling-sweep bound is
the key of any selected member.  This is the semantic step that lets a
saved cheap-boundary return absorb every unvisited sibling. -/
theorem boundEq {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells tail offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat} {bound : Key n}
    {tcell : VSet n} {cursor : Option Nat} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hsmall : SubtreeOk ctx level
      { lab := rsLab, ptn := rsPtn, active := base.active,
        numcells := numcells, hint := 0, maxpos := 0,
        longcode := numcells })
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1) (hoffset : offset < len) :
    bound = sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells offset := by
  let key := fun o => sweepKey ctx tcLevel specFuel level codes rsLab
    rsPtn tc numcells o
  have hkey : ∀ o, o < len → key o = key offset := by
    intro o ho
    apply congrArg (prefixKey codes)
    exact childKey_eq_of_subtree (tcLevel := tcLevel)
      (fuel := specFuel) (numcells := numcells) (oU := offset) (oV := o)
      hsmall hgsz hsymm hloop hinv.cell hinv.lenTwo hinv.range
      hoffset ho hinv.fuelBound
  rw [hbound]
  apply keysMax_eq_of_le
  · rw [show sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells 0 = key 0 by rfl, hkey 0 (by omega)]
    exact keyLe_refl _
  · intro y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy
    rw [show sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells (o + 1) = key (o + 1) by rfl,
      hkey (o + 1) (by rw [hlen]; have := List.mem_range.mp ho; omega)]
    exact keyLe_refl _
  · rcases offset with _ | offset
    · exact Or.inl rfl
    · right
      exact List.mem_map.mpr ⟨offset, List.mem_range.mpr (by omega), rfl⟩

end LoopInv

namespace OtherLoopRun

theorem reindexSet {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell tcell' : VSet n} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.proof.reindexSet, h.exit.reindexSet, h.short⟩

theorem step {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out best
      outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.proof.step ha, h.exit.step ha, h.short⟩

theorem prepend {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st recSt out : SearchSt n} {best mid outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (h : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.proof.prepend hfixed hcoset hpre, h.exit.prepend hpre, h.short⟩

/-- Compose an ordinary non-guiding child with the recursively proved
tail of an off-path sweep. -/
theorem next {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st child recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : tcell.nextElem cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = false)
    (hother : (tv == tv1) = false)
    (hrecover : recSt = recover n inf level
      { child with fixedpts := child.fixedpts.erase tv })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (hloop : otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (tcell.nextElem (some tv)) tcell recSt = (r, out))
    (hrec : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound recSt out
      mid outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest receiptTrail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  subst recSt
  simp only [hshort] at hloop hrec hfixed hcoset
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, Bool.false_eq_true, ite_false, hother]
  rw [hloop]
  exact (hrec.prepend hfixed hcoset hpre).step (nextElem_after hnext)

/-- Compose a guiding child with the long-pruned recursive tail of an
off-path sweep. -/
theorem nextLong {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv : Nat} {tcell filtered : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st child recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : tcell.nextElem cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = false)
    (hfirst : (tv == tv1) = true)
    (hfiltered : filtered = longprune tcell
      (child.fixedpts.erase tv) child.autos)
    (hrecover : recSt = recover n inf level
      { child with fixedpts := child.fixedpts.erase tv })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (hloop : otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (filtered.nextElem (some tv)) filtered recSt = (r, out))
    (hrec : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells filtered (some tv) bound recSt out
      mid outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest receiptTrail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  subst filtered
  subst recSt
  simp only [hshort] at hloop hrec hfixed hcoset
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, Bool.false_eq_true, ite_false, hfirst, ite_true]
  rw [hloop]
  exact ((hrec.prepend hfixed hcoset hpre).reindexSet).step
    (nextElem_after hnext)

/-- Compose a non-guiding child with the short-pruned recursive tail of
an off-path sweep. -/
theorem nextShort {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv : Nat} {tcell filtered : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st child recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : tcell.nextElem cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = true)
    (hother : (tv == tv1) = false)
    (hfiltered : filtered = shortprune tcell
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hrecover : recSt = recover n inf level
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (hloop : otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (filtered.nextElem (some tv)) filtered recSt = (r, out))
    (hrec : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells filtered (some tv) bound recSt out
      mid outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest receiptTrail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  subst filtered
  subst recSt
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, ite_true, hother, Bool.false_eq_true, ite_false]
  rw [hloop]
  exact ((hrec.prepend hfixed hcoset hpre).reindexSet).step
    (nextElem_after hnext)

/-- Compose a guiding child with the short- and long-pruned recursive
tail of an off-path sweep. -/
theorem nextBoth {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv : Nat} {tcell shortSet filtered : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st child recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : tcell.nextElem cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = true)
    (hfirst : (tv == tv1) = true)
    (hshortSet : shortSet = shortprune tcell
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hfiltered : filtered = longprune shortSet
      (child.fixedpts.erase tv) child.autos)
    (hrecover : recSt = recover n inf level
      { child with
        fixedpts := child.fixedpts.erase tv
        needshortprune := false })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (hloop : otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (filtered.nextElem (some tv)) filtered recSt = (r, out))
    (hrec : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells filtered (some tv) bound recSt out
      mid outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest receiptTrail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  subst filtered
  subst shortSet
  subst recSt
  unfold otherChildLoop
  simp only [Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, hfirst, ite_true]
  rw [hloop]
  exact ((hrec.prepend hfixed hcoset hpre).reindexSet).step
    (nextElem_after hnext)

/-- A frozen child return below the receiving loop absorbs the live suffix,
cleans the temporary fixed vertex, and exposes the ancestor event. -/
theorem childFrozen {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv tail offset : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {value : Int}
    {trail eventTrail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } = (value, out))
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail value)
    (hbelow : value < Int.ofNat level)
    (hfreeze : FrozenOut ctx codes out outBest value)
    (hexactChild : outBest = some (incMax best
      (nodeKey ctx tcLevel specFuel (level + 1) codes
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv }
        (numcells + 1))))
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      (numcells + 1)) bound)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1)
    (hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc
      len numcells tcell (some tv) outBest)
    (hfresh : st.fixedpts.mem tv = false) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest trail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change out.fixedpts.erase tv = st.fixedpts
    rw [hchild.node.fixed, erase_insert_of_miss hfresh]
  have hstate : otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell st = (some value, cleaned) := by
    unfold otherChildLoop
    simp only [Id.run_pure, apply_ite Id.run]
    rw [hcall, ite_eq_left hbelow]
  have hevent : EventOut G ctx tcLevel stem fs cleaned outBest eventTrail
      value :=
    (hchild.node.event.ancestor hstem hshorter).setFixed _
  have hsound := LoopSound.ofNode (NodeSound.ofExact hexactChild) hkey
  have hexact : outBest = some (incMax best bound) := by
    rw [hlen] at hcover
    exact hfreeze.exactLoop hpath hbelow hbound hcover hsound
  have hinstalled : cleaned.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc (hevent.read.trans hexact)
  rw [hstate]
  refine ⟨?_, LoopExit.frozen value rfl hbelow hexact
    (hfreeze.setFixed _), ?_⟩
  · exact {
      loop := {
        outcome := {
          receipt := .pruned value rfl hbelow (LoopSound.ofExact hexact)
            hinstalled hevent.read hexact
          event := by simpa only [loopReturn] using hevent
          preserved := hchild.node.preserved.ofPush }
        fixed := hfixed }
      coset := hchild.coset }
  · intro hshort
    refine ⟨value, rfl, ?_⟩
    apply ShortSource.setFixed
    apply hchild.node.short
    simpa only [cleaned] using hshort

/-- A saved cheap-boundary child return below the receiving loop absorbs
the whole verified small-cell sweep and cleans its temporary fixed vertex. -/
theorem childCheap {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv boundary offset : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound childKey : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail}
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv } =
        (Int.ofNat boundary - 1, out))
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail (Int.ofNat boundary - 1))
    (hpositive : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hsaved : out.noncheaplevel = boundary)
    (hbound : bound = childKey)
    (hexact : outBest = some (incMax best childKey))
    (hfresh : st.fixedpts.mem tv = false) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest trail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  let value := Int.ofNat boundary - 1
  let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
  have hvalue : value < Int.ofNat level := by
    simp only [value, Int.ofNat_eq_natCast]
    omega
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change out.fixedpts.erase tv = st.fixedpts
    rw [hchild.node.fixed, erase_insert_of_miss hfresh]
  have hstate : otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell st = (some value, cleaned) := by
    unfold otherChildLoop
    simp only [Id.run_pure, apply_ite Id.run]
    rw [hcall, ite_eq_left hvalue]
  have hevent : EventOut G ctx tcLevel stem fs cleaned outBest eventTrail
      value :=
    (hchild.node.event.ancestor hstem hshorter).setFixed _
  have hexactBound : outBest = some (incMax best bound) := by
    rwa [hbound]
  have hinstalled : cleaned.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc (hevent.read.trans hexactBound)
  rw [hstate]
  refine ⟨?_, LoopExit.cheap boundary rfl hpositive hbelow
    (by simpa only [cleaned] using hsaved) hexactBound, ?_⟩
  · exact {
      loop := {
        outcome := {
          receipt := .pruned value rfl hvalue
            (LoopSound.ofExact hexactBound) hinstalled hevent.read
            hexactBound
          event := by simpa only [loopReturn] using hevent
          preserved := hchild.node.preserved.ofPush }
        fixed := hfixed }
      coset := hchild.coset }
  · intro hshort
    refine ⟨value, rfl, ?_⟩
    apply ShortSource.setFixed
    apply hchild.node.short
    simpa only [cleaned, value] using hshort

/-- Package an already established frozen early return as a corrected
off-path loop result. -/
theorem frozen {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv tv1 : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail}
    {value : Int}
    (hstate : otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
      numcells tc tv1 (some tv) tcell st = (some value, out))
    (hevent : EventOut G ctx tcLevel stem fs out outBest eventTrail value)
    (hpreserved : TrailExt level trail eventTrail)
    (hfixed : out.fixedpts = st.fixedpts)
    (hcoset : out.cosetindex = st.cosetindex)
    (hbelow : value < Int.ofNat level)
    (hexact : outBest = some (incMax best bound))
    (hfreeze : FrozenOut ctx codes out outBest value)
    (hsource : out.needshortprune = true →
      ShortSource G ctx out eventTrail value) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest trail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  have hinstalled : out.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc (hevent.read.trans hexact)
  rw [hstate]
  refine ⟨?_, LoopExit.frozen value rfl hbelow hexact hfreeze, ?_⟩
  · exact {
    loop := {
      outcome := {
        receipt := .pruned value rfl hbelow (LoopSound.ofExact hexact)
          hinstalled hevent.read hexact
        event := by simpa only [loopReturn] using hevent
        preserved := hpreserved }
      fixed := hfixed }
    coset := hcoset }
  · intro hshort
    exact ⟨value, rfl, hsource hshort⟩

/-- Package an already established cheap-cell jump as a corrected
off-path loop result. -/
theorem cheap {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv tv1 boundary : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail}
    (hstate : otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
      numcells tc tv1 (some tv) tcell st =
        (some (Int.ofNat boundary - 1), out))
    (hevent : EventOut G ctx tcLevel stem fs out outBest eventTrail
      (Int.ofNat boundary - 1))
    (hpreserved : TrailExt level trail eventTrail)
    (hfixed : out.fixedpts = st.fixedpts)
    (hcoset : out.cosetindex = st.cosetindex)
    (hpositive : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hsaved : out.noncheaplevel = boundary)
    (hexact : outBest = some (incMax best bound))
    (hsource : out.needshortprune = true →
      ShortSource G ctx out eventTrail (Int.ofNat boundary - 1)) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest trail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  have hvalue : Int.ofNat boundary - 1 < Int.ofNat level := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hinstalled : out.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc (hevent.read.trans hexact)
  rw [hstate]
  refine ⟨?_, LoopExit.cheap boundary rfl hpositive hbelow hsaved hexact,
    ?_⟩
  · exact {
    loop := {
      outcome := {
        receipt := .pruned (Int.ofNat boundary - 1) rfl hvalue
          (LoopSound.ofExact hexact) hinstalled hevent.read hexact
        event := by simpa only [loopReturn] using hevent
        preserved := hpreserved }
      fixed := hfixed }
    coset := hcoset }
  · intro hshort
    exact ⟨Int.ofNat boundary - 1, rfl, hsource hshort⟩

/-- A generator unwind addressed strictly above this loop crosses the
temporary fixed-vertex cleanup and returns immediately. -/
theorem unwind {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv tv1 target offset : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail}
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      (numcells + 1)) bound)
    (hreturn : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }).1 = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv }).2 outBest)
    (hloc : payload.Located (trail.push level
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩))
    (hcontrol : target = (otherNode ctx inf tcLevel runFuel (level + 1)
        (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv }).2.gcaFirst ∨
      target = (otherNode ctx inf tcLevel runFuel (level + 1)
        (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv }).2.gcaCanon)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv }).2
      (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv }).1)
    (hfresh : st.fixedpts.mem tv = false) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).2
      best outBest trail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
  let node := otherNode ctx inf tcLevel runFuel (level + 1)
    (numcells + 1)
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv }
  let cleaned : SearchSt n :=
    { node.2 with fixedpts := node.2.fixedpts.erase tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change node.2.fixedpts.erase tv = st.fixedpts
    rw [hchild.node.fixed]
    exact erase_insert_of_miss hfresh
  have hstate : otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell st =
      (some node.1, cleaned) := by
    unfold otherChildLoop
    simp only [Id.run_pure, apply_ite Id.run]
    have hlt : node.1 < Int.ofNat level := by
      rw [hreturn]
      exact Int.ofNat_lt.mpr hbelow
    rw [ite_eq_left hlt]
  have hlocParent : payload.Located trail :=
    hloc.retrail (FrameTrail.push_of_ne trail _ (by omega))
  obtain ⟨payload', hloc'⟩ :
      ∃ payload' : Unwind ctx tcLevel target cleaned outBest,
        payload'.Located trail := by
    simpa only [cleaned, node] using
      hlocParent.setFixed (node.2.fixedpts.erase tv)
  have hreceipt := otherLoop_childReceipt ctx inf tcLevel specFuel runFuel
    loopFuel level numcells tc tv1 tv codes rsLab rsPtn len tcell cursor
    bound st best outBest target trail hsound hkey hreturn hbelow payload
    hlocParent
  have hevent : EventOut G ctx tcLevel stem fs cleaned outBest eventTrail
      node.1 := by
    exact (hchild.node.event.ancestor hstem hshorter).setFixed _
  have hproof : OtherLoopProof G ctx tcLevel specFuel runFuel
      (loopFuel + 1) level stem codes fs rsLab rsPtn tc len numcells tcell
      cursor bound st (otherChildLoop ctx inf tcLevel runFuel
        (loopFuel + 1) level numcells tc tv1 (some tv) tcell st).2
      best outBest trail eventTrail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell st).1 := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨hreceipt, ?_, hchild.node.preserved.ofPush⟩
        rw [hstate]
        simpa only [loopReturn] using hevent
      · rw [hstate]
        exact hfixed
    · rw [hstate]
      exact hchild.coset
  refine ⟨hproof, ?_, ?_⟩
  · rw [hstate, hreturn]
    exact LoopExit.unwind target rfl hbelow (LoopSound.ofNode hsound hkey)
      payload' hloc' (by simpa only [cleaned, node] using hcontrol)
  · intro hshort
    rw [hstate] at hshort ⊢
    refine ⟨node.1, rfl, ?_⟩
    apply ShortSource.setFixed
    apply hchild.node.short
    simpa only [cleaned] using hshort

/-- Zero cursor fuel is retained as exhaustion, never mistaken for a
completed sibling sweep. -/
theorem zero {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv1 : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < n) :
    OtherLoopRun G ctx tcLevel specFuel runFuel 0 level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).1 := by
  refine ⟨OtherLoopProof.zero hpath hstem hpast hnp hinv hlive hcursor,
    ?_, ?_⟩
  · apply LoopExit.exhausted (finalCursor := cursor)
    · unfold otherChildLoop
      rfl
    · omega
    · exact hcursor
  · intro hshort
    unfold otherChildLoop at hshort
    simp only at hshort
    rw [hinv.shortClear] at hshort
    cases hshort

/-- A positive-fuel loop with no next vertex has genuinely covered the
fixed original target cell and returns its exact maximum. -/
theorem done {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tail : Nat} {tcell : VSet n}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : tcell.nextElem cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).1 := by
  have hproof := OtherLoopProof.done (inf := inf) (runFuel := runFuel)
    (loopFuel := loopFuel) (tv1 := tv1) (bound := bound)
    hpath hstem hpast hnext hnp hinv hlive
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st = some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  have hempty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o := by
    intro o ho
    exact no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2
  have hexact : best = some (incMax best bound) := by
    rw [hlen] at hinv hempty
    exact hinv.cover.exact_of_read hbound hempty
      (.refl ctx bound best) hinstalled hread
  refine ⟨hproof, LoopExit.done ?_ hexact, ?_⟩
  · unfold otherChildLoop
    rfl
  · intro hshort
    unfold otherChildLoop at hshort
    simp only at hshort
    rw [hinv.shortClear] at hshort
    cases hshort

end OtherLoopRun

/-- The first-path loop's input index is bookkeeping only: it can change
the returned index, but neither the return level nor the returned state. -/
theorem firstChildLoop_index (ctx : Ctx n) (inf tcLevel fuel : Nat) :
    ∀ (cfuel level numcells tc tv1 : Nat) (tv? : Option Nat) (tcell : VSet n)
      (index index' : Nat) (st : SearchSt n),
      (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1 tv?
          tcell index st).1 =
          (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1
            tv? tcell index' st).1 ∧
        (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1 tv?
          tcell index st).2.2 =
          (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1
            tv? tcell index' st).2.2 := by
  intro cfuel
  induction cfuel with
  | zero =>
      intro level numcells tc tv1 tv? tcell index index' st
      unfold firstChildLoop
      exact ⟨rfl, rfl⟩
  | succ cfuel ih =>
      intro level numcells tc tv1 tv? tcell index index' st
      cases tv? with
      | none =>
          unfold firstChildLoop
          exact ⟨rfl, rfl⟩
      | some tv =>
          unfold firstChildLoop
          simp only [Id.run_pure, apply_ite Id.run]
          repeat' split
          all_goals first
            | exact ⟨rfl, rfl⟩
            | apply ih

namespace FirstLoopRun

theorem reindexSet {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell tcell' : VSet n} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.proof.reindexSet, h.exit.reindexSet, h.short⟩

theorem step {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out best
      outBest receiptTrail eventTrail r) :
    FirstLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.proof.step ha, h.exit.step ha, h.short⟩

theorem prepend {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st recSt out : SearchSt n} {best mid outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (h : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.proof.prepend hfixed hpre, h.exit.prepend hpre, h.short⟩

/-- Continue a first-path sweep after an ordinary non-guiding child. -/
theorem nextOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st child recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = false)
    (hrecover : recSt = recover n inf level
      { child with fixedpts := child.fixedpts.erase tv })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (hloop : firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (tcell.nextElem (some tv)) tcell index recSt =
        (r, outIndex, out))
    (hrec : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells tcell (some tv) bound recSt out mid
        outBest receiptTrail eventTrail r) :
    FirstLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest receiptTrail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hret : ∀ i, (firstChildLoop ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 (tcell.nextElem (some tv)) tcell i recSt).1 = r := by
    intro i
    exact (firstChildLoop_index ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 _ tcell i index recSt).1.trans
        (congrArg Prod.fst hloop)
  have hout : ∀ i, (firstChildLoop ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 (tcell.nextElem (some tv)) tcell i recSt).2.2 = out := by
    intro i
    exact (firstChildLoop_index ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 _ tcell i index recSt).2.trans
        (congrArg (fun x => x.2.2) hloop)
  subst recSt
  simp only [hshort] at hret hout hrec hfixed
  unfold firstChildLoop
  simp only [hrep, ite_true, hother, Bool.false_eq_true, ite_false,
    Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, Bool.false_eq_true, ite_false]
  split <;> rw [hret, hout] <;>
    exact (hrec.prepend hfixed hpre).step (nextElem_after hnext)

/-- Continue a first-path sweep after its guiding child. -/
theorem nextGuide {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st child recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int} {outIndex : Nat}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = false)
    (hrecover : recSt = recover n inf level
      { { { child with fixedpts := child.fixedpts.erase tv } with
          gcaFirst := level } with stabvertex := tv1 })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (hloop : firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (tcell.nextElem (some tv)) tcell index recSt =
        (r, outIndex, out))
    (hrec : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells tcell (some tv) bound recSt out mid
        outBest receiptTrail eventTrail r) :
    FirstLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest receiptTrail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hret : ∀ i, (firstChildLoop ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 (tcell.nextElem (some tv)) tcell i recSt).1 = r := by
    intro i
    exact (firstChildLoop_index ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 _ tcell i index recSt).1.trans
        (congrArg Prod.fst hloop)
  have hout : ∀ i, (firstChildLoop ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 (tcell.nextElem (some tv)) tcell i recSt).2.2 = out := by
    intro i
    exact (firstChildLoop_index ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 _ tcell i index recSt).2.trans
        (congrArg (fun x => x.2.2) hloop)
  subst recSt
  simp only [hshort] at hret hout hrec hfixed
  unfold firstChildLoop
  simp only [hrep, ite_true, hfirst, Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, Bool.false_eq_true, ite_false]
  split <;> rw [hret, hout] <;>
    exact (hrec.prepend hfixed hpre).step (nextElem_after hnext)

/-- Continue a non-guiding first-path sweep after consuming a short-prune
request from its child. -/
theorem nextOtherShort {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv index : Nat} {tcell filtered : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st child recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int} {outIndex : Nat}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = true)
    (hfiltered : filtered = shortprune tcell
      { { child with fixedpts := child.fixedpts.erase tv } with
        needshortprune := false })
    (hrecover : recSt = recover n inf level
      { { child with fixedpts := child.fixedpts.erase tv } with
        needshortprune := false })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (hloop : firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (filtered.nextElem (some tv)) filtered index recSt =
        (r, outIndex, out))
    (hrec : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells filtered (some tv) bound recSt out mid
        outBest receiptTrail eventTrail r) :
    FirstLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest receiptTrail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hret : ∀ i, (firstChildLoop ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 (filtered.nextElem (some tv)) filtered i recSt).1 = r := by
    intro i
    exact (firstChildLoop_index ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 _ filtered i index recSt).1.trans
        (congrArg Prod.fst hloop)
  have hout : ∀ i, (firstChildLoop ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 (filtered.nextElem (some tv)) filtered i recSt).2.2 =
      out := by
    intro i
    exact (firstChildLoop_index ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 _ filtered i index recSt).2.trans
        (congrArg (fun x => x.2.2) hloop)
  subst filtered
  subst recSt
  unfold firstChildLoop
  simp only [hrep, ite_true, hother, Bool.false_eq_true, ite_false,
    Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, ite_true]
  split <;> rw [hret, hout] <;>
    exact ((hrec.prepend hfixed hpre).reindexSet).step
      (nextElem_after hnext)

/-- Continue the guiding first-path sweep after consuming its child's
short-prune request. -/
theorem nextGuideShort {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv index : Nat} {tcell filtered : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st child recSt out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int} {outIndex : Nat}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true)
    (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = true)
    (hfiltered : filtered = shortprune tcell
      { { { { child with fixedpts := child.fixedpts.erase tv } with
          gcaFirst := level } with stabvertex := tv1 } with
        needshortprune := false })
    (hrecover : recSt = recover n inf level
      { { { { child with fixedpts := child.fixedpts.erase tv } with
          gcaFirst := level } with stabvertex := tv1 } with
        needshortprune := false })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (hloop : firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (filtered.nextElem (some tv)) filtered index recSt =
        (r, outIndex, out))
    (hrec : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells filtered (some tv) bound recSt out mid
        outBest receiptTrail eventTrail r) :
    FirstLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest receiptTrail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hret : ∀ i, (firstChildLoop ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 (filtered.nextElem (some tv)) filtered i recSt).1 = r := by
    intro i
    exact (firstChildLoop_index ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 _ filtered i index recSt).1.trans
        (congrArg Prod.fst hloop)
  have hout : ∀ i, (firstChildLoop ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 (filtered.nextElem (some tv)) filtered i recSt).2.2 =
      out := by
    intro i
    exact (firstChildLoop_index ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 _ filtered i index recSt).2.trans
        (congrArg (fun x => x.2.2) hloop)
  subst filtered
  subst recSt
  unfold firstChildLoop
  simp only [hrep, ite_true, hfirst, Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  simp only [hshort, ite_true]
  split <;> rw [hret, hout] <;>
    exact ((hrec.prepend hfixed hpre).reindexSet).step
      (nextElem_after hnext)

/-- Zero cursor fuel is retained as exhaustion for the first-path sweep. -/
theorem zero {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv1 index : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < n)
    (hfirst : FirstTrail ctx (level + 1) st trail)
    (hcanon : CanonTrail ctx level st trail)
    (hguide : level ≤ st.gcaFirst) (horder : st.gcaFirst ≤ st.gcaCanon) :
    FirstLoopRun G ctx tcLevel specFuel runFuel 0 level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).1 := by
  refine ⟨FirstLoopProof.zero hpath hstem hpast hnp hinv hlive hcursor
    hfirst hcanon hguide horder, ?_, ?_⟩
  · apply LoopExit.exhausted (finalCursor := cursor)
    · unfold firstChildLoop
      rfl
    · omega
    · exact hcursor
  · intro hshort
    unfold firstChildLoop at hshort
    simp only at hshort
    rw [hinv.shortClear] at hshort
    cases hshort

/-- An absent next vertex completes a positive-fuel first-path sweep. -/
theorem done {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 index tail : Nat} {tcell : VSet n}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : tcell.nextElem cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hfirst : FirstTrail ctx (level + 1) st trail)
    (hcanon : CanonTrail ctx level st trail)
    (hguide : level ≤ st.gcaFirst) (horder : st.gcaFirst ≤ st.gcaCanon) :
    FirstLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).1 := by
  have hproof := FirstLoopProof.done (inf := inf) (runFuel := runFuel)
    (loopFuel := loopFuel) (tv1 := tv1) (index := index) (bound := bound)
    hpath hstem hpast hnext hnp hbound hlen hinv hlive hfirst hcanon
      hguide horder
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st = some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  have hempty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o := by
    intro o ho
    exact no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2
  have hexact : best = some (incMax best bound) := by
    rw [hlen] at hinv hempty
    exact hinv.cover.exact_of_read hbound hempty
      (.refl ctx bound best) hinstalled hread
  refine ⟨hproof, LoopExit.done ?_ hexact, ?_⟩
  · unfold firstChildLoop
    rfl
  · intro hshort
    unfold firstChildLoop at hshort
    simp only at hshort
    rw [hinv.shortClear] at hshort
    cases hshort

end FirstLoopRun

end Hex.GraphIso.Nauty

/-!
Assembly of the corrected search induction.

The first descent needs more result-side history than an ordinary node.
`FirstRun` keeps the established first-path package while pairing it with
the explicit exit classification used to justify every abandoned sweep.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A first-path result with both its reference histories and the corrected
reason for its return. -/
structure FirstRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (codes fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  proof : FirstProof G ctx tcLevel specFuel runFuel level codes fs st out
    numcells outBest receiptTrail eventTrail r
  exit : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
    none outBest receiptTrail r
  short : out.needshortprune = true →
    ShortSource G ctx out eventTrail r

namespace FirstRun

/-- The final first-path counter adjustment preserves the complete
corrected first-node result. -/
theorem firstFinish {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {codes fs : List Nat} {st out : SearchSt n} {outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : FirstRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells outBest receiptTrail eventTrail r) :
    FirstRun G ctx tcLevel specFuel runFuel level codes fs st
      (Nauty.firstFinish level size index out) numcells outBest receiptTrail
      eventTrail r :=
  ⟨h.proof.firstFinish hfuel, h.exit.firstFinish hfuel, fun hshort => by
    apply ShortSource.firstFinish
    apply h.short
    rw [Nauty.firstFinish] at hshort
    split at hshort <;> exact hshort⟩

end FirstRun

namespace FirstLoopRun

/-- An early integer-valued first-path sweep becomes its enclosing node. -/
theorem toNodeSome {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out none outBest receiptTrail eventTrail (some r)) :
    FirstRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells outBest receiptTrail eventTrail r := by
  refine ⟨h.proof.toNodeSome hbound hfixed,
    h.exit.toNodeSome hbound hprefix, ?_⟩
  intro hshort
  obtain ⟨value, hreturned, hsource⟩ := h.short hshort
  cases Option.some.inj hreturned
  exact hsource

/-- A sufficiently fuelled `none` sweep is genuine completion and becomes
the enclosing first-path node's ordinary return. -/
theorem toNodeNone {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel (specFuel + 1) level nodeCodes
      nodeSt nodeNumcells)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCodes nodeSt
        nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCodes rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCodes rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hfuel : n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out none outBest receiptTrail eventTrail none) :
    FirstRun G ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCodes fs
      nodeSt out nodeNumcells outBest receiptTrail eventTrail
      (Int.ofNat level - 1) := by
  refine ⟨h.proof.toNodeNone hbound hchildren hlen hfuel hfixed,
    h.exit.toNodeNone hbound hfuel, ?_⟩
  intro hshort
  obtain ⟨value, hreturned, _⟩ := h.short hshort
  cases hreturned

end FirstLoopRun

namespace FirstInv

/-- The first discrete leaf is an ordinary exact return in the corrected
classification. -/
theorem terminalRun {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : level = codes.length + 1)
    (h : FirstInv G ctx level codes numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := codes ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    FirstRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes full st
      out.2 numcells (some (pathLeafKey ctx full rs.lab)) trail trail
      out.1 := by
  dsimp only
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [rs.longcode]
  let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
  have hproof : FirstProof G ctx tcLevel (specFuel + 1) (fuel + 1)
      level codes full st out.2 numcells
      (some (pathLeafKey ctx full rs.lab)) trail trail out.1 := by
    simpa only [rs, full, out] using
      h.terminalFirstProof (inf := inf) (tcLevel := tcLevel)
        (specFuel := specFuel) (fuel := fuel) hn0 hlevel hnum
  have hstate := firstPath_discrete_state ctx inf tcLevel fuel level
    numcells st hnum
  have hdisc : discreteAt rs.ptn level n = true := by
    rw [← refine_discrete_iff hn0 h.searchOk (by omega)]
    exact hnum
  have hnode : nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells = pathLeafKey ctx full rs.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey]
  refine ⟨hproof, ?_, ?_⟩
  apply NodeExit.done
  · exact congrArg Prod.fst hstate
  · rw [hnode, incMax]
  · intro hshort
    rw [hstate] at hshort
    rw [firstterminal_short, h.shortClear] at hshort
    cases hshort

end FirstInv

/-- The corrected first-path root result proves equality between the
unpruned specification key and the key installed by the transcription. -/
theorem dominated_of_firstRun {G : Colored n k} (hn0 : n ≠ 0)
    {fs : List Nat} {best : Option (Key n)}
    (hroot : FirstRun G { g := rowsOf G } 100 n (n + 2) 1 [] fs
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2)
      (initialPartition G).2.length best FrameTrail.empty FrameTrail.empty
      (firstPathNode { g := rowsOf G } (n + 2) 100 (n + 2) 1
        (initialPartition G).2.length
        (rootSt n (initialPartition G).1 (initialPartition G).2)).1) :
    canonSpecKey G = tracedKey G := by
  have hread := hroot.proof.node.outcome.event.read
  cases hroot.exit with
  | done returned exact =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | unwind target returned below sound payload located control =>
      cases payload with
      | first anchor carrier =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
      | canon anchor carrier =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
      | orbit payload =>
          exact ((Nat.not_lt_of_ge payload.positive) below).elim
  | frozen below exact freeze =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | cheap boundary returned positive atOrAbove saved exact =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | exhausted returned state incumbent emptyFuel => omega

end Hex.GraphIso.Nauty

/-!
Facts carried alongside the corrected search induction that no existing
package records: leaf events keep the orbit array sound, small-cell
subtree facts survive a within-cell relabelling, guide relations compose
across a refinement, and a frozen comparison bounds every key below the
current path.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Frame equations -/

theorem pushAuto_firstlab (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).firstlab = st.firstlab := by
  rw [pushAuto]
  split <;> rfl

theorem pushAuto_orbits' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).orbits = st.orbits := by
  rw [pushAuto]
  split <;> rfl

theorem pushAuto_genTrace' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

theorem recover_firstlab (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).firstlab = st.firstlab :=
  (recover_frames n inf level st).2.2.2.2.1

theorem recover_orbits (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).orbits = st.orbits :=
  (recover_frames n inf level st).2.2.2.2.2.2.2.2.1

theorem recover_genTrace (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).genTrace = st.genTrace :=
  (recover_store n inf level st).1

theorem recover_noncheaplevel (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).noncheaplevel =
      if level < st.noncheaplevel then level + 1 else st.noncheaplevel := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.noncheaplevel, ite_self]

theorem otherNodePrep_firstlab' (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).firstlab = st.firstlab :=
  (otherNodePrep_frames level code st).2.2.2.2.1

theorem otherNodePrep_orbits' (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).orbits = st.orbits :=
  (otherNodePrep_frames level code st).2.2.2.2.2.2.2.2.2.2.1

theorem otherNodePrep_genTrace' (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).genTrace = st.genTrace :=
  (otherNodePrep_store level code st).1

theorem processnode_firstlab' (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.firstlab = st.firstlab :=
  (processnode_frames ctx level numcells st).2.2.2.2.1

theorem processnode_noncheaplevel' (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.noncheaplevel = st.noncheaplevel :=
  (processnode_frames ctx level numcells st).2.2.2.2.2.2.2.1

/-! # Leaf events keep the orbit array sound -/

/-- The generator store paired with the orbit array, kept opaque while
the leaf event is unfolded. -/
@[expose] def genOrb (st : SearchSt n) : Array (Array Nat) × Array Nat :=
  (st.genTrace, st.orbits)

private theorem pushAuto_genOrb (st : SearchSt n) (pair : VSet n × VSet n) :
    genOrb (pushAuto st pair) = genOrb st := by
  rw [pushAuto]
  split <;> rfl

private theorem id_run_eq {α : Type} (x : Id α) : x.run = x := rfl

private theorem forIn_range_toList {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

private theorem forIn_scatter_eq (lab₁ lab₂ : Array Nat) :
    ∀ (l : List Nat) (base : Array Nat),
      (forIn l base (fun i r =>
        pure (ForInStep.yield (r.set! lab₁[i]! lab₂[i]!))) :
          Id (Array Nat)) =
      l.foldl (fun r i => r.set! lab₁[i]! lab₂[i]!) base
  | [], _ => rfl
  | i :: l, base => by
    rw [List.forIn_cons]
    exact forIn_scatter_eq lab₁ lab₂ l _

/-- `processnode` either leaves both the generator store and the orbit
array alone, or appends one generator and joins the orbits by it. -/
theorem processnode_genOrb (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    genOrb (processnode ctx level numcells st).2 = genOrb st ∨
    ∃ γ, genOrb (processnode ctx level numcells st).2 =
      (st.genTrace.push γ, (orbjoin st.orbits γ n).1) := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => genOrb x.2),
    pushAuto_genOrb]
  simp only [id_run_eq, forIn_range_toList, forIn_scatter_eq]
  simp only [genOrb, pushAuto_genTrace', pushAuto_orbits', ite_self]
  rcases Decidable.em (st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    with h1 | h1
  · rw [ite_eq_left h1]
    left
    rfl
  rw [ite_eq_right h1]
  rcases Decidable.em ((numcells == n) = true) with h2 | h2
  · rw [ite_eq_left h2]
    rcases Decidable.em (((st.eqlevFirst == level) &&
        (st.firstcode[level + 1]! == codeSentinel)) = true) with h3 | h3
    · rw [ite_eq_left h3]
      rcases Decidable.em (isautom ctx ((List.range n).foldl
            (fun r i => r.set! st.firstlab[i]! st.lab[i]!)
            (Array.replicate n 0)) = true) with h4 | h4
      · rw [ite_eq_left h4, ite_eq_right (by decide)]
        right
        exact ⟨_, rfl⟩
      · rw [ite_eq_right h4, ite_eq_left (by decide)]
        rcases Decidable.em ((st.compCanon == 0) = true) with h5 | h5
        · rw [ite_eq_left h5]
          rcases Decidable.em (level < st.canonlevel) with h6 | h6
          · rw [ite_eq_left h6, ite_eq_right (by decide)]
            left
            rfl
          · rw [ite_eq_right h6]
            rcases Decidable.em (((testcanlab ctx (updatecan ctx
                st.canong st.canonlab st.samerows) st.lab).1 == 0) =
                true) with h7 | h7
            · rw [ite_eq_left h7]
              right
              exact ⟨_, rfl⟩
            · rw [ite_eq_right h7]
              left
              rfl
        · rw [ite_eq_right h5, ite_eq_right h5]
          left
          rfl
    · rw [ite_eq_right h3, ite_eq_left (by decide)]
      rcases Decidable.em ((st.compCanon == 0) = true) with h5 | h5
      · rw [ite_eq_left h5]
        rcases Decidable.em (level < st.canonlevel) with h6 | h6
        · rw [ite_eq_left h6, ite_eq_right (by decide)]
          left
          rfl
        · rw [ite_eq_right h6]
          rcases Decidable.em (((testcanlab ctx (updatecan ctx
              st.canong st.canonlab st.samerows) st.lab).1 == 0) =
              true) with h7 | h7
          · rw [ite_eq_left h7]
            right
            exact ⟨_, rfl⟩
          · rw [ite_eq_right h7]
            left
            rfl
      · rw [ite_eq_right h5, ite_eq_right h5]
        left
        rfl
  · rw [ite_eq_right h2]
    left
    rfl

/-- Every checked generator list keeps the orbit relation symmetric. -/
theorem orbConn_symm_of_check {ctx : Ctx n} {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ = true) :
    ∀ a b, OrbConn gens n a b → OrbConn gens n b a :=
  orbConn_symm (fun γ hγ v hv' => checkAutom_bound (hv γ hγ) v hv')
    (fun γ hγ => checkAutom_inj (hv γ hγ))

/-- The orbit array stays sound across a leaf event whose appended
generator, if any, is checked. -/
theorem processnode_orbSound {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcheck : ∀ γ ∈ (processnode ctx level numcells st).2.genTrace,
      checkAutom ctx.g γ = true) :
    OrbSound
      (OrbConn (processnode ctx level numcells st).2.genTrace.toList n)
      (processnode ctx level numcells st).2.orbits n := by
  rcases processnode_genOrb ctx level numcells st with hsame | ⟨γ, hpush⟩
  · have hgen : (processnode ctx level numcells st).2.genTrace =
        st.genTrace := congrArg Prod.fst hsame
    have horb : (processnode ctx level numcells st).2.orbits =
        st.orbits := congrArg Prod.snd hsame
    rw [hgen, horb]
    exact hsound
  · have hgen : (processnode ctx level numcells st).2.genTrace =
        st.genTrace.push γ := congrArg Prod.fst hpush
    have horb : (processnode ctx level numcells st).2.orbits =
        (orbjoin st.orbits γ n).1 := congrArg Prod.snd hpush
    rw [hgen, horb]
    rw [hgen] at hcheck
    have hsub : ∀ δ ∈ st.genTrace.toList,
        δ ∈ (st.genTrace.push γ).toList := by
      intro δ hδ
      rw [Array.mem_toList_iff] at hδ ⊢
      exact Array.mem_push.mpr (Or.inl hδ)
    have hcheck' : ∀ δ ∈ (st.genTrace.push γ).toList,
        checkAutom ctx.g δ = true := by
      intro δ hδ
      exact hcheck δ (Array.mem_toList_iff.mp hδ)
    have hγ : γ ∈ (st.genTrace.push γ).toList := by
      rw [Array.mem_toList_iff]
      exact Array.mem_push.mpr (Or.inr rfl)
    apply orbjoin_orbSound (orbConn_symm_of_check hcheck')
      (orbConn_trans _)
      (orbSound_mono (orbConn_mono hsub) hsound)
    intro i hi
    refine ⟨checkAutom_bound (hcheck' γ hγ) i hi, ?_⟩
    unfold OrbConn
    exact ⟨hi, checkAutom_bound (hcheck' γ hγ) i hi, wordConn_step hγ i⟩

/-! # Small-cell subtree facts across a within-cell relabelling -/

/-- The small-cell subtree facts depend on the labelling only through
its cell contents. -/
theorem SubtreeOk.ofCellsPerm {ctx : Ctx n} {level : Nat} {r : RefineSt n}
    {lab' : Array Nat} (h : SubtreeOk ctx level r)
    (hperm : cellsPerm r.ptn level r.lab lab')
    (hsz : lab'.size = n) (hok : LabOk lab' n)
    (hinj : LabInj lab' n) :
    SubtreeOk ctx level { r with lab := lab' } := by
  refine ⟨⟨⟨hsz, hok, h.it.ok.ptnSize, h.it.ok.ptnEnd⟩,
    hinj, h.it.vals, h.it.lvl⟩, ?_, h.acc, h.shape⟩
  exact h.eqt.ofCellsPerm hperm h.it.ok.ptnSize h.it.ok.ptnEnd

/-- The subtree facts ignore the refinement bookkeeping fields. -/
theorem SubtreeOk.ofFrames {ctx : Ctx n} {level : Nat} {r r' : RefineSt n}
    (h : SubtreeOk ctx level r) (hlab : r'.lab = r.lab)
    (hptn : r'.ptn = r.ptn)
    (hcells : r'.numcells = r.numcells) :
    SubtreeOk ctx level r' := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, h.it.lvl⟩, ?_, ?_, ?_⟩
  · rw [hlab]; exact h.it.ok.labSize
  · rw [hlab]; exact h.it.ok.labOk
  · rw [hptn]; exact h.it.ok.ptnSize
  · rw [hptn]; exact h.it.ok.ptnEnd
  · rw [hlab]; exact h.it.inj
  · rw [hptn]; exact h.it.vals
  · rw [hlab, hptn]; exact h.eqt
  · rw [hptn, hcells]; exact h.acc
  · rw [hptn]; exact h.shape

/-! # Guide relations across a refinement -/

namespace GuideRel

/-- Compose a guide relation whose second leg is stated over the refined
frame of the first leg's endpoint.  Refinement only closes more cell
boundaries, so a within-cell permutation of the refined frame is one of
the coarser frame. -/
theorem transRefine {level : Nat} {a b c : SearchSt n}
    (hab : GuideRel level a b) (hbc : GuideRel level b c)
    (hsz : a.ptn.size = b.ptn.size) (hlb : b.lab.size = b.ptn.size)
    (hlc : c.canonlab.size = b.ptn.size)
    (hendB : b.ptn[b.ptn.size - 1]! ≤ level)
    (hendA : a.ptn[a.ptn.size - 1]! ≤ level)
    (hgrow : ∀ q : Nat, a.ptn[q]! ≤ level → b.ptn[q]! ≤ level)
    (hperm : cellsPerm a.ptn level a.lab b.lab) :
    GuideRel level a c := by
  constructor
  · exact hbc.first.trans hab.first
  · exact hbc.order
  · rcases hbc.canon with hold | hnew
    · rw [hold.1, hold.2]
      exact hab.canon
    · right
      refine ⟨hnew.1, ?_⟩
      have hcoarse : cellsPerm a.ptn level b.lab c.canonlab :=
        cellsPerm_coarsen hsz hlb hlc hnew.2 hendB hendA hgrow
      exact cellsPerm_trans hperm hcoarse

end GuideRel

/-! # Result-side facts -/

/-- Every packaged event leaves the comparison sign nonpositive. -/
theorem EventOut.nonpositive {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    out.compCanon ≤ 0 := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ =>
      rcases event.machines with hplain | hreset
      · exact hplain.1
      · exact Int.le_of_lt hreset.1

/-- A negative comparison sign is exactly the frozen downward machine. -/
theorem CodeCmpInv.neg_eq {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon compCanon : Int}
    (h : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon compCanon)
    (hneg : compCanon < 0) : compCanon = -1 := by
  rcases h.tri with hzero | ⟨_, _, _, _, _, _, hdown | hup⟩
  · omega
  · exact hdown.1
  · omega

/-- With the machine frozen downward, every key below the current path is
dominated by the incumbent. -/
theorem CodeCmpInv.frozenBound {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon compCanon : Int}
    {canonlab : Array Nat}
    (h : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon compCanon)
    (hneg : compCanon < 0) (K : Key n) :
    keyLe (prefixKey cs K) (incKey ctx bs canonlab) := by
  have hcc := h.neg_eq hneg
  subst hcc
  exact frozen_keyLe h K

/-- A frozen node's exact maximum is the unchanged incumbent: every child
key is dominated. -/
theorem incMax_of_frozen {ctx : Ctx n} {bs : List Nat} {canonlab : Array Nat}
    {K : Key n} (hle : keyLe K (incKey ctx bs canonlab)) :
    incMax (some (incKey ctx bs canonlab)) K = incKey ctx bs canonlab := by
  rw [incMax]
  exact keyMax_eq_left hle

/-- Every off-path run only improves the incumbent. -/
theorem OtherRun.grows {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : OtherRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r)
    (hfuel : runFuel ≠ 0) : IncGrows best outBest := by
  cases h.node.exit with
  | done returned exact => rw [exact]; exact IncGrows.incMax best _
  | unwind target returned below sound payload located control =>
      exact sound.grows
  | frozen below exact freeze => rw [exact]; exact IncGrows.incMax best _
  | cheap boundary returned positive atOrAbove saved exact =>
      rw [exact]; exact IncGrows.incMax best _
  | exhausted returned state incumbent emptyFuel => exact (hfuel emptyFuel).elim

end Hex.GraphIso.Nauty

/-!
The negative-comparison arms of an internal off-path node.

When the refined code is already below the incumbent's, `othernode`
either prunes at once (the first-path agreement is broken) or descends
through the first path's own target cell looking for automorphisms.  The
subtree is dominated in both cases, so its exact maximum is the unchanged
incumbent; what remains is the executable state bookkeeping.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Frame equations of the frozen-downward arm -/

private theorem pushAuto_genTrace'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_orbits'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).orbits = st.orbits := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_gcaCanon'' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).gcaCanon = st.gcaCanon := by
  rw [pushAuto]
  split <;> rfl

/-- The frozen-downward arm records no generator. -/
theorem processnode_fast_genTrace {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.genTrace),
    pushAuto_genTrace'', ite_self]
  rw [ite_eq_left hg]

/-- The frozen-downward arm leaves the orbit array alone. -/
theorem processnode_fast_orbits {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.orbits = st.orbits := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.orbits),
    pushAuto_orbits'', ite_self]
  rw [ite_eq_left hg]

/-- The frozen-downward arm leaves the canonical guide alone. -/
theorem processnode_fast_gcaCanon {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.gcaCanon = st.gcaCanon := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.gcaCanon),
    pushAuto_gcaCanon'', ite_self]
  rw [ite_eq_left hg, ite_eq_right (by decide)]

/-! # State equations of the internal negative branches -/

/-- The prepared state of an off-path node: refinement followed by the
comparison step, before any target selection. -/
theorem otherLeafSt_eq (ctx : Ctx n) (level numcells : Nat) (st : SearchSt n) :
    otherLeafSt ctx level numcells st =
      otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 } := rfl

/-- With the first-path agreement broken under a negative comparison,
an internal node prunes at once and returns the leaf event's result. -/
theorem otherNode_gate_state (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hgate : (otherLeafSt ctx level numcells st).eqlevFirst ≠ level ∧
      (otherLeafSt ctx level numcells st).compCanon < 0)
    (hearly : (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level
        (refine ctx level st.lab st.ptn st.active numcells).numcells
        (otherLeafSt ctx level numcells st) := by
  dsimp only [otherLeafSt] at hgate hearly ⊢
  rw [otherNode]
  simp only [hnum, true_and]
  rw [ite_eq_right (by
    intro h
    rcases h with h | h
    · exact hgate.1 (beq_iff_eq.mp h)
    · exact absurd hgate.2 (Int.not_lt.mpr h))]
  rw [ite_eq_left hearly]
  rfl

/-- A negative comparison whose hinted target disagrees with the first
path demotes the agreement depth and prunes at once. -/
theorem otherNode_hintFail_state (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmis : Int.ofNat (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 ≠
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hearly : (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal +
          (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
            (otherLeafSt ctx level numcells st).ptn level tcLevel
            (otherLeafSt ctx level numcells st).firsttc[level]!).2.2
        eqlevFirst := level - 1 }).1 < Int.ofNat level) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level
        (refine ctx level st.lab st.ptn st.active numcells).numcells
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal +
            (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
              (otherLeafSt ctx level numcells st).ptn level tcLevel
              (otherLeafSt ctx level numcells st).firsttc[level]!).2.2
          eqlevFirst := level - 1 } := by
  dsimp only [otherLeafSt] at heq hneg hmis hearly ⊢
  rw [otherNode]
  simp only [hnum, true_and, heq, true_or, ite_true, hneg, ne_eq,
    not_false_eq_true, ite_true, hmis]
  rw [ite_eq_left hearly]
  rfl

/-- A negative comparison whose hinted target agrees with the first path
enters its child loop over that target cell with the comparison still
frozen. -/
theorem otherNode_hint_state (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmatch : Int.ofNat (maketargetcell ctx
        (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 =
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hshort : SearchSt.needshortprune (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal +
          (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
            (otherLeafSt ctx level numcells st).ptn level tcLevel
            (otherLeafSt ctx level numcells st).firsttc[level]!).2.2 }).2 =
      false) :
    let pre := otherLeafSt ctx level numcells st
    let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel
      pre.firsttc[level]!
    let base := { pre with tctotal := pre.tctotal + mt.2.2 }
    let pr := processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells base
    let start := if ¬ cheapautom pr.2.ptn level n then
      { pr.2 with noncheaplevel := level + 1 } else pr.2
    let L := otherChildLoop ctx inf tcLevel fuel (n + 1) level
      (refine ctx level st.lab st.ptn st.active numcells).numcells mt.1
      ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 start
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      if pr.1 < Int.ofNat level then pr
      else match L.1 with
        | some rtn => (rtn, L.2)
        | none => (Int.ofNat level - 1, L.2) := by
  dsimp only
  dsimp only [otherLeafSt] at heq hneg hmatch hshort ⊢
  have hnot : ¬ (Int.ofNat (maketargetcell ctx
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).lab
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).ptn level tcLevel
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).firsttc[level]!).1 ≠
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).firsttc[level]!) :=
    fun h => h hmatch
  simp only [Int.ofNat_eq_natCast] at hnot
  rw [otherNode]
  simp only [hnum, true_and, heq, true_or, ite_true, hneg,
    Int.ofNat_eq_natCast, ite_eq_right hnot, hshort, Bool.false_eq_true,
    ite_false, Int.toNat_natCast]
  generalize hpr : processnode ctx level
    (refine ctx level st.lab st.ptn st.active numcells).numcells _ = pr
  rcases hc : cheapautom pr.2.ptn level n with _ | _ <;>
    simp only [Bool.false_eq_true, not_false_eq_true, ite_true,
      not_true_eq_false, ite_false] <;>
    generalize hL : (otherChildLoop ctx inf tcLevel fuel (n + 1)
      level _ _ _ _ _ _) = L <;>
    rcases L with ⟨r, out⟩ <;>
    cases r <;> simp only [Id.run_pure, apply_ite Id.run] <;> rfl

/-! # Facts an off-path fragment preserves beyond its packaged run -/

/-- Off-path bookkeeping never rewrites the first leaf, keeps the orbit
array sound, and lowers the saved cheap-cell boundary only to a value
it already had on entry. -/
structure OtherKeep (ctx : Ctx n) (level : Nat) (st out : SearchSt n) : Prop where
  firstlab : out.firstlab = st.firstlab
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  boundary : out.noncheaplevel < level → out.noncheaplevel = st.noncheaplevel

/-- Lowering the first-path agreement depth preserves the prepared
state. -/
theorem RunPrep.setEqlevFirst {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells e : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (he : e ≤ st.eqlevFirst) :
    RunPrep G ctx tcLevel level codes bs fs numcells
      { st with eqlevFirst := e } best trail := by
  let st' : SearchSt n := { st with eqlevFirst := e }
  have hok : SearchOk G level numcells st' := by
    refine ⟨h.searchOk.labSize, h.searchOk.ptnSize, h.searchOk.reach,
      h.searchOk.init1, h.searchOk.vals, h.searchOk.count, h.searchOk.bc,
      h.searchOk.canon⟩
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  refine ⟨hok, h.codeInv, firstCodeInv_mono h.firstInv he, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- The frozen-downward arm of `processnode`, at any cell count, yields
the packaged event with the incumbent unchanged. -/
theorem RunPrep.fastEvent {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : st.noncheaplevel ≤ level)
    (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    EventOut G ctx tcLevel stem fs (processnode ctx level numcells st).2
      best trail (processnode ctx level numcells st).1 := by
  obtain ⟨hr, hcomp, heqlev, hcode, hcanonlevel, hcanonlab, hcanong,
      hsamerows⟩ :=
    processnode_fast (ctx := ctx) (level := level) (numcells := numcells)
      (st := st) hg
  have hframes := processnode_frames ctx level numcells st
  have hgen := processnode_fast_genTrace (ctx := ctx) (numcells := numcells)
    hg
  have hgcaCanon := processnode_fast_gcaCanon (ctx := ctx)
    (numcells := numcells) hg
  have hef : ¬((st.eqlevFirst == level) = true) :=
    fun h => hg.1 (beq_iff_eq.mp h)
  have hevent : RunEvent G ctx tcLevel level codes bs fs
      (processnode ctx level numcells st).2 best trail := by
    refine ⟨Or.inl ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, hprep.bestCodes, ?_⟩
    · rw [hcomp]
      exact Int.le_of_lt hg.2
    · rw [hcomp, heqlev, hcode, hcanonlevel]
      exact hprep.codeInv
    · rw [hframes.2.2.1, hframes.2.2.2.1]
      exact hprep.firstInv
    · rw [hcanong, hcanonlab, hsamerows]
      exact hprep.canongInv
    · exact hprep.leafRefs.processnodeGen hn0 hsymm hloop
        hprep.searchOk hprep.canongInv hprep.genTraceOk
    · exact hprep.processnodeAutos hn0 hsymm hloop hbound
    · exact hprep.workspace.processOff hprep.codeInv hef
    · exact hprep.cheap.processnode
    · exact hprep.leafRefs.processnode hprep.searchOk
    · exact hprep.guides.stateEq hframes.2.2.2.2.2.2.1 hframes.2.2.2.2.1
        hgcaCanon hcanonlab
    · exact hprep.trailOk.processnode
    · rw [hframes.2.2.2.2.2.2.1]
      exact hprep.firstPositive
    · rw [hgcaCanon]
      exact hprep.canonPositive
    · rw [hframes.2.2.2.2.2.2.1]
      exact hprep.firstBound
    · rw [hgcaCanon]
      exact hprep.canonBound
    · rw [hcanonlab]
      exact hprep.incumbent
  apply EventOut.intro level codes bs hevent hpath hstem hpast
  · rw [hr]
    have hlt := pruneReturn_lt (noncheaplevel := st.noncheaplevel)
      (allsamelevel := st.allsamelevel) (eqlevCanon := st.eqlevCanon)
    have hb : Int.ofNat st.noncheaplevel ≤ Int.ofNat level :=
      Int.ofNat_le.mpr hbound
    omega
  · have hs := hlive.stable.ofGenTraceEq hgen
    rw [hframes.2.2.2.2.2.2.1]
    exact hs.lower (Int.min_le_right _ _)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- The return of the frozen-downward arm lies strictly below the node
whenever the saved boundary does not exceed it. -/
theorem processnode_fast_below {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    (hbound : st.noncheaplevel ≤ level) :
    (processnode ctx level numcells st).1 < Int.ofNat level := by
  rw [(processnode_fast (ctx := ctx) (numcells := numcells) hg).1]
  have hlt := pruneReturn_lt (noncheaplevel := st.noncheaplevel)
    (allsamelevel := st.allsamelevel) (eqlevCanon := st.eqlevCanon)
  have hb : Int.ofNat st.noncheaplevel ≤ Int.ofNat level :=
    Int.ofNat_le.mpr hbound
  omega

/-! # The frozen bound at an internal node -/

/-- With the comparison frozen downward at the refined code, every key
of the node's specification subtree is dominated by the incumbent. -/
theorem nodeKey_le_of_frozen {ctx : Ctx n} {tcLevel specFuel level numcells
    tail : Nat} {codes bs : List Nat} {st : SearchSt n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon compCanon : Int}
    {canonlab : Array Nat}
    (hinv : CodeCmpInv n (codes ++
      [(refine ctx level st.lab st.ptn st.active numcells).longcode]) bs
      canoncode canonlevel eqlevCanon compCanon)
    (hneg : compCanon < 0)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = false)
    (hlen : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn level
      tcLevel).2.2 = tail + 1) :
    keyLe (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)
      (incKey ctx bs canonlab) := by
  unfold nodeKey
  rw [specNode_internal codes hdisc hlen]
  apply keysMax_le
  · exact hinv.frozenBound hneg _
  · intro y hy
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hy
    exact hinv.frozenBound hneg _

/-! # The immediately pruning internal node -/

/-- An internal off-path node whose prepared state prunes at once through
the frozen-downward arm: its exact maximum is the unchanged incumbent,
and its return is either a frozen comparison or a cheap-cell jump. -/
theorem NodeInv.fastRun {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st pre : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hstate : otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level
        (refine ctx level st.lab st.ptn st.active numcells).numcells pre)
    (hprep : RunPrep G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells pre
      best trail)
    (hlive : Live ctx level pre trail)
    (hgate : pre.eqlevFirst ≠ level ∧ pre.compCanon < 0)
    (hbound : pre.noncheaplevel ≤ level)
    (hclear : pre.needshortprune = false)
    (hfirst : pre.gcaFirst = st.gcaFirst)
    (hcanon : pre.gcaCanon = st.gcaCanon)
    (hcanonlab : pre.canonlab = st.canonlab)
    (hcoset : pre.cosetindex = st.cosetindex)
    (hfixed : pre.fixedpts = st.fixedpts)
    (hfirstlab : pre.firstlab = st.firstlab)
    (hgen : pre.genTrace = st.genTrace)
    (horb : pre.orbits = st.orbits)
    (hncl : pre.noncheaplevel = st.noncheaplevel)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [rs.longcode]
  let pr := processnode ctx level rs.numcells pre
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hgsz : ctx.g.size = n := by
    rw [hg]
    exact size_rowsOf G
  have hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
    rw [hg]
    exact rowsOf_symm G
  have hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false := by
    rw [hg]
    exact rowsOf_loopless G
  have hframes := processnode_frames ctx level rs.numcells pre
  have hearly : pr.1 < Int.ofNat level :=
    processnode_fast_below hgate hbound
  have hne : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ n := Nat.ne_of_lt hnum
  have hdisc : discreteAt rs.ptn level n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff hn0
      hnode.run.searchOk hlevel]
    exact hne
  obtain ⟨tc, len, -, hspec, -, hlen, -⟩ :=
    hnode.target hg hn0 hlevel hne
  have hkeyLe : keyLe (nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells) (incKey ctx bs pre.canonlab) := by
    apply nodeKey_le_of_frozen (tail := len - 1) hprep.codeInv hgate.2
      hdisc
    rw [hspec]
    simp only
    omega
  have hexact : best = some (incMax best
      (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
    rw [hprep.incumbent, incMax, keyMax_eq_left hkeyLe]
  have hevent : EventOut G ctx tcLevel codes fs pr.2 best trail pr.1 :=
    hprep.fastEvent hn0 hsymm hloop hfull hstem (by omega) hbound
      hgate hlive
  have hgenOut : pr.2.genTrace = pre.genTrace :=
    processnode_fast_genTrace hgate
  have horbOut : pr.2.orbits = pre.orbits :=
    processnode_fast_orbits hgate
  have hcanonOut : pr.2.gcaCanon = pre.gcaCanon :=
    processnode_fast_gcaCanon hgate
  have hcanonlabOut : pr.2.canonlab = pre.canonlab :=
    (processnode_fast (ctx := ctx) (numcells := rs.numcells) hgate).2.2.2.2.2.1
  have hexit : NodeExit ctx tcLevel (specFuel + 1) (fuel + 1) level codes st
      pr.2 numcells best best trail pr.1 := by
    have hfirstNe : pre.eqlevFirst ≠ level := hgate.1
    rcases hprep.pruneMode hfull hstem hfirstNe hgate.2 with
      hfreeze | hjump
    · exact NodeExit.frozen hearly hexact hfreeze
    · apply NodeExit.cheap pre.noncheaplevel hjump hprep.cheap.positive
        hbound
      · exact hframes.2.2.2.2.2.2.2.1
      · exact hexact
  rw [hstate]
  refine ⟨⟨⟨hexit, hevent, TrailExt.refl level trail, ?_, ?_⟩, ?_, ?_, ?_,
    ?_⟩, ?_, ?_, ?_⟩
  · rw [processnode_fixedpts, hfixed]
  · intro hshort
    exact hprep.fastSource hbound hgate hclear hshort
  · rw [hframes.2.2.2.2.2.2.1, hfirst]
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).2
  · left
    exact ⟨hcanonOut.trans hcanon, hcanonlabOut.trans hcanonlab⟩
  · rw [processnode_coset, hcoset]
  · rw [hframes.2.2.2.2.1, hfirstlab]
  · rw [hgenOut, horbOut, hgen, horb]
    exact hsound
  · intro _
    rw [hframes.2.2.2.2.2.2.2.1, hncl]

/-- The prepared state of an off-path node keeps every field the
immediate-prune packaging reads. -/
theorem otherLeafSt_frames (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).gcaFirst = st.gcaFirst ∧
    (otherLeafSt ctx level numcells st).gcaCanon = st.gcaCanon ∧
    (otherLeafSt ctx level numcells st).canonlab = st.canonlab ∧
    (otherLeafSt ctx level numcells st).cosetindex = st.cosetindex ∧
    (otherLeafSt ctx level numcells st).fixedpts = st.fixedpts ∧
    (otherLeafSt ctx level numcells st).firstlab = st.firstlab ∧
    (otherLeafSt ctx level numcells st).genTrace = st.genTrace ∧
    (otherLeafSt ctx level numcells st).orbits = st.orbits ∧
    (otherLeafSt ctx level numcells st).noncheaplevel = st.noncheaplevel ∧
    (otherLeafSt ctx level numcells st).needshortprune =
      st.needshortprune := by
  refine ⟨RefTrail.otherLeaf_gcaFirst ctx level numcells st,
    RefTrail.otherLeaf_gcaCanon ctx level numcells st, ?_, ?_,
    otherLeafSt_fixedpts ctx level numcells st, ?_, ?_, ?_,
    RefTrail.otherLeaf_noncheaplevel ctx level numcells st,
    otherLeafSt_short ctx level numcells st⟩
  · rw [otherLeafSt_eq, (otherNodePrep_frames _ _ _).1]
  · rw [otherLeafSt_eq, otherNodePrep_coset]
  · rw [otherLeafSt_eq, otherNodePrep_firstlab']
  · rw [otherLeafSt_eq, otherNodePrep_genTrace']
  · rw [otherLeafSt_eq, otherNodePrep_orbits']

/-- The broken-agreement negative branch of an internal node. -/
theorem NodeInv.gateRun {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (hgate : (otherLeafSt ctx level numcells st).eqlevFirst ≠ level ∧
      (otherLeafSt ctx level numcells st).compCanon < 0)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  have hprep := hnode.run.otherLeaf hn0 hlevel hpath
  have hbound : (otherLeafSt ctx level numcells st).noncheaplevel ≤ level := by
    rw [hf9]
    exact hcheap
  have hstate := otherNode_gate_state ctx inf tcLevel fuel level numcells st
    hnum hgate (processnode_fast_below hgate hbound)
  exact hnode.fastRun hg hn0 hlevel hpath hnum hstate hprep
    (hlive.otherLeaf (numcells := numcells)) hgate hbound
    (by rw [hf10, hnode.shortClear]) hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9
    hsound

/-- The mismatched-hint negative branch of an internal node. -/
theorem NodeInv.hintFailRun {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmis : Int.ofNat (maketargetcell ctx
        (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 ≠
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n) :
    OtherRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best best trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      OtherKeep ctx level st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10⟩ :=
    otherLeafSt_frames ctx level numcells st
  let pre0 := otherLeafSt ctx level numcells st
  let pre : SearchSt n :=
    { pre0 with
      tctotal := pre0.tctotal +
        (maketargetcell ctx pre0.lab pre0.ptn level tcLevel
          pre0.firsttc[level]!).2.2
      eqlevFirst := level - 1 }
  have hprep0 := hnode.run.otherLeaf hn0 hlevel hpath
  have hprep : RunPrep G ctx tcLevel level
      (codes ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells pre
      best trail := by
    have h1 := hprep0.setTctotal (value := pre0.tctotal +
      (maketargetcell ctx pre0.lab pre0.ptn level tcLevel
        pre0.firsttc[level]!).2.2)
    have h2 := h1.setEqlevFirst (e := level - 1) (by
      change level - 1 ≤ pre0.eqlevFirst
      rw [beq_iff_eq.mp heq]
      omega)
    exact h2
  have hgate : pre.eqlevFirst ≠ level ∧ pre.compCanon < 0 := by
    refine ⟨?_, hneg⟩
    change level - 1 ≠ level
    omega
  have hbound : pre.noncheaplevel ≤ level := by
    change pre0.noncheaplevel ≤ level
    rw [hf9]
    exact hcheap
  have hlive' : Live ctx level pre trail :=
    (hlive.otherLeaf (numcells := numcells)).stateEq rfl rfl rfl rfl rfl
  have hstate := otherNode_hintFail_state ctx inf tcLevel fuel level numcells
    st hnum heq hneg hmis (processnode_fast_below hgate hbound)
  exact hnode.fastRun hg hn0 hlevel hpath hnum hstate hprep hlive' hgate
    hbound (by change pre0.needshortprune = false; rw [hf10, hnode.shortClear])
    hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hsound

end Hex.GraphIso.Nauty

/-!
Per-child transport for the off-path sibling sweep: the guide relation to
the frozen loop entry, the small-cell descent invariant into each
individualized child, and the key identification used by every early
exit.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Key n identification -/

/-- The node key reads only the labelling, partition, and active set. -/
theorem nodeKey_congr {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {cs : List Nat} {st st' : SearchSt n}
    (hlab : st'.lab = st.lab) (hptn : st'.ptn = st.ptn)
    (hactive : st'.active = st.active) :
    nodeKey ctx tcLevel fuel level cs st' numcells =
      nodeKey ctx tcLevel fuel level cs st numcells := by
  unfold nodeKey
  rw [hlab, hptn, hactive]

/-- Every frozen offset carrying the selected vertex has the key of the
executable child built from it. -/
theorem LoopInv.childKeyAll {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv offset currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hoffset : offset < len)
    (hfrozen : rsLab[tc + offset]! = tv)
    (hcurrentAt : st.lab[tc + currentOffset]! = tv) :
    ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := st.fixedpts.insert tv }
          (numcells + 1) := by
  intro o ho hotv
  have hinj : LabInj rsLab n := by
    rw [← h.baseLab]
    exact labInj_of_reach h.baseOk.labSize h.nonempty h.baseOk.reach
  have hoo : o = offset := by
    have := hinj.eq_of_getElem! (i := tc + o) (j := tc + offset)
      (by have := h.range; omega) (by have := h.range; omega)
      (hotv.trans hfrozen.symm)
    omega
  subst hoo
  have hkey := h.childKey (coset := st.cosetindex) ho hotv hcurrentAt
  rw [hcurrentAt] at hkey
  rw [hkey]

/-- The start of a sweep always has a first vertex. -/
theorem nextElem_windowSet_some {lab : Array Nat} {tc len : Nat}
    (hlen : 1 ≤ len) (hlt : lab[tc]! < n) :
    ∃ v, (windowSet n lab tc len).nextElem none = some v := by
  rcases hnext : (windowSet n lab tc len).nextElem none with _ | v
  · exfalso
    have hmem : (windowSet n lab tc len).mem lab[tc]! = true := by
      refine mem_windowSet.mpr ⟨hlt, ?_⟩
      rw [segN]
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), by simp⟩
    exact no_child_after hnext lab[tc]! hmem trivial
  · exact ⟨v, rfl⟩

/-! # Guide relation across one child -/

namespace GuideRel

/-- The guide relation depends only on the guide controls and the two
reference labellings. -/
theorem stateEq {level : Nat} {base st st' : SearchSt n}
    (h : GuideRel level base st)
    (hfirst : st'.gcaFirst = st.gcaFirst)
    (hcanon : st'.gcaCanon = st.gcaCanon)
    (hcanonlab : st'.canonlab = st.canonlab) :
    GuideRel level base st' := by
  refine ⟨hfirst.trans h.first, ?_, ?_⟩
  · rw [hfirst, hcanon]
    exact h.order
  · rw [hcanon, hcanonlab]
    exact h.canon

/-- A completed or early-returning off-path child of a sweep keeps the
guide relation to the sweep's frozen entry. -/
theorem ofChild {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hguide : GuideRel level base st)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      out (numcells + 1) best outBest receiptTrail eventTrail r) :
    GuideRel level base out := by
  let child : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv }
  have hfirst : out.gcaFirst = st.gcaFirst := hchild.firstGuide
  refine ⟨hfirst.trans hguide.first, hchild.order, ?_⟩
  rcases hchild.canonGuide with hold | hnew
  · rw [hold.1, hold.2]
    exact hguide.canon
  · right
    refine ⟨Nat.le_trans (Nat.le_succ level) hnew.1, ?_⟩
    have hok := hinv.run.searchOk
    have hstSize : st.lab.size = n := hok.labSize
    have hstPtnSize : st.ptn.size = n := hok.ptnSize
    have htcPtn : tc < st.ptn.size := by
      rw [hstPtnSize]
      exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hinv.range
    have hrangePtn : tc + len ≤ st.ptn.size := by
      rw [hstPtnSize]
      exact hinv.range
    have hchildPtn : child.ptn = st.ptn.set! tc (level + 1) :=
      breakout_ptn (n := n) st.lab st.ptn (level + 1) tc tv
    have hchildOk : SearchOk G (level + 1) (numcells + 1) child := by
      apply breakout_searchOk hinv.nonempty hok hinv.positive
        hinv.currentCell hinv.lenTwo hinv.range hcurrent
      · change (breakout n st.lab st.ptn (level + 1) tc tv).1 = _
        rw [hat]
      · exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc tv
      · rfl
    have hfine : cellsPerm st.ptn level child.lab out.canonlab := by
      apply cellsPerm_coarsen (ptnF := child.ptn) (levF := level + 1)
      · rw [hchildPtn, Array.size_set!]
      · exact hchildOk.labSize.trans hchildOk.ptnSize.symm
      · rw [hchild.node.event.canonSize, hchildOk.ptnSize]
      · exact hnew.2
      · exact searchOk_end hinv.nonempty hchildOk (by omega)
      · exact searchOk_end hinv.nonempty hok hinv.positive
      · intro q hq
        rw [hchildPtn]
        rcases Decidable.em (tc = q) with rfl | hne
        · rw [Array.getElem!_set!_self _ _ _ htcPtn]
          exact Nat.le_refl _
        · rw [Array.getElem!_set!_ne _ _ _ _ hne]
          omega
    have hbreak : cellsPerm st.ptn level st.lab child.lab := by
      change cellsPerm st.ptn level st.lab
        (breakout n st.lab st.ptn (level + 1) tc tv).1
      rw [← hat]
      exact breakout_cellsPerm hinv.currentCell hrangePtn
        (by rw [hstSize, hstPtnSize]) hcurrent
    have hperm : cellsPerm st.ptn level st.lab out.canonlab :=
      cellsPerm_trans hbreak hfine
    have hbasePtn : st.ptn = base.ptn := by
      rw [hinv.ptnEq, hinv.basePtn]
    rw [hbasePtn] at hperm
    have hbasePerm : cellsPerm base.ptn level base.lab st.lab :=
      hinv.effect.perm
    exact cellsPerm_trans hbasePerm hperm

/-- Recovery to the sweep level keeps the guide relation once the
sweep entry's canonical control is at most the sweep level. -/
theorem recover {level inf : Nat} {base out : SearchSt n}
    (h : GuideRel level base out) (hbase : base.gcaCanon ≤ level)
    (horder : (Nauty.recover n inf level out).gcaFirst ≤
      (Nauty.recover n inf level out).gcaCanon) :
    GuideRel level base (Nauty.recover n inf level out) := by
  have hframes := recover_frames n inf level out
  refine ⟨hframes.2.2.2.2.2.2.1.trans h.first, horder, ?_⟩
  rw [recover_gcaCanon, hframes.1]
  rcases h.canon with hold | hnew
  · left
    refine ⟨?_, hold.2⟩
    rw [hold.1]
    exact ite_eq_right (Nat.not_lt_of_ge hbase)
  · right
    refine ⟨?_, hnew.2⟩
    split
    · exact Nat.le_refl level
    · exact hnew.1

end GuideRel

/-! # Small-cell descent into a child -/

/-- The subtree facts survive a change of the recorded active set. -/
theorem SubtreeOk.setActive {ctx : Ctx n} {level : Nat} {r : RefineSt n}
    {a : VSet n} (h : SubtreeOk ctx level r) :
    SubtreeOk ctx level { r with active := a } :=
  ⟨⟨⟨h.it.ok.labSize, h.it.ok.labOk, h.it.ok.ptnSize,
    h.it.ok.ptnEnd⟩, h.it.inj, h.it.vals, h.it.lvl⟩, h.eqt, h.acc,
    h.shape⟩

/-- The frozen frame of a sweep, as a refinement state. -/
@[expose] def LoopInv.frame (rsLab rsPtn : Array Nat) (numcells : Nat) :
    RefineSt n :=
  { lab := rsLab, ptn := rsPtn, active := VSet.empty, numcells := numcells,
    hint := 0, maxpos := 0, longcode := numcells }

/-- A sweep frame with a live target cell has an open position. -/
theorem LoopInv.levelLt {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    level < n := by
  have hbc := h.run.searchOk.bc
  rw [h.ptnEq] at hbc
  have hopen : rsPtn[tc]! > level := by
    have := h.cell.2.2.1 tc (Nat.le_refl tc) (by have := h.lenTwo; omega)
    omega
  have htc : tc < n := by
    have := h.range
    have := h.lenTwo
    omega
  have hne : bcount rsPtn level n ≠ n := by
    intro heq
    rw [bcount] at heq
    have hall := List.countP_eq_length.mp (by
      rw [heq, List.length_range])
    have := of_decide_eq_true (hall tc (List.mem_range.mpr htc))
    omega
  have hle := bcount_le rsPtn level n
  omega

/-- The small-cell descent invariant at the frozen frame transports to
the individualized child of the current recovered state. -/
theorem LoopInv.childDesc {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hpark : cheapautom rsPtn level n = false →
      st.noncheaplevel = level + 1)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv) :
    CheapDesc ctx (level + 1) st.noncheaplevel
      (refine ctx (level + 1) (breakout n st.lab st.ptn (level + 1) tc tv).1
        (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        (breakout n st.lab st.ptn (level + 1) tc tv).2.2 (numcells + 1)) := by
  have hok := h.run.searchOk
  have hsz : st.lab.size = n := hok.labSize
  have hpsz : rsPtn.size = n := h.frozenPtnSize
  have hlabOk : LabOk st.lab n :=
    labOk_of_reach hok.labSize hok.reach
  have hinj : LabInj st.lab n :=
    labInj_of_reach hok.labSize h.nonempty hok.reach
  let cur : RefineSt n := { LoopInv.frame rsLab rsPtn numcells with lab := st.lab }
  have hcur : CheapDesc ctx level st.noncheaplevel cur := by
    intro hlt
    exact (hdesc hlt).ofCellsPerm h.labPerm hsz hlabOk hinj
  have hend : rsPtn[rsPtn.size - 1]! ≤ level := h.frozenEnd
  have hit : IterOk ctx level cur := by
    refine ⟨⟨hsz, hlabOk, hpsz, hend⟩, hinj, ?_, ?_⟩
    · intro q hq
      exact h.values q
    · exact Nat.le_of_lt h.levelLt
  have heq : Equitable ctx level cur.lab cur.ptn := by
    change Equitable ctx level st.lab rsPtn
    rw [← h.ptnEq]
    exact h.currentEquitable
  have hcount : bcount cur.ptn level n = cur.numcells := by
    change bcount rsPtn level n = numcells
    rw [← h.ptnEq]
    exact hok.count.symm
  have hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
    rw [hg]
    exact rowsOf_symm G
  have hchild := hcur.child hit heq hcount hsymm h.levelLt h.cell h.lenTwo
    h.range hcurrent
  have hboundary : (if st.noncheaplevel ≥ level ∧
      ¬cheapautom cur.ptn level n then level + 1
      else st.noncheaplevel) = st.noncheaplevel := by
    change (if st.noncheaplevel ≥ level ∧
      ¬cheapautom rsPtn level n then level + 1
      else st.noncheaplevel) = st.noncheaplevel
    rcases hc : cheapautom rsPtn level n with _ | _
    · rw [hpark hc]
      simp
    · simp
  rw [hboundary] at hchild
  have hcurLab : cur.lab[tc + currentOffset]! = tv := hat
  rw [hcurLab] at hchild
  have hptn : st.ptn = rsPtn := h.ptnEq
  change CheapDesc ctx (level + 1) st.noncheaplevel
    (refine ctx (level + 1) (breakout n st.lab rsPtn (level + 1) tc tv).1
      (rsPtn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1)) at hchild
  rw [breakout_ptn, hptn]
  exact hchild

/-- A small-cell subtree fact at the frozen frame, in the form the
sibling-sweep bound identification consumes. -/
theorem LoopInv.subtreeAt {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hpark : cheapautom rsPtn level n = false →
      st.noncheaplevel = level + 1)
    (hle : st.noncheaplevel ≤ level) :
    SubtreeOk ctx level
      { lab := rsLab, ptn := rsPtn, active := base.active,
        numcells := numcells, hint := 0, maxpos := 0,
        longcode := numcells } := by
  have hsub : SubtreeOk ctx level (LoopInv.frame rsLab rsPtn numcells) := by
    apply hdesc.atLevel
    · refine ⟨⟨h.frozenLabSize, h.frozenLabOk, h.frozenPtnSize, h.frozenEnd⟩, ?_, ?_, ?_⟩
      · rw [← h.baseLab]
        exact labInj_of_reach h.baseOk.labSize h.nonempty h.baseOk.reach
      · intro q hq
        exact h.values q
      · exact Nat.le_of_lt h.levelLt
    · exact h.equitable
    · change bcount rsPtn level n = numcells
      rw [← h.basePtn]
      exact h.baseOk.count.symm
    · exact hle
    · intro heq
      rcases hc : cheapautom rsPtn level n with _ | _
      · have := hpark hc
        omega
      · exact hc
  exact hsub.setActive

end Hex.GraphIso.Nauty

/-!
Fuel-separated totality statements for the transcribed search.

The logical fuel in `nodeKey`, the node recursion fuel, and a sibling
loop's cursor fuel are deliberately kept distinct.  The strict node-fuel
bound is preserved by descent and makes the executable zero-fuel branch
unreachable at every well-formed node.

Beyond the packaged run, each node statement carries the facts the
enclosing loops thread through it: the saved cheap-cell boundary, the
small-cell descent invariant at the refined frame, orbit soundness, the
coset cursor, and domination of the first leaf by the incumbent.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Facts a first-path node preserves or establishes beyond its packaged
run. -/
structure FirstKeep (ctx : Ctx n) (level : Nat) (st out : SearchSt n)
    (fs : List Nat) (outBest : Option (Key n)) : Prop where
  dom : ∀ b, outBest = some b → keyLe (pathLeafKey ctx fs out.firstlab) b
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  coset : st.cosetindex < n → out.cosetindex < n
  boundary : out.noncheaplevel < level → out.noncheaplevel = st.noncheaplevel
  guide : level ≤ out.gcaFirst

/-- Totality of one off-path node at a fixed executable recursion fuel.
Off-path nodes are never the root, so the level is at least two. -/
@[expose] def OtherTotal (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel runFuel : Nat) : Prop :=
  ∀ (specFuel level numcells : Nat) (codes bs fs : List Nat)
    (st : SearchSt n) (best : Option (Key n)) (trail : FrameTrail),
    ctx.g = rowsOf G → inf = n + 2 → 0 < n →
    2 ≤ level → level = codes.length + 1 →
    level + specFuel = n + 1 → n + 2 < level + runFuel →
    st.noncheaplevel ≤ level →
    CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells) →
    NodeInv G ctx tcLevel level codes bs fs numcells st best trail →
    Live ctx level st trail →
    PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st →
    OrbSound (OrbConn st.genTrace.toList n) st.orbits n →
    st.cosetindex < n →
    (∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b) →
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel specFuel runFuel level codes fs st
          (otherNode ctx inf tcLevel runFuel level numcells st).2 numcells
          best outBest trail eventTrail
          (otherNode ctx inf tcLevel runFuel level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel runFuel level numcells st).2

/-- Totality of one node on the unique descent preceding the first leaf. -/
@[expose] def FirstTotal (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel runFuel : Nat) : Prop :=
  ∀ (specFuel level numcells : Nat) (codes : List Nat)
    (st : SearchSt n) (trail : FrameTrail),
    ctx.g = rowsOf G → inf = n + 2 → 0 < n →
    1 ≤ level → level = codes.length + 1 →
    level + specFuel = n + 1 → n + 2 < level + runFuel →
    st.noncheaplevel ≤ level →
    CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells) →
    OrbSound (OrbConn st.genTrace.toList n) st.orbits n →
    FirstInv G ctx level codes numcells st trail →
    PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st →
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel specFuel runFuel level codes fs st
          (firstPathNode ctx inf tcLevel runFuel level numcells st).2
          numcells outBest trail eventTrail
          (firstPathNode ctx inf tcLevel runFuel level numcells st).1 ∧
        FirstKeep ctx level st
          (firstPathNode ctx inf tcLevel runFuel level numcells st).2 fs
          outBest

/-- A well-formed search node cannot occur deeper than the graph. -/
theorem SearchOk.levelLe {G : Colored n k} {level numcells : Nat}
    {st : SearchSt n} (h : SearchOk G level numcells st) : level ≤ n :=
  Nat.le_trans h.bc (bcount_le st.ptn level n)

/-- The strict node-fuel invariant rules out the zero-fuel off-path
branch before any operational case analysis is needed. -/
theorem OtherTotal.zero (G : Colored n k) (ctx : Ctx n) (inf tcLevel : Nat) :
    OtherTotal G ctx inf tcLevel 0 := by
  intro specFuel level numcells codes bs fs st best trail _ _ _ _ _ _
    hfuel _ _ hnode _ _ _ _ _
  have hle : level ≤ n := hnode.run.searchOk.levelLe
  omega

/-- The same strict bound rules out zero executable fuel on the initial
descent. -/
theorem FirstTotal.zero (G : Colored n k) (ctx : Ctx n) (inf tcLevel : Nat) :
    FirstTotal G ctx inf tcLevel 0 := by
  intro specFuel level numcells codes st trail _ _ _ _ _ _ hfuel _ _ _
    hfirst _
  have hle : level ≤ n := hfirst.searchOk.levelLe
  omega

end Hex.GraphIso.Nauty
