/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeExit

public section

/-!
Base cases and transport for the corrected sibling-sweep induction.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

namespace OtherOutcome

/-- Resolving an ordinary off-path child after clearing a pending
short-prune request rebuilds the parent invariant.  This is the uniform
recovery form used by both filtered and unfiltered executable branches. -/
theorem nextClear {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells tc len tcell tv offset
      currentOffset inf : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt}
    {best outBest : Option Key} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail)
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      out)
    (hinf : inf = n + 2) (hpath : codes.length = level)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (hnext : nextElem tcell cursor = some tv)
    (hoffset : offset < len) (hcurrent : currentOffset < len)
    (htv : rsLab[tc + offset]! = tv)
    (hat : st.lab[tc + currentOffset]! = tv)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).1
            ptn := (breakout st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.1
            active := (breakout st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.2
            fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
          (numcells + 1)) :
    let cleaned : SearchSt :=
      { out with
        fixedpts := erase out.fixedpts tv
        needshortprune := false }
    let recovered := Nauty.recover ctx.n inf level cleaned
    ∃ bs',
      LoopInv G ctx tcLevel specFuel level codes bs' fs numcells rsLab rsPtn
          tc len tcell (some tv) base recovered outBest eventTrail ∧
        OtherLive ctx level recovered eventTrail := by
  dsimp only
  let child : SearchSt :=
    { st with
      lab := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
  let oldCleaned : SearchSt :=
    { out with fixedpts := erase out.fixedpts tv }
  let cleaned : SearchSt :=
    { oldCleaned with needshortprune := false }
  let oldRecovered := Nauty.recover ctx.n inf level oldCleaned
  let recovered := Nauty.recover ctx.n inf level cleaned
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
    exact recover_clearShort ctx.n inf level oldCleaned
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
    (h.node.event.clearShort.setFixed (erase out.fixedpts tv)).recoverRun
      hreturn hpath hinv.positive hinfLevel hfirstClean hok
  have hlive' : OtherLive ctx level recovered eventTrail := by
    constructor
    · constructor
      · exact hhistory
      · exact RefTrail.recover_order h.order hfirstClean
      · exact hstable
    · rw [(recover_frames ctx.n inf level cleaned).2.2.2.2.2.2.1]
      exact hfirstOut
  have hrefsOld := h.refs hinv hlive hcoverage hfuel hnext hoffset hcurrent
    htv hat (inf := inf) (fixedpts := erase out.fixedpts tv)
  have hrefs : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells recovered outBest := by
    rw [hrecovered]
    exact ⟨hrefsOld.first, hrefsOld.canon⟩
  refine ⟨bs', ?_, hlive'⟩
  exact {
    nodeCount := hinv.nodeCount
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
theorem ancestor {G : Colored n k} {ctx : Ctx} {tcLevel : Nat}
    {stem codes fs : List Nat} {out : SearchSt} {best : Option Key}
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
theorem restrict {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell tcell' : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true)
    (hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell' cursor best) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
      tc len tcell' cursor base st best trail := by
  exact {
    nodeCount := h.nodeCount
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

/-- The long-prune filter preserves the full mutable sweep invariant.
The root ledger supplies valid pairs at the current ordering, and the
frozen-frame permutation transports their cell stabilization back to the
specification ordering. -/
theorem longprune {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hgsz : ctx.g.size = ctx.n)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
      tc len (Nauty.longprune tcell st.fixedpts st.autos) cursor base st
      best trail := by
  have hlocal : LocalAutos ctx level st := hpath.autos h.run
  have hstSize : st.lab.size = ctx.n := by
    rw [h.nodeCount]
    exact h.run.searchOk.labSize
  have haut : ∀ p ∈ st.autos.toList,
      (st.fixedpts &&& p.1 == st.fixedpts) = true →
      PairOk ctx.g rsPtn rsLab level ctx.n p.1 p.2 := by
    intro p hp hfix
    have hpair := hlocal p hp hfix
    rw [h.ptnEq] at hpair
    exact LocalAutos.reindexPair hpair (cellsPerm_symm h.labPerm)
      h.frozenPtnSize hstSize h.frozenLabSize h.frozenEnd
  apply h.restrict (fun _ hm => longprune_subset hm)
  exact h.cover.longprune hgsz h.frozenLabSize h.frozenLabOk
    h.frozenPtnSize h.frozenEnd h.values h.cell h.range h.fuelBound haut

/-- The short-prune filter preserves the full mutable sweep invariant
once the one-shot protocol identifies its newest workspace pair as valid
at the frozen parent frame. -/
theorem shortprune {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hgsz : ctx.g.size = ctx.n)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlast : ∀ fix mcr, st.autos.back? = some (fix, mcr) →
      PairOk ctx.g rsPtn rsLab level ctx.n fix mcr) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab rsPtn
      tc len (Nauty.shortprune tcell st) cursor base st best trail := by
  apply h.restrict (fun _ hm => shortprune_subset hm)
  exact h.cover.shortprune hgsz h.frozenLabSize h.frozenLabOk
    h.frozenPtnSize h.frozenEnd h.values h.cell h.range h.fuelBound hlast

/-- The mutable child selected for a frozen offset has exactly that
offset's specification key. -/
theorem childKey {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell tv offset currentOffset
      coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
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
          lab := (breakout st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).1
          ptn := (breakout st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).2.1
          active := (breakout st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).2.2
          fixedpts := insert st.fixedpts st.lab[tc + currentOffset]!
          cosetindex := coset }
        (numcells + 1) := by
  let child : SearchSt :=
    { st with
      lab := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := insert st.fixedpts st.lab[tc + currentOffset]!
      cosetindex := coset }
  rw [← h.baseLab, ← h.basePtn]
  apply SearchOut.breakoutKey h.nodeCount h.effect h.baseOk h.run.searchOk
    h.nonempty h.positive
  · rw [h.basePtn]
    exact h.cell
  · exact h.lenTwo
  · rw [← h.nodeCount]
    exact h.range
  · exact hoffset
  · change child.lab = (breakout st.lab st.ptn (level + 1) tc
      base.lab[tc + offset]!).1
    rw [h.baseLab, hfrozen, ← hcurrentAt]
  · change child.ptn = (breakout st.lab st.ptn (level + 1) tc
      base.lab[tc + offset]!).2.1
    rw [h.baseLab, hfrozen, ← hcurrentAt]
  · change child.active = (breakout st.lab st.ptn (level + 1) tc
      base.lab[tc + offset]!).2.2
    rw [h.baseLab, hfrozen, ← hcurrentAt]
  · rfl
  · simpa only [h.nodeCount] using h.fuelBound

/-- Every original target-cell child key is below the fixed sweep bound. -/
theorem keyLeBound {ctx : Ctx}
    {tcLevel specFuel level tc len numcells tail offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {bound : Key}
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

end LoopInv

namespace OtherLoopRun

theorem reindexSet {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell tcell' : Nat} {cursor : Option Nat}
    {bound : Key} {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.proof.reindexSet, h.exit.reindexSet⟩

theorem step {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : OtherLoopRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out best
      outBest receiptTrail eventTrail r) :
    OtherLoopRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.proof.step ha, h.exit.step ha⟩

theorem prepend {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st recSt out : SearchSt} {best mid outBest : Option Key}
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
  ⟨h.proof.prepend hfixed hcoset hpre, h.exit.prepend hpre⟩

/-- Compose an ordinary non-guiding child with the recursively proved
tail of an off-path sweep. -/
theorem next {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv1
      tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st child recSt out : SearchSt}
    {best mid outBest : Option Key} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : nextElem tcell cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = false)
    (hother : (tv == tv1) = false)
    (hrecover : recSt = recover ctx.n inf level
      { child with fixedpts := erase child.fixedpts tv })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (hloop : otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (nextElem tcell (some tv)) tcell recSt = (r, out))
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
theorem nextLong {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      filtered tv1 tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st child recSt out : SearchSt}
    {best mid outBest : Option Key} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : nextElem tcell cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = false)
    (hfirst : (tv == tv1) = true)
    (hfiltered : filtered = longprune tcell
      (erase child.fixedpts tv) child.autos)
    (hrecover : recSt = recover ctx.n inf level
      { child with fixedpts := erase child.fixedpts tv })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (hloop : otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (nextElem filtered (some tv)) filtered recSt = (r, out))
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
theorem nextShort {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      filtered tv1 tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st child recSt out : SearchSt}
    {best mid outBest : Option Key} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : nextElem tcell cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = true)
    (hother : (tv == tv1) = false)
    (hfiltered : filtered = shortprune tcell
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hrecover : recSt = recover ctx.n inf level
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (hloop : otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (nextElem filtered (some tv)) filtered recSt = (r, out))
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
theorem nextBoth {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      shortSet filtered tv1 tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st child recSt out : SearchSt}
    {best mid outBest : Option Key} {value : Int}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hnext : nextElem tcell cursor = some tv)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv } = (value, child))
    (hstay : ¬(value < Int.ofNat level))
    (hshort : child.needshortprune = true)
    (hfirst : (tv == tv1) = true)
    (hshortSet : shortSet = shortprune tcell
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hfiltered : filtered = longprune shortSet
      (erase child.fixedpts tv) child.autos)
    (hrecover : recSt = recover ctx.n inf level
      { child with
        fixedpts := erase child.fixedpts tv
        needshortprune := false })
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hcoset : recSt.cosetindex = st.cosetindex)
    (hpre : LoopSound ctx bound best mid)
    (hloop : otherChildLoop ctx inf tcLevel runFuel loopFuel level numcells
      tc tv1 (nextElem filtered (some tv)) filtered recSt = (r, out))
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

/-- Package an already established frozen early return as a corrected
off-path loop result. -/
theorem frozen {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv
      tv1 : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best outBest : Option Key} {trail eventTrail : FrameTrail}
    {value : Int}
    (hstate : otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
      numcells tc tv1 (some tv) tcell st = (some value, out))
    (hevent : EventOut G ctx tcLevel stem fs out outBest eventTrail value)
    (hpreserved : TrailExt level trail eventTrail)
    (hfixed : out.fixedpts = st.fixedpts)
    (hcoset : out.cosetindex = st.cosetindex)
    (hbelow : value < Int.ofNat level)
    (hexact : outBest = some (incMax best bound))
    (hfreeze : FrozenOut ctx codes out outBest value) :
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
  refine ⟨?_, LoopExit.frozen value rfl hbelow hexact hfreeze⟩
  exact {
    loop := {
      outcome := {
        receipt := .pruned value rfl hbelow (LoopSound.ofExact hexact)
          hinstalled hevent.read hexact
        event := by simpa only [loopReturn] using hevent
        preserved := hpreserved }
      fixed := hfixed }
    coset := hcoset }

/-- Package an already established cheap-cell jump as a corrected
off-path loop result. -/
theorem cheap {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv
      tv1 boundary : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best outBest : Option Key} {trail eventTrail : FrameTrail}
    (hstate : otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
      numcells tc tv1 (some tv) tcell st =
        (some (Int.ofNat boundary - 1), out))
    (hevent : EventOut G ctx tcLevel stem fs out outBest eventTrail
      (Int.ofNat boundary - 1))
    (hpreserved : TrailExt level trail eventTrail)
    (hfixed : out.fixedpts = st.fixedpts)
    (hcoset : out.cosetindex = st.cosetindex)
    (hpositive : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hexact : outBest = some (incMax best bound)) :
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
  refine ⟨?_, LoopExit.cheap boundary rfl hpositive hbelow hexact⟩
  exact {
    loop := {
      outcome := {
        receipt := .pruned (Int.ofNat boundary - 1) rfl hvalue
          (LoopSound.ofExact hexact) hinstalled hevent.read hexact
        event := by simpa only [loopReturn] using hevent
        preserved := hpreserved }
      fixed := hfixed }
    coset := hcoset }

/-- A generator unwind addressed strictly above this loop crosses the
temporary fixed-vertex cleanup and returns immediately. -/
theorem unwind {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv
      tv1 target offset : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st : SearchSt}
    {best outBest : Option Key} {trail eventTrail : FrameTrail}
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }
      (numcells + 1)) bound)
    (hreturn : (otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }).1 = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := insert st.fixedpts tv }).2 outBest)
    (hloc : payload.Located (trail.push level
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩))
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv }
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := insert st.fixedpts tv }).2
      (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail
      (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := insert st.fixedpts tv }).1)
    (hfresh : elem st.fixedpts tv = false) :
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
      lab := (breakout st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := insert st.fixedpts tv }
  let cleaned : SearchSt :=
    { node.2 with fixedpts := erase node.2.fixedpts tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change erase node.2.fixedpts tv = st.fixedpts
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
      hlocParent.setFixed (erase node.2.fixedpts tv)
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
  refine ⟨hproof, ?_⟩
  rw [hstate, hreturn]
  exact LoopExit.unwind target rfl hbelow (LoopSound.ofNode hsound hkey)
    payload' hloc'

/-- Zero cursor fuel is retained as exhaustion, never mistaken for a
completed sibling sweep. -/
theorem zero {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel level numcells tc len tcell tv1 : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tv? cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail)
    (hcursor : ∀ v, cursor = some v → v < ctx.n) :
    OtherLoopRun G ctx tcLevel specFuel runFuel 0 level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).1 := by
  refine ⟨OtherLoopProof.zero hpath hstem hpast hnp hinv hlive hcursor,
    ?_⟩
  apply LoopExit.exhausted (finalCursor := cursor)
  · unfold otherChildLoop
    rfl
  · omega
  · exact hcursor

/-- A positive-fuel loop with no next vertex has genuinely covered the
fixed original target cell and returns its exact maximum. -/
theorem done {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 tail : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : nextElem tcell cursor = none)
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
  refine ⟨hproof, LoopExit.done ?_ hexact⟩
  unfold otherChildLoop
  rfl

end OtherLoopRun

end Hex.GraphIso.Nauty
