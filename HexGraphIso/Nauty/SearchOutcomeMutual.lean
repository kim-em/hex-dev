/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexGraphIso.Nauty.SearchOutcomeResult

public section

/-!
The live hypotheses shared by the corrected mutual search induction.

These clauses deliberately describe a state at which search may continue.
GCA ordering is not a result-side invariant: the first-child loop raises
`gcaFirst` before an early unwind, so a returned state need not satisfy it.
-/

namespace Hex.GraphIso.Nauty

/-- Reference history, ordered live guides, and stabilization of every
ancestor frame to which the current node may return. -/
structure Live (ctx : Ctx) (level : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop where
  history : RefTrail ctx level st trail
  order : st.gcaFirst ≤ st.gcaCanon
  stable : ReturnStab trail (Int.ofNat st.gcaFirst) st

namespace Live

/-- `Live` depends only on the two reference controls and labellings and
on the recorded-generator store. -/
theorem stateEq {ctx : Ctx} {level : Nat} {st st' : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail)
    (hfirstGca : st'.gcaFirst = st.gcaFirst)
    (hfirst : st'.firstlab = st.firstlab)
    (hcanonGca : st'.gcaCanon = st.gcaCanon)
    (hcanon : st'.canonlab = st.canonlab)
    (hgen : st'.genTrace = st.genTrace) :
    Live ctx level st' trail := by
  constructor
  · exact h.history.stateEq hfirstGca hfirst hcanonGca hcanon
  · rw [hfirstGca, hcanonGca]
    exact h.order
  · rw [hfirstGca]
    exact h.stable.ofGenTraceEq hgen

/-- Target-cell accounting changes no live field. -/
theorem setTctotal {ctx : Ctx} {level value : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with tctotal := value } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Parking the cheap-automorphism boundary changes no live field. -/
theorem park {ctx : Ctx} {level boundary : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with noncheaplevel := boundary } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Fixed-point cleanup changes no live field. -/
theorem setFixed {ctx : Ctx} {level fixedpts : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with fixedpts := fixedpts } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Clearing the one-shot short-prune flag changes no live field. -/
theorem clearShort {ctx : Ctx} {level : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with needshortprune := false } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Refinement and the off-path comparison step preserve the complete live
package. -/
theorem otherLeaf {ctx : Ctx} {level numcells : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level (otherLeafSt ctx level numcells st) trail :=
  ⟨h.history.otherLeaf, RefTrail.otherLeaf_order h.order, by
    simpa only [RefTrail.otherLeaf_gcaFirst] using h.stable.otherLeaf⟩

/-- A leaf event preserves reference history and live GCA ordering.  Its
return-indexed generator stabilization is supplied separately by the
admission classifier. -/
theorem processnode {ctx : Ctx} {level numcells : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail)
    (htrail : TrailOk ctx level st trail) (hfirst : st.gcaFirst ≤ level) :
    RefTrail ctx level (Nauty.processnode ctx level numcells st).2 trail ∧
      (Nauty.processnode ctx level numcells st).2.gcaFirst ≤
        (Nauty.processnode ctx level numcells st).2.gcaCanon :=
  ⟨h.history.processnode htrail,
    RefTrail.processnode_order h.order hfirst⟩

end Live

/-- The live state of an off-path sweep.  `gcaFirst` stays strictly above
the divergence ancestor, so a child push introduces no new stabilization
obligation at the current frame. -/
structure OtherLive (ctx : Ctx) (level : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop extends Live ctx level st trail where
  firstBelow : st.gcaFirst < level

/-- The live state of a first-path sweep.  Once generators exist, the
guiding child has already been absorbed, and every recorded generator
stabilizes this frozen frame; before that point the store is empty and the
same clause is vacuous. -/
structure FirstLive (ctx : Ctx) (level : Nat) (st : SearchSt)
    (trail : FrameTrail) (rsLab rsPtn : Array Nat) : Prop
    extends Live ctx level st trail where
  frameStab : ∀ γ ∈ st.genTrace.toList,
    CellStab rsPtn level rsLab γ

namespace OtherOutcome

/-- Cleaning and recovering a completed off-path child reconstructs both
the parent's stable run invariant and its off-path live package. -/
theorem recover {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel childNumcells numcells level inf fixedpts : Nat}
    {codes fs : List Nat} {child out : SearchSt}
    {best outBest : Option Key} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      child out childNumcells best outBest receiptTrail eventTrail r)
    (hreturn : r = Int.ofNat level) (hpath : codes.length = level)
    (hlevel : 1 ≤ level) (hinf : level < inf)
    (hfirst : child.gcaFirst < level)
    (hok : SearchOk G level numcells
      (Nauty.recover ctx.n inf level { out with fixedpts := fixedpts })) :
    ∃ bs,
      RunInv G ctx tcLevel level codes bs fs numcells
          (Nauty.recover ctx.n inf level { out with fixedpts := fixedpts })
          outBest eventTrail ∧
        OtherLive ctx level
          (Nauty.recover ctx.n inf level { out with fixedpts := fixedpts })
          eventTrail := by
  have hfirstOut : out.gcaFirst < level := by
    rw [h.firstGuide]
    exact hfirst
  have hfirstClean : ({ out with fixedpts := fixedpts } : SearchSt).gcaFirst ≤
      level := Nat.le_of_lt hfirstOut
  obtain ⟨bs, hrun, hstable, hhistory⟩ :=
    h.node.event.setFixed fixedpts |>.recoverRun hreturn hpath hlevel hinf
      hfirstClean hok
  refine ⟨bs, hrun, ?_⟩
  constructor
  · constructor
    · exact hhistory
    · exact RefTrail.recover_order (by simpa only using h.order)
        hfirstClean
    · exact hstable
  · rw [(recover_frames ctx.n inf level
      { out with fixedpts := fixedpts }).2.2.2.2.2.2.1]
    exact hfirstOut

end OtherOutcome

/-- The bookkeeping between an off-path node's refinement and its fresh
child sweep preserves the live package and the strict first-reference
bound. -/
theorem NodeInv.otherLive {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells len : Nat} {codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    let pre := otherLeafSt ctx level numcells st
    let base : SearchSt := { pre with tctotal := pre.tctotal + len }
    let start := if cheapautom base.ptn level ctx.n then base
      else { base with noncheaplevel := level + 1 }
    OtherLive ctx level start trail := by
  dsimp only
  let pre := otherLeafSt ctx level numcells st
  let base : SearchSt := { pre with tctotal := pre.tctotal + len }
  have hpre : Live ctx level pre trail := by
    simpa only [pre] using hlive.otherLeaf (numcells := numcells)
  have hbase : Live ctx level base trail := by
    simpa only [base] using hpre.setTctotal (value := pre.tctotal + len)
  have hbelow : base.gcaFirst < level := by
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [RefTrail.otherLeaf_gcaFirst]
    exact hnode.firstBelow
  split
  · exact ⟨hbase, hbelow⟩
  · exact ⟨hbase.park, hbelow⟩

/-- A loop child inherits reference history and stabilization through its
live first-reference GCA.  The current frozen frame is required only when
that GCA is exactly the loop level. -/
theorem LoopInv.childLive {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) (offset currentOffset : Nat)
    (hframe : st.gcaFirst = level → ∀ γ ∈ st.genTrace.toList,
      CellStab rsPtn level rsLab γ) :
    Live ctx (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]!
        cosetindex := coset }
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) := by
  let entry : TrailEntry :=
    ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
  have hstable : ReturnStab (trail.push level entry)
      (Int.ofNat st.gcaFirst) st := by
    apply hlive.stable.push
    intro hle γ hγ
    have hbound := hinv.run.firstBound
    have heq := Nat.le_antisymm hbound (Int.ofNat_le.mp hle)
    exact hframe heq γ hγ
  constructor
  · simpa only [entry] using
      RefTrail.LoopInv.childHistory hinv hlive.history offset currentOffset
  · simpa only using hlive.order
  · unfold ReturnStab at hstable ⊢
    exact hstable

/-- An off-path loop's strict first-reference bound discharges the only
new-frame premise of `childLive`. -/
theorem LoopInv.otherChildLive {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail) (offset currentOffset : Nat) :
    Live ctx (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) := by
  apply hinv.childLive hlive.toLive offset currentOffset
  intro heq
  exact (Nat.ne_of_lt hlive.firstBelow heq).elim

/-- A first-path loop carries stabilization of its frozen frame directly,
including the initial empty-store phase. -/
theorem LoopInv.firstChildLive {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : FirstLive ctx level st trail rsLab rsPtn)
    (offset currentOffset : Nat) :
    Live ctx (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]!
        cosetindex := coset }
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) :=
  hinv.childLive hlive.toLive offset currentOffset fun _ => hlive.frameStab

/-- A non-first leaf event whose branch does not append a generator
produces the complete result-side package.  The caller supplies the strict
return bound because `processnode` itself also has a non-unwinding result
at the current level. -/
theorem RunPrep.leafEvent {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hreturn : (processnode ctx level numcells st).1 ≤
      Int.ofNat level - 1)
    (hgen : (processnode ctx level numcells st).2.genTrace = st.genTrace)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ bs',
      EventOut G ctx tcLevel stem fs
          (processnode ctx level numcells st).2
          (some (incKey ctx bs'
            (processnode ctx level numcells st).2.canonlab)) trail
          (processnode ctx level numcells st).1 ∧
        incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
          keyMax (incKey ctx bs st.canonlab)
            (pathLeafKey ctx codes st.lab) := by
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf hn hn0 hgb hsymm hloop
    hlevel hpath hbound hef hnc
  refine ⟨bs', ?_, hmax⟩
  apply EventOut.intro level codes bs' hevent hpath hstem hpast
  · omega
  · have hs := hlive.stable.ofGenTraceEq hgen
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A code-one admission with a nonpositive incumbent comparison is a
fully verified generator event.  The semantic loop proof supplies the
nonpositivity premise from coverage of the guiding child. -/
theorem RunPrep.firstEvent {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbelow : st.gcaFirst < level) (hnp : st.compCanon ≤ 0)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == ctx.n) = true)
    (hpass : isautom ctx
      (firstScatter ctx.n st.firstlab st.lab) = true)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    EventOut G ctx tcLevel stem fs
      (processnode ctx level numcells st).2 best trail
      (processnode ctx level numcells st).1 := by
  obtain ⟨hreturn, hcomp, heqCanon, hcode, hcanonlevel, hcanonlab,
      hcanong, hsamerows⟩ := processnode_auto heq hsent hnc hpass
  have hframes := processnode_frames ctx level numcells st
  have hgcaCanon := processnode_auto_gcaCanon heq hsent hnc hpass
  have hevent : RunEvent G ctx tcLevel level codes bs fs
      (processnode ctx level numcells st).2 best trail := by
    refine ⟨Or.inl ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, hprep.bestCodes, ?_⟩
    · rw [hcomp]
      exact hnp
    · rw [hcomp, heqCanon, hcode, hcanonlevel]
      exact hprep.codeInv
    · rw [hframes.2.2.1, hframes.2.2.2.1]
      exact hprep.firstInv
    · rw [hcanong, hcanonlab, hsamerows]
      exact hprep.canongInv
    · exact hprep.leafRefs.processnodeGen hn hn0 hgb hsymm hloop
        hprep.searchOk hprep.canongInv hprep.genTraceOk
    · exact hprep.autosOk.processnodeAuto hn hn0 hgb hsymm hloop
        hprep.searchOk hprep.leafRefs heq hsent hnc hpass
    · exact hprep.cheap.processnode
    · exact hprep.leafRefs.processnode hprep.searchOk
    · apply hprep.guides.processnode (IncGrows.refl best)
        hframes.2.2.2.2.2.2.1 hframes.2.2.2.2.1
      intro _
      exact ⟨hgcaCanon, hcanonlab⟩
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
  · rw [hreturn]
    exact Int.ofNat_le.mpr (Nat.le_of_lt hbelow)
  · have hs := hlive.history.processnodeFirstStab hn hn0
      hprep.trailOk hprep.leafRefs hlive.stable hbelow heq hsent hnc hpass
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A code-two row tie produces a verified event for either its canonical
return or its special first-ancestor orbit return. -/
theorem RunPrep.tiedEvent {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true) (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0)
    (hcanonBelow : st.gcaCanon < level)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ bs',
      EventOut G ctx tcLevel stem fs
          (processnode ctx level numcells st).2
          (some (incKey ctx bs'
            (processnode ctx level numcells st).2.canonlab)) trail
          (processnode ctx level numcells st).1 ∧
        incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
          keyMax (incKey ctx bs st.canonlab)
            (pathLeafKey ctx codes st.lab) ∧
        some (incKey ctx bs'
          (processnode ctx level numcells st).2.canonlab) = best := by
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf hn hn0 hgb hsymm hloop
    hlevel hpath hbound hef hnc
  have hcinv : CodeCmpInv n codes bs st.canoncode st.canonlevel
      st.eqlevCanon 0 := by
    simpa only [hcc] using hprep.codeInv
  have hlen : codes.length = bs.length := by
    have hle := codeInv_tied_le hcinv
    have hblen := hcinv.blen
    omega
  have hcodes : codes = bs := codeInv_eq_of_tied hcinv hlen
  have hrows : leafRows ctx st.canonlab = leafRows ctx st.lab :=
    rows_eq_of_testcanlab_tie hprep.canongInv htie
  have hkey : pathLeafKey ctx codes st.lab =
      incKey ctx bs st.canonlab := by
    unfold pathLeafKey incKey
    rw [hcodes, ← hrows]
  have houtBest : some (incKey ctx bs'
      (processnode ctx level numcells st).2.canonlab) = best := by
    rw [hmax, hkey, keyMax_eq_left (keyLe_refl _)]
    exact hprep.incumbent.symm
  have hreturns := (processnode_rowTie hef hnc hcc hge htie).1
  have hreturned : (processnode ctx level numcells st).1 ≤
      Int.ofNat level := by
    rcases hreturns with hfirst | hcanon
    · rw [hfirst]
      exact Int.ofNat_le.mpr
        (Nat.le_trans hlive.order hprep.canonBound)
    · rw [hcanon]
      exact Int.ofNat_le.mpr hprep.canonBound
  refine ⟨bs', ?_, hmax, houtBest⟩
  apply EventOut.intro level codes bs' hevent hpath hstem hpast hreturned
  · have hs := hlive.history.processnodeTiedStab hn hn0 hprep.trailOk
      hprep.leafRefs hlive.order hlive.stable hcanonBelow hef hnc hcc hge
      htie
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A discrete code-one branch closes the complete node outcome.  Its
guide supplies the located unwind receipt, while `firstEvent` supplies
the result-state invariants. -/
theorem NodeInv.firstLeaf {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hnp : (otherLeafSt ctx level numcells st).compCanon ≤ 0)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true)
    (hsent : (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
      codeSentinel)
    (hpass : isautom ctx (firstScatter ctx.n
      (otherLeafSt ctx level numcells st).firstlab
      (otherLeafSt ctx level numcells st).lab) = true)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  subst n
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs ctx.n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf rfl hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hbelow : leaf.gcaFirst < level := by
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [RefTrail.otherLeaf_gcaFirst]
    exact hnode.firstBelow
  have hevent : EventOut G ctx tcLevel codes fs
      (processnode ctx level ctx.n leaf).2 best trail
      (processnode ctx level ctx.n leaf).1 := by
    apply hprep.firstEvent rfl hn0 hgb hsymm hloop hfull hstem (by omega)
      hbelow hnp
      heq hsent (by simp) hpass hlive'
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    apply otherNode_leaf_firstReceipt hnum hprep.guides hprep.trailOk
      hprep.firstPositive hbelow hgsz hprep.leafRefs.firstSize
      (isPerm_of_cellsReach hprep.leafRefs.firstSize hn0
        hprep.leafRefs.firstReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach)
      hsymm hloop hgb heq hsent hpass
  have hreturn := (processnode_auto (ctx := ctx) (level := level)
    (numcells := ctx.n) (st := leaf) heq hsent (by simp) hpass).1
  have hearly : (processnode ctx level ctx.n leaf).1 <
      Int.ofNat level := by
    rw [hreturn]
    exact Int.ofNat_lt.mpr hbelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  constructor
  · exact hreceipt
  · rw [hout]
    exact hevent
  · exact TrailExt.refl level trail

/-- A discrete code-two row tie closes the complete node outcome for both
the canonical-guide and first-ancestor orbit return arms. -/
theorem NodeInv.tiedLeaf {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hcc : (otherLeafSt ctx level numcells st).compCanon = 0)
    (hge : ¬(level < (otherLeafSt ctx level numcells st).canonlevel))
    (htie : (testcanlab ctx (updatecan ctx
      (otherLeafSt ctx level numcells st).canong
      (otherLeafSt ctx level numcells st).canonlab
      (otherLeafSt ctx level numcells st).samerows)
      (otherLeafSt ctx level numcells st).lab).1 = 0)
    (hcoset : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.cosetindex < ctx.n)
    (horbit : OrbSound (OrbConn (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.genTrace.toList ctx.n)
      (processnode ctx level ctx.n
        (otherLeafSt ctx level numcells st)).2.orbits ctx.n)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  subst n
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs ctx.n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf rfl hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcanonBelow : leaf.gcaCanon < level := by
    change (otherLeafSt ctx level numcells st).gcaCanon < level
    rw [RefTrail.otherLeaf_gcaCanon]
    exact hnode.canonBelow
  have hfirstBelow : leaf.gcaFirst < level :=
    Nat.lt_of_le_of_lt hlive'.order hcanonBelow
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨bs', hevent, -, houtBest⟩ := hprep.tiedEvent rfl hn0 hgb
    hsymm hloop hlevel hfull hstem (by omega) hcheap' hef (by simp) hcc hge
    htie hcanonBelow hlive'
  rw [houtBest] at hevent
  have hrows : leafRows ctx leaf.canonlab = leafRows ctx leaf.lab :=
    rows_eq_of_testcanlab_tie hprep.canongInv htie
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    apply otherNode_leaf_tiedReceipt hnum hprep.guides hprep.trailOk
      hprep.canonPositive hcanonBelow hgsz hprep.leafRefs.canonSize
      (isPerm_of_cellsReach hprep.leafRefs.canonSize hn0
        hprep.leafRefs.canonReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach)
      hgb hrows hef hcc hge htie hprep.firstPositive hfirstBelow hcoset
      horbit
  have hreturns := (processnode_rowTie (ctx := ctx) (level := level)
    (numcells := ctx.n) (st := leaf) hef (by simp) hcc hge htie).1
  have hearly : (processnode ctx level ctx.n leaf).1 <
      Int.ofNat level := by
    rcases hreturns with hfirst | hcanon
    · rw [hfirst]
      exact Int.ofNat_lt.mpr hfirstBelow
    · rw [hcanon]
      exact Int.ofNat_lt.mpr hcanonBelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  constructor
  · exact hreceipt
  · rw [hout]
    exact hevent
  · exact TrailExt.refl level trail

/-- An early non-generator leaf absorbs its singleton subtree and returns
the explicit local-prune outcome. -/
theorem NodeInv.plainLeaf {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hgen : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hearly : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  subst n
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs ctx.n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf rfl hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  have hreturn : (processnode ctx level ctx.n leaf).1 ≤
      Int.ofNat level - 1 := Int.le_sub_one_iff.mpr hearly
  obtain ⟨bs', hevent, hmax⟩ := hprep.leafEvent rfl hn0 hgb hsymm
    hloop hlevel hfull hstem (by omega) hcheap' hef (by simp) hreturn hgen
    hlive'
  let outKey := incKey ctx bs'
    (processnode ctx level ctx.n leaf).2.canonlab
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    simpa only [leaf, otherLeafSt, rs, base] using
      (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hnodeKey : nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells = pathLeafKey ctx full leaf.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey, hleafLab]
  have houtFull : some outKey = some (incMax best
      (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
    rw [hprep.incumbent, incMax, hnodeKey]
    exact congrArg some hmax
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (processnode ctx level ctx.n leaf).2 numcells best (some outKey)
      (processnode ctx level ctx.n leaf).1 := by
    apply NodeReceipt.pruned (NodeSound.ofExact houtFull)
      (processnode ctx level ctx.n leaf).1 rfl hearly
    · apply processnode_installed hlevel
      apply Nat.ne_of_gt
      rw [hprep.codeInv.blen]
      cases bs with
      | nil => exact (hprep.bestCodes rfl).elim
      | cons _ _ => simp
    · simpa only [outKey] using hevent.read
    · exact houtFull
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  refine ⟨some outKey, ?_⟩
  constructor
  · rw [hout]
    exact hreceipt
  · rw [hout]
    exact hevent
  · exact TrailExt.refl level trail

/-- A non-generator leaf that does not unwind completes after the empty
child sweep and returns the exact singleton-subtree maximum. -/
theorem NodeInv.plainLeafDone {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hgen : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hdone : ¬((processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  subst n
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs ctx.n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf rfl hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf rfl hn0 hgb hsymm
    hloop hlevel hfull hcheap' hef (by simp)
  let outKey := incKey ctx bs'
    (processnode ctx level ctx.n leaf).2.canonlab
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    simpa only [leaf, otherLeafSt, rs, base] using
      (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hnodeKey : nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells = pathLeafKey ctx full leaf.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey, hleafLab]
  have houtFull : some outKey = some (incMax best
      (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
    rw [hprep.incumbent, incMax, hnodeKey]
    exact congrArg some hmax
  let final := leafFinish ctx level
    (processnode ctx level ctx.n leaf).2
  have hread : stInc ctx final = some outKey := by
    change stInc ctx (leafFinish ctx level
      (processnode ctx level ctx.n leaf).2) = some outKey
    rw [stInc_leafFinish]
    simpa only [outKey] using hevent.read
  have hfinalEvent : EventOut G ctx tcLevel codes fs final
      (some outKey) trail (Int.ofNat level - 1) := by
    apply EventOut.intro level full bs' hevent.leafFinish hfull hstem
      (by omega)
    · omega
    · have hs := ReturnStab.leafFinish (ctx := ctx) (level := level)
        (hlive'.stable.ofGenTraceEq hgen)
      have hfirst : final.gcaFirst = leaf.gcaFirst := by
        unfold final Nauty.leafFinish
        split <;> simp only <;> split <;>
          exact (processnode_frames ctx level ctx.n leaf).2.2.2.2.2.2.1
      rw [hfirst]
      exact hs.lower (by omega)
    · exact (hlive'.history.processnode hprep.trailOk).leafFinish
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st final numcells best (some outKey)
      (Int.ofNat level - 1) := by
    apply NodeReceipt.complete (NodeSound.ofExact houtFull) rfl
    · exact canonlevel_ne_zero_of_stInc hread
    · exact hread
    · exact houtFull
  have hout := otherNode_leaf_done_state ctx inf tcLevel fuel level
    numcells st hnum hdone
  refine ⟨some outKey, ?_⟩
  constructor
  · rw [hout]
    exact hreceipt
  · rw [hout]
    exact hfinalEvent
  · exact TrailExt.refl level trail

/-! # Completed child sweeps -/

/-- An empty positive-fuel first-path sweep closes the coupled loop
outcome.  The comparison sign is explicit: a freshly prepared node may
enter its first child with sign one, whereas every state that reaches the
end of a real sweep has already absorbed a child and restored a
nonpositive sign. -/
theorem LoopInv.firstDone {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 index : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key}
    {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : nextElem tcell cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    LoopOutcome G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor
      bound
      st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell index st).1 := by
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st =
      some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  constructor
  · exact firstLoop_doneReceipt ctx inf tcLevel specFuel runFuel
      loopFuel level numcells tc tv1 codes rsLab rsPtn len tcell index
      cursor _ st best trail hinstalled hread hinv.cover hnext
  · simpa only [firstChildLoop, loopReturn] using
      (EventOut.ofRun hinv.run hpath hstem hpast (by omega) hnp
        (hlive.stable.lower (by omega)) hlive.history)
  · exact TrailExt.refl level trail

/-- An empty positive-fuel off-path sweep closes the coupled loop outcome
with the same frozen-frame coverage and result event. -/
theorem LoopInv.otherDone {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key}
    {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : nextElem tcell cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    LoopOutcome G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor
      bound
      st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell st).1 := by
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st =
      some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  constructor
  · exact otherLoop_doneReceipt ctx inf tcLevel specFuel runFuel
      loopFuel level numcells tc tv1 codes rsLab rsPtn len tcell cursor _
      st best trail hinstalled hread hinv.cover hnext
  · simpa only [otherChildLoop, loopReturn] using
      (EventOut.ofRun hinv.run hpath hstem hpast (by omega) hnp
        (hlive.stable.lower (by omega)) hlive.history)
  · exact TrailExt.refl level trail

end Hex.GraphIso.Nauty
