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
The first-path sibling sweep, part one: the state equations of one
iteration of `firstChildLoop`, the packaged sweep result `FirstSweepRun`,
and the constructors for early exits and for continuing after a child.

`FirstSweepRun` keeps the first leaf's history only below the loop level.
The library's `FirstLoopRun` additionally pins the frame entry at the loop
level to the guiding child, which an off-path child's event trail
contradicts, so that package is not used here.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}


/-! # State equations of one iteration -/

/-- A vertex that is not its orbit's representative is skipped. -/
theorem firstChildLoop_skip (ctx : Ctx)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv tcell index : Nat)
    (st : SearchSt) (horb : (st.orbits[tv]! == tv) = false) :
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem tcell (some tv)) tcell
        (if (st.orbits[tv]! == tv1) = true then index + 1 else index) st := by
  conv =>
    lhs
    unfold firstChildLoop
    simp only [horb, Bool.false_eq_true, ite_false, Id.run_pure,
      apply_ite Id.run]
  split <;> rfl

/-- An early off-path child return leaves the loop after cleaning the
temporary fixed vertex. -/
theorem firstChildLoop_earlyOther (ctx : Ctx)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv tcell index : Nat)
    (st : SearchSt) (value : Int) (out : SearchSt)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hearly : value < Int.ofNat level) :
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      (some value, index, { out with fixedpts := erase out.fixedpts tv }) := by
  unfold firstChildLoop
  simp only [hrep, ite_true, hother, Bool.false_eq_true, ite_false,
    Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_left hearly]

/-- An early guiding child return leaves the loop after installing the
first-path controls and cleaning the temporary fixed vertex. -/
theorem firstChildLoop_earlyGuide (ctx : Ctx)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv tcell index : Nat)
    (st : SearchSt) (value : Int) (out : SearchSt)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hearly : value < Int.ofNat level) :
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      (some value, index,
        { out with
          gcaFirst := level
          stabvertex := tv1
          fixedpts := erase out.fixedpts tv }) := by
  unfold firstChildLoop
  simp only [hrep, ite_true, hfirst, Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_left hearly]

/-- An off-path child that stays at the loop level continues with the
recursive tail on the recovered, possibly filtered, state. -/
theorem firstChildLoop_stayOther (ctx : Ctx)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv tcell index : Nat)
    (st : SearchSt) (value : Int) (out : SearchSt)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level) :
    let cleaned : SearchSt := { out with fixedpts := erase out.fixedpts tv }
    let cleared := clearShortIf cleaned.needshortprune cleaned
    let tcell' := if cleaned.needshortprune then shortprune tcell cleared
      else tcell
    let recSt := recover ctx.n inf level cleared
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem tcell' (some tv)) tcell'
        (if (recSt.orbits[tv]! == tv1) = true then index + 1 else index)
        recSt := by
  dsimp only
  conv =>
    lhs
    unfold firstChildLoop
    simp only [hrep, ite_true, hother, Bool.false_eq_true, ite_false,
      Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  unfold clearShortIf
  dsimp only
  split <;> split <;> rfl

/-- The guiding child that stays at the loop level continues with the
recursive tail on the recovered, possibly filtered, state carrying the
installed first-path controls. -/
theorem firstChildLoop_stayGuide (ctx : Ctx)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv tcell index : Nat)
    (st : SearchSt) (value : Int) (out : SearchSt)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level) :
    let cleaned : SearchSt :=
      { out with
        gcaFirst := level
        stabvertex := tv1
        fixedpts := erase out.fixedpts tv }
    let cleared := clearShortIf cleaned.needshortprune cleaned
    let tcell' := if cleaned.needshortprune then shortprune tcell cleared
      else tcell
    let recSt := recover ctx.n inf level cleared
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (nextElem tcell' (some tv)) tcell'
        (if (recSt.orbits[tv]! == tv1) = true then index + 1 else index)
        recSt := by
  dsimp only
  conv =>
    lhs
    unfold firstChildLoop
    simp only [hrep, ite_true, hfirst, Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_right hstay]
  unfold clearShortIf
  dsimp only
  split <;> split <;> rfl

/-! # The sweep package -/

/-- A first-path sibling sweep result: the established loop proof, the
corrected exit classification, the one-shot short-prune provenance, and
the first-leaf and canonical histories strictly below the loop level. -/
structure FirstSweepRun (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells tcell : Nat) (cursor : Option Nat) (bound : Key)
    (st out : SearchSt) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  proof : LoopProof G ctx tcLevel specFuel runFuel loopFuel level stem codes
    fs rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail eventTrail r
  exit : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
    rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail r
  short : out.needshortprune = true → ∃ value,
    r = some value ∧ ShortSource G ctx out eventTrail value
  trail : FirstTrail ctx level out eventTrail
  canonTrail : CanonTrail ctx level out eventTrail
  guideLevel : level ≤ out.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon

namespace FirstSweepRun

/-- Rebase the receipt trail onto any trail agreeing below the loop. -/
theorem retrail {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest source eventTrail r) :
    FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.proof.retrail htrail, h.exit.retrail htrail, h.short, h.trail,
    h.canonTrail, h.guideLevel, h.order⟩

/-- Prepending a sound fragment adjusts only the incoming incumbent. -/
theorem prepend {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st recSt out : SearchSt} {best mid outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hfixed : recSt.fixedpts = st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (h : FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.proof.prepend hfixed hpre, h.exit.prepend hpre, h.short, h.trail,
    h.canonTrail, h.guideLevel, h.order⟩

/-- Advancing the cursor by one visited vertex costs one unit of fuel. -/
theorem step {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out best
      outBest receiptTrail eventTrail r) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.proof.step ha, h.exit.step ha, h.short, h.trail, h.canonTrail,
    h.guideLevel, h.order⟩

/-- The recorded live set is bookkeeping only. -/
theorem reindexSet {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell tcell' : Nat} {cursor : Option Nat}
    {bound : Key} {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.proof.reindexSet, h.exit.reindexSet, h.short, h.trail, h.canonTrail,
    h.guideLevel, h.order⟩

/-- Zero cursor fuel is retained as exhaustion. -/
theorem zero {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel level numcells tc len tcell tv1 index : Nat}
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
    (hcursor : ∀ v, cursor = some v → v < ctx.n)
    (hfirst : FirstTrail ctx level st trail)
    (hcanon : CanonTrail ctx level st trail)
    (hguide : level ≤ st.gcaFirst) :
    FirstSweepRun G ctx tcLevel specFuel runFuel 0 level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).1 := by
  have hsame : (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc
      tv1 tv? tcell index st).2.2 = st := by
    unfold firstChildLoop
    rfl
  refine ⟨LoopInv.firstZero hpath hstem hpast hnp hinv hlive hcursor,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply LoopExit.exhausted (finalCursor := cursor)
    · unfold firstChildLoop
      rfl
    · omega
    · exact hcursor
  · intro hshort
    rw [hsame, hinv.shortClear] at hshort
    cases hshort
  · rw [hsame]
    exact hfirst
  · rw [hsame]
    exact hcanon
  · rw [hsame]
    exact hguide
  · rw [hsame]
    exact hlive.order

/-- A positive-fuel loop with no next vertex has covered the whole target
cell and returns its exact maximum. -/
theorem done {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 index tail : Nat}
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
    (hlive : Live ctx level st trail)
    (hfirst : FirstTrail ctx level st trail)
    (hcanon : CanonTrail ctx level st trail)
    (hguide : level ≤ st.gcaFirst) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).1 := by
  have hsame : (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
      numcells tc tv1 none tcell index st).2.2 = st := by
    unfold firstChildLoop
    rfl
  have hproof := LoopInv.firstDoneProof (inf := inf) (runFuel := runFuel)
    (loopFuel := loopFuel) (tv1 := tv1) (index := index) (bound := bound)
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
  refine ⟨hproof, LoopExit.done ?_ hexact, ?_, ?_, ?_, ?_, ?_⟩
  · unfold firstChildLoop
    rfl
  · intro hshort
    rw [hsame, hinv.shortClear] at hshort
    cases hshort
  · rw [hsame]
    exact hfirst
  · rw [hsame]
    exact hcanon
  · rw [hsame]
    exact hguide
  · rw [hsame]
    exact hlive.order

/-! ## Early exits of an off-path child -/

/-- A located unwind below the loop from an off-path child leaves the
sweep at once. -/
theorem childUnwind {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv
      tv1 index target offset : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt} {value : Int}
    {best outBest : Option Key} {trail eventTrail : FrameTrail}
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      (numcells + 1)) bound)
    (hreturn : value = Int.ofNat target)
    (hbelow : target < level)
    (payload : Unwind ctx tcLevel target out outBest)
    (hloc : payload.Located (trail.push level
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩))
    (hcontrol : target = out.gcaFirst ∨ target = out.gcaCanon)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail value)
    (hfresh : elem st.fixedpts tv = false)
    (htrail : FirstTrail ctx level { out with fixedpts := erase out.fixedpts tv }
      eventTrail)
    (hcanon : CanonTrail ctx level { out with fixedpts := erase out.fixedpts tv }
      eventTrail)
    (hguide : level ≤ st.gcaFirst) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let cleaned : SearchSt := { out with fixedpts := erase out.fixedpts tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change erase out.fixedpts tv = st.fixedpts
    rw [hchild.node.fixed]
    exact erase_insert_of_miss hfresh
  have hlt : value < Int.ofNat level := by
    rw [hreturn]
    exact Int.ofNat_lt.mpr hbelow
  have hstate : firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell index st =
      (some value, index, cleaned) :=
    firstChildLoop_earlyOther ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 tv tcell index st value out hrep hother hcall hlt
  have hlocParent : payload.Located trail :=
    hloc.retrail (FrameTrail.push_of_ne trail _ (by omega))
  obtain ⟨payload', hloc'⟩ :
      ∃ payload' : Unwind ctx tcLevel target cleaned outBest,
        payload'.Located trail := by
    simpa only [cleaned] using
      hlocParent.setFixed (erase out.fixedpts tv)
  obtain ⟨payloadN, hlocN⟩ :
      ∃ payloadN : Unwind ctx tcLevel target
        (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
          { st with
            lab := (breakout st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := insert st.fixedpts tv
            cosetindex := tv }).2 outBest,
        payloadN.Located trail := by
    rw [hcall]
    exact ⟨payload, hlocParent⟩
  have hreceipt := firstLoop_otherReceipt ctx inf tcLevel specFuel runFuel
    loopFuel level numcells tc tv1 tv codes rsLab rsPtn len tcell index
    cursor bound st best outBest target trail hrep hother hsound hkey
    (by rw [hcall]; exact hreturn) hbelow payloadN hlocN
  have hevent : EventOut G ctx tcLevel stem fs cleaned outBest eventTrail
      value :=
    (hchild.node.event.ancestor hstem hshorter).setFixed _
  refine ⟨⟨⟨hreceipt, ?_, hchild.node.preserved.ofPush⟩, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hstate]
    simpa only [loopReturn] using hevent
  · rw [hstate]
    exact hfixed
  · rw [hstate, hreturn]
    exact LoopExit.unwind target rfl hbelow (LoopSound.ofNode hsound hkey)
      payload' hloc' (by simpa only [cleaned] using hcontrol)
  · intro hshort
    rw [hstate] at hshort ⊢
    refine ⟨value, rfl, ?_⟩
    apply ShortSource.setFixed
    apply hchild.node.short
    simpa only [cleaned] using hshort
  · rw [hstate]
    exact htrail
  · rw [hstate]
    exact hcanon
  · rw [hstate]
    change level ≤ out.gcaFirst
    rw [hchild.firstGuide]
    exact hguide
  · rw [hstate]
    exact hchild.order

/-- A comparison-frozen off-path child return below the loop absorbs the
whole sweep. -/
theorem childFrozen {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv1
      tv tail offset index : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best outBest : Option Key} {value : Int}
    {trail eventTrail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail value)
    (hbelow : value < Int.ofNat level)
    (hfreeze : FrozenOut ctx codes out outBest value)
    (hexactChild : outBest = some (incMax best
      (nodeKey ctx tcLevel specFuel (level + 1) codes
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := insert st.fixedpts tv
          cosetindex := tv }
        (numcells + 1))))
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
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
    (hfresh : elem st.fixedpts tv = false)
    (htrail : FirstTrail ctx level { out with fixedpts := erase out.fixedpts tv }
      eventTrail)
    (hcanon : CanonTrail ctx level { out with fixedpts := erase out.fixedpts tv }
      eventTrail)
    (hguide : level ≤ st.gcaFirst) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let cleaned : SearchSt := { out with fixedpts := erase out.fixedpts tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change erase out.fixedpts tv = st.fixedpts
    rw [hchild.node.fixed, erase_insert_of_miss hfresh]
  have hstate : firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell index st =
      (some value, index, cleaned) :=
    firstChildLoop_earlyOther ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 tv tcell index st value out hrep hother hcall hbelow
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
  refine ⟨⟨⟨.pruned value rfl hbelow (LoopSound.ofExact hexact) hinstalled
    hevent.read hexact, by simpa only [loopReturn] using hevent,
    hchild.node.preserved.ofPush⟩, hfixed⟩,
    LoopExit.frozen value rfl hbelow hexact (hfreeze.setFixed _), ?_,
    htrail, hcanon, ?_, hchild.order⟩
  · intro hshort
    refine ⟨value, rfl, ?_⟩
    apply ShortSource.setFixed
    apply hchild.node.short
    simpa only [cleaned] using hshort
  · change level ≤ out.gcaFirst
    rw [hchild.firstGuide]
    exact hguide

/-- A saved cheap-boundary off-path child return below the loop absorbs
the whole verified small-cell sweep. -/
theorem childCheap {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv1
      tv boundary offset index : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound childKey : Key} {st out : SearchSt}
    {best outBest : Option Key} {trail eventTrail : FrameTrail}
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } =
        (Int.ofNat boundary - 1, out))
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail (Int.ofNat boundary - 1))
    (hpositive : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hsaved : out.noncheaplevel = boundary)
    (hbound : bound = childKey)
    (hexact : outBest = some (incMax best childKey))
    (hfresh : elem st.fixedpts tv = false)
    (htrail : FirstTrail ctx level { out with fixedpts := erase out.fixedpts tv }
      eventTrail)
    (hcanon : CanonTrail ctx level { out with fixedpts := erase out.fixedpts tv }
      eventTrail)
    (hguide : level ≤ st.gcaFirst) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let value := Int.ofNat boundary - 1
  let cleaned : SearchSt := { out with fixedpts := erase out.fixedpts tv }
  have hvalue : value < Int.ofNat level := by
    simp only [value, Int.ofNat_eq_natCast]
    omega
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change erase out.fixedpts tv = st.fixedpts
    rw [hchild.node.fixed, erase_insert_of_miss hfresh]
  have hstate : firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell index st =
      (some value, index, cleaned) :=
    firstChildLoop_earlyOther ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 tv tcell index st value out hrep hother hcall hvalue
  have hevent : EventOut G ctx tcLevel stem fs cleaned outBest eventTrail
      value :=
    (hchild.node.event.ancestor hstem hshorter).setFixed _
  have hexactBound : outBest = some (incMax best bound) := by
    rwa [hbound]
  have hinstalled : cleaned.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc (hevent.read.trans hexactBound)
  rw [hstate]
  refine ⟨⟨⟨.pruned value rfl hvalue (LoopSound.ofExact hexactBound)
    hinstalled hevent.read hexactBound,
    by simpa only [loopReturn] using hevent,
    hchild.node.preserved.ofPush⟩, hfixed⟩,
    LoopExit.cheap boundary rfl hpositive hbelow
      (by simpa only [cleaned] using hsaved) hexactBound, ?_,
    htrail, hcanon, ?_, hchild.order⟩
  · intro hshort
    refine ⟨value, rfl, ?_⟩
    apply ShortSource.setFixed
    apply hchild.node.short
    simpa only [cleaned, value] using hshort
  · change level ≤ out.gcaFirst
    rw [hchild.firstGuide]
    exact hguide

end FirstSweepRun

/-! ## The guiding child -/

/-- The first-path controls do not affect a short-prune source. -/
theorem ShortSource.setFirst {G : Colored n k} {ctx : Ctx} {out : SearchSt}
    {trail : FrameTrail} {r : Int} (h : ShortSource G ctx out trail r)
    (gcaFirst stabvertex : Nat) :
    ShortSource G ctx { out with gcaFirst := gcaFirst, stabvertex := stabvertex }
      trail r := by
  cases h with
  | explicit target fix mcr returned back valid =>
      exact .explicit target fix mcr returned back valid
  | implicit target returned below back root =>
      exact .implicit target returned below back root

/-- Installing the first-path controls after a guiding child that returned
below its parent loop: the fully covered child supplies the guide. -/
theorem FirstRun.markEvent {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells tc len offset tv1 : Nat}
    {cs fs : List Nat} {rsLab rsPtn : Array Nat}
    {child out : SearchSt} {outBest : Option Key}
    {trail eventTrail : FrameTrail} {r : Int}
    (hn : ctx.n = n) (hpath : cs.length = level)
    (hreturn : r < Int.ofNat level) (hgca : level + 1 ≤ out.gcaFirst)
    (h : FirstRun G ctx tcLevel specFuel runFuel (level + 1) cs fs child
      out (numcells + 1) outBest
      (trail.push level
        ⟨sweepFrame specFuel cs rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hdone : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells outBest offset)
    (hlevel : 1 ≤ level) (hls : rsLab.size = ctx.n)
    (hlab : LabOk rsLab ctx.n) (hps : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hcell : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hoff : offset < len) (hfuel : level + 1 + specFuel ≤ ctx.n + 1) :
    EventOut G ctx tcLevel cs fs
      { out with gcaFirst := level, stabvertex := tv1 }
      outBest eventTrail r := by
  let entry : TrailEntry :=
    ⟨sweepFrame specFuel cs rsLab rsPtn tc numcells, offset⟩
  have hentry : eventTrail level = some entry := by
    exact h.proof.node.outcome.preserved.pushAt
  have hreach : cellsPerm rsPtn level rsLab out.firstlab := by
    simpa only [entry, sweepFrame] using
      h.proof.trail.reach level entry (by omega) hentry
  obtain ⟨_, _, _, hat⟩ := h.proof.trail.picked level entry (by omega) hentry
  have hat' : out.firstlab[tc]! = rsLab[tc + offset]! := by
    simpa only [entry, sweepFrame] using hat
  cases hevent : h.proof.node.outcome.event with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      have hcurrent : level < current := by omega
      let g := Guide.ofSweep hlevel hdone hls hlab hps hend hvals hcell
        hrange hoff hfuel hat' (by rw [hn]; exact event.leafRefs.firstSize)
        hreach
      have hlocated : g.Located eventTrail := by
        refine ⟨entry, hentry, ?_⟩
        simp only [g, Guide.ofSweep, Guide.frame, entry, sweepFrame]
      have hguides : GuideStore ctx tcLevel current
          { out with gcaFirst := level, stabvertex := tv1 }
          outBest eventTrail := by
        constructor
        · intro hp hlt
          change 0 < level at hp
          change level < current at hlt
          exact ⟨g, rfl, hlocated⟩
        · intro hp hlt
          exact event.guides.canon hp hlt
      have event' := event.setFirst hguides (by omega) (by omega)
      have hhistory : RefTrail ctx current
          { out with gcaFirst := level, stabvertex := tv1 } eventTrail := by
        constructor
        · exact history.frameSize
        · intro target found htarget hbound hfound
          change target ≤ level at hbound
          exact h.proof.trail.reach target found (by omega) hfound
        · exact history.canon
      have hstable : ReturnStab eventTrail r
          { out with gcaFirst := level, stabvertex := tv1 } := by
        have hmin : min r (Int.ofNat out.gcaFirst) = r := by
          apply Int.min_eq_left
          have := Int.ofNat_le.mpr hgca
          simp only [Int.ofNat_eq_natCast] at this hreturn ⊢
          omega
        rw [hmin] at stable
        exact stable.setFirst level tv1
      have hmin' : min r (Int.ofNat
          ({ out with gcaFirst := level, stabvertex := tv1 } : SearchSt).gcaFirst)
          = r := by
        change min r (Int.ofNat level) = r
        exact Int.min_eq_left (Int.le_of_lt hreturn)
      exact .intro current codes bestCodes event' depth stemEq past returned
        (by rw [hmin']; exact hstable) hhistory

namespace FirstSweepRun

/-- A comparison-frozen guiding child return below the loop absorbs the
whole sweep. -/
theorem guideFrozen {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv1
      tv tail offset index : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {outBest : Option Key} {value : Int}
    {trail eventTrail : FrameTrail}
    (hn : ctx.n = n)
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hchild : FirstRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      out (numcells + 1) outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail value)
    (hgca : level + 1 ≤ out.gcaFirst)
    (hbelow : value < Int.ofNat level)
    (hfreeze : FrozenOut ctx codes out outBest value)
    (hexactChild : outBest = some (incMax none
      (nodeKey ctx tcLevel specFuel (level + 1) codes
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := insert st.fixedpts tv
          cosetindex := tv }
        (numcells + 1))))
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
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
    (hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells outBest offset)
    (hfresh : elem st.fixedpts tv = false)
    (hlevel : 1 ≤ level) (hls : rsLab.size = ctx.n)
    (hlab : LabOk rsLab ctx.n) (hps : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hcell : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hoff : offset < len) (hfuel : level + 1 + specFuel ≤ ctx.n + 1) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      none outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let marked : SearchSt := { out with gcaFirst := level, stabvertex := tv1 }
  let cleaned : SearchSt :=
    { marked with fixedpts := erase marked.fixedpts tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change erase out.fixedpts tv = st.fixedpts
    rw [hchild.proof.node.fixed, erase_insert_of_miss hfresh]
  have hstate : firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell index st =
      (some value, index, cleaned) :=
    firstChildLoop_earlyGuide ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 tv tcell index st value out hrep hfirst hcall hbelow
  have hmark : EventOut G ctx tcLevel codes fs marked outBest eventTrail
      value :=
    hchild.markEvent hn hpath.symm hbelow hgca hdone hlevel hls hlab hps
      hend hvals hcell hrange hoff hfuel
  have hevent : EventOut G ctx tcLevel stem fs cleaned outBest eventTrail
      value :=
    (hmark.ancestor hstem hshorter).setFixed _
  have hsound := LoopSound.ofNode (NodeSound.ofExact hexactChild) hkey
  have hexact : outBest = some (incMax none bound) := by
    rw [hlen] at hcover
    exact hfreeze.exactLoop hpath hbelow hbound hcover hsound
  have hinstalled : cleaned.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc (hevent.read.trans hexact)
  rw [hstate]
  refine ⟨⟨⟨.pruned value rfl hbelow (LoopSound.ofExact hexact) hinstalled
    hevent.read hexact, by simpa only [loopReturn] using hevent,
    hchild.proof.node.outcome.preserved.ofPush⟩, hfixed⟩,
    LoopExit.frozen value rfl hbelow hexact
      ((hfreeze.setFirst level tv1).setFixed _), ?_, ?_, ?_, ?_, ?_⟩
  · intro hshort
    refine ⟨value, rfl, ?_⟩
    apply ShortSource.setFixed
    apply ShortSource.setFirst
    apply hchild.short
    simpa only [cleaned, marked] using hshort
  · exact hchild.proof.trail.lower.retrail rfl (TrailExt.refl _ _)
  · exact hchild.proof.canonTrail.lower.retrail rfl (TrailExt.refl _ _)
  · exact Nat.le_refl level
  · change level ≤ out.gcaCanon
    exact Nat.le_trans (Nat.le_trans (Nat.le_succ level) hgca)
      hchild.proof.order

/-- A saved cheap-boundary guiding child return below the loop absorbs
the whole verified small-cell sweep. -/
theorem guideCheap {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell tv1
      tv boundary offset index : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound childKey : Key} {st out : SearchSt}
    {outBest : Option Key} {trail eventTrail : FrameTrail}
    (hn : ctx.n = n)
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (Int.ofNat boundary - 1, out))
    (hchild : FirstRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv }
      out (numcells + 1) outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail (Int.ofNat boundary - 1))
    (hgca : level + 1 ≤ out.gcaFirst)
    (hpositive : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hsaved : out.noncheaplevel = boundary)
    (hbound : bound = childKey)
    (hexact : outBest = some (incMax none childKey))
    (hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
      numcells outBest offset)
    (hfresh : elem st.fixedpts tv = false)
    (hlevel : 1 ≤ level) (hls : rsLab.size = ctx.n)
    (hlab : LabOk rsLab ctx.n) (hps : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hcell : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hoff : offset < len) (hfuel : level + 1 + specFuel ≤ ctx.n + 1) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      none outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let value := Int.ofNat boundary - 1
  let marked : SearchSt := { out with gcaFirst := level, stabvertex := tv1 }
  let cleaned : SearchSt :=
    { marked with fixedpts := erase marked.fixedpts tv }
  have hvalue : value < Int.ofNat level := by
    simp only [value, Int.ofNat_eq_natCast]
    omega
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change erase out.fixedpts tv = st.fixedpts
    rw [hchild.proof.node.fixed, erase_insert_of_miss hfresh]
  have hstate : firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell index st =
      (some value, index, cleaned) :=
    firstChildLoop_earlyGuide ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 tv tcell index st value out hrep hfirst hcall hvalue
  have hmark : EventOut G ctx tcLevel codes fs marked outBest eventTrail
      value :=
    hchild.markEvent hn hpath.symm hvalue hgca hdone hlevel hls hlab hps
      hend hvals hcell hrange hoff hfuel
  have hevent : EventOut G ctx tcLevel stem fs cleaned outBest eventTrail
      value :=
    (hmark.ancestor hstem hshorter).setFixed _
  have hexactBound : outBest = some (incMax none bound) := by
    rwa [hbound]
  have hinstalled : cleaned.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc (hevent.read.trans hexactBound)
  rw [hstate]
  refine ⟨⟨⟨.pruned value rfl hvalue (LoopSound.ofExact hexactBound)
    hinstalled hevent.read hexactBound,
    by simpa only [loopReturn] using hevent,
    hchild.proof.node.outcome.preserved.ofPush⟩, hfixed⟩,
    LoopExit.cheap boundary rfl hpositive hbelow
      (by simpa only [cleaned, marked] using hsaved) hexactBound, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro hshort
    refine ⟨value, rfl, ?_⟩
    apply ShortSource.setFixed
    apply ShortSource.setFirst
    apply hchild.short
    simpa only [cleaned, marked, value] using hshort
  · exact hchild.proof.trail.lower.retrail rfl (TrailExt.refl _ _)
  · exact hchild.proof.canonTrail.lower.retrail rfl (TrailExt.refl _ _)
  · exact Nat.le_refl level
  · change level ≤ out.gcaCanon
    exact Nat.le_trans (Nat.le_trans (Nat.le_succ level) hgca)
      hchild.proof.order

/-! ## Continuing after a child -/

/-- Compose an off-path child that stays at the loop level with the
recursive tail on the recovered, possibly filtered, state. -/
theorem nextOther {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 tv index : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best mid outBest : Option Key} {value : Int}
    {receiptTrail eventTrail : FrameTrail}
    (hnext : nextElem tcell cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level)
    (hfixed : (recover ctx.n inf level
      (clearShortIf out.needshortprune
        { out with fixedpts := erase out.fixedpts tv })).fixedpts =
        st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (hrec :
      FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells
        (if out.needshortprune then
          shortprune tcell (clearShortIf out.needshortprune
            { out with fixedpts := erase out.fixedpts tv })
        else tcell)
        (some tv) bound
        (recover ctx.n inf level
          (clearShortIf out.needshortprune
            { out with fixedpts := erase out.fixedpts tv }))
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1
          (nextElem
            (if out.needshortprune then
              shortprune tcell (clearShortIf out.needshortprune
                { out with fixedpts := erase out.fixedpts tv })
            else tcell) (some tv))
          (if out.needshortprune then
            shortprune tcell (clearShortIf out.needshortprune
              { out with fixedpts := erase out.fixedpts tv })
          else tcell)
          (if ((recover ctx.n inf level
            (clearShortIf out.needshortprune
              { out with fixedpts := erase out.fixedpts tv })).orbits[tv]! ==
              tv1) = true then index + 1 else index)
          (recover ctx.n inf level
            (clearShortIf out.needshortprune
              { out with fixedpts := erase out.fixedpts tv }))).2.2
        mid outBest receiptTrail eventTrail
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1
          (nextElem
            (if out.needshortprune then
              shortprune tcell (clearShortIf out.needshortprune
                { out with fixedpts := erase out.fixedpts tv })
            else tcell) (some tv))
          (if out.needshortprune then
            shortprune tcell (clearShortIf out.needshortprune
              { out with fixedpts := erase out.fixedpts tv })
          else tcell)
          (if ((recover ctx.n inf level
            (clearShortIf out.needshortprune
              { out with fixedpts := erase out.fixedpts tv })).orbits[tv]! ==
              tv1) = true then index + 1 else index)
          (recover ctx.n inf level
            (clearShortIf out.needshortprune
              { out with fixedpts := erase out.fixedpts tv }))).1) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest receiptTrail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hstate := firstChildLoop_stayOther ctx inf tcLevel runFuel loopFuel
    level numcells tc tv1 tv tcell index st value out hrep hother hcall hstay
  dsimp only at hstate
  rw [hstate]
  exact (hrec.prepend hfixed hpre).step (nextElem_after hnext)
    |>.reindexSet

/-- Compose the guiding child, when it stays at the loop level, with the
recursive tail on the recovered, possibly filtered, state carrying the
installed first-path controls. -/
theorem nextGuide {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 tv index : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best mid outBest : Option Key} {value : Int}
    {receiptTrail eventTrail : FrameTrail}
    (hnext : nextElem tcell cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := insert st.fixedpts tv
        cosetindex := tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level)
    (hfixed : (recover ctx.n inf level
      (clearShortIf out.needshortprune
        { out with
          gcaFirst := level
          stabvertex := tv1
          fixedpts := erase out.fixedpts tv })).fixedpts =
        st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (hrec :
      FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells
        (if out.needshortprune then
          shortprune tcell (clearShortIf out.needshortprune
            { out with
              gcaFirst := level
              stabvertex := tv1
              fixedpts := erase out.fixedpts tv })
        else tcell)
        (some tv) bound
        (recover ctx.n inf level
          (clearShortIf out.needshortprune
            { out with
              gcaFirst := level
              stabvertex := tv1
              fixedpts := erase out.fixedpts tv }))
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1
          (nextElem
            (if out.needshortprune then
              shortprune tcell (clearShortIf out.needshortprune
                { out with
                  gcaFirst := level
                  stabvertex := tv1
                  fixedpts := erase out.fixedpts tv })
            else tcell) (some tv))
          (if out.needshortprune then
            shortprune tcell (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := erase out.fixedpts tv })
          else tcell)
          (if ((recover ctx.n inf level
            (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := erase out.fixedpts tv })).orbits[tv]! ==
              tv1) = true then index + 1 else index)
          (recover ctx.n inf level
            (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := erase out.fixedpts tv }))).2.2
        mid outBest receiptTrail eventTrail
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1
          (nextElem
            (if out.needshortprune then
              shortprune tcell (clearShortIf out.needshortprune
                { out with
                  gcaFirst := level
                  stabvertex := tv1
                  fixedpts := erase out.fixedpts tv })
            else tcell) (some tv))
          (if out.needshortprune then
            shortprune tcell (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := erase out.fixedpts tv })
          else tcell)
          (if ((recover ctx.n inf level
            (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := erase out.fixedpts tv })).orbits[tv]! ==
              tv1) = true then index + 1 else index)
          (recover ctx.n inf level
            (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := erase out.fixedpts tv }))).1) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest receiptTrail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hstate := firstChildLoop_stayGuide ctx inf tcLevel runFuel loopFuel
    level numcells tc tv1 tv tcell index st value out hrep hfirst hcall hstay
  dsimp only at hstate
  rw [hstate]
  exact (hrec.prepend hfixed hpre).step (nextElem_after hnext)
    |>.reindexSet

/-- Skipping a vertex that is not its orbit's representative. -/
theorem skip {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 tv index : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {st : SearchSt}
    {best outBest : Option Key} {receiptTrail eventTrail : FrameTrail}
    (hnext : nextElem tcell cursor = some tv)
    (horb : (st.orbits[tv]! == tv) = false)
    (hrec :
      FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells tcell (some tv) bound st
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell
          (if (st.orbits[tv]! == tv1) = true then index + 1 else index)
          st).2.2
        best outBest receiptTrail eventTrail
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell
          (if (st.orbits[tv]! == tv1) = true then index + 1 else index)
          st).1) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest receiptTrail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  rw [firstChildLoop_skip ctx inf tcLevel runFuel loopFuel level numcells tc
    tv1 tv tcell index st horb]
  exact hrec.step (nextElem_after hnext)

end FirstSweepRun

end Hex.GraphIso.Nauty
