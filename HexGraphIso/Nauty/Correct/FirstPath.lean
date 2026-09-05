/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.OffPath
import all HexGraphIso.Nauty.Search

public section

/-!
Totality along the first path.

The state equations and packaged result of one `firstChildLoop`
iteration, the hypotheses carried through the sweep after its guiding
child has been absorbed, the cursor-fuel induction that finishes the
sweep, and the first-path node step of the totality induction.
-/

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
theorem firstChildLoop_skip (ctx : Ctx n)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv : Nat) (tcell : VSet n) (index : Nat)
    (st : SearchSt n) (horb : (st.orbits[tv]! == tv) = false) :
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (tcell.nextElem (some tv)) tcell
        (if (st.orbits[tv]! == tv1) = true then index + 1 else index) st := by
  conv =>
    lhs
    unfold firstChildLoop
    simp only [horb, Bool.false_eq_true, ite_false, Id.run_pure,
      apply_ite Id.run]
  split <;> rfl

/-- An early off-path child return leaves the loop after cleaning the
temporary fixed vertex. -/
theorem firstChildLoop_earlyOther (ctx : Ctx n)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv : Nat) (tcell : VSet n) (index : Nat)
    (st : SearchSt n) (value : Int) (out : SearchSt n)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hearly : value < Int.ofNat level) :
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      (some value, index, { out with fixedpts := out.fixedpts.erase tv }) := by
  unfold firstChildLoop
  simp only [hrep, ite_true, hother, Bool.false_eq_true, ite_false,
    Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_left hearly]

/-- An early guiding child return leaves the loop after installing the
first-path controls and cleaning the temporary fixed vertex. -/
theorem firstChildLoop_earlyGuide (ctx : Ctx n)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv : Nat) (tcell : VSet n) (index : Nat)
    (st : SearchSt n) (value : Int) (out : SearchSt n)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hearly : value < Int.ofNat level) :
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      (some value, index,
        { out with
          gcaFirst := level
          stabvertex := tv1
          fixedpts := out.fixedpts.erase tv }) := by
  unfold firstChildLoop
  simp only [hrep, ite_true, hfirst, Id.run_pure, apply_ite Id.run]
  rw [hcall, ite_eq_left hearly]

/-- An off-path child that stays at the loop level continues with the
recursive tail on the recovered, possibly filtered, state. -/
theorem firstChildLoop_stayOther (ctx : Ctx n)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv : Nat) (tcell : VSet n) (index : Nat)
    (st : SearchSt n) (value : Int) (out : SearchSt n)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level) :
    let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
    let cleared := clearShortIf cleaned.needshortprune cleaned
    let tcell' := if cleaned.needshortprune then shortprune tcell cleared
      else tcell
    let recSt := recover n inf level cleared
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (tcell'.nextElem (some tv)) tcell'
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
theorem firstChildLoop_stayGuide (ctx : Ctx n)
    (inf tcLevel runFuel loopFuel level numcells tc tv1 tv : Nat) (tcell : VSet n) (index : Nat)
    (st : SearchSt n) (value : Int) (out : SearchSt n)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level) :
    let cleaned : SearchSt n :=
      { out with
        gcaFirst := level
        stabvertex := tv1
        fixedpts := out.fixedpts.erase tv }
    let cleared := clearShortIf cleaned.needshortprune cleaned
    let tcell' := if cleaned.needshortprune then shortprune tcell cleared
      else tcell
    let recSt := recover n inf level cleared
    firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells tc
        tv1 (some tv) tcell index st =
      firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc tv1
        (tcell'.nextElem (some tv)) tcell'
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
structure FirstSweepRun (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
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
theorem retrail {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
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
theorem prepend {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st recSt out : SearchSt n} {best mid outBest : Option (Key n)}
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
theorem step {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
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
theorem reindexSet {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell tcell' : VSet n} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
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
theorem childUnwind {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv tv1 index target offset : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n} {value : Int}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail}
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hsound : NodeSound ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      (numcells + 1) best outBest)
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
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
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail value)
    (hfresh : st.fixedpts.mem tv = false)
    (htrail : FirstTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
      eventTrail)
    (hcanon : CanonTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
      eventTrail)
    (hguide : level ≤ st.gcaFirst) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change out.fixedpts.erase tv = st.fixedpts
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
      hlocParent.setFixed (out.fixedpts.erase tv)
  obtain ⟨payloadN, hlocN⟩ :
      ∃ payloadN : Unwind ctx tcLevel target
        (otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := st.fixedpts.insert tv
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
theorem childFrozen {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv tail offset index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {value : Int}
    {trail eventTrail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
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
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
          cosetindex := tv }
        (numcells + 1))))
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
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
    (hfresh : st.fixedpts.mem tv = false)
    (htrail : FirstTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
      eventTrail)
    (hcanon : CanonTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
      eventTrail)
    (hguide : level ≤ st.gcaFirst) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change out.fixedpts.erase tv = st.fixedpts
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
theorem childCheap {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv boundary offset index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound childKey : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail}
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } =
        (Int.ofNat boundary - 1, out))
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail (Int.ofNat boundary - 1))
    (hpositive : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hsaved : out.noncheaplevel = boundary)
    (hbound : bound = childKey)
    (hexact : outBest = some (incMax best childKey))
    (hfresh : st.fixedpts.mem tv = false)
    (htrail : FirstTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
      eventTrail)
    (hcanon : CanonTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
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
  let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
  have hvalue : value < Int.ofNat level := by
    simp only [value, Int.ofNat_eq_natCast]
    omega
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change out.fixedpts.erase tv = st.fixedpts
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
theorem ShortSource.setFirst {G : Colored n k} {ctx : Ctx n} {out : SearchSt n}
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
theorem FirstRun.markEvent {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len offset tv1 : Nat}
    {cs fs : List Nat} {rsLab rsPtn : Array Nat}
    {child out : SearchSt n} {outBest : Option (Key n)}
    {trail eventTrail : FrameTrail} {r : Int}
    (hpath : cs.length = level)
    (hreturn : r < Int.ofNat level) (hgca : level + 1 ≤ out.gcaFirst)
    (h : FirstRun G ctx tcLevel specFuel runFuel (level + 1) cs fs child
      out (numcells + 1) outBest
      (trail.push level
        ⟨sweepFrame specFuel cs rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hdone : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells outBest offset)
    (hlevel : 1 ≤ level) (hls : rsLab.size = n)
    (hlab : LabOk rsLab n) (hps : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hcell : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hoff : offset < len) (hfuel : level + 1 + specFuel ≤ n + 1) :
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
        hrange hoff hfuel hat' event.leafRefs.firstSize
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
          ({ out with gcaFirst := level, stabvertex := tv1 } : SearchSt n).gcaFirst)
          = r := by
        change min r (Int.ofNat level) = r
        exact Int.min_eq_left (Int.le_of_lt hreturn)
      exact .intro current codes bestCodes event' depth stemEq past returned
        (by rw [hmin']; exact hstable) hhistory

namespace FirstSweepRun

/-- A comparison-frozen guiding child return below the loop absorbs the
whole sweep. -/
theorem guideFrozen {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv tail offset index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {outBest : Option (Key n)} {value : Int}
    {trail eventTrail : FrameTrail}
   
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hchild : FirstRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
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
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
          cosetindex := tv }
        (numcells + 1))))
    (hkey : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
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
    (hfresh : st.fixedpts.mem tv = false)
    (hlevel : 1 ≤ level) (hls : rsLab.size = n)
    (hlab : LabOk rsLab n) (hps : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hcell : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hoff : offset < len) (hfuel : level + 1 + specFuel ≤ n + 1) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      none outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let marked : SearchSt n := { out with gcaFirst := level, stabvertex := tv1 }
  let cleaned : SearchSt n :=
    { marked with fixedpts := marked.fixedpts.erase tv }
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change out.fixedpts.erase tv = st.fixedpts
    rw [hchild.proof.node.fixed, erase_insert_of_miss hfresh]
  have hstate : firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell index st =
      (some value, index, cleaned) :=
    firstChildLoop_earlyGuide ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 tv tcell index st value out hrep hfirst hcall hbelow
  have hmark : EventOut G ctx tcLevel codes fs marked outBest eventTrail
      value :=
    hchild.markEvent hpath.symm hbelow hgca hdone hlevel hls hlab hps
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
theorem guideCheap {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv boundary offset index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound childKey : Key n} {st out : SearchSt n}
    {outBest : Option (Key n)} {trail eventTrail : FrameTrail}
   
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hshorter : stem.length < codes.length)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1)
      (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (Int.ofNat boundary - 1, out))
    (hchild : FirstRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
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
    (hfresh : st.fixedpts.mem tv = false)
    (hlevel : 1 ≤ level) (hls : rsLab.size = n)
    (hlab : LabOk rsLab n) (hps : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hcell : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hoff : offset < len) (hfuel : level + 1 + specFuel ≤ n + 1) :
    FirstSweepRun G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      none outBest trail eventTrail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  let value := Int.ofNat boundary - 1
  let marked : SearchSt n := { out with gcaFirst := level, stabvertex := tv1 }
  let cleaned : SearchSt n :=
    { marked with fixedpts := marked.fixedpts.erase tv }
  have hvalue : value < Int.ofNat level := by
    simp only [value, Int.ofNat_eq_natCast]
    omega
  have hfixed : cleaned.fixedpts = st.fixedpts := by
    change out.fixedpts.erase tv = st.fixedpts
    rw [hchild.proof.node.fixed, erase_insert_of_miss hfresh]
  have hstate : firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
      level numcells tc tv1 (some tv) tcell index st =
      (some value, index, cleaned) :=
    firstChildLoop_earlyGuide ctx inf tcLevel runFuel loopFuel level
      numcells tc tv1 tv tcell index st value out hrep hfirst hcall hvalue
  have hmark : EventOut G ctx tcLevel codes fs marked outBest eventTrail
      value :=
    hchild.markEvent hpath.symm hvalue hgca hdone hlevel hls hlab hps
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
theorem nextOther {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int}
    {receiptTrail eventTrail : FrameTrail}
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true) (hother : (tv == tv1) = false)
    (hcall : otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level)
    (hfixed : (recover n inf level
      (clearShortIf out.needshortprune
        { out with fixedpts := out.fixedpts.erase tv })).fixedpts =
        st.fixedpts)
    (hpre : LoopSound ctx bound best mid)
    (hrec :
      FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells
        (if out.needshortprune then
          shortprune tcell (clearShortIf out.needshortprune
            { out with fixedpts := out.fixedpts.erase tv })
        else tcell)
        (some tv) bound
        (recover n inf level
          (clearShortIf out.needshortprune
            { out with fixedpts := out.fixedpts.erase tv }))
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1
          ((if out.needshortprune then
              shortprune tcell (clearShortIf out.needshortprune
                { out with fixedpts := out.fixedpts.erase tv })
            else tcell).nextElem (some tv))
          (if out.needshortprune then
            shortprune tcell (clearShortIf out.needshortprune
              { out with fixedpts := out.fixedpts.erase tv })
          else tcell)
          (if ((recover n inf level
            (clearShortIf out.needshortprune
              { out with fixedpts := out.fixedpts.erase tv })).orbits[tv]! ==
              tv1) = true then index + 1 else index)
          (recover n inf level
            (clearShortIf out.needshortprune
              { out with fixedpts := out.fixedpts.erase tv }))).2.2
        mid outBest receiptTrail eventTrail
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1
          ((if out.needshortprune then
              shortprune tcell (clearShortIf out.needshortprune
                { out with fixedpts := out.fixedpts.erase tv })
            else tcell).nextElem (some tv))
          (if out.needshortprune then
            shortprune tcell (clearShortIf out.needshortprune
              { out with fixedpts := out.fixedpts.erase tv })
          else tcell)
          (if ((recover n inf level
            (clearShortIf out.needshortprune
              { out with fixedpts := out.fixedpts.erase tv })).orbits[tv]! ==
              tv1) = true then index + 1 else index)
          (recover n inf level
            (clearShortIf out.needshortprune
              { out with fixedpts := out.fixedpts.erase tv }))).1) :
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
theorem nextGuide {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best mid outBest : Option (Key n)} {value : Int}
    {receiptTrail eventTrail : FrameTrail}
    (hnext : tcell.nextElem cursor = some tv)
    (hrep : (st.orbits[tv]! == tv) = true) (hfirst : (tv == tv1) = true)
    (hcall : firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (value, out))
    (hstay : ¬ value < Int.ofNat level)
    (hfixed : (recover n inf level
      (clearShortIf out.needshortprune
        { out with
          gcaFirst := level
          stabvertex := tv1
          fixedpts := out.fixedpts.erase tv })).fixedpts =
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
              fixedpts := out.fixedpts.erase tv })
        else tcell)
        (some tv) bound
        (recover n inf level
          (clearShortIf out.needshortprune
            { out with
              gcaFirst := level
              stabvertex := tv1
              fixedpts := out.fixedpts.erase tv }))
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1
          ((if out.needshortprune then
              shortprune tcell (clearShortIf out.needshortprune
                { out with
                  gcaFirst := level
                  stabvertex := tv1
                  fixedpts := out.fixedpts.erase tv })
            else tcell).nextElem (some tv))
          (if out.needshortprune then
            shortprune tcell (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := out.fixedpts.erase tv })
          else tcell)
          (if ((recover n inf level
            (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := out.fixedpts.erase tv })).orbits[tv]! ==
              tv1) = true then index + 1 else index)
          (recover n inf level
            (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := out.fixedpts.erase tv }))).2.2
        mid outBest receiptTrail eventTrail
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1
          ((if out.needshortprune then
              shortprune tcell (clearShortIf out.needshortprune
                { out with
                  gcaFirst := level
                  stabvertex := tv1
                  fixedpts := out.fixedpts.erase tv })
            else tcell).nextElem (some tv))
          (if out.needshortprune then
            shortprune tcell (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := out.fixedpts.erase tv })
          else tcell)
          (if ((recover n inf level
            (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := out.fixedpts.erase tv })).orbits[tv]! ==
              tv1) = true then index + 1 else index)
          (recover n inf level
            (clearShortIf out.needshortprune
              { out with
                gcaFirst := level
                stabvertex := tv1
                fixedpts := out.fixedpts.erase tv }))).1) :
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
theorem skip {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 tv index : Nat} {tcell : VSet n}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {st : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    (hnext : tcell.nextElem cursor = some tv)
    (horb : (st.orbits[tv]! == tv) = false)
    (hrec :
      FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
        fs rsLab rsPtn tc len numcells tcell (some tv) bound st
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (tcell.nextElem (some tv)) tcell
          (if (st.orbits[tv]! == tv1) = true then index + 1 else index)
          st).2.2
        best outBest receiptTrail eventTrail
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (tcell.nextElem (some tv)) tcell
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

/-!
The first-path sibling sweep, part two: the hypotheses carried through the
sweep after its guiding child has been absorbed, and their transport across
an off-path child that stays at the loop level.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Hypotheses of the sweep after its guiding child -/

/-- The coset cursor plays no role in the reach relation. -/
theorem SearchOut.ofCoset {G : Colored n k} {B lev coset : Nat}
    {st out : SearchSt n}
    (h : SearchOut G B lev { st with cosetindex := coset } out) :
    SearchOut G B lev st out :=
  ⟨h.labSize, h.ptnSize, h.reach, h.low, h.perm, h.firstStore,
    h.canonStore, h.canon⟩

/-- Every generator recorded by an event is a checked automorphism. -/
theorem EventOut.checkGen {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    ∀ γ ∈ out.genTrace.toList, checkAutom ctx.g γ = true := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ =>
      intro γ hγ
      exact event.genTraceOk.check hγ

/-- A canonical reference that is a cell permutation of the current
labelling at the current level reaches every active ancestor frame and
picks the same child there. -/
theorem CanonTrail.ofPerm {ctx : Ctx n} {level : Nat} {st out : SearchSt n}
    {trail : FrameTrail}
    (htrail : TrailOk ctx level st trail)
    (hlab : st.lab.size = n) (hptn : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hperm : cellsPerm st.ptn level st.lab out.canonlab)
    (hcsz : out.canonlab.size = n) :
    CanonTrail ctx level out trail := by
  constructor
  · intro target entry hlt hentry
    have h1 := htrail.reach target entry hlt hentry
    have h2 : cellsPerm entry.frame.rsPtn target st.lab out.canonlab := by
      apply cellsPerm_coarsen (ptnF := st.ptn) (levF := level)
      · rw [htrail.ptnSize target entry hlt hentry, hptn]
      · rw [hlab, hptn]
      · rw [hcsz, hptn]
      · exact hperm
      · exact hend
      · exact htrail.endClosed target entry hlt hentry
      · intro q hq
        rw [htrail.frozen target entry hlt hentry q hq]
        omega
    exact cellsPerm_trans h1 h2
  · intro target entry hlt hentry
    obtain ⟨len, hcell, hoff, _, hsingle, hat⟩ :=
      htrail.picked target entry hlt hentry
    refine ⟨len, hcell, hoff, ?_⟩
    rw [← cellsPerm_singleton hperm hsingle]
    exact hat

/-- What the first-path sweep knows at every cursor position after its
guiding child: the loop invariant, the live package with frame
stabilization, path facts, both reference histories below the loop, the
first-path controls, orbit and coset facts, first-leaf domination, and the
cheap-cell boundary discipline relative to the node entry boundary `e`. -/
structure FirstSweepHyp (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel level : Nat) (codes bs fs : List Nat)
    (numcells : Nat) (rsLab rsPtn : Array Nat) (tc len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (e tv1 : Nat) (base st : SearchSt n)
    (best : Option (Key n)) (trail : FrameTrail) : Prop where
  inv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab
    rsPtn tc len tcell cursor base st best trail
  live : FirstLive ctx level st trail rsLab rsPtn
  path : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
    (initialPartition G).1 level st
  after : ∃ v, cursor = some v ∧ tv1 ≤ v
  cursorLt : ∀ v, cursor = some v → v < n
  sign : st.compCanon ≤ 0
  guide : st.gcaFirst = level
  firstTrail : FirstTrail ctx level st trail
  canonTrail : CanonTrail ctx level st trail
  orbits : OrbSound (OrbConn st.genTrace.toList n) st.orbits n
  coset : st.cosetindex < n
  firstDom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b
  desc : CheapDesc ctx level st.noncheaplevel
    (LoopInv.frame rsLab rsPtn numcells)
  bnd : st.noncheaplevel ≤ level + 1
  park : cheapautom rsPtn level n = false → st.noncheaplevel ≠ level
  keep : st.noncheaplevel < level → st.noncheaplevel = e

/-- What a finished first-path sweep preserves for its enclosing node. -/
structure FirstSweepKeep (ctx : Ctx n) (level e : Nat) (fs : List Nat)
    (st out : SearchSt n) (outBest : Option (Key n)) : Prop where
  dom : ∀ b, outBest = some b → keyLe (pathLeafKey ctx fs out.firstlab) b
  firstlab : out.firstlab = st.firstlab
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  coset : out.cosetindex < n
  boundary : out.noncheaplevel < level → out.noncheaplevel = e

/-- The small-cell descent invariant of a child, when the loop boundary is
merely known to avoid the loop level. -/
theorem LoopInv.childDescWeak {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hg : ctx.g = rowsOf G)
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hbnd : st.noncheaplevel ≤ level + 1)
    (hpark : cheapautom rsPtn level n = false →
      st.noncheaplevel ≠ level)
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
    · have := hpark hc
      rcases Decidable.em (st.noncheaplevel ≥ level) with hge | hge
      · rw [ite_eq_left ⟨hge, by simp⟩]
        omega
      · rw [ite_eq_right (fun h => hge h.1)]
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

/-- The small-cell subtree fact at the frozen frame, when the boundary is
merely known to avoid the loop level. -/
theorem LoopInv.subtreeAtWeak {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (LoopInv.frame rsLab rsPtn numcells))
    (hpark : cheapautom rsPtn level n = false →
      st.noncheaplevel ≠ level)
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
      · exact (hpark hc heq).elim
      · exact hc
  exact hsub.setActive

namespace FirstSweepHyp

/-- The cheap-cell ledger is ready for the next child. -/
theorem cheapOk {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {e tv1 : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} (hg : ctx.g = rowsOf G)
    (h : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e tv1 base st best trail) :
    CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) (level + 1) st := by
  apply BoundaryOk.nextCheap _ h.inv.run
  rcases hc : cheapautom rsPtn level n with _ | _
  · intro heq
    exact (h.park hc heq).elim
  · apply BoundaryOk.ofCheap hg h.inv
    rw [h.inv.ptnEq]
    exact hc

/-- Filtering the live set leaves every other hypothesis unchanged. -/
theorem filter {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell tcell' : VSet n} {e tv1 : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e tv1 base st best trail)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells rsLab
      rsPtn tc len tcell' cursor base st best trail) :
    FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell' cursor e tv1 base st best trail :=
  ⟨hinv, h.live, h.path, h.after, h.cursorLt, h.sign, h.guide, h.firstTrail,
    h.canonTrail, h.orbits, h.coset, h.firstDom, h.desc, h.bnd, h.park,
    h.keep⟩

end FirstSweepHyp

/-- The reach relation depends on its input state only through the
labelling and partition. -/
theorem SearchOut.inputEq {G : Colored n k} {B lev : Nat}
    {st st' out : SearchSt n} (h : SearchOut G B lev st out)
    (hlab : st'.lab = st.lab) (hptn : st'.ptn = st.ptn)
    (hfirst : st'.firstlab = st.firstlab)
    (hcanon : st'.canonlab = st.canonlab) :
    SearchOut G B lev st' out :=
  ⟨by rw [hlab]; exact h.labSize, by rw [hptn]; exact h.ptnSize, h.reach,
    fun q hq => by rw [hptn]; exact h.low q (by rw [hptn] at hq; exact hq),
    by rw [hlab, hptn]; exact h.perm,
    by rw [hlab, hptn, hfirst]; exact h.firstStore,
    by rw [hlab, hptn, hcanon]; exact h.canonStore,
    by rw [hcanon]; exact h.canon⟩

/-- A new canonical reference installed below a child is a cell
permutation of the loop labelling at the loop level. -/
theorem LoopInv.childCanonPerm {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {tv currentOffset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {canonlab : Array Nat}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hcsz : canonlab.size = n)
    (hnew : cellsPerm (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      (level + 1) (breakout n st.lab st.ptn (level + 1) tc tv).1 canonlab) :
    cellsPerm st.ptn level st.lab canonlab := by
  let child : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
  have hnew' : cellsPerm child.ptn (level + 1) child.lab canonlab := by
    change cellsPerm (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + currentOffset]!).2.1 (level + 1)
      (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1 canonlab
    rw [hat]
    exact hnew
  have hstPtnSize : st.ptn.size = n := by
    exact hinv.run.searchOk.ptnSize
  have htcPtn : tc < st.ptn.size := by
    rw [hstPtnSize]
    exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hinv.range
  have hrangePtn : tc + len ≤ st.ptn.size := by
    rw [hstPtnSize]
    exact hinv.range
  have hchildPtn : child.ptn = st.ptn.set! tc (level + 1) :=
    breakout_ptn (n := n) st.lab st.ptn (level + 1) tc st.lab[tc + currentOffset]!
  have hchildOk : SearchOk G (level + 1) (numcells + 1) child := by
    apply breakout_searchOk hinv.nonempty hinv.run.searchOk hinv.positive
      hinv.currentCell hinv.lenTwo
      hinv.range hcurrent
    · rfl
    · exact hchildPtn
    · rfl
  have hfine : cellsPerm st.ptn level child.lab canonlab := by
    apply cellsPerm_coarsen (ptnF := child.ptn) (levF := level + 1)
    · rw [hchildPtn, Array.size_set!]
    · exact hchildOk.labSize.trans hchildOk.ptnSize.symm
    · rw [hcsz, hchildOk.ptnSize]
    · exact hnew'
    · exact searchOk_end hinv.nonempty hchildOk (by omega)
    · exact searchOk_end hinv.nonempty hinv.run.searchOk hinv.positive
    · intro q hq
      rw [hchildPtn]
      rcases Decidable.em (tc = q) with rfl | hne
      · rw [Array.getElem!_set!_self _ _ _ htcPtn]
        exact Nat.le_refl _
      · rw [Array.getElem!_set!_ne _ _ _ _ hne]
        omega
  have hbreak : cellsPerm st.ptn level st.lab child.lab := by
    change cellsPerm st.ptn level st.lab
      (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
    exact breakout_cellsPerm hinv.currentCell hrangePtn
      (by rw [hinv.run.searchOk.labSize, hinv.run.searchOk.ptnSize])
      hcurrent
  exact cellsPerm_trans hbreak hfine

namespace FirstSweepHyp

set_option maxHeartbeats 1600000 in
/-- An off-path child that stays at the loop level rebuilds every sweep
hypothesis for the recursive tail on the recovered state. -/
theorem next {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tv offset currentOffset e tv1 : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best childBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hh : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e tv1 base st best trail)
    (hcodesLen : codes.length = level) (hfuel : runFuel ≠ 0)
    (hnext : tcell.nextElem cursor = some tv)
    (hoffset : offset < len) (hcurrent : currentOffset < len)
    (hatFrozen : rsLab[tc + offset]! = tv)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      out (numcells + 1) best childBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hkeep : OtherKeep ctx (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } out)
    (hstay : ¬ r < Int.ofNat level)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } out)
    (clear : Bool)
    (hshort : (clearShortIf clear
      { out with fixedpts := out.fixedpts.erase tv }).needshortprune =
        false) :
    ∃ bs', FirstSweepHyp G ctx tcLevel specFuel level codes bs' fs numcells
      rsLab rsPtn tc len tcell (some tv) e tv1 base
      (recover n inf level
        (clearShortIf clear { out with fixedpts := out.fixedpts.erase tv }))
      childBest eventTrail := by
  let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
  let cleared := clearShortIf clear cleaned
  let recSt := recover n inf level cleared
  obtain ⟨hfix, hcos, hcomp, hgen, horb, hfl, hncl, hgf, hgc, hcl, -⟩ :=
    clearShortIf_fields clear cleaned
  have hgsz : ctx.g.size = n := by
    rw [hg]
    exact size_rowsOf G
  have hreturn : r = Int.ofNat level :=
    hchild.node.toOutcome.parentEq hfuel hstay
  have hgrows : IncGrows best childBest := hchild.grows hfuel
  have hstFirst : ({ st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv
      cosetindex := tv } : SearchSt n).gcaFirst = level := hh.guide
  have houtFirst : out.gcaFirst = level := hchild.firstGuide.trans hstFirst
  -- coverage
  have hret := NodeOutcome.parentReturn hchild.node.toOutcome hfuel hstay
  have heq0 := hh.inv.childKeyAll hoffset hatFrozen hat
  have heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := st.fixedpts.insert tv
            cosetindex := tv }
          (numcells + 1) := by
    intro o ho h
    exact (heq0 o ho h).trans (nodeKey_congr rfl rfl rfl).symm
  have hinj : LabInj rsLab rsLab.size := by
    rw [← hh.inv.baseLab, hh.inv.baseOk.labSize]
    exact labInj_of_reach hh.inv.baseOk.labSize hh.inv.nonempty
      hh.inv.baseOk.reach
  have hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc
      len numcells tcell (some tv) childBest :=
    SweepCover.receipt hh.inv.cover hnext hchild.node.toOutcome.receipt hfuel
      hret heq hoffset hatFrozen hchild.coset hgsz
      hchild.node.event.checkGen hh.inv.frozenLabSize hinj
      hh.inv.frozenLabOk hh.inv.frozenPtnSize hh.inv.frozenEnd
      hh.inv.frozenVals hh.inv.cell hh.inv.range hh.inv.fuelBound
  -- recovery
  have hout' : SearchOut G level (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out := by
    rw [hat]
    exact hout.inputEq rfl rfl rfl rfl
  have hfixedChild : out.fixedpts =
      st.fixedpts.insert st.lab[tc + currentOffset]! := by
    rw [hchild.node.fixed, hat]
  have hrecovered := hh.inv.recoverChild hinf hcurrent hout'
  rw [hat] at hrecovered
  have hpathRec := hh.inv.recoverPath hh.path hout' hfixedChild hinf hcurrent
  rw [hat] at hpathRec
  have hrecEq : recSt = clearShortIf clear (recover n inf level cleaned) :=
    recover_clearShortIf n inf level clear cleaned
  have heffect : SearchOut G level level base recSt := by
    rw [hrecEq]
    cases clear
    · exact hrecovered.1
    · exact hrecovered.1.congr rfl rfl rfl rfl
  have hok : SearchOk G level numcells recSt := by
    rw [hrecEq]
    cases clear
    · exact hrecovered.2
    · exact {
        labSize := hrecovered.2.labSize
        ptnSize := hrecovered.2.ptnSize
        reach := hrecovered.2.reach
        init1 := hrecovered.2.init1
        vals := hrecovered.2.vals
        count := hrecovered.2.count
        bc := hrecovered.2.bc
        canon := hrecovered.2.canon }
  have hpath : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level recSt := by
    rw [hrecEq]
    exact hpathRec.1.clearShortIf clear
  have hfixedRec : recSt.fixedpts = st.fixedpts := by
    rw [hrecEq, (clearShortIf_fields clear _).1]
    exact hpathRec.2
  have hev : EventOut G ctx tcLevel codes fs cleared childBest eventTrail
      r := by
    cases clear
    · exact hchild.node.event.setFixed _
    · exact (hchild.node.event.setFixed _).clearShort
  have hfirstLe : cleared.gcaFirst ≤ level := by
    rw [hgf]
    exact Nat.le_of_eq houtFirst
  have hinfLevel : level < inf := by
    rw [hinf]
    have hle : level ≤ n := Nat.le_trans hh.inv.run.searchOk.bc
      (bcount_le st.ptn level n)
    omega
  obtain ⟨bs', hrun, hstable, hhistory⟩ := hev.recoverRun hreturn hcodesLen
    hh.inv.positive hinfLevel hfirstLe hok
  -- frames of the recovered state
  have hframes := recover_frames n inf level cleared
  have hgfRec : recSt.gcaFirst = level := by
    rw [show recSt = recover n inf level cleared from rfl,
      hframes.2.2.2.2.2.2.1, hgf]
    exact houtFirst
  have horderOut : level ≤ out.gcaCanon := by
    rw [← houtFirst]
    exact hchild.order
  have hgcRec : level ≤ recSt.gcaCanon := by
    rw [show recSt = recover n inf level cleared from rfl,
      recover_gcaCanon, hgc]
    change level ≤ if level < out.gcaCanon then level else out.gcaCanon
    split <;> omega
  have hfirstlabRec : recSt.firstlab = st.firstlab := by
    rw [show recSt = recover n inf level cleared from rfl,
      hframes.2.2.2.2.1, hfl]
    exact hkeep.firstlab
  have hcanonlabRec : recSt.canonlab = out.canonlab := by
    rw [show recSt = recover n inf level cleared from rfl, hframes.1, hcl]
  have hext : TrailExt level trail eventTrail :=
    TrailExt.ofPush hchild.node.preserved
  have hentry : eventTrail level = some
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩ :=
    hchild.node.preserved.pushAt
  have hlive : FirstLive ctx level recSt eventTrail rsLab rsPtn := by
    refine ⟨⟨hhistory, ?_, hstable⟩, ?_⟩
    · rw [hgfRec]
      exact hgcRec
    · intro γ hγ
      exact hstable level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
        (by rw [hgfRec]; exact Int.le_refl _) hentry γ hγ
  have hfirstTrail : FirstTrail ctx level recSt eventTrail :=
    hh.firstTrail.retrail hfirstlabRec hext
  have hstLab : st.lab.size = n := by
    exact hh.inv.run.searchOk.labSize
  have hstPtn : st.ptn.size = n := by
    exact hh.inv.run.searchOk.ptnSize
  have hstEnd : st.ptn[st.ptn.size - 1]! ≤ level :=
    searchOk_end hh.inv.nonempty hh.inv.run.searchOk hh.inv.positive
  have hcsz : out.canonlab.size = n := by
    exact hchild.node.event.canonSize
  have hcanonTrail : CanonTrail ctx level recSt eventTrail := by
    rcases hchild.canonGuide with hold | hnew
    · apply hh.canonTrail.retrail _ hext
      rw [hcanonlabRec, hold.2]
    · have hperm := hh.inv.childCanonPerm hcurrent hat hcsz hnew.2
      exact (CanonTrail.ofPerm hh.inv.run.trailOk hstLab hstPtn hstEnd hperm
        hcsz).retrail hcanonlabRec hext
  -- frame references
  have hrefs : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells recSt childBest := by
    constructor
    · intro _
      obtain ⟨o, ho, hdone, hatRef, hperm⟩ :=
        (hh.inv.refs.grow hgrows).first hh.guide
      refine ⟨o, ho, hdone, ?_, ?_⟩
      · rw [hfirstlabRec]
        exact hatRef
      · rw [hfirstlabRec]
        exact hperm
    · intro heqc
      have hcanonRec := recover_gcaCanon n inf level cleared
      rcases hchild.canonGuide with hold | hnew
      · have hcanonEq : st.gcaCanon = level := by
          rw [show recSt = recover n inf level cleared from rfl,
            hcanonRec, hgc] at heqc
          change (if level < out.gcaCanon then level else out.gcaCanon) =
            level at heqc
          rw [hold.1] at heqc
          change (if level < st.gcaCanon then level else st.gcaCanon) =
            level at heqc
          rw [ite_eq_right (Nat.not_lt_of_ge hh.inv.run.canonBound)] at heqc
          exact heqc
        obtain ⟨o, ho, hdone, hatRef, hperm⟩ :=
          (hh.inv.refs.grow hgrows).canon hcanonEq
        refine ⟨o, ho, hdone, ?_, ?_⟩
        · rw [hcanonlabRec, hold.2]
          exact hatRef
        · rw [hcanonlabRec, hold.2]
          exact hperm
      · have hmem : tcell.mem rsLab[tc + offset]! = true := by
          rw [hatFrozen]
          exact VSet.nextElem_mem hnext
        have hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn
            tc numcells childBest offset :=
          hcover.past offset hoffset hmem (by
            simp only [After, hatFrozen]
            omega)
        have hstInj : LabInj st.lab st.lab.size := by
          rw [hh.inv.run.searchOk.labSize]
          exact labInj_of_reach hh.inv.run.searchOk.labSize hh.inv.nonempty
            hh.inv.run.searchOk.reach
        have hcurrentPos : tc + currentOffset < st.lab.size := by
          rw [hstLab]
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcurrent tc)
            hh.inv.range
        have htcPtn : tc < st.ptn.size := by
          rw [hstPtn]
          exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hh.inv.range
        have hchildAt : (breakout n st.lab st.ptn (level + 1) tc tv).1[tc]! =
            tv := by
          rw [← hat, breakout_at_target hstInj hcurrentPos]
        have hchildCell : IsCell (breakout n st.lab st.ptn (level + 1) tc
            tv).2.1 (level + 1) tc 1 := by
          rw [breakout_ptn]
          exact isCell_breakout_target (n := n) (lab := st.lab) (tv := tv) htcPtn
            hh.inv.currentCell.2.1
        have houtAt : out.canonlab[tc]! = tv := by
          rw [← hchildAt]
          exact (cellsPerm_singleton hnew.2 hchildCell).symm
        have hperm := hh.inv.childCanonPerm hcurrent hat hcsz hnew.2
        have hperm' : cellsPerm rsPtn level rsLab out.canonlab := by
          rw [hh.inv.ptnEq] at hperm
          exact cellsPerm_trans hh.inv.labPerm hperm
        refine ⟨offset, hoffset, hdone, ?_, ?_⟩
        · rw [hcanonlabRec, houtAt, hatFrozen]
        · rw [hcanonlabRec]
          exact hperm'
  have hshortRec : recSt.needshortprune = false := by
    rw [show recSt = recover n inf level cleared from rfl,
      recover_needshortprune]
    exact hshort
  have hnclRec : recSt.noncheaplevel = if level < out.noncheaplevel
      then level + 1 else out.noncheaplevel := by
    rw [show recSt = recover n inf level cleared from rfl,
      recover_noncheaplevel, hncl]
  have hboundaryChild : out.noncheaplevel < level + 1 →
      out.noncheaplevel = st.noncheaplevel := hkeep.boundary
  refine ⟨bs', ?_⟩
  refine ⟨?_, hlive, hpath, ?_, ?_, ?_, hgfRec, hfirstTrail, hcanonTrail,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact {
      nonempty := hh.inv.nonempty
      positive := hh.inv.positive
      baseOk := hh.inv.baseOk
      run := hrun
      effect := heffect
      baseLab := hh.inv.baseLab
      basePtn := hh.inv.basePtn
      equitable := hh.inv.equitable
      cell := hh.inv.cell
      lenTwo := hh.inv.lenTwo
      range := hh.inv.range
      values := hh.inv.values
      members := hh.inv.members
      cover := hcover
      refs := hrefs
      shortClear := hshortRec
      fuelBound := hh.inv.fuelBound }
  · obtain ⟨v, hv, hle⟩ := hh.after
    have ha := nextElem_after hnext
    rw [hv] at ha
    simp only [After] at ha
    exact ⟨tv, rfl, by omega⟩
  · intro v hv
    cases hv
    exact hh.inv.nextLt hnext
  · apply recover_nonpositive
    rw [hcomp]
    exact hchild.node.event.nonpositive
  · rw [recover_orbits, recover_genTrace, horb, hgen]
    exact hkeep.orbits
  · rw [recover_coset, hcos]
    change out.cosetindex < n
    rw [hchild.coset]
    exact hh.inv.nextLt hnext
  · intro b hb
    obtain ⟨b0, hb0⟩ : ∃ b0, best = some b0 :=
      ⟨_, hh.inv.run.incumbent⟩
    obtain ⟨b', hb', hle⟩ := hgrows b0 hb0
    have hbb : b = b' := Option.some.inj (hb.symm.trans hb')
    subst hbb
    rw [hfirstlabRec]
    exact keyLe_trans (hh.firstDom b0 hb0) hle
  · intro hlt
    rw [hnclRec] at hlt
    rcases Decidable.em (level < out.noncheaplevel) with hc | hc
    · rw [ite_eq_left hc] at hlt
      exfalso
      omega
    · rw [ite_eq_right hc] at hlt
      rw [hboundaryChild (by omega)] at hlt
      exact hh.desc hlt
  · rw [hnclRec]
    rcases Decidable.em (level < out.noncheaplevel) with hc | hc
    · exact Nat.le_of_eq (ite_eq_left hc)
    · rw [ite_eq_right hc]
      omega
  · intro hpark
    rw [hnclRec]
    rcases Decidable.em (level < out.noncheaplevel) with hc | hc
    · rw [ite_eq_left hc]
      omega
    · rw [ite_eq_right hc]
      rw [hboundaryChild (by omega)]
      exact hh.park hpark
  · intro hlt
    rw [hnclRec] at hlt ⊢
    rcases Decidable.em (level < out.noncheaplevel) with hc | hc
    · rw [ite_eq_left hc] at hlt
      exfalso
      omega
    · rw [ite_eq_right hc] at hlt ⊢
      rw [hboundaryChild (by omega)] at hlt ⊢
      exact hh.keep hlt

end FirstSweepHyp

/-- Clearing the request keeps the labelling and partition. -/
theorem clearShortIf_lab (clear : Bool) (st : SearchSt n) :
    (clearShortIf clear st).lab = st.lab := by
  cases clear <;> rfl

theorem clearShortIf_ptn (clear : Bool) (st : SearchSt n) :
    (clearShortIf clear st).ptn = st.ptn := by
  cases clear <;> rfl

/-- The receiving-loop validity of a child's live short-prune pair, from
the child's return bound alone. -/
theorem shortPairAtReceiver {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    {fix mcr : VSet n}
    (hpathCodes : level = codes.length)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hrBelow : r < Int.ofNat (level + 1))
    (hevent : EventOut G ctx tcLevel codes fs out outBest eventTrail r)
    (hpreserved : TrailExt (level + 1)
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail)
    (hsource : ShortSource G ctx out eventTrail r)
    (hstay : ¬ r < Int.ofNat level)
    (hback : out.autos.back? = some (fix, mcr)) :
    PairOk ctx.g rsPtn rsLab level fix mcr := by
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

/-- Clearing the request exactly when it is raised leaves none. -/
theorem clearShortIf_self (st : SearchSt n) :
    (clearShortIf st.needshortprune st).needshortprune = false := by
  rcases h : st.needshortprune <;> simp [clearShortIf, h]

namespace FirstSweepHyp

/-- Both reference histories below the loop after an off-path child,
whatever its return. -/
theorem childTrails {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len tv offset currentOffset e tv1 : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best childBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
   
    (hh : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e tv1 base st best trail)
    (hcurrent : currentOffset < len)
    (hat : st.lab[tc + currentOffset]! = tv)
    (hchild : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      out (numcells + 1) best childBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hfirstlab : out.firstlab = st.firstlab) :
    FirstTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
        eventTrail ∧
      CanonTrail ctx level { out with fixedpts := out.fixedpts.erase tv }
        eventTrail := by
  have hext : TrailExt level trail eventTrail :=
    TrailExt.ofPush hchild.node.preserved
  refine ⟨hh.firstTrail.retrail hfirstlab hext, ?_⟩
  have hstLab : st.lab.size = n := by
    exact hh.inv.run.searchOk.labSize
  have hstPtn : st.ptn.size = n := by
    exact hh.inv.run.searchOk.ptnSize
  have hstEnd : st.ptn[st.ptn.size - 1]! ≤ level :=
    searchOk_end hh.inv.nonempty hh.inv.run.searchOk hh.inv.positive
  have hcsz : out.canonlab.size = n := by
    exact hchild.node.event.canonSize
  rcases hchild.canonGuide with hold | hnew
  · apply hh.canonTrail.retrail _ hext
    exact hold.2
  · have hperm := hh.inv.childCanonPerm hcurrent hat hcsz hnew.2
    exact (CanonTrail.ofPerm hh.inv.run.trailOk hstLab hstPtn hstEnd hperm
      hcsz).retrail rfl hext

end FirstSweepHyp

end Hex.GraphIso.Nauty

/-!
The first-path sibling sweep, part three: the cursor-fuel induction after
the guiding child, the guiding child itself, and the conversion of the
whole sweep back to the enclosing first-path node.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # The sweep induction after the guiding child -/

set_option maxHeartbeats 3200000 in
/-- Totality of the first-path sweep after its guiding child, at every
cursor fuel exceeding the remaining cursor range, given totality of every
off-path child. -/
theorem firstTail {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tv1 tail e : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat} {base : SearchSt n}
    {bound : Key n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (hrun : n + 2 < level + 1 + runFuel)
    (hspec : level + 1 + specFuel = n + 1)
    (hpath : level = codes.length) (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1) :
    ∀ (loopFuel : Nat) (cursor : Option Nat) (tcell : VSet n) (st : SearchSt n)
      (best : Option (Key n)) (trail : FrameTrail) (bs : List Nat) (index : Nat),
      FirstSweepHyp G ctx tcLevel specFuel level codes bs fs numcells rsLab
        rsPtn tc len tcell cursor e tv1 base st best trail →
      n < cursorRank cursor + loopFuel →
      ∃ outBest eventTrail,
        FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem codes
            fs rsLab rsPtn tc len numcells tcell cursor bound st
            (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell index st).2.2
            best outBest trail eventTrail
            (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell index st).1 ∧
          FirstSweepKeep ctx level e fs st
            (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
              tv1 (tcell.nextElem cursor) tcell index st).2.2
            outBest := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro cursor tcell st best trail bs index hh hfuel
      exfalso
      have := cursorRank_le hh.cursorLt
      omega
  | succ loopFuel ihLoop =>
    intro cursor tcell st best trail bs index hh hfuel
    have hgsz : ctx.g.size = n := by
      rw [hg]
      exact size_rowsOf G
    have hsymm : ∀ u v, u < n → v < n →
        (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
      rw [hg]
      exact rowsOf_symm G
    have hloopless : ∀ v, v < n → (ctx.g[v]!).mem v = false := by
      rw [hg]
      exact rowsOf_loopless G
    have hlevelLt : level < n := hh.inv.levelLt
    have hfuelNe : runFuel ≠ 0 := by
      intro h0
      rw [h0] at hrun
      omega
    have hcodesLen : codes.length = level := hpath.symm
    have hshorter : stem.length < codes.length := by
      rw [← hpath]
      exact hpast
    have hguideLe : level ≤ st.gcaFirst := Nat.le_of_eq hh.guide.symm
    rcases hnext : tcell.nextElem cursor with _ | tv
    · -- the sweep is finished
      have hsame : (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1)
          level numcells tc tv1 none tcell index st).2.2 = st := by
        unfold firstChildLoop
        rfl
      refine ⟨best, trail, ?_, ?_⟩
      · exact FirstSweepRun.done (inf := inf) (runFuel := runFuel)
          (loopFuel := loopFuel) (tv1 := tv1) (index := index) hpath hstem
          hpast hnext hh.sign hbound hlen hh.inv hh.live.toLive hh.firstTrail
          hh.canonTrail hguideLe
      · rw [hsame]
        exact ⟨hh.firstDom, rfl, hh.orbits, hh.coset, hh.keep⟩
    · -- one more vertex
      have htvLt : tv < n := hh.inv.nextLt hnext
      have hafter : tv1 < tv := by
        obtain ⟨v, hv, hle⟩ := hh.after
        have ha := nextElem_after hnext
        rw [hv] at ha
        simp only [After] at ha
        omega
      have hother : (tv == tv1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      obtain ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen, hat⟩ :=
        hh.inv.nextOffsets hnext
      have hfuelRec : n < cursorRank (some tv) + loopFuel :=
        cursorFuel_step (nextElem_after hnext) hfuel
      rcases horb : (st.orbits[tv]! == tv) with _ | _
      · -- an orbit skip
        have hinj : LabInj rsLab rsLab.size := by
          rw [← hh.inv.baseLab, hh.inv.baseOk.labSize]
          exact labInj_of_reach hh.inv.baseOk.labSize hh.inv.nonempty
            hh.inv.baseOk.reach
        have hcover := hh.inv.cover.orbitSkip hnext hoffset hatFrozen hgsz
          (fun γ hγ => hh.inv.run.genTraceOk.check hγ) hh.live.frameStab
          hh.inv.frozenLabSize hinj hh.inv.frozenLabOk hh.inv.frozenPtnSize
          hh.inv.frozenEnd hh.inv.frozenVals hh.inv.cell hh.inv.range
          hh.inv.fuelBound hh.orbits (by
            intro heq
            rw [heq] at horb
            simp at horb)
        have hhSkip : FirstSweepHyp G ctx tcLevel specFuel level codes bs fs
            numcells rsLab rsPtn tc len tcell (some tv) e tv1 base st best
            trail :=
          ⟨{ hh.inv with cover := hcover }, hh.live, hh.path,
            ⟨tv, rfl, Nat.le_of_lt hafter⟩,
            fun v hv => by cases hv; exact htvLt, hh.sign, hh.guide,
            hh.firstTrail, hh.canonTrail, hh.orbits, hh.coset, hh.firstDom,
            hh.desc, hh.bnd, hh.park, hh.keep⟩
        have hstate := firstChildLoop_skip ctx inf tcLevel runFuel loopFuel
          level numcells tc tv1 tv tcell index st horb
        obtain ⟨outBest, eventTrail, hrunTail, hkeepTail⟩ :=
          ihLoop (some tv) tcell st best trail bs
            (if (st.orbits[tv]! == tv1) = true then index + 1 else index)
            hhSkip hfuelRec
        refine ⟨outBest, eventTrail, ?_, ?_⟩
        · rw [hstate]
          exact hrunTail.step (nextElem_after hnext)
        · rw [hstate]
          exact hkeepTail
      · -- an off-path child
        have hcheapOk := hh.cheapOk hg
        obtain ⟨offset', currentOffset', hoffset', hcurrent', hatFrozen',
            hat', hnodeChild⟩ :=
          hh.inv.child (coset := tv) hnext hcheapOk
        rw [hat'] at hnodeChild
        have hlabOk : LabOk st.lab n := by
          exact labOk_of_reach hh.inv.run.searchOk.labSize
            hh.inv.run.searchOk.reach
        have hinj : LabInj st.lab n := by
          exact labInj_of_reach hh.inv.run.searchOk.labSize hh.inv.nonempty
            hh.inv.run.searchOk.reach
        have hsz : st.lab.size = n := by
          exact hh.inv.run.searchOk.labSize
        have hfresh : st.fixedpts.mem tv = false := by
          rw [← hat]
          exact hh.path.fixed.fresh hlabOk hinj hsz hh.inv.currentCell
            hh.inv.lenTwo hh.inv.range hcurrent
        let child : SearchSt n :=
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
            fixedpts := st.fixedpts.insert tv
            cosetindex := tv }
        let childTrail := trail.push level
          ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset'⟩
        have hdescChild := hh.inv.childDescWeak hg hh.desc hh.bnd hh.park
          hcurrent hat
        have hliveChild : Live ctx (level + 1) child childTrail := by
          have := hh.inv.firstChildLive (coset := tv) hh.live offset'
            currentOffset'
          rw [hat'] at this
          exact this
        have hpathChild : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
            (initialPartition G).1 (level + 1) child := by
          have := hh.path.breakout hh.inv hcurrent
          rw [hat] at this
          exact this.stateEq rfl rfl rfl
        obtain ⟨childBest, eventTrail, hrunChild, hkeepChild⟩ :=
          ih specFuel (level + 1) (numcells + 1) codes bs fs child best
            childTrail hg hinf hn0 (by omega) (by omega) (by omega)
            (by omega) hh.bnd hdescChild hnodeChild hliveChild hpathChild
            hh.orbits htvLt hh.firstDom
        obtain ⟨value, out, hcall⟩ : ∃ value out,
            otherNode ctx inf tcLevel runFuel (level + 1) (numcells + 1)
              child = (value, out) := ⟨_, _, rfl⟩
        have hout : SearchOut G level (level + 1) child out := by
          have := otherNode_ok G ctx inf hinf tcLevel hn0 runFuel
            (level + 1) (numcells + 1) child hnodeChild.run.searchOk
            (by omega) (by omega)
          rw [Nat.add_sub_cancel, hcall] at this
          exact this
        rw [hcall] at hrunChild hkeepChild
        dsimp only at hrunChild hkeepChild
        have heq0 := hh.inv.childKeyAll hoffset' hatFrozen' hat'
        have heq : ∀ o, o < len → rsLab[tc + o]! = tv →
            sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
              numcells o =
            nodeKey ctx tcLevel specFuel (level + 1) codes child
              (numcells + 1) := by
          intro o ho h
          exact (heq0 o ho h).trans (nodeKey_congr rfl rfl rfl).symm
        have hkeyLe : keyLe (nodeKey ctx tcLevel specFuel (level + 1) codes
            child (numcells + 1)) bound := by
          rw [← heq offset' hoffset' hatFrozen']
          exact LoopInv.keyLeBound hbound hlen hoffset'
        have hsoundChild : NodeSound ctx tcLevel specFuel (level + 1) codes
            child (numcells + 1) best childBest :=
          hrunChild.toProof.outcome.node.receipt.sound hfuelNe
        have hgrows : IncGrows best childBest := hrunChild.grows hfuelNe
        have hfirstlabChild : out.firstlab = st.firstlab :=
          hkeepChild.firstlab
        have hboundaryChild : out.noncheaplevel < level + 1 →
            out.noncheaplevel = st.noncheaplevel :=
          hkeepChild.boundary
        have htrailExt : TrailExt level trail eventTrail :=
          TrailExt.ofPush hrunChild.node.preserved
        have hcosetChild : out.cosetindex = tv := hrunChild.coset
        -- domination of the first leaf by the child's incumbent
        have hdomChild : ∀ b, childBest = some b →
            keyLe (pathLeafKey ctx fs out.firstlab) b := by
          intro b hb
          obtain ⟨b0, hb0⟩ : ∃ b0, best = some b0 :=
            ⟨_, hh.inv.run.incumbent⟩
          obtain ⟨b', hb', hle⟩ := hgrows b0 hb0
          have hbb : b = b' := Option.some.inj (hb.symm.trans hb')
          subst hbb
          rw [hfirstlabChild]
          exact keyLe_trans (hh.firstDom b0 hb0) hle
        by_cases hstay : value < Int.ofNat level
        · -- early exit
          obtain ⟨htrail, hcanon⟩ := hh.childTrails hcurrent hat
            (r := value) hrunChild hfirstlabChild
          have hstate := firstChildLoop_earlyOther ctx inf tcLevel runFuel
            loopFuel level numcells tc tv1 tv tcell index st value out horb
            hother hcall hstay
          have hkeepOut : FirstSweepKeep ctx level e fs st
              (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
                numcells tc tv1 (some tv) tcell index st).2.2 childBest := by
            rw [hstate]
            refine ⟨hdomChild, hfirstlabChild, hkeepChild.orbits, ?_, ?_⟩
            · change out.cosetindex < n
              rw [hcosetChild]
              exact htvLt
            · intro hlt
              change out.noncheaplevel < level at hlt
              change out.noncheaplevel = e
              have hb := hboundaryChild (Nat.lt_succ_of_lt hlt)
              rw [hb] at hlt ⊢
              exact hh.keep hlt
          refine ⟨childBest, eventTrail, ?_, hkeepOut⟩
          rcases hexit : hrunChild.node.exit with
            ⟨returned, exact⟩ |
            ⟨target, returned, below, sound, payload, located, control⟩ |
            ⟨below, exact, freeze⟩ |
            ⟨boundary, returned, positive, atOrAbove, saved, exact⟩ |
            ⟨returned, state, incumbent, emptyFuel⟩
          · exfalso
            rw [returned] at hstay
            simp only [Int.ofNat_eq_natCast] at hstay
            omega
          · have hbelowNat : target < level := by
              rw [returned] at hstay
              exact Int.ofNat_lt.mp hstay
            exact FirstSweepRun.childUnwind hstem hshorter horb hother hcall
              hsoundChild hkeyLe returned hbelowNat payload located control
              hrunChild hfresh htrail hcanon hguideLe
          · exact FirstSweepRun.childFrozen hpath hstem hshorter horb hother
              hcall hrunChild hstay freeze exact hkeyLe hbound hlen
              (hh.inv.cover.advanceKey hnext exact heq) hfresh htrail hcanon
              hguideLe
          · have hbelowNat : boundary ≤ level := by
              rw [returned] at hstay
              simp only [Int.ofNat_eq_natCast] at hstay
              omega
            have hle : st.noncheaplevel ≤ level := by
              have h1 := hboundaryChild (by rw [saved]; omega)
              rw [saved] at h1
              omega
            have hsmall := hh.inv.subtreeAtWeak hh.desc hh.park hle
             
            have hboundEq : bound = nodeKey ctx tcLevel specFuel (level + 1)
                codes child (numcells + 1) := by
              rw [← heq offset' hoffset' hatFrozen']
              exact hh.inv.boundEq hsmall hgsz hsymm hloopless hbound
                hlen hoffset'
            rw [returned] at hcall hrunChild
            exact FirstSweepRun.childCheap hstem hshorter horb hother hcall
              hrunChild positive hbelowNat saved hboundEq exact hfresh htrail
              hcanon hguideLe
          · exact (hfuelNe emptyFuel).elim
        · -- the child stays at the loop level
          let cleaned : SearchSt n :=
            { out with fixedpts := out.fixedpts.erase tv }
          let cleared := clearShortIf out.needshortprune cleaned
          let recSt := recover n inf level cleared
          let tcell' := if out.needshortprune then shortprune tcell cleared
            else tcell
          have hshortRec : cleared.needshortprune = false :=
            clearShortIf_self cleaned
          obtain ⟨bs', hhRec⟩ := hh.next hg hinf hcodesLen hfuelNe hnext
            hoffset' hcurrent' hatFrozen' hat' hrunChild hkeepChild hstay hout
            out.needshortprune hshortRec
          have hinvRec : LoopInv G ctx tcLevel specFuel level codes bs' fs
              numcells rsLab rsPtn tc len tcell' (some tv) base recSt
              childBest eventTrail := by
            rcases hshortC : out.needshortprune with _ | _
            · simpa only [tcell', recSt, cleared, cleaned, hshortC,
                Bool.false_eq_true, ite_false] using hhRec.inv
            · have hlast : ∀ fix mcr : VSet n,
                  cleared.autos.back? = some (fix, mcr) →
                    PairOk ctx.g rsPtn rsLab level fix mcr := by
                intro fix mcr hback
                apply LoopInv.ShortSource.atReceiver hpath hh.inv hh.path
                  hrunChild.node.exit hrunChild.node.event
                  hrunChild.node.preserved (hrunChild.node.short hshortC)
                  hstay
                simpa only [cleared, cleaned, clearShortIf, hshortC, ite_true]
                  using hback
              simpa only [tcell', recSt, cleared, cleaned, hshortC, ite_true]
                using hhRec.inv.shortpruneWith hgsz hlast
          have hhRec' := hhRec.filter hinvRec
          obtain ⟨outBest, eventTrail', hrunTail, hkeepTail⟩ :=
            ihLoop (some tv) tcell' recSt childBest eventTrail bs'
              (if (recSt.orbits[tv]! == tv1) = true then index + 1 else index)
              hhRec' hfuelRec
          have hfixedRec : recSt.fixedpts = st.fixedpts := by
            change (recover n inf level cleared).fixedpts = st.fixedpts
            rw [recover_clearShortIf, (clearShortIf_fields _ _).1,
              recover_fixedpts]
            change out.fixedpts.erase tv = st.fixedpts
            rw [hrunChild.node.fixed, erase_insert_of_miss hfresh]
          have hpre : LoopSound ctx bound best childBest :=
            LoopSound.ofNode hsoundChild hkeyLe
          have hstate := firstChildLoop_stayOther ctx inf tcLevel runFuel
            loopFuel level numcells tc tv1 tv tcell index st value out horb
            hother hcall hstay
          dsimp only at hstate
          refine ⟨outBest, eventTrail', ?_, ?_⟩
          · exact (FirstSweepRun.nextOther hnext horb hother hcall hstay
              hfixedRec hpre hrunTail).retrail htrailExt
          · rw [hstate]
            refine ⟨hkeepTail.dom, ?_, hkeepTail.orbits, hkeepTail.coset,
              hkeepTail.boundary⟩
            rw [hkeepTail.firstlab]
            change (recover n inf level cleared).firstlab = st.firstlab
            rw [recover_firstlab, (clearShortIf_fields _ _).2.2.2.2.2.1]
            exact hfirstlabChild

/-- A node exit depends on its receipt trail only at its unwind target. -/
theorem NodeExit.retrail {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {source dest : FrameTrail} {r : Int}
    (htrail : ∀ target, target < level → source target = dest target)
    (h : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
      best outBest source r) :
    NodeExit ctx tcLevel specFuel runFuel level codes st out numcells best
      outBest dest r := by
  cases h with
  | done returned exact => exact .done returned exact
  | unwind target returned below sound payload located control =>
      exact .unwind target returned below sound payload
        (located.retrail (htrail target below)) control
  | frozen below exact freeze => exact .frozen below exact freeze
  | cheap boundary returned positive atOrAbove saved exact =>
      exact .cheap boundary returned positive atOrAbove saved exact
  | exhausted returned state incumbent emptyFuel =>
      exact .exhausted returned state incumbent emptyFuel

/-! # The whole sweep from its guiding child -/

/-- What the whole first-path sweep establishes for its enclosing node,
relative to the node entry boundary `e`. -/
structure FirstSweepOut (ctx : Ctx n) (level e : Nat) (fs : List Nat)
    (out : SearchSt n) (outBest : Option (Key n)) : Prop where
  dom : ∀ b, outBest = some b → keyLe (pathLeafKey ctx fs out.firstlab) b
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  coset : out.cosetindex < n
  boundary : out.noncheaplevel < level → out.noncheaplevel = e

/-- The sweep bound is every child's key once the frozen frame is a
verified small-cell subtree. -/
theorem boundEq_of_subtree {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells tail offset : Nat} {active : VSet n}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {bound : Key n}
    (hsmall : SubtreeOk ctx level
      { lab := rsLab, ptn := rsPtn, active := active,
        numcells := numcells, hint := 0, maxpos := 0,
        longcode := numcells })
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : IsCell rsPtn level tc len) (hlen2 : 2 ≤ len)
    (hrange : tc + len ≤ n)
    (hfuel : level + 1 + specFuel ≤ n + 1)
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
      hsmall hgsz hsymm hloop hcell hlen2 hrange hoffset ho hfuel
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

set_option maxHeartbeats 6400000 in
/-- Totality of the whole first-path sibling sweep of an internal node on
the first descent, from the parked refined state at cursor `none`, given
totality of the guiding child through `FirstTotal` and of every later
sibling through `OtherTotal`. -/
theorem firstLoopTotal {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells tc len tail : Nat}
    {cs : List Nat} {st : SearchSt n} {trail : FrameTrail} {bound : Key n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (ihFirst : FirstTotal G ctx inf tcLevel runFuel)
    (hrun : n + 2 < level + 1 + runFuel)
    (hspec : level + 1 + specFuel = n + 1)
    (hlevel : 1 ≤ level) (hpath : level = cs.length + 1) (hlt : level < n)
    (hfirst : FirstInv G ctx level cs numcells st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcell : IsCell (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tc len)
    (hlen2 : 2 ≤ len) (hrange : tc + len ≤ n)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level
        (cs ++ [(refine ctx level st.lab st.ptn st.active numcells).longcode])
        (refine ctx level st.lab st.ptn st.active numcells).lab
        (refine ctx level st.lab st.ptn st.active numcells).ptn tc
        (refine ctx level st.lab st.ptn st.active numcells).numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level
          (cs ++ [(refine ctx level st.lab st.ptn st.active
            numcells).longcode])
          (refine ctx level st.lab st.ptn st.active numcells).lab
          (refine ctx level st.lab st.ptn st.active numcells).ptn tc
          (refine ctx level st.lab st.ptn st.active numcells).numcells
          (o + 1)))
    (hlen : len = tail + 1) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [r.longcode]
    let pre0 : SearchSt n := { st with
      lab := r.lab
      ptn := r.ptn
      active := r.active
      firstcode := st.firstcode.set! level r.longcode
      firsttc := st.firsttc.set! level (Int.ofNat tc)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + len }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let tcell := windowSet n r.lab tc len
    let tv1 := (tcell.nextElem none).getD 0
    ∃ fs outBest eventTrail,
      FirstSweepRun G ctx tcLevel specFuel runFuel (n + 1) level cs full
          fs r.lab r.ptn tc len r.numcells tcell none bound pre
          (firstChildLoop ctx inf tcLevel runFuel (n + 1) level
            r.numcells tc tv1 (tcell.nextElem none) tcell 0 pre).2.2
          none outBest trail eventTrail
          (firstChildLoop ctx inf tcLevel runFuel (n + 1) level
            r.numcells tc tv1 (tcell.nextElem none) tcell 0 pre).1 ∧
        FirstSweepOut ctx level st.noncheaplevel fs
          (firstChildLoop ctx inf tcLevel runFuel (n + 1) level
            r.numcells tc tv1 (tcell.nextElem none) tcell 0 pre).2.2
          outBest := by
  intro r full pre0 pre tcell tv1
  obtain ⟨hit, heqt, hcount⟩ := hfirst.refined hg hn0 hlevel
  have hgsz : ctx.g.size = n := by
    rw [hg]
    exact size_rowsOf G
  have hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
    rw [hg]
    exact rowsOf_symm G
  have hloopless : ∀ v, v < n → (ctx.g[v]!).mem v = false := by
    rw [hg]
    exact rowsOf_loopless G
  have hfuelNe : runFuel ≠ 0 := by
    intro h0
    rw [h0] at hrun
    omega
  have hfull : full.length = level := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take cs.length = cs := by
    simp only [full, List.take_left']
  have hpast : cs.length < level := by omega
  have hshorter : cs.length < full.length := by
    rw [hfull]
    exact hpast
  have hfuel : level + 1 + specFuel ≤ n + 1 := by
    omega
  have hls : r.lab.size = n := hit.ok.labSize
  have hlabOk : LabOk r.lab n := hit.ok.labOk
  have hps : r.ptn.size = n := hit.ok.ptnSize
  have hend : r.ptn[r.ptn.size - 1]! ≤ level := hit.ok.ptnEnd
  have hinj : LabInj r.lab n := hit.inj
  have hvals : ∀ q : Nat, r.ptn[q]! ≤ level ∨ r.ptn[q]! = n + 2 := by
    intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · exact hit.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [hps]; omega)]
      exact Nat.zero_le _
  -- the start state
  have hpreLab : pre.lab = r.lab := by
    simp only [pre]
    split <;> rfl
  have hprePtn : pre.ptn = r.ptn := by
    simp only [pre]
    split <;> rfl
  have hpreActive : pre.active = r.active := by
    simp only [pre]
    split <;> rfl
  have hpreFixed : pre.fixedpts = st.fixedpts := by
    simp only [pre]
    split <;> rfl
  have hpreOrbits : pre.orbits = st.orbits := by
    simp only [pre]
    split <;> rfl
  have hpreGen : pre.genTrace = st.genTrace := by
    simp only [pre]
    split <;> rfl
  have hpreFirstlab : pre.firstlab = st.firstlab := by
    simp only [pre]
    split <;> rfl
  have hpreCanonlab : pre.canonlab = st.canonlab := by
    simp only [pre]
    split <;> rfl
  have hpreShort : pre.needshortprune = false := by
    simp only [pre]
    split <;> exact hfirst.shortClear
  have hpreNclEq : pre.noncheaplevel = if st.noncheaplevel ≥ level ∧
      ¬ cheapautom r.ptn level n = true then level + 1
      else st.noncheaplevel := by
    by_cases hc : st.noncheaplevel ≥ level ∧
      ¬ cheapautom r.ptn level n = true
    · simp only [pre, pre0, ite_eq_left hc]
    · simp only [pre, pre0, ite_eq_right hc]
  have hpreNcl : pre.noncheaplevel = st.noncheaplevel ∨
      (pre.noncheaplevel = level + 1 ∧
        cheapautom r.ptn level n = false ∧ st.noncheaplevel ≥ level) := by
    rw [hpreNclEq]
    by_cases hc : st.noncheaplevel ≥ level ∧
      ¬ cheapautom r.ptn level n = true
    · rw [ite_eq_left hc]
      right
      refine ⟨rfl, ?_, hc.1⟩
      rcases hc' : cheapautom r.ptn level n with _ | _
      · rfl
      · exact absurd hc' hc.2
    · rw [ite_eq_right hc]
      left
      rfl
  have hpreParkWeak : cheapautom r.ptn level n = false →
      pre.noncheaplevel ≠ level := by
    intro hc heq
    rw [hpreNclEq] at heq
    by_cases hc' : st.noncheaplevel ≥ level ∧
      ¬ cheapautom r.ptn level n = true
    · rw [ite_eq_left hc'] at heq
      omega
    · rw [ite_eq_right hc'] at heq
      exact hc' ⟨by omega, by simp [hc]⟩
  have hpreBnd : pre.noncheaplevel ≤ level + 1 := by
    rcases hpreNcl with h | h <;> omega
  have hpreKeep : pre.noncheaplevel < level →
      pre.noncheaplevel = st.noncheaplevel := by
    intro hlt'
    rcases hpreNcl with h | h
    · exact h
    · omega
  have hpreOk : SearchOk G level r.numcells pre :=
    refine_searchOk hn0 hfirst.searchOk hlevel hpreLab hprePtn
      (Or.inl hpreCanonlab)
  have hpathPre : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level pre :=
    (hpathOk.refine hn0 hlevel hgsz hfirst.searchOk
      hfirst.activeStarts).stateEq hpreLab hprePtn hpreFixed
  have hcellPre : IsCell pre.ptn level tc len := by
    rw [hprePtn]
    exact hcell
  have horbPre : OrbSound (OrbConn pre.genTrace.toList n) pre.orbits
      n := by
    rw [hpreGen, hpreOrbits]
    exact horb
  -- the guiding vertex
  obtain ⟨v, hv⟩ := nextElem_windowSet_some (lab := r.lab) (tc := tc)
    (len := len) (by omega) (hlabOk _ (by rw [hit.ok.labSize]; omega))
  have hnext : tcell.nextElem none = some tv1 := by
    simp only [tv1, tcell, hv, Option.getD_some]
  have hmem : tv1 ∈ segN r.lab tc len := by
    exact (mem_windowSet.mp (VSet.nextElem_mem hnext)).2
  obtain ⟨o, ho, hato⟩ : ∃ o, o < len ∧ r.lab[tc + o]! = tv1 := by
    simp only [segN, List.mem_map, List.mem_range] at hmem
    obtain ⟨o, ho, h⟩ := hmem
    exact ⟨o, ho, h⟩
  have hat : pre.lab[tc + o]! = tv1 := by
    rw [hpreLab]
    exact hato
  have htvLt : tv1 < n := by
    rw [← hato]
    exact hlabOk _ (by omega)
  have hrep : (pre.orbits[tv1]! == tv1) = true := by
    rw [hpreOrbits, hfirst.orbitId tv1 htvLt]
    simp
  have hfirstTv : (tv1 == tv1) = true := by simp
  have hfresh : pre.fixedpts.mem tv1 = false := by
    rw [← hat]
    apply hpathPre.fixed.fresh
    · rw [hpreLab]; exact hlabOk
    · rw [hpreLab]; exact hinj
    · rw [hpreLab]; exact hls
    · exact hcellPre
    · exact hlen2
    · exact hrange
    · exact ho
  -- the guiding child
  let child : SearchSt n :=
    { pre with
      lab := (breakout n pre.lab pre.ptn (level + 1) tc tv1).1
      ptn := (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.1
      active := (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.2
      fixedpts := pre.fixedpts.insert tv1
      cosetindex := tv1 }
  let childTrail := trail.push level
    ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩
  have hfirstChild : FirstInv G ctx (level + 1) full (r.numcells + 1) child
      childTrail := by
    have h := hfirst.child (specFuel := specFuel) hg hn0 hpath hlt hcell
      hlen2 hrange ho
    dsimp only at h
    rw [show pre.lab[tc + o]! = tv1 from hat] at h
    exact h
  have hpathChild : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 (level + 1) child := by
    have h := hfirst.childPath hg hn0 hpath
      hpathOk hcell hlen2 hrange ho
    dsimp only at h
    rw [show pre.lab[tc + o]! = tv1 from hat] at h
    exact h
  have hchildNcl : child.noncheaplevel = pre.noncheaplevel := rfl
  have hdescChild : CheapDesc ctx (level + 1) child.noncheaplevel
      (refine ctx (level + 1) child.lab child.ptn child.active
        (r.numcells + 1)) := by
    have hlvl : level < n := hlt
    have h := hdesc.child hit heqt hcount hsymm hlvl hcell hlen2 hrange ho
    dsimp only at h
    rw [hato] at h
    change CheapDesc ctx (level + 1) _
      (refine ctx (level + 1) (breakout n r.lab r.ptn (level + 1) tc tv1).1
        (r.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (r.numcells + 1)) at h
    change CheapDesc ctx (level + 1) pre.noncheaplevel
      (refine ctx (level + 1) (breakout n pre.lab pre.ptn (level + 1) tc tv1).1
        (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.1
        (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.2 (r.numcells + 1))
    rw [breakout_ptn, hpreLab, hprePtn, hpreNclEq]
    exact h
  obtain ⟨fs, outBest, eventTrail, hrunG, hkeepG⟩ :=
    ihFirst specFuel (level + 1) (r.numcells + 1) full child childTrail
      hg hinf hn0 (by omega) (by rw [hfull]) (by omega) (by omega)
      (by rw [hchildNcl]; exact hpreBnd) hdescChild horbPre hfirstChild
      hpathChild
  obtain ⟨value, out, hcall⟩ : ∃ value out,
      firstPathNode ctx inf tcLevel runFuel (level + 1) (r.numcells + 1)
        child = (value, out) := ⟨_, _, rfl⟩
  have hout : SearchOut G level (level + 1) child out := by
    have := (firstPathNode_ok G ctx inf hinf tcLevel hn0 runFuel
      (level + 1) (r.numcells + 1) child hfirstChild.searchOk (by omega)
      (by omega)).1
    rw [Nat.add_sub_cancel, hcall] at this
    exact this
  rw [hcall] at hrunG hkeepG
  dsimp only at hrunG hkeepG
  have hgca : level + 1 ≤ out.gcaFirst := hkeepG.guide
  have horderG : level + 1 ≤ out.gcaCanon :=
    Nat.le_trans hgca hrunG.proof.order
  have hsoundG : NodeSound ctx tcLevel specFuel (level + 1) full child
      (r.numcells + 1) none outBest :=
    hrunG.proof.node.outcome.receipt.sound hfuelNe
  -- the guiding child's key is one of the swept keys
  have hkeyEq : ∀ o', o' < len → r.lab[tc + o']! = tv1 →
      sweepKey ctx tcLevel specFuel level full r.lab r.ptn tc r.numcells o' =
        nodeKey ctx tcLevel specFuel (level + 1) full child
          (r.numcells + 1) := by
    intro o' ho' hato'
    have hoo : o' = o := by
      have := hinj.eq_of_getElem! (i := tc + o') (j := tc + o)
        (by omega) (by omega) (hato'.trans hato.symm)
      omega
    subst hoo
    have h := SearchOut.breakoutKey (ctx := ctx) (codes := full) (specFuel := specFuel)
      (tcLevel := tcLevel) (SearchOut.refl G level level hpreOk.reach)
      hpreOk hpreOk hn0 hlevel hcellPre hlen2 hrange ho
      (child := child) (by rw [hat]) (by rw [hat]) (by rw [hat]) rfl
      hfuel
    rw [hpreLab, hprePtn] at h
    exact h
  have hkeyG : keyLe (nodeKey ctx tcLevel specFuel (level + 1) full child
      (r.numcells + 1)) bound := by
    rw [← hkeyEq o ho hato]
    exact LoopInv.keyLeBound hbound hlen ho
  have hpreG : LoopSound ctx bound none outBest :=
    LoopSound.ofNode hsoundG hkeyG
  have hdoneOf : outBest = some (incMax none
      (nodeKey ctx tcLevel specFuel (level + 1) full child
        (r.numcells + 1))) →
      ChildDone ctx tcLevel specFuel level full r.lab r.ptn tc r.numcells
        outBest o := by
    intro hfullKey
    apply ChildDone.ofExact hfullKey
    · rw [hato]
      change (breakout n pre.lab pre.ptn (level + 1) tc tv1).1 = _
      rw [hpreLab, hprePtn]
    · rw [hato]
      change (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.1 = _
      rw [hpreLab, hprePtn]
    · rw [hato]
      change (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.2 = _
      rw [hpreLab, hprePtn]
  have hcoverOf : outBest = some (incMax none
      (nodeKey ctx tcLevel specFuel (level + 1) full child
        (r.numcells + 1))) →
      SweepCover ctx tcLevel specFuel level full r.lab r.ptn tc len
        r.numcells tcell (some tv1) outBest := by
    intro hfullKey
    exact (sweepCover_init ctx tcLevel specFuel level full r.lab r.ptn tc len
      r.numcells none (fun o ho => hlabOk _ (by rw [hit.ok.labSize]; omega))).advanceKey
      hnext hfullKey hkeyEq
  have horbOut : OrbSound (OrbConn out.genTrace.toList n) out.orbits
      n :=
    hkeepG.orbits
  have hcosetOut : out.cosetindex < n := hkeepG.coset htvLt
  have hboundaryG : out.noncheaplevel < level + 1 →
      out.noncheaplevel = pre.noncheaplevel := hkeepG.boundary
  have hext : TrailExt level trail eventTrail :=
    TrailExt.ofPush hrunG.proof.node.outcome.preserved
  have hentry : eventTrail level = some
      ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩ :=
    hrunG.proof.node.outcome.preserved.pushAt
  rw [hnext]
  refine ⟨fs, ?_⟩
  by_cases hstay : value < Int.ofNat level
  · -- the guiding child exits below the loop
    have hstate := firstChildLoop_earlyGuide ctx inf tcLevel runFuel n
      level r.numcells tc tv1 tv1 tcell 0 pre value out hrep hfirstTv hcall
      hstay
    have hkeepOut : FirstSweepOut ctx level st.noncheaplevel fs
        (firstChildLoop ctx inf tcLevel runFuel (n + 1) level r.numcells
          tc tv1 (some tv1) tcell 0 pre).2.2 outBest := by
      rw [hstate]
      refine ⟨hkeepG.dom, horbOut, hcosetOut, ?_⟩
      intro hlt'
      change out.noncheaplevel < level at hlt'
      change out.noncheaplevel = st.noncheaplevel
      have hb := hboundaryG (Nat.lt_succ_of_lt hlt')
      rw [hb] at hlt' ⊢
      exact hpreKeep hlt'
    refine ⟨outBest, eventTrail, ?_, hkeepOut⟩
    rcases hexit : hrunG.exit with
      ⟨returned, exact⟩ |
      ⟨target, returned, below, sound, payload, located, control⟩ |
      ⟨below, exact, freeze⟩ |
      ⟨boundary, returned, positive, atOrAbove, saved, exact⟩ |
      ⟨returned, state, incumbent, emptyFuel⟩
    · exfalso
      rw [returned] at hstay
      simp only [Int.ofNat_eq_natCast] at hstay
      omega
    · exfalso
      have htarget : target < level := by
        rw [returned] at hstay
        exact Int.ofNat_lt.mp hstay
      rcases control with h | h <;> omega
    · exact FirstSweepRun.guideFrozen hfull.symm hstem hshorter hrep hfirstTv
        hcall hrunG hgca hstay freeze exact hkeyG hbound hlen (hcoverOf exact)
        (hdoneOf exact) hfresh hlevel hls hlabOk hps hend hvals hcell hrange
        ho hfuel
    · have hbelowNat : boundary ≤ level := by
        rw [returned] at hstay
        simp only [Int.ofNat_eq_natCast] at hstay
        omega
      have hpreLe : pre.noncheaplevel ≤ level := by
        have h1 := hboundaryG (by rw [saved]; omega)
        rw [saved] at h1
        omega
      have hstLe : st.noncheaplevel ≤ level := by
        rcases hpreNcl with h | h <;> omega
      have hsmall : SubtreeOk ctx level
          { lab := r.lab, ptn := r.ptn, active := pre.active,
            numcells := r.numcells, hint := 0, maxpos := 0,
            longcode := r.numcells } := by
        rw [hpreActive]
        refine SubtreeOk.ofFrames (r := r) ?_ rfl rfl rfl
        apply hdesc.atLevel hit heqt hcount hstLe
        intro heq
        rcases hc : cheapautom r.ptn level n with _ | _
        · exfalso
          have := hpreParkWeak hc
          rcases hpreNcl with h | h <;> omega
        · rfl
      have hboundEq : bound = nodeKey ctx tcLevel specFuel (level + 1) full
          child (r.numcells + 1) := by
        rw [← hkeyEq o ho hato]
        exact boundEq_of_subtree hsmall hgsz hsymm hloopless hcell hlen2
          hrange hfuel hbound hlen ho
      rw [returned] at hcall hrunG
      exact FirstSweepRun.guideCheap hfull.symm hstem hshorter hrep hfirstTv
        hcall hrunG hgca positive hbelowNat saved hboundEq exact
        (hdoneOf exact) hfresh hlevel hls hlabOk hps hend hvals hcell hrange
        ho hfuel
    · exact (hfuelNe emptyFuel).elim
  · -- the guiding child stays at the loop level
    have hreturn : value = Int.ofNat level :=
      hrunG.proof.node.outcome.parentEq hfuelNe hstay
    have hfullKey : outBest = some (incMax none
        (nodeKey ctx tcLevel specFuel (level + 1) full child
          (r.numcells + 1))) := by
      rcases hexit : hrunG.exit with
        ⟨returned, exact⟩ |
        ⟨target, returned, below, sound, payload, located, control⟩ |
        ⟨below, exact, freeze⟩ |
        ⟨boundary, returned, positive, atOrAbove, saved, exact⟩ |
        ⟨returned, state, incumbent, emptyFuel⟩
      · exact exact
      · exfalso
        have htarget : target = level := by
          rw [returned] at hreturn
          exact (Int.ofNat_inj.mp hreturn)
        rcases control with h | h <;> omega
      · exact exact
      · exact exact
      · exact (hfuelNe emptyFuel).elim
    have hdone := hdoneOf hfullKey
    have hcover := hcoverOf hfullKey
    let marked : SearchSt n := { out with gcaFirst := level, stabvertex := tv1 }
    let cleaned : SearchSt n :=
      { out with
        gcaFirst := level
        stabvertex := tv1
        fixedpts := out.fixedpts.erase tv1 }
    let cleared := clearShortIf cleaned.needshortprune cleaned
    let recSt := recover n inf level cleared
    let tcell' := if cleaned.needshortprune then shortprune tcell cleared
      else tcell
    obtain ⟨hfix, hcos, hcomp, hgen, horbC, hfl, hncl, hgf, hgc, hcl, -⟩ :=
      clearShortIf_fields cleaned.needshortprune cleaned
    have hmark : EventOut G ctx tcLevel full fs marked outBest eventTrail
        value :=
      hrunG.proof.setFirstEvent hfull hreturn hdone hlevel hls hlabOk hps
        hend hvals hcell hrange ho hfuel
    have hev : EventOut G ctx tcLevel full fs cleared outBest eventTrail
        value := by
      have h := hmark.setFixed (out.fixedpts.erase tv1)
      rcases hc : cleaned.needshortprune with _ | _
      · simpa only [cleared, hc, clearShortIf, Bool.false_eq_true, ite_false]
          using h
      · simpa only [cleared, hc, clearShortIf, ite_true] using h.clearShort
    have hfirstLe : cleared.gcaFirst ≤ level := by
      rw [hgf]
      exact Nat.le_refl level
    have hinfLevel : level < inf := by
      rw [hinf]
      omega
    have hbaseOut : SearchOut G level level pre out := by
      apply breakout_child_out (stC := child) hn0 hpreOk hlevel hcellPre hlen2
        hrange ho hout
      · rw [hat]
      · exact breakout_ptn (n := n) pre.lab pre.ptn (level + 1) tc tv1
      · rfl
      · rfl
    have hbaseCleared : SearchOut G level level pre cleared := by
      apply hbaseOut.congr
      · exact clearShortIf_lab _ _
      · exact clearShortIf_ptn _ _
      · rw [hfl]
      · rw [hcl]
    have hrecOk := hbaseCleared.recoverOk hinf hlevel hpreOk
    obtain ⟨bs, hrunRec, hstable, hhistory⟩ := hev.recoverRun hreturn hfull
      hlevel hinfLevel hfirstLe hrecOk.2
    have hframes := recover_frames n inf level cleared
    have hgfRec : recSt.gcaFirst = level := by
      rw [show recSt = recover n inf level cleared from rfl,
        hframes.2.2.2.2.2.2.1, hgf]
    have hgcRec : level ≤ recSt.gcaCanon := by
      rw [show recSt = recover n inf level cleared from rfl,
        recover_gcaCanon, hgc]
      change level ≤ if level < out.gcaCanon then level else out.gcaCanon
      split <;> omega
    have hfirstlabRec : recSt.firstlab = out.firstlab := by
      rw [show recSt = recover n inf level cleared from rfl,
        hframes.2.2.2.2.1, hfl]
    have hcanonlabRec : recSt.canonlab = out.canonlab := by
      rw [show recSt = recover n inf level cleared from rfl,
        hframes.1, hcl]
    have hlive : FirstLive ctx level recSt eventTrail r.lab r.ptn := by
      refine ⟨⟨hhistory, ?_, hstable⟩, ?_⟩
      · rw [hgfRec]
        exact hgcRec
      · intro γ hγ
        exact hstable level
          ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩
          (by rw [hgfRec]; exact Int.le_refl _) hentry γ hγ
    obtain ⟨htrailRec, hcanonRec⟩ := hrunG.proof.recoverTrails
      (inf := inf) (fixedpts := out.fixedpts.erase tv1) (tv1 := tv1)
    have hrecEqPlain : recSt = clearShortIf cleaned.needshortprune
        (recover n inf level cleaned) :=
      recover_clearShortIf n inf level cleaned.needshortprune cleaned
    have hfirstTrail : FirstTrail ctx level recSt eventTrail := by
      refine htrailRec.lower.retrail ?_ (TrailExt.refl _ _)
      rw [hfirstlabRec, (recover_frames n inf level _).2.2.2.2.1]
    have hcanonTrail : CanonTrail ctx level recSt eventTrail := by
      refine hcanonRec.retrail ?_ (TrailExt.refl _ _)
      rw [hcanonlabRec, (recover_frames n inf level _).1]
    have hrefs : FrameRefs ctx tcLevel specFuel level full r.lab r.ptn tc len
        r.numcells recSt outBest := by
      have h := hrunG.proof.recoverRefs (inf := inf)
        (fixedpts := out.fixedpts.erase tv1) (tv1 := tv1) hdone ho
      rw [hrecEqPlain]
      rcases hc : cleaned.needshortprune with _ | _
      · simpa only [clearShortIf, Bool.false_eq_true, ite_false] using h
      · simp only [clearShortIf, ite_true]
        exact ⟨h.first, h.canon⟩
    have hshortRec : recSt.needshortprune = false := by
      rw [show recSt = recover n inf level cleared from rfl,
        recover_needshortprune]
      exact clearShortIf_self cleaned
    have hfixedRec : recSt.fixedpts = pre.fixedpts := by
      rw [show recSt = recover n inf level cleared from rfl,
        recover_clearShortIf, (clearShortIf_fields _ _).1, recover_fixedpts]
      change out.fixedpts.erase tv1 = pre.fixedpts
      rw [hrunG.proof.node.fixed]
      exact erase_insert_of_miss hfresh
    have hpathRec : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 level recSt :=
      PathOk.ofSearchOut hn0 hlevel hpathPre hfixedRec hpreOk hrecOk.2
        hrecOk.1
    have hnclRec : recSt.noncheaplevel = if level < out.noncheaplevel
        then level + 1 else out.noncheaplevel := by
      rw [show recSt = recover n inf level cleared from rfl,
        recover_noncheaplevel, hncl]
    have hhRec : FirstSweepHyp G ctx tcLevel specFuel level full bs fs
        r.numcells r.lab r.ptn tc len tcell (some tv1) st.noncheaplevel tv1
        pre recSt outBest eventTrail := by
      refine ⟨?_, hlive, hpathRec, ⟨tv1, rfl, Nat.le_refl _⟩,
        fun v hv => by cases hv; exact htvLt, ?_, hgfRec, hfirstTrail,
        hcanonTrail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact {
          nonempty := hn0
          positive := hlevel
          baseOk := hpreOk
          run := hrunRec
          effect := hrecOk.1
          baseLab := hpreLab
          basePtn := hprePtn
          equitable := heqt
          cell := hcell
          lenTwo := hlen2
          range := hrange
          values := hvals
          members := fun v hv => (mem_windowSet.mp hv).2
          cover := hcover
          refs := hrefs
          shortClear := hshortRec
          fuelBound := hfuel }
      · apply recover_nonpositive
        rw [hcomp]
        exact hmark.nonpositive
      · rw [show recSt = recover n inf level cleared from rfl,
          recover_orbits, recover_genTrace, horbC, hgen]
        exact horbOut
      · rw [show recSt = recover n inf level cleared from rfl,
          recover_coset, hcos]
        exact hcosetOut
      · intro b hb
        rw [hfirstlabRec]
        exact hkeepG.dom b hb
      · intro hlt'
        rw [hnclRec] at hlt'
        rcases Decidable.em (level < out.noncheaplevel) with hc | hc
        · rw [ite_eq_left hc] at hlt'
          exfalso
          omega
        · rw [ite_eq_right hc] at hlt'
          rw [hboundaryG (by omega)] at hlt'
          have hst := hpreKeep hlt'
          rw [hst] at hlt'
          exact SubtreeOk.ofFrames ((hdesc hlt').setActive (a := VSet.empty))
            rfl rfl rfl
      · rw [hnclRec]
        rcases Decidable.em (level < out.noncheaplevel) with hc | hc
        · exact Nat.le_of_eq (ite_eq_left hc)
        · rw [ite_eq_right hc]
          omega
      · intro hpark
        rw [hnclRec]
        rcases Decidable.em (level < out.noncheaplevel) with hc | hc
        · rw [ite_eq_left hc]
          omega
        · rw [ite_eq_right hc]
          rw [hboundaryG (by omega)]
          exact hpreParkWeak hpark
      · intro hlt'
        rw [hnclRec] at hlt' ⊢
        rcases Decidable.em (level < out.noncheaplevel) with hc | hc
        · rw [ite_eq_left hc] at hlt'
          exfalso
          omega
        · rw [ite_eq_right hc] at hlt' ⊢
          rw [hboundaryG (by omega)] at hlt' ⊢
          exact hpreKeep hlt'
    have hinvRec : LoopInv G ctx tcLevel specFuel level full bs fs
        r.numcells r.lab r.ptn tc len tcell' (some tv1) pre recSt outBest
        eventTrail := by
      rcases hc : cleaned.needshortprune with _ | _
      · simpa only [tcell', recSt, cleared, hc, Bool.false_eq_true,
          ite_false] using hhRec.inv
      · have hlast : ∀ fix mcr : VSet n,
            cleared.autos.back? = some (fix, mcr) →
              PairOk ctx.g r.ptn r.lab level fix mcr := by
          intro fix mcr hback
          have hrBelow : value < Int.ofNat (level + 1) :=
            hrunG.exit.below (by omega)
          have hpreserved' : TrailExt (level + 1)
              (eventTrail.push level
                ⟨sweepFrame specFuel full r.lab r.ptn tc r.numcells, o⟩)
              eventTrail := by
            intro target htarget
            rcases Decidable.em (target = level) with rfl | hne
            · rw [FrameTrail.push_self]
              exact hentry
            · rw [FrameTrail.push_of_ne _ _ hne]
          apply shortPairAtReceiver hfull.symm hhRec.inv hpathRec hrBelow
            hrunG.proof.node.outcome.event hpreserved'
            (hrunG.short (by simpa only [cleaned] using hc)) hstay
          simpa only [cleared, clearShortIf, hc, ite_true] using hback
        simpa only [tcell', recSt, cleared, hc, ite_true] using
          hhRec.inv.shortpruneWith hgsz hlast
    have hhRec' := hhRec.filter hinvRec
    have hfuelRec : n < cursorRank (some tv1) + n := by
      simp only [cursorRank]
      omega
    obtain ⟨outBest', eventTrail', hrunTail, hkeepTail⟩ :=
      firstTail hg hinf hn0 ih hrun hspec hfull.symm hstem hpast hbound
        hlen n (some tv1) tcell' recSt outBest eventTrail bs
        (if (recSt.orbits[tv1]! == tv1) = true then 0 + 1 else 0) hhRec'
        hfuelRec
    have hstate := firstChildLoop_stayGuide ctx inf tcLevel runFuel n
      level r.numcells tc tv1 tv1 tcell 0 pre value out hrep hfirstTv hcall
      hstay
    dsimp only at hstate
    refine ⟨outBest', eventTrail', ?_, ?_⟩
    · refine (FirstSweepRun.nextGuide hnext hrep hfirstTv hcall hstay
        ?_ hpreG hrunTail).retrail hext
      exact hfixedRec
    · rw [hstate]
      exact ⟨hkeepTail.dom, hkeepTail.orbits, hkeepTail.coset,
        hkeepTail.boundary⟩

/-! # Back to the enclosing first-path node -/

namespace FirstSweepRun

/-- The escape classification of a sweep result.  Below-loop unwinds are
direct, since the first-path controls keep every orbit pointer at or above
the loop level. -/
theorem escape {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    LoopEscape ctx tcLevel level bound out best outBest receiptTrail r := by
  rcases h.exit with
    ⟨returned, exact⟩ |
    ⟨target, returned, below, sound, payload, located, control⟩ |
    ⟨value, returned, below, exact, freeze⟩ |
    ⟨boundary, returned, positive, below', saved, exact⟩ |
    ⟨returned, finalCursor, progress, bounded⟩
  · exact .full exact
  · cases payload with
    | first anchor carrier =>
        cases located with
        | first _ _ loc => exact .first target returned below anchor carrier loc
    | canon anchor carrier =>
        cases located with
        | canon _ _ loc => exact .canon target returned below anchor carrier loc
    | orbit payload =>
        exfalso
        have := h.guideLevel
        have := h.order
        rcases control with hc | hc <;> omega
  · exact .full exact
  · exact .full exact
  · exact .pending returned

/-- An early integer-valued sweep becomes its enclosing first-path node. -/
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
    (h : FirstSweepRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out none outBest receiptTrail eventTrail (some r)) :
    FirstRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells outBest receiptTrail eventTrail r := by
  have hescape : NodeEscape ctx tcLevel nodeSpecFuel level nodeCodes nodeSt
      out nodeNumcells none outBest receiptTrail r := by
    cases h.escape with
    | full eq => exact .full (by simpa only [hbound] using eq)
    | first target returned below anchor carrier located =>
        exact .first target (Option.some.inj returned) below anchor carrier
          located
    | canon target returned below anchor carrier located =>
        exact .canon target (Option.some.inj returned) below anchor carrier
          located
    | pending returned => cases returned
  refine ⟨⟨⟨h.proof.outcome.toNodeSome hbound, h.proof.fixed.trans hfixed⟩,
    hescape, h.trail, h.canonTrail,
    fun _ => Nat.le_trans (Nat.sub_le level 1) h.guideLevel, h.order⟩,
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
    (h : FirstSweepRun G ctx tcLevel specFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out none outBest receiptTrail eventTrail none) :
    FirstRun G ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCodes fs
      nodeSt out nodeNumcells outBest receiptTrail eventTrail
      (Int.ofNat level - 1) := by
  have hfull : outBest = some (incMax none bound) := by
    cases h.proof.outcome.receipt with
    | complete returned sound installed read finalSet finalCursor cover
        empty =>
        rw [hlen] at cover empty
        exact cover.exact_of_read (hbound.trans hchildren) empty sound
          installed read
    | unwind sound target returned below payload located => cases returned
    | pruned target returned below sound installed read full =>
        cases returned
    | exhausted returned sound finalSet finalCursor cover progress
        bounded =>
        exact (LoopResult.exhaustion_false hfuel progress bounded).elim
  have hescape : NodeEscape ctx tcLevel (specFuel + 1) level nodeCodes
      nodeSt out nodeNumcells none outBest receiptTrail
      (Int.ofNat level - 1) := by
    apply NodeEscape.full
    simpa only [hbound] using hfull
  refine ⟨⟨⟨h.proof.outcome.toNodeNone hbound hchildren hlen hfuel,
      h.proof.fixed.trans hfixed⟩,
    hescape, h.trail, h.canonTrail,
    fun _ => Nat.le_trans (Nat.sub_le level 1) h.guideLevel, h.order⟩,
    h.exit.toNodeNone hbound hfuel, ?_⟩
  intro hshort
  obtain ⟨value, hreturned, _⟩ := h.short hshort
  cases hreturned

end FirstSweepRun

end Hex.GraphIso.Nauty

/-!
The first-path node step of the totality induction: the discrete arm
installs the first leaf, and the internal arm runs the first-path sibling
sweep, each carrying the facts the enclosing sweep needs.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Installing the first leaf leaves the orbit ledger, the coset cursor
and the cheap-cell boundary alone. -/
theorem firstterminal_ledger (level : Nat) (st : SearchSt n) :
    (firstterminal level st).orbits = st.orbits ∧
    (firstterminal level st).cosetindex = st.cosetindex ∧
    (firstterminal level st).noncheaplevel = st.noncheaplevel := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]
  simp

/-- The discrete first-path arm is total and carries the sweep facts. -/
theorem FirstInv.leafTotal {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hn0 : 0 < n) (hpath : level = codes.length + 1)
    (h : FirstInv G ctx level codes numcells st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n) :
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
          numcells outBest trail eventTrail
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
        FirstKeep ctx level st
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2 fs
          outBest := by
  have hrun := h.terminalRun (inf := inf) (tcLevel := tcLevel)
    (specFuel := specFuel) (fuel := fuel) hn0 hpath hnum
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
theorem firstFinish_ledger (level size index : Nat) (st : SearchSt n) :
    (firstFinish level size index st).orbits = st.orbits ∧
    (firstFinish level size index st).genTrace = st.genTrace ∧
    (firstFinish level size index st).cosetindex = st.cosetindex ∧
    (firstFinish level size index st).noncheaplevel = st.noncheaplevel ∧
    (firstFinish level size index st).gcaFirst = st.gcaFirst := by
  rw [firstFinish]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The internal first-path arm is total once every node at the current
fuel is. -/
theorem FirstInv.internalTotal {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hn0 : 0 < n)
    (ih : OtherTotal G ctx inf tcLevel runFuel)
    (ihFirst : FirstTotal G ctx inf tcLevel runFuel)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + (specFuel + 1) = n + 1)
    (hfuel : n + 2 < level + (runFuel + 1))
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hfirst : FirstInv G ctx level codes numcells st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ n) :
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel (specFuel + 1) (runFuel + 1) level codes fs st
          (firstPathNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          numcells outBest trail eventTrail
          (firstPathNode ctx inf tcLevel (runFuel + 1) level numcells st).1 ∧
        FirstKeep ctx level st
          (firstPathNode ctx inf tcLevel (runFuel + 1) level numcells st).2
          fs outBest := by
  have href := hfirst.refined hg hn0 hlevel
  have hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff hn0 hfirst.searchOk
      hlevel]
    exact hnum
  have hpsz := href.1.ok.ptnSize
  have hend := href.1.ok.ptnEnd
  have hcount := href.2.2
  have hbc : bcount (refine ctx level st.lab st.ptn st.active numcells).ptn
      level n < n := by
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
    have hok := refine_searchOk hn0 hfirst.searchOk hlevel
      (st2 := firstLeafSt ctx level numcells st) rfl rfl (Or.inl rfl)
    have hle := hok.bc
    have hptn : (firstLeafSt ctx level numcells st).ptn =
      (refine ctx level st.lab st.ptn st.active numcells).ptn := rfl
    rw [hptn] at hle
    omega
  have hL := firstLoopTotal (tail := len - 1) (level := level)
    (specFuel := specFuel) (runFuel := runFuel) (cs := codes) (st := st)
    (numcells := numcells) (tc := tc) (len := len) (inf := inf)
    (tcLevel := tcLevel) (trail := trail) hg hinf hn0 ih ihFirst
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
  generalize hL : firstChildLoop ctx inf tcLevel runFuel (n + 1) level
    (refine ctx level st.lab st.ptn st.active numcells).numcells tc
    (((windowSet n (refine ctx level st.lab st.ptn st.active
      numcells).lab tc len).nextElem none).getD 0)
    ((windowSet n (refine ctx level st.lab st.ptn st.active
      numcells).lab tc len).nextElem none)
    (windowSet n (refine ctx level st.lab st.ptn st.active numcells).lab tc
      len) 0 _ = L at hrunL hout ⊢
  rcases L with ⟨rr, index, out⟩
  cases rr with
  | none =>
      dsimp only
      refine ⟨fs, outBest, eventTrail, ?_, ?_⟩
      · exact (hrunL.toNodeNone (nodeRunFuel := runFuel + 1)
          (tail := len - 1) hchildren.symm hchildren
          (show len = len - 1 + 1 by omega)
          (show n < cursorRank none + (n + 1) by
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
theorem FirstTotal.succ (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel runFuel : Nat) (ih : OtherTotal G ctx inf tcLevel runFuel)
    (ihFirst : FirstTotal G ctx inf tcLevel runFuel) :
    FirstTotal G ctx inf tcLevel (runFuel + 1) := by
  intro specFuel level numcells codes st trail hg hinf hn0 hlevel hpath
    hspec hfuel hcheap hdesc horb hfirst hpathOk
  have hle : level ≤ n := hfirst.searchOk.levelLe
  obtain ⟨sf, rfl⟩ : ∃ sf, specFuel = sf + 1 := ⟨specFuel - 1, by omega⟩
  by_cases hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n
  · exact hfirst.leafTotal hn0 hpath horb hnum
  · exact hfirst.internalTotal hg hinf hn0 ih ihFirst hlevel hpath hspec
      hfuel hcheap hdesc horb hpathOk hnum

end Hex.GraphIso.Nauty
