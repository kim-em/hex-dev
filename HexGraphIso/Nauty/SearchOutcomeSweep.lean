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
