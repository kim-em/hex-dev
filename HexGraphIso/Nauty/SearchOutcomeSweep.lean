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
  apply LoopExit.exhausted
  · unfold otherChildLoop
    rfl
  · unfold otherChildLoop
    rfl
  · rfl
  · rfl

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
