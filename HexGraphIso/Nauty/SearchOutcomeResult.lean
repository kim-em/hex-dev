/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeEvent

public section

/-!
Corrected node outcomes coupled to their result-side invariants.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The semantic node receipt and the concrete result state produced by
one recursive node call. -/
structure NodeOutcome (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
    (trail : FrameTrail) (r : Int) : Prop where
  receipt : NodeReceipt trail ctx tcLevel specFuel runFuel level cs st out
    numcells best outBest r
  event : EventOut G ctx tcLevel cs fs out outBest trail r

/-- Forgetting the concrete result invariant recovers the corrected
semantic node result consumed by the root reduction. -/
theorem NodeOutcome.toResult {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {cs fs : List Nat}
    {st out : SearchSt} {best outBest : Option Key} {trail : FrameTrail}
    {r : Int}
    (h : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest trail r) :
    NodeResult ctx tcLevel specFuel runFuel level cs st out numcells best
      outBest r :=
  h.receipt.toResult

/-- An off-path node additionally leaves the first-path guide unchanged.
This is the fact its parent needs before recovering a completed child. -/
structure OtherOutcome (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
    (trail : FrameTrail) (r : Int) : Prop where
  node : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
    numcells best outBest trail r
  firstGuide : out.gcaFirst = st.gcaFirst

/-- First-path exit bookkeeping preserves a corrected node outcome. -/
theorem NodeOutcome.firstFinish {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs fs : List Nat} {st out : SearchSt} {best outBest : Option Key}
    {trail : FrameTrail} {r : Int} (hfuel : runFuel ≠ 0)
    (h : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest trail r) :
    NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st
      (Nauty.firstFinish level size index out) numcells best outBest trail
      r := by
  constructor
  · exact h.receipt.firstFinish hfuel
  · unfold Nauty.firstFinish
    split
    · exact h.event.setAllsame
    · exact h.event

/-- The first discrete leaf closes the corrected result package.  Its
generator store is still empty, so every return-frame stabilization
obligation is vacuous. -/
theorem FirstInv.terminalOutcome {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level cs full st
      out.2 numcells none (some (pathLeafKey ctx full rs.lab)) trail
      out.1 := by
  dsimp only
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := cs ++ [rs.longcode]
  let leaf := firstLeafSt ctx level numcells st
  have hstate := firstPath_discrete_state ctx inf tcLevel fuel level
    numcells st hnum
  have hbase := h.terminalReceipt
    (inf := inf) (tcLevel := tcLevel) (specFuel := specFuel)
    (fuel := fuel) hn hn0 hlevel hnum
  have hdepth : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take cs.length = cs := by
    simp only [full, List.take_left']
  have hempty : (firstterminal level leaf).genTrace = #[] := by
    rw [(firstterminal_store level leaf).1]
    exact h.genEmpty
  constructor
  · exact hbase.1
  · rw [hstate]
    have hrun := hbase.2
    rw [hstate] at hrun
    apply EventOut.ofRun hrun hdepth hstem
    · omega
    · rw [(firstterminal_state level leaf).2.2.2.2]
      omega
    · exact ReturnStab.empty hempty

end Hex.GraphIso.Nauty
