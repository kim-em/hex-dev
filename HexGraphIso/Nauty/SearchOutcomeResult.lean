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

/-- An output trail retains every frame that was active on entry.  A
node may additionally replace deeper scratch entries used by its own
recursive sweep. -/
@[expose] def TrailExt (level : Nat) (before after : FrameTrail) : Prop :=
  ∀ target, target < level → after target = before target

theorem TrailExt.refl (level : Nat) (trail : FrameTrail) :
    TrailExt level trail trail := fun _ _ => rfl

theorem TrailExt.trans {level : Nat} {a b c : FrameTrail}
    (hab : TrailExt level a b) (hbc : TrailExt level b c) :
    TrailExt level a c := fun target htarget =>
  (hbc target htarget).trans (hab target htarget)

/-- Retaining a pushed child trail retains every older parent frame. -/
theorem TrailExt.ofPush {level : Nat} {trail out : FrameTrail}
    {entry : TrailEntry}
    (h : TrailExt (level + 1) (trail.push level entry) out) :
    TrailExt level trail out := by
  intro target htarget
  rw [h target (by omega), FrameTrail.push_of_ne]
  omega

/-- Retaining a pushed child trail keeps the newly active parent frame
at its exact level. -/
theorem TrailExt.pushAt {level : Nat} {trail out : FrameTrail}
    {entry : TrailEntry}
    (h : TrailExt (level + 1) (trail.push level entry) out) :
    out level = some entry := by
  rw [h level (by omega), FrameTrail.push_self]

/-- Location evidence can be moved between trails that agree at the
unwind target. -/
theorem Unwind.Located.retrail {ctx : Ctx} {tcLevel target : Nat}
    {out : SearchSt} {best : Option Key} {source dest : FrameTrail}
    {payload : Unwind ctx tcLevel target out best}
    (h : payload.Located source) (heq : source target = dest target) :
    payload.Located dest := by
  cases h with
  | first anchor carrier located =>
      apply Unwind.Located.first anchor carrier
      unfold Anchor.Located at located ⊢
      rw [← heq]
      exact located
  | canon anchor carrier located =>
      apply Unwind.Located.canon anchor carrier
      unfold Anchor.Located at located ⊢
      rw [← heq]
      exact located
  | orbit payload => exact .orbit payload

/-- A loop receipt depends on its trail only below the loop level. -/
theorem LoopReceipt.retrail {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {st out : SearchSt}
    {best outBest : Option Key} {source dest : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : LoopReceipt source ctx tcLevel specFuel runFuel loopFuel level cs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest r) :
    LoopReceipt dest ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned sound installed read finalSet finalCursor
        cover empty
  | unwind sound target returned below payload located =>
      exact .unwind sound target returned below payload
        (located.retrail (htrail target below))
  | pruned target returned below sound installed read full =>
      exact .pruned target returned below sound installed read full
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover progress
        bounded

/-- The semantic node receipt and the concrete result state produced by
one recursive node call. -/
structure NodeOutcome (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  receipt : NodeReceipt receiptTrail ctx tcLevel specFuel runFuel level cs st out
    numcells best outBest r
  event : EventOut G ctx tcLevel cs fs out outBest eventTrail r
  preserved : TrailExt level receiptTrail eventTrail

/-- Forgetting the concrete result invariant recovers the corrected
semantic node result consumed by the root reduction. -/
theorem NodeOutcome.toResult {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {cs fs : List Nat}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (h : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeResult ctx tcLevel specFuel runFuel level cs st out numcells best
      outBest r :=
  h.receipt.toResult

/-- At a parent boundary, a child outcome either supplies its exact
subtree maximum or a located unwind whose generator store stabilizes the
receiving frozen frame. -/
theorem NodeOutcome.parentReturn {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {cs fs : List Nat}
    {st out : SearchSt} {best outBest : Option Key} {r : Int}
    {trail eventTrail : FrameTrail} {entry : TrailEntry}
    (h : NodeOutcome G ctx tcLevel specFuel runFuel (level + 1) cs fs st
      out numcells best outBest (trail.push level entry) eventTrail r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level)) :
    outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel (level + 1) cs st numcells)) ∨
      ∃ payload : Unwind ctx tcLevel level out outBest,
        payload.Located (trail.push level entry) ∧
          payload.FrameStable entry.frame.rsPtn level entry.frame.rsLab := by
  cases h.receipt with
  | complete sound returned installed read full => exact Or.inl full
  | unwind sound target returned below payload located =>
      have hle : level ≤ target := by
        apply Int.ofNat_le.mp
        rw [returned] at hstay
        exact Int.not_lt.mp hstay
      have htarget : target = level := by omega
      subst target
      right
      refine ⟨payload, located, ?_⟩
      rw [returned] at h
      apply h.event.returnStab.frameStable
      exact h.preserved.pushAt
  | pruned sound target returned below installed read full =>
      exact Or.inl full
  | exhausted empty => exact (hfuel empty).elim

/-- An off-path node additionally leaves the first-path guide unchanged.
This is the fact its parent needs before recovering a completed child. -/
structure OtherOutcome (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  node : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
    numcells best outBest receiptTrail eventTrail r
  firstGuide : out.gcaFirst = st.gcaFirst

/-- The integer return represented by a loop result.  Exhausting the
sweep completes its parent node one level up. -/
@[expose] def loopReturn (level : Nat) : Option Int → Int
  | some r => r
  | none => Int.ofNat level - 1

/-- A loop receipt coupled to the concrete result invariant ultimately
returned by its parent node.  `stem` is the parent node's entry prefix;
the loop's own `codes` include that node's refinement code. -/
structure LoopOutcome (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells tcell : Nat) (cursor : Option Nat) (bound : Key)
    (st out : SearchSt) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail)
    (r : Option Int) : Prop where
  receipt : LoopReceipt receiptTrail ctx tcLevel specFuel runFuel loopFuel level
    codes rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest r
  event : EventOut G ctx tcLevel stem fs out outBest eventTrail
    (loopReturn level r)
  preserved : TrailExt level receiptTrail eventTrail

/-- A loop that returns an integer supplies its parent node outcome. -/
theorem LoopOutcome.toNodeSome {G : Colored n k} {ctx : Ctx}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level : Nat}
    {nodeCs loopCs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {best outBest : Option Key} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCs nodeSt
      nodeNumcells)
    (h : LoopOutcome G ctx tcLevel loopSpecFuel runFuel loopFuel level nodeCs
      loopCs fs rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt
      out best outBest receiptTrail eventTrail (some r)) :
    NodeOutcome G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCs fs
      nodeSt out nodeNumcells best outBest receiptTrail eventTrail r := by
  exact ⟨NodeReceipt.ofLoopSome hbound h.receipt, h.event, h.preserved⟩

/-- A completed loop with sufficient cursor fuel supplies its parent
node's completed outcome. -/
theorem LoopOutcome.toNodeNone {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCs loopCs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {best outBest : Option Key} {receiptTrail eventTrail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel (specFuel + 1) level nodeCs
      nodeSt nodeNumcells)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hfuel : ctx.n < cursorRank cursor + loopFuel)
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level nodeCs
      loopCs fs rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt
      out best outBest receiptTrail eventTrail none) :
    NodeOutcome G ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCs fs
      nodeSt out nodeNumcells best outBest receiptTrail eventTrail
      (Int.ofNat level - 1) := by
  exact ⟨NodeReceipt.ofLoopNone hbound hchildren hlen hfuel h.receipt,
    h.event, h.preserved⟩

/-- Prepending a semantic loop fragment leaves the concrete result
package unchanged. -/
theorem LoopOutcome.prefix {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st recSt out : SearchSt} {best mid outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hpre : LoopSound ctx bound best mid)
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.receipt.prefix hpre, h.event, h.preserved⟩

/-- Changing the mutable entry workset does not affect a completed loop
outcome. -/
theorem LoopOutcome.reindexSet {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell tcell' : Nat} {cursor : Option Nat}
    {bound : Key} {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.receipt.reindexSet, h.event, h.preserved⟩

/-- One successful cursor step preserves the coupled loop outcome. -/
theorem LoopOutcome.step {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out
      best outBest receiptTrail eventTrail r) :
    LoopOutcome G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.receipt.step ha, h.event, h.preserved⟩

/-- A coupled loop outcome can be rebased onto an entry trail that
agrees below the loop level. -/
theorem LoopOutcome.retrail {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat} {bound : Key}
    {st out : SearchSt} {best outBest : Option Key}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest source eventTrail r) :
    LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.receipt.retrail htrail, h.event, htrail.trans h.preserved⟩

/-- First-path exit bookkeeping preserves a corrected node outcome. -/
theorem NodeOutcome.firstFinish {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs fs : List Nat} {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st
      (Nauty.firstFinish level size index out) numcells best outBest
      receiptTrail eventTrail r := by
  constructor
  · exact h.receipt.firstFinish hfuel
  · unfold Nauty.firstFinish
    split
    · exact h.event.setAllsame
    · exact h.event
  · exact h.preserved

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
      out.2 numcells none (some (pathLeafKey ctx full rs.lab)) trail trail
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
    · apply RefTrail.ofCurrent hrun.trailOk h.frameSize
      · rw [firstterminal_firstlab, (firstterminal_state level leaf).1]
      · rw [firstterminal_canonlab, (firstterminal_state level leaf).1]
  · exact TrailExt.refl level trail

set_option maxHeartbeats 800000 in
/-- A coupled child-loop outcome supplies the complete outcome of a
non-discrete first-path node. -/
theorem firstPath_internal_outcome {G : Colored n k} (ctx : Ctx)
    (inf tcLevel specFuel fuel level numcells tail : Nat)
    (cs fs : List Nat) (st : SearchSt) (best outBest : Option Key)
    (trail outTrail : FrameTrail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ ctx.n)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      let rs := refine ctx level st.lab st.ptn st.active numcells
      let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
      keysMax
        (sweepKey ctx tcLevel specFuel level (cs ++ [rs.longcode])
          rs.lab rs.ptn mt.1 rs.numcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level (cs ++ [rs.longcode])
            rs.lab rs.ptn mt.1 rs.numcells (o + 1)))
    (hlen : (maketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn level
      tcLevel (-1)).2.2 = tail + 1) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
    let pre0 : SearchSt := { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      firstcode := st.firstcode.set! level rs.longcode
      firsttc := st.firsttc.set! level (Int.ofNat mt.1)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + mt.2.2 }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level ctx.n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let L := firstChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
      rs.numcells mt.1 ((nextElem mt.2.1 none).getD 0)
      (nextElem mt.2.1 none) mt.2.1 0 pre
    LoopOutcome G ctx tcLevel specFuel fuel (ctx.n + 1) level cs
      (cs ++ [rs.longcode]) fs rs.lab rs.ptn mt.1 mt.2.2 rs.numcells
      mt.2.1 none
      (nodeKey ctx tcLevel (specFuel + 1) level cs st numcells)
      pre L.2.2 best outBest trail outTrail L.1 →
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level cs fs st
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail outTrail
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  dsimp only
  intro hloop
  rw [firstPath_internal_state ctx inf tcLevel fuel level numcells st hnum]
  generalize hL : firstChildLoop ctx inf tcLevel fuel (ctx.n + 1)
      level _ _ _ _ _ _ _ = L at hloop ⊢
  rcases L with ⟨r, index, out⟩
  cases r with
  | none =>
      have hnode := hloop.toNodeNone (nodeRunFuel := fuel + 1)
        rfl hchildren hlen
        (by simp only [cursorRank]; omega)
      exact hnode.firstFinish (by omega)
  | some r =>
      exact hloop.toNodeSome (nodeRunFuel := fuel + 1) rfl

/-- Once the imperative prefix exposes an off-path child loop, its
coupled outcome constructs the corresponding node outcome. -/
theorem otherNode_outcome {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level nodeNumcells loopNumcells tail : Nat}
    {nodeCs loopCs fs : List Nat} {nodeSt loopSt : SearchSt}
    {rsLab rsPtn : Array Nat} {tc len tcell : Nat}
    {best outBest : Option Key} {trail outTrail : FrameTrail}
    {L : Option Int × SearchSt}
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hstate : otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt =
      match L.1 with
      | some r => (r, L.2)
      | none => (Int.ofNat level - 1, L.2))
    (hloop : LoopOutcome G ctx tcLevel specFuel fuel (ctx.n + 1) level
      nodeCs loopCs fs rsLab rsPtn tc len loopNumcells tcell none
      (nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells)
      loopSt L.2 best outBest trail outTrail L.1) :
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level nodeCs fs
      nodeSt (otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt).2
      nodeNumcells best outBest trail outTrail
      (otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt).1 := by
  rw [hstate]
  rcases L with ⟨r, out⟩
  cases r with
  | none =>
      exact hloop.toNodeNone (nodeRunFuel := fuel + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega)
  | some r =>
      exact hloop.toNodeSome (nodeRunFuel := fuel + 1) rfl

end Hex.GraphIso.Nauty
