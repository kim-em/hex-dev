/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeLocated
public import HexGraphIso.Nauty.SearchOutcomeProof

public section

/-!
Operational composition lemmas for frame-aware search receipts.
-/

namespace Hex.GraphIso.Nauty

/-- First-path exit bookkeeping preserves the location of a transported
generator unwind. -/
theorem Unwind.Located.firstFinish {ctx : Ctx}
    {tcLevel target level size index : Nat} {st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    {payload : Unwind ctx tcLevel target st best}
    (h : payload.Located trail) :
    (payload.firstFinish (level := level) (size := size)
      (index := index)).Located trail := by
  cases h with
  | first anchor carrier located =>
      apply Unwind.Located.first anchor
      · rw [Nauty.firstFinish]
        split <;> exact carrier
      · exact located
  | canon anchor carrier located =>
      apply Unwind.Located.canon anchor
      · rw [Nauty.firstFinish]
        split <;> exact carrier
      · exact located
  | orbit orbitPayload =>
      exact .orbit {
        positive := orbitPayload.positive
        currentLt := by
          rw [Nauty.firstFinish]
          split <;> exact orbitPayload.currentLt
        smaller := by
          rw [Nauty.firstFinish]
          split <;> exact orbitPayload.smaller
        sound := by
          rw [Nauty.firstFinish]
          split <;> exact orbitPayload.sound }

/-- Every located node receipt crosses the first-path exit-counter
update. -/
theorem NodeReceipt.firstFinish {trail : FrameTrail} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs : List Nat} {st out : SearchSt} {best outBest : Option Key}
    {r : Int} (hfuel : runFuel ≠ 0)
    (h : NodeReceipt trail ctx tcLevel specFuel runFuel level cs st out
      numcells best outBest r) :
    NodeReceipt trail ctx tcLevel specFuel runFuel level cs st
      (Nauty.firstFinish level size index out) numcells best outBest r := by
  cases h with
  | complete sound returned installed read full =>
      exact .complete sound returned
        (by rw [canonlevel_firstFinish]; exact installed)
        ((stInc_firstFinish ctx level size index out).trans read) full
  | unwind sound target returned below payload located =>
      exact .unwind sound target returned below payload.firstFinish
        located.firstFinish
  | pruned sound target returned below installed read full =>
      exact .pruned sound target returned below
        (by rw [canonlevel_firstFinish]; exact installed)
        ((stInc_firstFinish ctx level size index out).trans read) full
  | exhausted empty returned unchanged bestUnchanged =>
      exact (hfuel empty).elim

set_option maxHeartbeats 800000 in
/-- A located child-loop receipt supplies the complete outcome of a
non-discrete first-path node. -/
theorem firstPath_internal_receipt (ctx : Ctx)
    (inf tcLevel specFuel fuel level numcells tail : Nat)
    (cs : List Nat) (st : SearchSt) (best outBest : Option Key)
    (trail : FrameTrail)
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
    LoopReceipt trail ctx tcLevel specFuel fuel (ctx.n + 1) level
      (cs ++ [rs.longcode]) rs.lab rs.ptn mt.1 mt.2.2 rs.numcells
      mt.2.1 none
      (nodeKey ctx tcLevel (specFuel + 1) level cs st numcells)
      pre L.2.2 best outBest L.1 →
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  dsimp only
  intro hloop
  rw [firstPath_internal_state ctx inf tcLevel fuel level numcells st hnum]
  generalize hL : firstChildLoop ctx inf tcLevel fuel (ctx.n + 1)
      level _ _ _ _ _ _ _ = L at hloop ⊢
  rcases L with ⟨r, index, out⟩
  cases r with
  | none =>
      have hnode := NodeReceipt.ofLoopNone (ctx := ctx)
        (nodeRunFuel := fuel + 1) (cursor := none)
        (loopFuel := ctx.n + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega) hloop
      exact hnode.firstFinish (by omega)
  | some r =>
      exact NodeReceipt.ofLoopSome (ctx := ctx)
        (nodeRunFuel := fuel + 1) rfl hloop

/-- Once the imperative prefix exposes an off-path child loop, its
located receipt constructs the corresponding located node receipt. -/
theorem otherNode_receipt {ctx : Ctx}
    {inf tcLevel specFuel fuel level nodeNumcells loopNumcells tail : Nat}
    {nodeCs loopCs : List Nat} {nodeSt loopSt : SearchSt}
    {rsLab rsPtn : Array Nat} {tc len tcell : Nat}
    {best outBest : Option Key} {trail : FrameTrail}
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
    (hloop : LoopReceipt trail ctx tcLevel specFuel fuel (ctx.n + 1) level
      loopCs rsLab rsPtn tc len loopNumcells tcell none
      (nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells)
      loopSt L.2 best outBest L.1) :
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level nodeCs
      nodeSt (otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt).2
      nodeNumcells best outBest
      (otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells nodeSt).1 := by
  rw [hstate]
  rcases L with ⟨r, out⟩
  cases r with
  | none =>
      exact NodeReceipt.ofLoopNone (ctx := ctx)
        (nodeRunFuel := fuel + 1) (cursor := none)
        (loopFuel := ctx.n + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega) hloop
  | some r =>
      exact NodeReceipt.ofLoopSome (ctx := ctx)
        (nodeRunFuel := fuel + 1) rfl hloop

end Hex.GraphIso.Nauty
