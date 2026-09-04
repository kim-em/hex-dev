/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexGraphIso.Nauty.SearchOutcomePrune

public section

/-!
Return classifications for the corrected mutual search induction.

Local exactness and the reason for an early return are deliberately
separate.  A comparison-frozen or cheap-cell child may be exact at its own
node while still causing its parent loop to skip a suffix; the extra
payload is what justifies that skipped suffix.
-/

namespace Hex.GraphIso.Nauty

/-- Result of one node call.  `done` is the ordinary one-level return;
`frozen` and `cheap` retain the distinct witnesses needed when the return
crosses more than one loop; `unwind` is reserved for stored generators. -/
inductive NodeExit (ctx : Ctx) (tcLevel specFuel runFuel level : Nat)
    (codes : List Nat) (st out : SearchSt) (numcells : Nat)
    (best outBest : Option Key) (trail : FrameTrail) (r : Int) : Prop where
  | done
      (returned : r = Int.ofNat level - 1)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
  | unwind (target : Nat)
      (returned : r = Int.ofNat target) (below : target < level)
      (sound : NodeSound ctx tcLevel specFuel level codes st numcells
        best outBest)
      (payload : Unwind ctx tcLevel target out outBest)
      (located : payload.Located trail)
  | frozen
      (below : r < Int.ofNat level)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
      (freeze : FrozenOut ctx codes out outBest r)
  | cheap (boundary : Nat)
      (returned : r = Int.ofNat boundary - 1)
      (positive : 1 ≤ boundary) (atOrAbove : boundary ≤ level)
      (exact : outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel level codes st numcells)))
  | exhausted
      (returned : r = 0) (state : out = st) (incumbent : outBest = best)
      (emptyFuel : runFuel = 0)

/-- Result of a sibling loop.  Early comparison and cheap-cell exits carry
both the exact loop maximum and the payload required to cross an older
frame.  Cursor-fuel exhaustion remains explicit and cannot be confused
with completion. -/
inductive LoopExit (ctx : Ctx) (tcLevel specFuel runFuel loopFuel level : Nat)
    (codes : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells tcell : Nat) (cursor : Option Nat) (bound : Key)
    (st out : SearchSt) (best outBest : Option Key) (trail : FrameTrail)
    (r : Option Int) : Prop where
  | done
      (returned : r = none)
      (exact : outBest = some (incMax best bound))
  | unwind (target : Nat)
      (returned : r = some (Int.ofNat target)) (below : target < level)
      (sound : LoopSound ctx bound best outBest)
      (payload : Unwind ctx tcLevel target out outBest)
      (located : payload.Located trail)
  | frozen (value : Int)
      (returned : r = some value)
      (below : value < Int.ofNat level)
      (exact : outBest = some (incMax best bound))
      (freeze : FrozenOut ctx codes out outBest value)
  | cheap (boundary : Nat)
      (returned : r = some (Int.ofNat boundary - 1))
      (positive : 1 ≤ boundary) (below : boundary ≤ level)
      (exact : outBest = some (incMax best bound))
  | exhausted
      (returned : r = none) (state : out = st) (incumbent : outBest = best)
      (emptyFuel : loopFuel = 0)

/-- Concrete node result paired with the corrected return classification.
The event and trail clauses are independent of the semantic maximum and
remain reusable from the established leaf machinery. -/
structure NodeRun (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (codes fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  exit : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
    best outBest receiptTrail r
  event : EventOut G ctx tcLevel codes fs out outBest eventTrail r
  preserved : TrailExt level receiptTrail eventTrail
  fixed : out.fixedpts = st.fixedpts

/-- Off-path nodes additionally preserve the first-path control and coset
cursor needed by their enclosing sibling loop. -/
structure OtherRun (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (codes fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  node : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
    numcells best outBest receiptTrail eventTrail r
  firstGuide : out.gcaFirst = st.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon
  canonGuide :
    (out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (level ≤ out.gcaCanon ∧ cellsPerm st.ptn level st.lab out.canonlab)
  coset : out.cosetindex = st.cosetindex

/-- Concrete sibling-loop result paired with its corrected exit reason. -/
structure LoopRun (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells tcell : Nat) (cursor : Option Nat) (bound : Key)
    (st out : SearchSt) (best outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Option Int) : Prop where
  exit : LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab
    rsPtn tc len numcells tcell cursor bound st out best outBest
    receiptTrail r
  event : EventOut G ctx tcLevel stem fs out outBest eventTrail
    (loopReturn level r)
  preserved : TrailExt level receiptTrail eventTrail
  fixed : out.fixedpts = st.fixedpts

namespace NodeRun

/-- A corrected node run can be viewed through the older local outcome
interface.  This conversion is safe at one node: both early exit variants
already carry exactness for that node.  What is deliberately not recovered
is the old loop rule that treated such an exit as coverage of every later
sibling. -/
theorem toOutcome {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeOutcome G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r := by
  have hreceipt : NodeReceipt receiptTrail ctx tcLevel specFuel runFuel
      level codes st out numcells best outBest r := by
    cases h.exit with
    | done returned exact =>
        apply NodeReceipt.complete (NodeSound.ofExact exact) returned
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | unwind target returned below sound payload located =>
        exact NodeReceipt.unwind sound target returned below payload located
    | frozen below exact freeze =>
        apply NodeReceipt.pruned (NodeSound.ofExact exact) r rfl below
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | cheap boundary returned positive atOrAbove exact =>
        apply NodeReceipt.pruned (NodeSound.ofExact exact) r rfl
        · rw [returned]
          simp only [Int.ofNat_eq_natCast]
          omega
        · exact canonlevel_ne_zero_of_stInc (h.event.read.trans exact)
        · exact h.event.read
        · exact exact
    | exhausted returned state incumbent emptyFuel =>
        exact NodeReceipt.exhausted emptyFuel returned state incumbent
  exact ⟨hreceipt, h.event, h.preserved⟩

/-- Restore the established result interface used by the invariant
transport lemmas after the corrected exit has been classified. -/
theorem toProof {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : NodeRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeProof G ctx tcLevel specFuel runFuel level codes fs st out numcells
      best outBest receiptTrail eventTrail r :=
  ⟨h.toOutcome, h.fixed⟩

end NodeRun

namespace OtherRun

/-- Restore the established off-path interface for ordinary parent-level
consumption and recovery. -/
theorem toProof {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt} {best outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : OtherRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r) :
    OtherProof G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r :=
  ⟨⟨h.node.toOutcome, h.firstGuide, h.order, h.canonGuide⟩,
    h.node.fixed, h.coset⟩

end OtherRun

namespace LoopExit

/-- At a small-cell node, exactness of the selected child is exactness of
the whole sibling sweep, so the saved-boundary return remains a cheap exit
after fixed-point cleanup. -/
theorem ofCheap {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level boundary tc len numcells tcell
      fixedpts : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound childKey : Key} {st out : SearchSt}
    {best outBest : Option Key} {trail : FrameTrail}
    (hboundary : 1 ≤ boundary) (hbelow : boundary ≤ level)
    (hbound : bound = childKey)
    (hexact : outBest = some (incMax best childKey)) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st { out with fixedpts := fixedpts }
      best outBest trail (some (Int.ofNat boundary - 1)) := by
  apply LoopExit.cheap boundary rfl hboundary hbelow
  rwa [hbound]

/-- An early frozen child absorbs both the explored prefix and every live
suffix child, yielding the exact loop maximum while retaining the frozen
payload for the next enclosing frame. -/
theorem ofFrozen {ctx : Ctx}
    {tcLevel specFuel runFuel loopFuel level tail tc len numcells tcell
      fixedpts : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {cursor : Option Nat}
    {bound : Key} {st out : SearchSt} {best outBest : Option Key}
    {trail : FrameTrail} {value : Int}
    (hfreeze : FrozenOut ctx codes out outBest value)
    (hlevel : level = codes.length) (hbelow : value < Int.ofNat level)
    (hbound : bound = keysMax
      (sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells 0)
      ((List.range tail).map fun o =>
        sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells (o + 1)))
    (hlen : len = tail + 1)
    (hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc
      len numcells tcell cursor outBest)
    (hsound : LoopSound ctx bound best outBest) :
    LoopExit ctx tcLevel specFuel runFuel loopFuel level codes rsLab rsPtn
      tc len numcells tcell cursor bound st { out with fixedpts := fixedpts }
      best outBest trail (some value) := by
  have hfreeze' := hfreeze.setFixed fixedpts
  apply LoopExit.frozen value rfl hbelow
  · rw [hlen] at hcover
    exact hfreeze.exactLoop hlevel hbelow hbound hcover hsound
  · exact hfreeze'

/-- Convert an integer-valued loop exit to the enclosing node, shortening
the frozen comparison prefix at the node boundary. -/
theorem toNodeSome {ctx : Ctx}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      tc len nodeNumcells loopNumcells tcell : Nat}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {best outBest : Option Key} {trail : FrameTrail} {value : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail (some value)) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail value := by
  cases h with
  | done returned => cases returned
  | unwind target returned below sound payload located =>
      refine NodeExit.unwind (target := target)
        (returned := Option.some.inj returned) (below := below)
        (sound := ?_) (payload := payload) located
      constructor
      · intro b hb
        rw [← hbound]
        exact sound.upper b hb
      · exact sound.grows
  | frozen value returned below exact freeze =>
      cases Option.some.inj returned
      apply NodeExit.frozen
      · exact below
      · simpa only [← hbound] using exact
      · exact (freeze.shrink hprefix)
  | cheap boundary returned positive below exact =>
      apply NodeExit.cheap boundary (Option.some.inj returned) positive below
      simpa only [← hbound] using exact
  | exhausted returned => cases returned

/-- With nonzero cursor fuel, a `none` loop result is genuine completion
and supplies the enclosing node's ordinary one-level return. -/
theorem toNodeNone {ctx : Ctx}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      tc len nodeNumcells loopNumcells tcell : Nat}
    {nodeCodes loopCodes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {best outBest : Option Key} {trail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hfuel : loopFuel ≠ 0)
    (h : LoopExit ctx tcLevel loopSpecFuel runFuel loopFuel level loopCodes
      rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt out best
      outBest trail none) :
    NodeExit ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes nodeSt out
      nodeNumcells best outBest trail (Int.ofNat level - 1) := by
  cases h with
  | done _ exact =>
      apply NodeExit.done rfl
      simpa only [← hbound] using exact
  | unwind _ returned => cases returned
  | frozen _ returned => cases returned
  | cheap _ returned => cases returned
  | exhausted _ _ _ emptyFuel => exact (hfuel emptyFuel).elim

end LoopExit

namespace NodeInv

/-- A negative, non-generator discrete leaf produces the corrected exit:
ordinary comparison pruning retains its frozen prefix, while the only
remaining return is the explicit cheap-cell jump. -/
theorem negativeLeaf {G : Colored n k} {ctx : Ctx}
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
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hgen : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hearly : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
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
      hnode.run.otherLeaf hn hn0 hlevel hpath
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨outBest, houtcome, hexact⟩ := hnode.plainLeaf
    (inf := inf) (specFuel := specFuel) (fuel := fuel) hn hn0 hgb
    hsymm hloop hlevel hpath hcheap hnum hdisc hef hgen hearly hlive
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  have hfirstNe : leaf.eqlevFirst ≠ level := by
    intro heq
    apply hef
    simpa only [leaf, heq, beq_self_eq_true]
  have hmode := hprep.pruneMode hn hfull hstem hfirstNe hneg
  have hexit : NodeExit ctx tcLevel (specFuel + 1) (fuel + 1) level
      codes st (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    rcases hmode with hfreeze | hjump
    · rw [hout]
      apply NodeExit.frozen hearly hexact
      have hreadOut : stInc ctx (processnode ctx level ctx.n leaf).2 =
          outBest := by
        rw [← hout]
        exact houtcome.event.read
      have hsame : best = outBest := hfreeze.read.symm.trans hreadOut
      rw [← hsame]
      simpa only [leaf] using hfreeze
    · apply NodeExit.cheap leaf.noncheaplevel
      · rw [hout]
        exact hjump
      · exact hprep.cheap.positive
      · exact hcheap'
      · exact hexact
  refine ⟨outBest, ?_⟩
  exact {
    exit := hexit
    event := houtcome.event
    preserved := houtcome.preserved
    fixed := otherNode_leaf_early_fixedpts ctx inf tcLevel fuel level
      numcells st hnum hearly }

end NodeInv

end Hex.GraphIso.Nauty
