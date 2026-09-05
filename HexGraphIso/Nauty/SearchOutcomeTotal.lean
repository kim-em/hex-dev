/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeExit

public section

/-!
Assembly of the corrected search induction.

The first descent needs more result-side history than an ordinary node.
`FirstRun` keeps the established first-path package while pairing it with
the explicit exit classification used to justify every abandoned sweep.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A first-path result with both its reference histories and the corrected
reason for its return. -/
structure FirstRun (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel runFuel level : Nat) (codes fs : List Nat)
    (st out : SearchSt) (numcells : Nat) (outBest : Option Key)
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  proof : FirstProof G ctx tcLevel specFuel runFuel level codes fs st out
    numcells outBest receiptTrail eventTrail r
  exit : NodeExit ctx tcLevel specFuel runFuel level codes st out numcells
    none outBest receiptTrail r
  short : out.needshortprune = true →
    ShortSource G ctx out eventTrail r

namespace FirstRun

/-- The final first-path counter adjustment preserves the complete
corrected first-node result. -/
theorem firstFinish {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {codes fs : List Nat} {st out : SearchSt} {outBest : Option Key}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : FirstRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells outBest receiptTrail eventTrail r) :
    FirstRun G ctx tcLevel specFuel runFuel level codes fs st
      (Nauty.firstFinish level size index out) numcells outBest receiptTrail
      eventTrail r :=
  ⟨h.proof.firstFinish hfuel, h.exit.firstFinish hfuel, fun hshort => by
    apply ShortSource.firstFinish
    apply h.short
    rw [Nauty.firstFinish] at hshort
    split at hshort <;> exact hshort⟩

end FirstRun

namespace FirstLoopRun

/-- An early integer-valued first-path sweep becomes its enclosing node. -/
theorem toNodeSome {G : Colored n k} {ctx : Ctx}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level
      : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {outBest : Option Key} {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCodes
      nodeSt nodeNumcells)
    (hprefix : loopCodes.take nodeCodes.length = nodeCodes)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstLoopRun G ctx tcLevel loopSpecFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out none outBest receiptTrail eventTrail (some r)) :
    FirstRun G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCodes fs nodeSt
      out nodeNumcells outBest receiptTrail eventTrail r := by
  refine ⟨h.proof.toNodeSome hbound hfixed,
    h.exit.toNodeSome hbound hprefix, ?_⟩
  intro hshort
  obtain ⟨value, hreturned, hsource⟩ := h.short hshort
  cases Option.some.inj hreturned
  exact hsource

/-- A sufficiently fuelled `none` sweep is genuine completion and becomes
the enclosing first-path node's ordinary return. -/
theorem toNodeNone {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCodes loopCodes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells tcell : Nat}
    {cursor : Option Nat} {bound : Key} {nodeSt loopSt out : SearchSt}
    {outBest : Option Key} {receiptTrail eventTrail : FrameTrail}
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
    (hfuel : ctx.n < cursorRank cursor + loopFuel)
    (hfixed : loopSt.fixedpts = nodeSt.fixedpts)
    (h : FirstLoopRun G ctx tcLevel specFuel runFuel loopFuel level
      nodeCodes loopCodes fs rsLab rsPtn tc len loopNumcells tcell cursor
      bound loopSt out none outBest receiptTrail eventTrail none) :
    FirstRun G ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCodes fs
      nodeSt out nodeNumcells outBest receiptTrail eventTrail
      (Int.ofNat level - 1) := by
  refine ⟨h.proof.toNodeNone hbound hchildren hlen hfuel hfixed,
    h.exit.toNodeNone hbound hfuel, ?_⟩
  intro hshort
  obtain ⟨value, hreturned, _⟩ := h.short hshort
  cases hreturned

end FirstLoopRun

namespace FirstInv

/-- The first discrete leaf is an ordinary exact return in the corrected
classification. -/
theorem terminalRun {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : level = codes.length + 1)
    (h : FirstInv G ctx level codes numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := codes ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    FirstRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes full st
      out.2 numcells (some (pathLeafKey ctx full rs.lab)) trail trail
      out.1 := by
  dsimp only
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [rs.longcode]
  let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
  have hproof : FirstProof G ctx tcLevel (specFuel + 1) (fuel + 1)
      level codes full st out.2 numcells
      (some (pathLeafKey ctx full rs.lab)) trail trail out.1 := by
    simpa only [rs, full, out] using
      h.terminalFirstProof (inf := inf) (tcLevel := tcLevel)
        (specFuel := specFuel) (fuel := fuel) hn hn0 hlevel hnum
  have hstate := firstPath_discrete_state ctx inf tcLevel fuel level
    numcells st hnum
  have hdisc : discreteAt rs.ptn level ctx.n = true := by
    rw [← refine_discrete_iff hn hn0 h.searchOk (by omega)]
    exact hnum
  have hnode : nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells = pathLeafKey ctx full rs.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey]
  refine ⟨hproof, ?_, ?_⟩
  apply NodeExit.done
  · exact congrArg Prod.fst hstate
  · rw [hnode, incMax]
  · intro hshort
    rw [hstate] at hshort
    rw [firstterminal_short, h.shortClear] at hshort
    cases hshort

end FirstInv

/-- The corrected first-path root result proves equality between the
unpruned specification key and the key installed by the transcription. -/
theorem dominated_of_firstRun {G : Colored n k} (hn0 : n ≠ 0)
    {fs : List Nat} {best : Option Key}
    (hroot : FirstRun G { n := n, g := rowsOf G } 100 n (n + 2) 1 [] fs
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2)
      (initialPartition G).2.length best FrameTrail.empty FrameTrail.empty
      (firstPathNode { n := n, g := rowsOf G } (n + 2) 100 (n + 2) 1
        (initialPartition G).2.length
        (rootSt n (initialPartition G).1 (initialPartition G).2)).1) :
    canonSpecKey G = tracedKey G := by
  have hread := hroot.proof.node.outcome.event.read
  cases hroot.exit with
  | done returned exact =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | unwind target returned below sound payload located control =>
      cases payload with
      | first anchor carrier =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
      | canon anchor carrier =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
      | orbit payload =>
          exact ((Nat.not_lt_of_ge payload.positive) below).elim
  | frozen below exact freeze =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | cheap boundary returned positive atOrAbove saved exact =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | exhausted returned state incumbent emptyFuel => omega

end Hex.GraphIso.Nauty
