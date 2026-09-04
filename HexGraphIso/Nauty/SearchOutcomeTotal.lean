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
  refine ⟨hproof, ?_⟩
  apply NodeExit.done
  · exact congrArg Prod.fst hstate
  · rw [hnode, incMax]

end FirstInv

/-- The corrected first-path root result proves equality between the
unpruned specification key and the key installed by the transcription. -/
theorem dominated_of_firstRun {G : Colored n k} (hn0 : n ≠ 0)
    {best : Option Key}
    (hroot : FirstRun G { n := n, g := rowsOf G } 100 n (n + 2) 1 [] []
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
  | unwind target returned below sound payload located =>
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
  | cheap boundary returned positive atOrAbove exact =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | exhausted returned state incumbent emptyFuel => omega

end Hex.GraphIso.Nauty
