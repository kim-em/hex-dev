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
