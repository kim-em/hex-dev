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

end Hex.GraphIso.Nauty
