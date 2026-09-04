/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcome
import all HexGraphIso.Nauty.Search

public section

/-!
Base cases of the outcome-indexed search induction.

These lemmas keep node fuel and child-loop fuel visibly separate.  In
particular, loop-fuel exhaustion is represented by `LoopResult.exhausted`,
whereas reaching the end cursor with positive fuel is a genuine completed
sweep.
-/

namespace Hex.GraphIso.Nauty

/-- A first-path node with no runtime fuel reports exhaustion. -/
theorem firstPath_zero (ctx : Ctx) (inf tcLevel specFuel level numcells : Nat)
    (cs : List Nat) (st : SearchSt) :
    NodeResult ctx tcLevel specFuel 0 level cs st
      (firstPathNode ctx inf tcLevel 0 level numcells st).2 numcells
      (firstPathNode ctx inf tcLevel 0 level numcells st).1 := by
  rw [firstPathNode]
  exact .exhausted rfl rfl rfl

/-- An off-path node with no runtime fuel reports exhaustion. -/
theorem otherNode_zero (ctx : Ctx) (inf tcLevel specFuel level numcells : Nat)
    (cs : List Nat) (st : SearchSt) :
    NodeResult ctx tcLevel specFuel 0 level cs st
      (otherNode ctx inf tcLevel 0 level numcells st).2 numcells
      (otherNode ctx inf tcLevel 0 level numcells st).1 := by
  rw [otherNode]
  exact .exhausted rfl rfl rfl

/-- First-path child-loop fuel exhaustion is not completion. -/
theorem firstLoop_zero (ctx : Ctx)
    (inf tcLevel specFuel runFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tv? : Option Nat) (tcell index : Nat) (bound : Key)
    (st : SearchSt) :
    LoopResult ctx tcLevel specFuel runFuel 0 level cs rsLab rsPtn tc len
      numcells tcell none bound st
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).2.2
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).1 := by
  rw [firstChildLoop]
  exact .exhausted rfl rfl rfl

/-- Off-path child-loop fuel exhaustion is not completion. -/
theorem otherLoop_zero (ctx : Ctx)
    (inf tcLevel specFuel runFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tv? : Option Nat) (tcell : Nat) (bound : Key) (st : SearchSt) :
    LoopResult ctx tcLevel specFuel runFuel 0 level cs rsLab rsPtn tc len
      numcells tcell none bound st
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).2
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).1 := by
  rw [otherChildLoop]
  exact .exhausted rfl rfl rfl

/-- With positive loop fuel, an absent next child completes the first-path
sweep rather than exhausting it. -/
theorem firstLoop_done (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tcell index : Nat) (cursor : Option Nat) (bound : Key)
    (st : SearchSt)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor st)
    (hnext : nextElem tcell cursor = none) :
    LoopResult ctx tcLevel specFuel runFuel (loopFuel + 1) level cs rsLab
      rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).2.2
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).1 := by
  rw [firstChildLoop]
  case x_1 => omega
  exact .complete rfl (.refl ctx bound st) tcell cursor hcover fun o ho =>
    no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- With positive loop fuel, an absent next child completes the off-path
sweep rather than exhausting it. -/
theorem otherLoop_done (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor st)
    (hnext : nextElem tcell cursor = none) :
    LoopResult ctx tcLevel specFuel runFuel (loopFuel + 1) level cs rsLab
      rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).2
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).1 := by
  rw [otherChildLoop]
  case x_1 => omega
  exact .complete rfl (.refl ctx bound st) tcell cursor hcover fun o ho =>
    no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

end Hex.GraphIso.Nauty
