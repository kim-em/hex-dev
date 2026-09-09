/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

/-!
The nauty policy uses the direct search's local operations. The mutual
equalities identify every fuelled node and sweep with the generic
recursion, including exhausted calls and nonlocal exits.
-/

namespace Hex.GraphIso.Nauty

instance policy : Generic.Policy (Search n) n where
  visit := visit
  recordFirst := recordFirst
  compareCodes := compareCodes
  chooseTarget := chooseTarget
  firstterminal := firstterminal
  classify := classify
  leafExit := leafExit
  cheapCheck := cheapCheck
  child := child
  afterChildFirst := afterChildFirst
  leaveChild tv st := { st with fixedpts := st.fixedpts.erase tv }
  orbit st tv := st.orbits[tv]!
  shortprune := shortprune
  longprune tcell st := Nauty.longprune tcell st.fixedpts st.autos
  recover inf level st := Nauty.recover inf level st
  afterSweep := afterSweep

variable {n : Nat}

mutual

/-- The direct node is the generic recursion at the nauty policy. -/
theorem node_eq_generic (first : Bool) (ctx : Ctx n) (inf tcLevel fuel : Nat)
    (level numcells : Nat) (st : Search n) :
    node first ctx inf tcLevel fuel level numcells st =
      Generic.node first ctx inf tcLevel fuel level numcells st := by
  cases fuel with
  | zero => simp only [node, Generic.node]
  | succ fuel =>
    rw [node, Generic.node]
    unfold Generic.nodeStep
    dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
      Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.firstterminal,
      Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck,
      Generic.Policy.afterSweep, Generic.Policy.child, Generic.Policy.afterChildFirst,
      Generic.Policy.leaveChild, Generic.Policy.orbit, Generic.Policy.shortprune,
      Generic.Policy.longprune, Generic.Policy.recover]
    simp only [← sweep_eq_generic (fuel := fuel) (cfuel := n + 1)]
    rfl
termination_by (fuel, 0, 0)

/-- The direct sweep is the generic recursion at the nauty policy. -/
theorem sweep_eq_generic (first : Bool) (ctx : Ctx n) (inf tcLevel fuel cfuel : Nat)
    (level numcells tc tv1 : Nat) (tv? : Option Nat) (tcell : VSet n)
    (index : Nat) (st : Search n) :
    sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 tv? tcell index st =
      Generic.sweep first ctx inf tcLevel fuel cfuel
        level numcells tc tv1 tv? tcell index st := by
  cases tv? with
  | none => simp only [sweep, Generic.sweep]
  | some tv =>
    cases cfuel with
    | zero => simp only [sweep, Generic.sweep]
    | succ cfuel =>
      rw [sweep, Generic.sweep]
      unfold Generic.sweepStep
      dsimp only [policy, Generic.Policy.child, Generic.Policy.afterChildFirst,
        Generic.Policy.leaveChild, Generic.Policy.orbit, Generic.Policy.shortprune,
        Generic.Policy.longprune, Generic.Policy.recover]
      simp only [← node_eq_generic (fuel := fuel),
        ← sweep_eq_generic (fuel := fuel) (cfuel := cfuel)]
      rfl
termination_by (fuel, 1, cfuel)

end

end Hex.GraphIso.Nauty
