/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- The actual classification used by an off-path node. -/
def verdict (G : Colored n k) (tcLevel level numcells : Nat) (st : Search n) : Leaf :=
  let p := prepareOther { g := rowsOf G } tcLevel level numcells st
  (classify { g := rowsOf G } level p.1 p.2.2.2.2.2).1

/-- One node branch, with only the smaller sweep's contract assumed. -/
def NodeRule (G : Colored n k) (tcLevel : Nat) (first : Bool)
    (guard : Nat → Nat → Search n → Prop) : Prop :=
  ∀ fuel,
    (contract G tcLevel).sweepValid fuel (n + 1)
      (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel (n + 1)) →
    ∀ level numcells st, guard level numcells st →
      (keyContract G tcLevel).nodePost (fuel + 1) first level numcells st
        (Generic.nodeStep { g := rowsOf G } tcLevel
          (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel (n + 1))
          first level numcells st)

/-- One sweep branch, with only its smaller node and suffix contracts assumed. -/
def SweepRule (G : Colored n k) (tcLevel : Nat) (visits : Bool) : Prop :=
  ∀ fuel cfuel,
    (contract G tcLevel).nodeValid fuel (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel) →
    (contract G tcLevel).sweepValid fuel cfuel
      (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel cfuel) →
    ∀ first level numcells tc tv1 tv cell index st,
      (!first || st.orbits[tv]! == tv) = visits →
      (keyContract G tcLevel).sweepPost fuel (cfuel + 1) first level numcells tc tv1 (some tv) cell index st
        (Generic.sweepStep (n + 2)
          (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel)
          (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel cfuel)
          first level numcells tc tv1 tv cell index st)

/-- The node's generator conclusion uses the same smaller sweep contract
as its key bounds. -/
def NodeTraceRule (G : Colored n k) (tcLevel : Nat) : Prop :=
  ∀ fuel,
    (contract G tcLevel).sweepValid fuel (n + 1)
      (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel (n + 1)) →
    ∀ first level numcells st cs bs fs parents,
      NodeInput G { g := rowsOf G } tcLevel (fuel + 1) first ⟨level, numcells, cs, st⟩ bs fs parents →
      let result := Generic.nodeStep { g := rowsOf G } tcLevel
        (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel (n + 1)) first level numcells st
      Keeps parents result.1 result.2

/-- The sweep's accumulated trace is preserved by its actual smaller
child and suffix calls, in the same induction as maximum coverage. -/
def SweepTraceRule (G : Colored n k) (tcLevel : Nat) : Prop :=
  ∀ fuel cfuel,
    (contract G tcLevel).nodeValid fuel (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel) →
    (contract G tcLevel).sweepValid fuel cfuel
      (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel cfuel) →
    ∀ first level numcells tc tv1 tv cell index st l bs fs parents,
      SweepInput G { g := rowsOf G } tcLevel fuel (cfuel + 1) first level numcells tc tv1 (some tv)
        cell index st l bs fs parents →
      let result := Generic.sweepStep (n + 2)
        (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel)
        (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel cfuel)
        first level numcells tc tv1 tv cell index st
      Keeps parents result.1 result.2.2

/-- Local maximum obligations for every node verdict and both sweep
branches, assuming only the contracts of smaller recursive calls. -/
structure Rules (G : Colored n k) (tcLevel : Nat) : Prop where
  first_leaf : NodeRule G tcLevel true (fun level numcells st =>
    (Generic.prepareFirst { g := rowsOf G } tcLevel level numcells st).1 = n)
  first_branch : NodeRule G tcLevel true (fun level numcells st =>
    (Generic.prepareFirst { g := rowsOf G } tcLevel level numcells st).1 ≠ n)
  other_branch : NodeRule G tcLevel false (fun level numcells st =>
    verdict G tcLevel level numcells st = .internal)
  auto_first : NodeRule G tcLevel false (fun level numcells st =>
    verdict G tcLevel level numcells st = .autoFirst)
  auto_canon : NodeRule G tcLevel false (fun level numcells st =>
    verdict G tcLevel level numcells st = .autoCanon)
  better : ∀ sr, NodeRule G tcLevel false (fun level numcells st =>
    verdict G tcLevel level numcells st = .better sr)
  bad : NodeRule G tcLevel false (fun level numcells st =>
    verdict G tcLevel level numcells st = .bad)
  visit : SweepRule G tcLevel true
  skip : SweepRule G tcLevel false
  finish : ∀ fuel cfuel first level numcells tc tv1 cell index st,
    (keyContract G tcLevel).sweepPost fuel cfuel first level numcells tc tv1 none cell index st
      (.done, index, st)
  node_trace : NodeTraceRule G tcLevel
  sweep_trace : SweepTraceRule G tcLevel

/-- The exhaustive branch obligations instantiate the single generic recursion. -/
theorem Rules.calls {G : Colored n k} {tcLevel : Nat} (h : Rules G tcLevel) :
    Generic.CallPolicy { g := rowsOf G } (n + 2) tcLevel (contract G tcLevel) where
  node_zero := fun first level numcells st _ => node_zero G tcLevel first level numcells st
  node_step := by
    intro fuel hs first level numcells st _
    refine ⟨?_, h.node_trace fuel hs first level numcells st⟩
    cases first with
    | true =>
      by_cases he : (Generic.prepareFirst { g := rowsOf G } tcLevel level numcells st).1 = n
      · exact h.first_leaf fuel hs level numcells st he
      · exact h.first_branch fuel hs level numcells st he
    | false =>
      cases he : verdict G tcLevel level numcells st with
      | internal => exact h.other_branch fuel hs level numcells st he
      | autoFirst => exact h.auto_first fuel hs level numcells st he
      | autoCanon => exact h.auto_canon fuel hs level numcells st he
      | better sr => exact h.better sr fuel hs level numcells st he
      | bad => exact h.bad fuel hs level numcells st he
  sweep_none := fun fuel cfuel first level numcells tc tv1 cell index st _ =>
    ⟨h.finish fuel cfuel first level numcells tc tv1 cell index st,
      fun _ _ _ _ hi => hi.scope.keeps .done⟩
  sweep_zero := fun fuel first level numcells tc tv1 tv cell index st _ =>
    sweep_zero G tcLevel fuel first level numcells tc tv1 tv cell index st
  sweep_step := by
    intro fuel cfuel hn hs first level numcells tc tv1 tv cell index st _
    refine ⟨?_, h.sweep_trace fuel cfuel hn hs first level numcells tc tv1 tv cell index st⟩
    cases he : (!first || st.orbits[tv]! == tv) with
    | true => exact h.visit fuel cfuel hn hs first level numcells tc tv1 tv cell index st he
    | false => exact h.skip fuel cfuel hn hs first level numcells tc tv1 tv cell index st he

end Hex.GraphIso.Nauty.Max
