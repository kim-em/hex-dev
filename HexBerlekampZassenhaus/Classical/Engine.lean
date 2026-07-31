/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Classical.Search

public section
set_option backward.proofsInPublic true

/-!
# Direct classical engine
-/

namespace Hex

/-- Directly checkable output invariants at the executable boundary.  The
Mathlib theorem proves these facts and irreducibility; this guard also keeps a
malformed low-level result from escaping in non-proof consumers. -/
@[expose]
def validDirectFactors (core : ZPoly) (factors : List ZPoly) : Bool :=
  !factors.isEmpty &&
    decide (Array.polyProduct factors.toArray = core) &&
    factors.all (fun g => decide (ZPoly.content g = 1)) &&
    factors.all (fun g => decide (normalizeFactorSign g = g)) &&
    factors.all (fun g => decide (0 < g.degree?.getD 0))

/-- One prime plan, one lift, and one greedy direct recombination search. -/
@[expose]
def factorDirectCore
    (core : CoreProblem) (budget : Nat := defaultSubsetBudget) :
    ClassicalOutcome :=
  match directPrimePlan? core with
  | none => .declined .noGoodPrime {}
  | some modular =>
      let liftPlan := directLiftPlan core modular
      let basis := directLiftedBasis core modular liftPlan
      let initialStats : ClassicalStats :=
        { prime := modular.prime
          primeProbes := modular.probes.size
          liftedFactorCount := basis.data.liftedFactors.size
          henselLifts := 1 }
      match searchDirect (DensePoly.leadingCoeff core.poly) core.poly basis.data
          budget initialStats with
      | .declined reason _ stats => .declined reason stats
      | .factored factors _ stats =>
          if validDirectFactors core.poly factors then
            .factored factors.toArray stats
          else
            .declined .invalidCandidate stats

end Hex

