/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.ChoosePrimeData
public import HexBerlekampZassenhaus.ReassemblyProofs
public import HexBerlekampZassenhaus.Recombination

public section
set_option backward.proofsInPublic true

/-!
# Data carried by the direct classical factorization engine

Both modular paths are indexed by their normalized square-free core.  A prime
plan, recovery lift, and search result therefore cannot accidentally be paired
with a different polynomial.
-/

namespace Hex

/-- Global cap on direct classical recombination candidates. -/
def defaultSubsetBudget : Nat := 262144

/-- A primitive square-free polynomial presented to the classical engine.
The executable layer stores the polynomial; the Mathlib correctness layer
supplies and retains the normalization invariants. -/
structure CoreProblem where
  poly : ZPoly
deriving DecidableEq

namespace CoreProblem

/-- Package the square-free core produced by the common normalization pass. -/
@[expose]
def ofNormalized (normalized : FactorNormalizationData) : CoreProblem :=
  ⟨normalized.squareFreeCore⟩

end CoreProblem

/-- One good-prime factorization computed while planning.  The candidate is
retained with its result so proof provenance and diagnostics never need to
recover it by searching the candidate table. -/
structure DirectPrimeProbe (core : CoreProblem) where
  candidate : SmallPrimeCandidate
  data : PrimeChoiceData
  /-- Degrees of the cached modular factors. -/
  factorDegrees : Array Nat
  /-- Subset-degree reachability bitset, indexed from zero through
  `degree core`.  This is computed once with the modular factorization and is
  reused by planning and optional degree-obstruction checks. -/
  reachableDegrees : Array Bool

/-- Cached direct-coordinate modular plan.  Every successful probe performed by
the planner is retained.  The selected probe is stored separately from the
other successful probes, so it is structurally impossible for selection to
refer to an uncached factorization. -/
structure DirectPrimePlan (core : CoreProblem) where
  selected : DirectPrimeProbe core
  otherProbes : Array (DirectPrimeProbe core)

namespace DirectPrimePlan

/-- Build a plan from its selected successful probe and all other successful
probes.  This is the only constructor exposed outside this module. -/
@[expose]
def ofSelection {core : CoreProblem} (selected : DirectPrimeProbe core)
    (otherProbes : Array (DirectPrimeProbe core)) : DirectPrimePlan core :=
  ⟨selected, otherProbes⟩

/-- All cached successful probes, with the selected value first. -/
@[expose]
def probes {core : CoreProblem} (plan : DirectPrimePlan core) :
    Array (DirectPrimeProbe core) :=
  #[plan.selected] ++ plan.otherProbes

/-- Selected modular factorization. -/
@[expose]
def data {core : CoreProblem} (plan : DirectPrimePlan core) : PrimeChoiceData :=
  plan.selected.data

/-- Selected prime. -/
@[expose]
def prime {core : CoreProblem} (plan : DirectPrimePlan core) : Nat :=
  plan.data.p

/-- Number of local factors at the selected prime. -/
@[expose]
def width {core : CoreProblem} (plan : DirectPrimePlan core) : Nat :=
  plan.data.factorsModP.size

end DirectPrimePlan

/-- Validated recovery precision for one direct modular plan.  There is no
`B = 0` meaning: construction fixes the ordinary Mignotte recovery bound and
the corresponding positive Hensel exponent. -/
structure DirectLiftPlan
    (core : CoreProblem) (modular : DirectPrimePlan core) where
deriving DecidableEq

namespace DirectLiftPlan

/-- The unique recovery plan indexed by a core and its selected modular
factorization. -/
@[expose]
def canonical (core : CoreProblem) (modular : DirectPrimePlan core) :
    DirectLiftPlan core modular :=
  ⟨⟩

/-- Ordinary direct Mignotte coefficient bound. -/
@[expose]
def coeffBound {core : CoreProblem} {modular : DirectPrimePlan core}
    (_plan : DirectLiftPlan core modular) : Nat :=
  ZPoly.defaultFactorCoeffBound core.poly

/-- Recovery precision derived from the indexed core, bound, and prime. -/
@[expose]
def precision {core : CoreProblem} {modular : DirectPrimePlan core}
    (plan : DirectLiftPlan core modular) : Nat :=
  precisionForCoeffBound plan.coeffBound modular.data.p

end DirectLiftPlan

/-- Token for the one direct-coordinate Hensel lift owned by a lift plan.
The lifted data is derived from the indices rather than stored, so a basis
from another core or precision cannot be inserted. -/
structure DirectLiftedBasis
    {core : CoreProblem} {modular : DirectPrimePlan core}
    (plan : DirectLiftPlan core modular) where

namespace DirectLiftedBasis

/-- Construct the unique basis token for a recovery plan. -/
@[expose]
def canonical {core : CoreProblem} {modular : DirectPrimePlan core}
    (plan : DirectLiftPlan core modular) : DirectLiftedBasis plan :=
  ⟨⟩

/-- Execute the lift determined by the indexed recovery plan. -/
@[expose]
def data {core : CoreProblem} {modular : DirectPrimePlan core}
    {plan : DirectLiftPlan core modular}
    (_basis : DirectLiftedBasis plan) : LiftData :=
  ZPoly.coreLiftData core.poly plan.coeffBound modular.data

end DirectLiftedBasis

/-- Why the bounded direct classical engine declined. -/
inductive DeclineReason where
  | noGoodPrime
  | subsetBudget
  | liftFailure
  | invalidCandidate
deriving DecidableEq

namespace DeclineReason

@[expose]
def name : DeclineReason → String
  | .noGoodPrime => "noGoodPrime"
  | .subsetBudget => "subsetBudget"
  | .liftFailure => "liftFailure"
  | .invalidCandidate => "invalidCandidate"

end DeclineReason

/-- Statistics from a direct classical attempt.  `completedLevels` records the
fully exhausted head-forced subset cardinalities, in execution order. -/
structure ClassicalStats where
  prime : Nat := 0
  primeProbes : Nat := 0
  liftedFactorCount : Nat := 0
  henselLifts : Nat := 0
  candidatesTried : Nat := 0
  completedLevels : Array Nat := #[]
deriving DecidableEq

/-- Typed result of the sole production classical engine. -/
inductive ClassicalOutcome where
  | factored (factors : Array ZPoly) (stats : ClassicalStats)
  | declined (reason : DeclineReason) (stats : ClassicalStats)
deriving DecidableEq

/-- Public dispatch tier. -/
inductive FactorTier where
  | constant
  | quadratic
  | classical
  | lattice
  | trial
deriving DecidableEq

namespace FactorTier

@[expose]
def name : FactorTier → String
  | .constant => "constant"
  | .quadratic => "quadratic"
  | .classical => "classical"
  | .lattice => "lattice"
  | .trial => "trial"

end FactorTier

/-- Trace derived from the same dispatcher result used by the untraced API. -/
structure DirectFactorTrace where
  tier : FactorTier
  classicalDecline : Option DeclineReason := none
  classical : ClassicalStats := {}
deriving DecidableEq

/-- Result of the shared normalization/classical dispatcher.  A successful
prime plan is retained even when recombination declines, so the lattice tier
can consume the exact modular factorization already computed. -/
structure ClassicalRun (f : ZPoly) where
  factors : Option (Array ZPoly)
  trace : DirectFactorTrace
  modular :
    Option (DirectPrimePlan (CoreProblem.ofNormalized (normalizeForFactor f))) :=
      none

/-- Raw factors and trace produced by the total dispatcher in one execution. -/
structure FactorRun where
  factors : Array ZPoly
  trace : DirectFactorTrace
deriving DecidableEq

end Hex
