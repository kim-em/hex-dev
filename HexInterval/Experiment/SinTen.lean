/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

@[expose] public section

/-!
# Candidate data for a first certified range-reduction canary

The executable side chooses a constant provider, an integer half-turn, and a
local sine method.  These values are untrusted replay data.  This module knows
nothing about real numbers or trigonometric theorems.
-/

namespace Hex.Interval.Experiment.SinTen

/-- Coarse rational endpoints proposed for a constant. -/
structure ConstantCandidate where
  lowerNumerator : Nat
  lowerDenominator : Nat
  upperNumerator : Nat
  upperDenominator : Nat
  deriving DecidableEq, Repr

namespace Machin

/-- The first provider asks replay to establish `3 < pi < 16/5`. -/
def candidate : ConstantCandidate :=
  { lowerNumerator := 3
    lowerDenominator := 1
    upperNumerator := 16
    upperDenominator := 5 }

/-- Provider-owned structural authentication before mathematical replay. -/
def accepts (candidate : ConstantCandidate) : Bool := candidate == Machin.candidate

end Machin

/-- Integer/quadrant data proposed by the range reducer. `negativeOutput`
records the sign introduced by an odd number of half-turns. -/
structure ReductionCandidate where
  halfTurns : Nat
  negativeOutput : Bool
  deriving DecidableEq, Repr

namespace Reduction

def candidate : ReductionCandidate :=
  { halfTurns := 3, negativeOutput := true }

def accepts (candidate : ReductionCandidate) : Bool :=
  candidate == Reduction.candidate

/-- Per-field preflight bound for the fixed reduction canary. Checking it
before the cross-products keeps malformed provider data fail-closed. -/
def endpointLimit : Nat := 32

/-- A provider enclosure is strong enough to select half-turn `3` when its
encoded endpoints are bounded, genuine rationals and satisfy
`3 * upper ≤ 10 ≤ 4 * lower`. -/
def adequate (constant : ConstantCandidate) : Bool :=
  decide (
    constant.lowerNumerator ≤ endpointLimit ∧
    constant.lowerDenominator ≤ endpointLimit ∧
    constant.upperNumerator ≤ endpointLimit ∧
    constant.upperDenominator ≤ endpointLimit ∧
    constant.lowerDenominator ≠ 0 ∧
    constant.upperDenominator ≠ 0 ∧
    3 * constant.upperNumerator ≤ 10 * constant.upperDenominator ∧
    10 * constant.lowerDenominator ≤ 4 * constant.lowerNumerator)

end Reduction

/-- The local sine package currently exposes only the strict-positive core
method needed by this acceptance case. -/
inductive LocalMethod where
  | positiveCore
  | taylorThree
  deriving DecidableEq, Repr

namespace Local

def accepts (method : LocalMethod) : Bool := method == .positiveCore

end Local

/-- Complete untrusted certificate assembled from independently owned roles. -/
structure Certificate where
  constant : ConstantCandidate
  reduction : ReductionCandidate
  method : LocalMethod
  deriving DecidableEq, Repr

def certificate : Certificate :=
  { constant := Machin.candidate
    reduction := Reduction.candidate
    method := .positiveCore }

end Hex.Interval.Experiment.SinTen

end
