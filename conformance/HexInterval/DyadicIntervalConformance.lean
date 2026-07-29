/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.DyadicInterval

/-!
# Concrete dyadic interval conformance

Conformance checks for the first concrete propagator fact domain.  These tests
exercise exact openness and endpoint attainment rather than merely checking
coarse numerical hulls.
-/

namespace Hex.Interval.DyadicIntervalConformance

open Experiment Propagator
open DyadicInterval

private def d (value : Int) : Dyadic := Dyadic.ofInt value

private def half : Dyadic := Dyadic.ofIntWithPrec 1 1

private def endpointLimit : EndpointLimit where
  maxEndpointHeight := 128
  maxAlignmentShift := 64

private def tightAlignmentLimit : EndpointLimit where
  maxEndpointHeight := 128
  maxAlignmentShift := 4

private def readyAs (result : Result) (expected : Raw) : Bool :=
  match result with
  | .ready fact => fact.view == expected
  | .inapplicable | .resourceLimit _ => false

private def finite (lower : Int) (lowerStrict : Bool)
    (upper : Int) (upperStrict : Bool) : Raw :=
  .bounds (.finite (d lower) lowerStrict) (.finite (d upper) upperStrict)

private def imported? (raw : Raw) : Option Fact :=
  match importRaw endpointLimit raw with
  | .ready fact => some fact
  | .malformed | .resourceLimit _ => none

/-! ## Canonical construction and checked import -/

#guard Fact.empty.view == .empty
#guard Fact.whole.view == .bounds .unbounded .unbounded
#guard readyAs (closed endpointLimit 0 1) (finite 0 false 1 false)
#guard readyAs (openInterval endpointLimit 0 1) (finite 0 true 1 true)
#guard readyAs (closedOpen endpointLimit 0 1) (finite 0 false 1 true)
#guard readyAs (openClosed endpointLimit 0 1) (finite 0 true 1 false)
#guard
  readyAs (atLeast endpointLimit 0)
    (.bounds (.finite 0 false) .unbounded)
#guard
  readyAs (lessThan endpointLimit 1)
    (.bounds .unbounded (.finite 1 true))

-- Smart construction canonicalizes inconsistent cuts to the unique empty
-- value, while the untrusted import boundary rejects the same shape.
#guard readyAs (openInterval endpointLimit 1 1) .empty
#guard readyAs (closed endpointLimit 2 1) .empty
#guard importRaw endpointLimit (finite 1 true 1 false) == .malformed
#guard importRaw endpointLimit (finite 2 false 1 false) == .malformed

/-! ## Intersection, unbounded sides, negation, and subtraction -/

private def intersectionExample : Option Result := do
  let left ← imported? (finite 0 false 2 false)
  let right ← imported? (finite 0 true 3 false)
  pure (intersect endpointLimit left right)

#guard
  match intersectionExample with
  | some result => readyAs result (finite 0 true 2 false)
  | none => false

private def upperTie : Option Result := do
  let left ← imported? (finite (-2) false 1 false)
  let right ← imported? (finite (-3) false 1 true)
  pure (intersect endpointLimit left right)

#guard
  match upperTie with
  | some result => readyAs result (finite (-2) false 1 true)
  | none => false

private def unboundedSub : Option Result := do
  let left ← imported? (.bounds (.finite 1 false) .unbounded)
  let right ← imported? (.bounds .unbounded (.finite 2 false))
  pure (sub endpointLimit left right)

#guard
  match unboundedSub with
  | some result =>
      readyAs result (.bounds (.finite (-1) false) .unbounded)
  | none => false

private def unboundedNeg : Option Result := do
  let input ← imported? (.bounds (.finite 1 true) .unbounded)
  pure (neg endpointLimit input)

#guard
  match unboundedNeg with
  | some result =>
      readyAs result (.bounds .unbounded (.finite (-1) true))
  | none => false

private def inverseShiftInput : Dyadic := .ofOdd 1 64 (by decide)

private def wide : Dyadic :=
  Dyadic.ofInt (Int.ofNat (2 ^ 128 - 1))

private def subtractionPreflight : Option Result := do
  let left ← imported?
    (.bounds (.finite (-wide) false) (.finite 1 false))
  let right ← imported?
    (.bounds (.finite inverseShiftInput false) (.finite wide false))
  pure (sub tightAlignmentLimit left right)

-- The lower subtraction itself would exceed the endpoint budget.
#guard
  match subtractionChecked tightAlignmentLimit (-wide) wide with
  | .error (.endpoint cost) => !cost.allowed tightAlignmentLimit
  | _ => false

-- Nevertheless, the whole operation reports the later upper-pair alignment
-- failure.  This distinguishes complete preflight from an implementation that
-- performs the lower subtraction before checking the upper pair.
#guard
  match subtractionPreflight with
  | some (.resourceLimit (.comparison cost)) => cost.alignmentShift == 64
  | _ => false

/-! ## Attainment-sensitive multiplication and square -/

private def closedZeroTimesOpenZero : Option Result := do
  let left ← imported? (finite 0 false 1 false)
  let right ← imported? (finite 0 true 1 false)
  pure (mul endpointLimit left right)

-- `[0,1] * (0,1] = [0,1]`: zero is attained through the left
-- factor even though the right lower cut is open.
#guard
  match closedZeroTimesOpenZero with
  | some result => readyAs result (finite 0 false 1 false)
  | none => false

private def zeroSingletonTimesOpen : Option Result := do
  let left ← imported? (finite 0 false 0 false)
  let right ← imported? (finite 0 true 1 true)
  pure (mul endpointLimit left right)

-- Interior points of the open factor still multiply the zero singleton to
-- an attained zero; corner openness alone would get this case wrong.
#guard
  match zeroSingletonTimesOpen with
  | some result => readyAs result (finite 0 false 0 false)
  | none => false

private def positiveOpenSquare : Option Result := do
  let input ← imported? (finite 0 true 1 false)
  pure (square endpointLimit input)

#guard
  match positiveOpenSquare with
  | some result => readyAs result (finite 0 true 1 false)
  | none => false

private def straddlingOpenSquare : Option Result := do
  let input ← imported? (finite (-1) true 1 true)
  pure (square endpointLimit input)

#guard
  match straddlingOpenSquare with
  | some result => readyAs result (finite 0 false 1 true)
  | none => false

private def tiedSquareOneClosed : Option Result := do
  let input ← imported? (finite (-1) false 1 true)
  pure (square endpointLimit input)

-- The tied upper magnitude is attained through the closed `-1` endpoint.
#guard
  match tiedSquareOneClosed with
  | some result => readyAs result (finite 0 false 1 false)
  | none => false

private def openProduct : Option Result := do
  let left ← imported? (finite 0 true 1 true)
  let right ← imported? (finite 0 true 1 true)
  pure (mul endpointLimit left right)

#guard
  match openProduct with
  | some result => readyAs result (finite 0 true 1 true)
  | none => false

private def attainedZeroProduct : Option Result := do
  let left ← imported? (finite 0 false 1 false)
  let right ← imported? (finite (-1) true 0 true)
  pure (mul endpointLimit left right)

#guard
  match attainedZeroProduct with
  | some result => readyAs result (finite (-1) true 0 false)
  | none => false

private def unboundedProduct : Option Result := do
  let left ← imported? (.bounds (.finite 1 false) .unbounded)
  let right ← imported? (finite 1 false 2 false)
  pure (mul endpointLimit left right)

#guard unboundedProduct == some .inapplicable

private def unboundedSquare : Option Result := do
  let input ← imported? (.bounds .unbounded (.finite (-1) true))
  pure (square endpointLimit input)

#guard
  match unboundedSquare with
  | some result =>
      readyAs result (.bounds (.finite 1 true) .unbounded)
  | none => false

/-! ## Singleton scaling and exact backward division -/

private def negativeScale : Option Result := do
  let input ← imported? (finite 1 true 3 false)
  pure (scale endpointLimit (-2) input)

#guard
  match negativeScale with
  | some result => readyAs result (finite (-6) false (-2) true)
  | none => false

private def unboundedScale : Option Result := do
  let input ← imported? (.bounds (.finite 1 false) .unbounded)
  pure (scale endpointLimit (-2) input)

#guard
  match unboundedScale with
  | some result =>
      readyAs result (.bounds .unbounded (.finite (-2) false))
  | none => false

private def exactBackward : Option Result := do
  let image ← imported? (finite 2 false 4 false)
  pure (unscaleExact endpointLimit 2 image)

#guard
  match exactBackward with
  | some result =>
      readyAs result
        (.bounds (.finite 1 false) (.finite (d 2) false))
  | none => false

private def nondyadicBackward : Option Result := do
  let image ← imported? (finite 3 false 6 false)
  pure (unscaleExact endpointLimit 3 image)

#guard nondyadicBackward == some .inapplicable

private def zeroBackward : Option Result := do
  let image ← imported? (finite 0 false 0 false)
  pure (unscaleExact endpointLimit 0 image)

#guard zeroBackward == some .inapplicable

/-! ## Positive and negative reciprocal components -/

private def positiveReciprocal : Option Result := do
  let input ← imported? (finite 1 false 2 false)
  pure (reciprocal endpointLimit 8 input)

#guard
  match positiveReciprocal with
  | some result =>
      readyAs result
        (.bounds (.finite half false) (.finite 1 false))
  | none => false

private def negativeReciprocal : Option Result := do
  let input ← imported? (finite (-2) false (-1) false)
  pure (reciprocal endpointLimit 8 input)

#guard
  match negativeReciprocal with
  | some result =>
      readyAs result
        (.bounds (.finite (-1) false) (.finite (-half) false))
  | none => false

private def positiveOpenZeroReciprocal : Option Result := do
  let input ← imported? (finite 0 true 2 false)
  pure (reciprocal endpointLimit 8 input)

#guard
  match positiveOpenZeroReciprocal with
  | some result =>
      readyAs result (.bounds (.finite half false) .unbounded)
  | none => false

private def positiveUnboundedReciprocal : Option Result := do
  let input ← imported? (.bounds (.finite 1 false) .unbounded)
  pure (reciprocal endpointLimit 8 input)

#guard
  match positiveUnboundedReciprocal with
  | some result =>
      readyAs result (.bounds (.finite 0 true) (.finite 1 false))
  | none => false

private def negativeOpenZeroReciprocal : Option Result := do
  let input ← imported? (finite (-2) false 0 true)
  pure (reciprocal endpointLimit 8 input)

#guard
  match negativeOpenZeroReciprocal with
  | some result =>
      readyAs result (.bounds .unbounded (.finite (-half) false))
  | none => false

private def negativeUnboundedReciprocal : Option Result := do
  let input ← imported? (.bounds .unbounded (.finite (-1) false))
  pure (reciprocal endpointLimit 8 input)

#guard
  match negativeUnboundedReciprocal with
  | some result =>
      readyAs result (.bounds (.finite (-1) false) (.finite 0 true))
  | none => false

private def mixedReciprocal : Option Result := do
  let input ← imported? (finite (-1) false 1 false)
  pure (reciprocal endpointLimit 8 input)

#guard mixedReciprocal == some .inapplicable

private def roundedReciprocal : Option Result := do
  let input ← imported? (finite 3 false 3 false)
  pure (reciprocal endpointLimit 2 input)

-- `1 / 3` is bracketed on the quarter grid.  Both moved bounds are open
-- because neither outward endpoint is attained by the singleton input.
#guard
  match roundedReciprocal with
  | some result =>
      readyAs result
        (.bounds (.finite (Dyadic.ofIntWithPrec 1 2) true)
          (.finite half true))
  | none => false

-- Cut inversion treats zero only as a component limit.  In particular, a
-- closed zero never reaches `invAtPrec`; the interval-level operation still
-- rejects intervals containing closed zero.
#guard
  match inverseLower endpointLimit 8 (.finite 0 false) with
  | .ok .unbounded => true
  | _ => false

#guard
  match inverseUpper endpointLimit 8 (.finite 0 false) with
  | .ok .unbounded => true
  | _ => false

private def reciprocalPreflight : Option Result := do
  let input ← imported? (finite 1 false 2 false)
  pure (reciprocal tightAlignmentLimit 16 input)

#guard
  match reciprocalPreflight with
  | some (.resourceLimit (.inverse _ 16 shift)) => shift > 4
  | _ => false

-- Core performs these two shifts separately: their signed exponents cancel,
-- but their allocation work does not.
#guard
  match inverseChecked tightAlignmentLimit (-64) inverseShiftInput with
  | .error (.inverse _ 64 shift) => shift == 128
  | _ => false

/-! ## Splitting -/

private def splitAtZero : Option (Fact × Fact) := do
  let input ← imported? (finite 0 false 1 false)
  match split endpointLimit input 0 with
  | .ok children => some children
  | .error _ => none

#guard
  match splitAtZero with
  | some (left, right) =>
      left.view == finite 0 false 0 false &&
        right.view == finite 0 true 1 false
  | none => false

private def splitOpenCut : Option (Fact × Fact) := do
  let input ← imported? (finite 0 true 1 false)
  match split endpointLimit input 0 with
  | .ok children => some children
  | .error _ => none

#guard
  match splitOpenCut with
  | some (left, right) =>
      left.view == .empty && right.view == finite 0 true 1 false
  | none => false

/-! ## Preflight and checked engine start -/

private def far : Dyadic := .ofOdd 1 1000000000 (by decide)

-- Empty splitting short-circuits before inspecting an otherwise over-budget
-- cut point, preserving the canonical empty image law.
#guard
  match split endpointLimit .empty far with
  | .ok (left, right) => left.isEmpty && right.isEmpty
  | .error _ => false

private def largeHeight : EndpointLimit where
  maxEndpointHeight := 1000000100
  maxAlignmentShift := 64

private def preflightedIntersection : Option Result := do
  let lower ←
    match importRaw largeHeight
        (.bounds (.finite 1 false) .unbounded) with
    | .ready fact => some fact
    | _ => none
  let upper ←
    match importRaw largeHeight
        (.bounds .unbounded (.finite far false)) with
    | .ready fact => some fact
    | _ => none
  pure (intersect largeHeight lower upper)

#guard
  match preflightedIntersection with
  | some (.resourceLimit (.comparison cost)) =>
      cost.alignmentShift == 1000000000
  | _ => false

private def domainImprovement : Option (NarrowResult Fact) := do
  let current ← imported? (finite 0 false 2 false)
  let candidate ← imported? (finite 0 true 3 false)
  pure ((factDomain endpointLimit).narrow { index := 0 } current candidate)

#guard
  match domainImprovement with
  | some (.improved fact) => fact.view == finite 0 true 2 false
  | _ => false

private def domainContradiction : Option (NarrowResult Fact) := do
  let current ← imported? (finite 0 false 1 false)
  let candidate ← imported? (finite 1 true 2 false)
  pure ((factDomain endpointLimit).narrow { index := 0 } current candidate)

#guard
  match domainContradiction with
  | some (.contradiction fact) => fact.isEmpty
  | _ => false

private def domainNoChange : Option (NarrowResult Fact) := do
  let current ← imported? (finite 0 false 1 false)
  let candidate ← imported? (finite (-1) false 2 false)
  pure ((factDomain endpointLimit).narrow { index := 0 } current candidate)

#guard
  match domainNoChange with
  | some .noChange => true
  | _ => false

-- Re-narrowing an already contradictory branch with the same empty fact is a
-- fixed point, not a newly discovered contradiction.
#guard
  match (factDomain endpointLimit).narrow { index := 0 } .empty .whole with
  | .noChange => true
  | _ => false

private def real : DomainId := { index := 0 }

private def sourceOp : OpKey := { name := "dyadic.source" }

private def sourceProgram : Program :=
  { operations := #[{ key := sourceOp, inputs := [], output := real }]
    nodes := #[{ domain := real, op := { index := 0 }, args := [] }] }

private def engineLimits : Limits :=
  { maxOperations := 4
    maxNodes := 4
    maxRules := 0
    maxArity := 2
    maxApplications := 0
    maxQueueEntries := 0
    maxActions := 4
    maxAcceptedFacts := 4
    maxRetainedSuggestions := 0
    maxEffort := 4
    maxObservationValue := 16
    maxDiagnosticValue := 16
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 0
    maxProposalItems := 2
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 16
    maxEqualities := 0
    splitEndpointLimit := endpointLimit }

#guard
  match start endpointLimit sourceProgram #[] #[.empty] engineLimits with
  | .error (.emptyFact 0) => true
  | _ => false

#guard
  match start endpointLimit sourceProgram #[] #[] engineLimits with
  | .error (.engine .wrongFactCount) => true
  | _ => false

#guard
  match start endpointLimit sourceProgram #[]
      #[.bounds (.finite 1 true) (.finite 1 false)] engineLimits with
  | .error (.malformedFact 0) => true
  | _ => false

#guard
  match start endpointLimit sourceProgram #[]
      #[.bounds .unbounded (.finite far false)] engineLimits with
  | .error (.factResource 0 _) => true
  | _ => false

#guard
  match start endpointLimit sourceProgram #[]
      #[.bounds (.finite 0 false) (.finite 1 false)] engineLimits with
  | .ok engine =>
      engine.facts.size == 1 &&
        (engine.facts[0]?).any fun fact =>
          fact.view == finite 0 false 1 false
  | .error _ => false

end Hex.Interval.DyadicIntervalConformance
