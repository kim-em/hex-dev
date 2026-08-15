/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession
public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# Source-pinned PNT+ exponential point bounds

This bounded Mathlib-free package authenticates the nine remaining exponential
sites in PNT+ `IEANTN/LogTables.lean`. Each row reduces its exact rational
argument to a natural multiple of a rational step in `[-1, 1]`, records one
side of a fourteen-term Taylor enclosure for the step, and checks the final
power comparison with exact natural arithmetic.
-/

namespace Hex.Interval.Experiment.PntExpPoint

open Propagator PayloadArena

inductive Direction where
  | lower
  | upper
  deriving DecidableEq, Repr

structure Source where
  sourceIndex : Nat
  negative : Bool
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

structure Cut where
  sourceIndex : Nat
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

inductive Bound where
  | all
  | exact (value : Source)
  | lower (value : Cut)
  | upper (value : Cut)
  | empty
  deriving DecidableEq, Repr

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    if current == proposed then .noChange
    else match current, proposed with
      | _, .all => .noChange
      | .all, proposed => .improved proposed
      | _, _ => .malformed 1

structure Certificate where
  sourceIndex : Nat
  sourceNegative : Bool
  sourceNumerator : Nat
  sourceDenominator : Nat
  stepNegative : Bool
  stepNumerator : Nat
  stepDenominator : Nat
  power : Nat
  terms : Nat
  direction : Direction
  anchorNumerator : Nat
  anchorDenominator : Nat
  resultNumerator : Nat
  resultDenominator : Nat
  deriving DecidableEq, Repr

def row (sourceIndex : Nat) (sourceNegative : Bool) (sourceNumerator
    sourceDenominator : Nat) (stepNegative : Bool) (stepNumerator
    stepDenominator power : Nat) (direction : Direction) (anchorNumerator
    anchorDenominator resultNumerator resultDenominator : Nat) : Certificate :=
  { sourceIndex, sourceNegative, sourceNumerator, sourceDenominator,
    stepNegative, stepNumerator, stepDenominator, power, terms := 14,
    direction, anchorNumerator, anchorDenominator, resultNumerator,
    resultDenominator }

def rowNegOne : Certificate :=
  row 0 true 1 1 true 1 1 1 .lower 367879441 1000000000 367879441 1000000000
def rowNegHalf : Certificate :=
  row 1 true 1 2 true 1 2 1 .upper 6065307 10000000 6065307 10000000
def rowNegTwoThirds : Certificate :=
  row 2 true 2 3 true 2 3 1 .upper 513418 1000000 513418 1000000
def rowNegFifty : Certificate :=
  row 3 true 50 1 true 1 1 50 .upper 46 125 1 100000000000000000000
def rowOne112 : Certificate :=
  row 4 false 139 125 false 139 250 2 .upper 8719 5000 3041 1000
def rowTwo : Certificate :=
  row 5 false 2 1 false 1 2 4 .upper 1649 1000 8 1
def rowTwenty : Certificate :=
  row 6 false 20 1 false 1 2 40 .upper 164872127071 100000000000 485165196 1
def rowTwentyTwo : Certificate :=
  row 7 false 22 1 false 1 1 22 .lower 27 10 1000000000 1
def rowNegThirteenHalf : Certificate :=
  row 8 true 27 2 true 1 2 27 .lower 1213 2000 1 900000

def rows : List Certificate :=
  [rowNegOne, rowNegHalf, rowNegTwoThirds, rowNegFifty, rowOne112, rowTwo,
    rowTwenty, rowTwentyTwo, rowNegThirteenHalf]

def rowFor? (sourceIndex : Nat) : Option Certificate :=
  rows.find? fun value => value.sourceIndex == sourceIndex

def Certificate.source (value : Certificate) : Source :=
  { sourceIndex := value.sourceIndex, negative := value.sourceNegative,
    numerator := value.sourceNumerator, denominator := value.sourceDenominator }

def Certificate.cut (value : Certificate) : Cut :=
  { sourceIndex := value.sourceIndex, numerator := value.resultNumerator,
    denominator := value.resultDenominator }

def Certificate.result (value : Certificate) : Bound :=
  match value.direction with
  | .lower => .lower value.cut
  | .upper => .upper value.cut

def Certificate.powerCheck (value : Certificate) : Bool :=
  match value.direction with
  | .lower =>
      value.resultNumerator * value.anchorDenominator ^ value.power ≤
        value.anchorNumerator ^ value.power * value.resultDenominator
  | .upper =>
      value.anchorNumerator ^ value.power * value.resultDenominator ≤
        value.resultNumerator * value.anchorDenominator ^ value.power

def Certificate.valid (value : Certificate) : Bool :=
  rowFor? value.sourceIndex == some value &&
    decide (0 < value.sourceDenominator) &&
    decide (0 < value.stepDenominator) &&
    decide (0 < value.anchorDenominator) &&
    decide (0 < value.resultDenominator) &&
    value.sourceNegative == value.stepNegative &&
    value.sourceNumerator * value.stepDenominator ==
      value.power * value.stepNumerator * value.sourceDenominator &&
    value.stepNumerator ≤ value.stepDenominator &&
    decide (0 < value.power) && value.terms == 14 &&
    decide (0 < value.anchorNumerator) && value.powerCheck

def Direction.encode : Direction → Nat
  | .lower => 0
  | .upper => 1

def Direction.decode? : Nat → Option Direction
  | 0 => some .lower
  | 1 => some .upper
  | _ => none

def encode (value : Certificate) : List Nat :=
  [value.sourceIndex, value.sourceNegative.toNat, value.sourceNumerator,
    value.sourceDenominator, value.stepNegative.toNat, value.stepNumerator,
    value.stepDenominator, value.power, value.terms, value.direction.encode,
    value.anchorNumerator, value.anchorDenominator, value.resultNumerator,
    value.resultDenominator]

def decode? : List Nat → Option Certificate
  | [sourceIndex, sourceNegative, sourceNumerator, sourceDenominator,
      stepNegative, stepNumerator, stepDenominator, power, terms, direction,
      anchorNumerator, anchorDenominator, resultNumerator, resultDenominator] => do
      let sourceNegative ← match sourceNegative with
        | 0 => some false | 1 => some true | _ => none
      let stepNegative ← match stepNegative with
        | 0 => some false | 1 => some true | _ => none
      let direction ← Direction.decode? direction
      let value : Certificate :=
        { sourceIndex, sourceNegative, sourceNumerator, sourceDenominator,
          stepNegative, stepNumerator, stepDenominator, power, terms, direction,
          anchorNumerator, anchorDenominator, resultNumerator, resultDenominator }
      if value.valid then some value else none
  | _ => none

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "pnt-exp-point.source" }
def expKey : OpKey := { name := "pnt-exp-point.exp" }
def ruleKey : RuleKey := { name := "pnt-exp-point.taylor-power" }
def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def expOperation : Operation := { key := expKey, inputs := [real], output := real }
def operations : Array Operation := #[sourceOperation, expOperation]
def node (index : Nat) : NodeId := { index }
def payload : PayloadId := { index := 0 }
def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def expInstruction : Node := { domain := real, op := { index := 1 }, args := [node 0] }
def program : Program := { operations, nodes := #[sourceInstruction, expInstruction] }

def registration : Registration :=
  { key := ruleKey, head := expKey, kind := .forward,
    watches := [.argument 0], writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun body => (decode? body).isSome }

def plan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      match input.fact with
      | .exact source =>
          match rowFor? source.sourceIndex with
          | some value =>
              if value.source == source then
                { outcome :=
                    .success [{ node := target, fact := value.result, payload }] []
                      { arithmeticWork := value.terms + value.power,
                        estimatedProofNodes := value.terms + value.power + 8 },
                  drafts :=
                    [{ label := payload, role := .fact, schema := 1,
                       body := encode value }] }
              else { outcome := .noChange {}, drafts := [] }
          | none => { outcome := .noChange {}, drafts := [] }
      | _ => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }
def expPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[expOperation],
    handlers := #[Handler.statelessPlanned registration plan #[factFormat]] }
def packages : Array (Package Bound) := #[sourcePackage, expPackage]

def checkerInput (value : Certificate) : SemanticReplay.CheckerInput Bound :=
  { baseProgram := program, initialFacts := #[.exact value.source, .all],
    target := { node := node 1, fact := value.result } }

def representativeInput : SemanticReplay.CheckerInput Bound := checkerInput rowTwenty

def engineLimits : Propagator.Limits :=
  { maxOperations := 2, maxNodes := 2, maxRules := 1, maxRegistryEntries := 8,
    maxReplayFormats := 2, maxArity := 1, maxScopeNodes := 1, maxApplications := 2,
    maxQueueEntries := 8, maxActions := 4, maxMatcherVisits := 2,
    matcherBatchSize := 2, maxAcceptedFacts := 2, maxRetainedSuggestions := 0,
    maxEffort := 0, maxObservationValue := 128, maxDiagnosticValue := 1024,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0, maxProposalItems := 1,
    maxInstances := 0, maxGeneration := 0, maxNodeDepth := 2, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 4 } }
def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8, maxTraversal := 32, maxLiveOffers := 8 }
def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4, maxBodyCells := 20, maxDrafts := 2, maxDraftCells := 20,
    maxAtom := 100000000000000000000, maxSchema := 1, maxUses := 2 }
def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.PntExpPoint
