/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# A Mathlib-free mixed-function propagation canary

This experiment puts two unrelated opaque unary functions in one package
registry.  The first establishes a unit-range fact; the second consumes that
fact to establish an upper bound.  Mathematical interpretations and replay
theorems belong to the companion module.
-/

namespace Hex.Interval.Experiment.MixedFunctions

open Propagator PayloadArena

/-- The smallest fact lattice needed to test a non-vacuous function chain. -/
inductive Bound where
  | all
  | unit
  | atMostThree
  | empty
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .unit, .unit => .unit
  | .atMostThree, .atMostThree => .atMostThree
  | .unit, .atMostThree | .atMostThree, .unit => .unit

def code : Bound → Nat
  | .all => 0
  | .unit => 1
  | .atMostThree => 2
  | .empty => 3

def ofCode? : Nat → Option Bound
  | 0 => some .all
  | 1 => some .unit
  | 2 => some .atMostThree
  | 3 => some .empty
  | _ => none

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "mixed-functions.source" }
def sineKey : OpKey := { name := "mixed-functions.sine" }
def expKey : OpKey := { name := "mixed-functions.exp" }

def sineRuleKey : RuleKey := { name := "mixed-functions.sine.unit" }
def expRuleKey : RuleKey := { name := "mixed-functions.exp.at-most-three" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def sineOperation : Operation :=
  { key := sineKey, inputs := [real], output := real }

def expOperation : Operation :=
  { key := expKey, inputs := [real], output := real }

def operations : Array Operation :=
  #[sourceOperation, sineOperation, expOperation]

def sineRule : Registration :=
  { key := sineRuleKey
    head := sineKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def expRule : Registration :=
  { key := expRuleKey
    head := expKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body =>
      match body with
      | [code] => (Bound.ofCode? code).isSome
      | _ => false }

def sinePlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [_], [target] =>
      { outcome :=
          .success
            [{ node := target, fact := .unit, payload := { index := 0 } }]
            [] {}
        drafts :=
          [{ label := { index := 0 }
             role := .fact
             schema := 1
             body := [Bound.unit.code] }] }
  | _, _ => { outcome := .failed 1, drafts := [] }

/-- Exponential propagation deliberately requires the sine package's exact
unit-range fact.  This makes the mixed-function chronology non-vacuous. -/
def expPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      if input.fact == .unit then
        { outcome :=
            .success
              [{ node := target, fact := .atMostThree, payload := { index := 0 } }]
              [] {}
          drafts :=
            [{ label := { index := 0 }
               role := .fact
               schema := 1
               body := [Bound.atMostThree.code] }] }
      else
        { outcome := .failed 2, drafts := [] }
  | _, _ => { outcome := .failed 3, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation]
    handlers := #[] }

def sinePackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[sineOperation]
    handlers := #[Handler.statelessPlanned sineRule sinePlan #[factFormat]] }

def expPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[expOperation]
    handlers := #[Handler.statelessPlanned expRule expPlan #[factFormat]] }

def packages : Array (Package Bound) :=
  #[sourcePackage, sinePackage, expPackage]

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 3
    maxNodes := 8
    maxRules := 2
    maxRegistryEntries := 16
    maxReplayFormats := 4
    maxArity := 1
    maxScopeNodes := 1
    maxApplications := 8
    maxQueueEntries := 24
    maxActions := 16
    maxMatcherVisits := 16
    matcherBatchSize := 8
    maxAcceptedFacts := 8
    maxRetainedSuggestions := 1
    maxEffort := 1
    maxObservationValue := 16
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 1
    maxProposalItems := 4
    maxInstances := 1
    maxGeneration := 1
    maxNodeDepth := 4
    maxEqualities := 1
    splitEndpointLimit :=
      { maxEndpointHeight := 8, maxAlignmentShift := 4 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 24
    maxTraversal := 256
    maxLiveOffers := 24 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 16
    maxBodyCells := 32
    maxDrafts := 8
    maxDraftCells := 8
    maxAtom := 32
    maxSchema := 1
    maxUses := 8 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.MixedFunctions
