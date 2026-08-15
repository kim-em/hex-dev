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
# Precision-indexed logarithm table experiment

The executable package accepts an exact input fact and an explicit decimal
precision request.  Its bounded provider selects a term count and rational
window, then records every numeric choice in the replay payload.  Real-number
and logarithm semantics remain in the Mathlib companion.
-/

namespace Hex.Interval.Experiment.LogTablePrecision

open Propagator PayloadArena

structure Window where
  digits : Nat
  lowerNumerator : Nat
  lowerDenominator : Nat
  upperNumerator : Nat
  upperDenominator : Nat
  deriving DecidableEq, Repr

inductive Bound where
  | all
  | two
  | precision (digits : Nat)
  | window (value : Window)
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
  digits : Nat
  terms : Nat
  lowerNumerator : Nat
  lowerDenominator : Nat
  upperNumerator : Nat
  upperDenominator : Nat
  deriving DecidableEq, Repr

def Certificate.window (certificate : Certificate) : Window :=
  { digits := certificate.digits
    lowerNumerator := certificate.lowerNumerator
    lowerDenominator := certificate.lowerDenominator
    upperNumerator := certificate.upperNumerator
    upperDenominator := certificate.upperDenominator }

def Certificate.valid (certificate : Certificate) : Bool :=
  certificate.lowerDenominator != 0 && certificate.upperDenominator != 0 &&
    certificate.lowerNumerator * certificate.upperDenominator <
      certificate.upperNumerator * certificate.lowerDenominator

def decimal20Certificate : Certificate :=
  { digits := 20
    terms := 22
    lowerNumerator := 69314718055994530941
    lowerDenominator := 100000000000000000000
    upperNumerator := 69314718055994530942
    upperDenominator := 100000000000000000000 }

def decimal50Certificate : Certificate :=
  { digits := 50
    terms := 53
    lowerNumerator := 69314718055994530941723212145817656807550013436025
    lowerDenominator := 100000000000000000000000000000000000000000000000000
    upperNumerator := 69314718055994530941723212145817656807550013436026
    upperDenominator := 100000000000000000000000000000000000000000000000000 }

def certificateFor? (digits : Nat) : Option Certificate :=
  if digits == 20 then some decimal20Certificate
  else if digits == 50 then some decimal50Certificate
  else none

def decimal20Fact : Bound := .window decimal20Certificate.window
def decimal50Fact : Bound := .window decimal50Certificate.window
def decimal20Request : Bound := .precision 20
def decimal50Request : Bound := .precision 50

def certificateBody (certificate : Certificate) : List Nat :=
  [1, certificate.digits, certificate.terms,
    certificate.lowerNumerator, certificate.lowerDenominator,
    certificate.upperNumerator, certificate.upperDenominator]

def decodeCertificate? : List Nat → Option Certificate
  | [1, digits, terms, lowerNumerator, lowerDenominator,
      upperNumerator, upperDenominator] =>
      let certificate :=
        { digits, terms, lowerNumerator, lowerDenominator,
          upperNumerator, upperDenominator }
      if certificate.valid then some certificate else none
  | _ => none

def real : DomainId := { index := 0 }
def request : DomainId := { index := 1 }

def sourceKey : OpKey := { name := "log-table-precision.source" }
def requestKey : OpKey := { name := "log-table-precision.request" }
def logKey : OpKey := { name := "log-table-precision.log" }
def logRuleKey : RuleKey := { name := "log-table-precision.series" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def requestOperation : Operation :=
  { key := requestKey, inputs := [], output := request }
def logOperation : Operation :=
  { key := logKey, inputs := [real, request], output := real }

def operations : Array Operation :=
  #[sourceOperation, requestOperation, logOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }
def requestInstruction : Node :=
  { domain := request, op := { index := 1 }, args := [] }
def logInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 0, node 1] }

def program : Program :=
  { operations, nodes := #[sourceInstruction, requestInstruction, logInstruction] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body => (decodeCertificate? body).isSome }

def logRule : Registration :=
  { key := logRuleKey
    head := logKey
    kind := .forward
    watches := [.argument 0, .argument 1]
    writes := [.result] }

def logPlan (ruleRequest : RuleRequest Bound) : Plan Bound :=
  match ruleRequest.inputs, ruleRequest.writes with
  | [source, precision], [target] =>
      if source.fact != .two then
        { outcome := .noChange {}, drafts := [] }
      else
        match precision.fact with
        | .precision digits =>
            match certificateFor? digits with
            | some certificate =>
                { outcome :=
                    .success
                      [{ node := target, fact := .window certificate.window,
                         payload := payload 0 }]
                      []
                      { arithmeticWork := certificate.terms,
                        estimatedProofNodes := certificate.terms + 1 }
                  drafts :=
                    [{ label := payload 0, role := .fact, schema := 1,
                       body := certificateBody certificate }] }
            | none => { outcome := .noChange {}, drafts := [] }
        | _ => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := ()
    operations := #[sourceOperation, requestOperation]
    handlers := #[] }

def logPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[logOperation]
    handlers := #[Handler.statelessPlanned logRule logPlan #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, logPackage]

def checkerInput (digits : Nat) (certificate : Certificate) :
    SemanticReplay.CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.two, .precision digits, .all]
    target := { node := node 2, fact := .window certificate.window } }

def decimal20Input : SemanticReplay.CheckerInput Bound :=
  checkerInput 20 decimal20Certificate
def decimal50Input : SemanticReplay.CheckerInput Bound :=
  checkerInput 50 decimal50Certificate

def engineLimits : Propagator.Limits :=
  { maxOperations := 3, maxNodes := 3, maxRules := 1, maxRegistryEntries := 8,
    maxReplayFormats := 2, maxArity := 2, maxScopeNodes := 1,
    maxApplications := 2, maxQueueEntries := 16, maxActions := 8,
    maxMatcherVisits := 4, matcherBatchSize := 2, maxAcceptedFacts := 2,
    maxRetainedSuggestions := 0, maxEffort := 0, maxObservationValue := 64,
    maxDiagnosticValue := 300, maxOutcomeCandidates := 1,
    maxOutcomeSuggestions := 0, maxProposalItems := 1, maxInstances := 0,
    maxGeneration := 0, maxNodeDepth := 2, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 4 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8, maxTraversal := 64, maxLiveOffers := 8 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4, maxBodyCells := 16, maxDrafts := 2, maxDraftCells := 8,
    maxAtom := 1000000000000000000000000000000000000000000000000000,
    maxSchema := 1, maxUses := 2 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.LogTablePrecision

end
