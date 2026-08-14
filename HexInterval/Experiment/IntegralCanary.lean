/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Mathlib-free bounded-integration canary

This package plans one checked Taylor integration certificate for
`exp (-x^2)` on the single cell `[0, 1]`.  Runtime code sees only a finite fact
lattice and natural-number certificate atoms.  The Mathlib companion checks
the polynomial integral and integrates the pointwise remainder.
-/

namespace Hex.Interval.Experiment.IntegralCanary

open Propagator PayloadArena

inductive Bound where
  | all
  | window7468_7469
  | empty
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .window7468_7469, .window7468_7469 => .window7468_7469

end Bound

/-- One-cell degree-seven Taylor certificate.  Every rational endpoint and
error component used by replay is retained as an exact natural-number pair. -/
structure IntegrationCertificate where
  cells : Nat
  leftNumerator : Nat
  leftDenominator : Nat
  rightNumerator : Nat
  rightDenominator : Nat
  terms : Nat
  approximationNumerator : Nat
  approximationDenominator : Nat
  errorNumerator : Nat
  errorDenominator : Nat
  lowerNumerator : Nat
  lowerDenominator : Nat
  upperNumerator : Nat
  upperDenominator : Nat
  deriving DecidableEq, Repr

def certificate : IntegrationCertificate :=
  { cells := 1
    leftNumerator := 0
    leftDenominator := 1
    rightNumerator := 1
    rightDenominator := 1
    terms := 8
    approximationNumerator := 1009219
    approximationDenominator := 1351350
    errorNumerator := 1
    errorDenominator := 609280
    lowerNumerator := 7468
    lowerDenominator := 10000
    upperNumerator := 7469
    upperDenominator := 10000 }

def certificateBody : List Nat :=
  [certificate.cells, certificate.leftNumerator, certificate.leftDenominator,
    certificate.rightNumerator, certificate.rightDenominator,
    certificate.terms, certificate.approximationNumerator,
    certificate.approximationDenominator, certificate.errorNumerator,
    certificate.errorDenominator, certificate.lowerNumerator,
    certificate.lowerDenominator, certificate.upperNumerator,
    certificate.upperDenominator]

def decodeCertificate? : List Nat → Option IntegrationCertificate
  | [1, 0, 1, 1, 1, 8, 1009219, 1351350, 1, 609280,
      7468, 10000, 7469, 10000] => some certificate
  | _ => none

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }

def integralKey : OpKey := { name := "integral-canary.integral01" }
def integrationRuleKey : RuleKey := { name := "integral-canary.taylor-cell" }

def integralOperation : Operation :=
  { key := integralKey, inputs := [], output := real }

def operations : Array Operation := #[integralOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def integralInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }

def program : Program :=
  { operations, nodes := #[integralInstruction] }

def integrationRule : Registration :=
  { key := integrationRuleKey
    head := integralKey
    kind := .forward
    watches := []
    writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body => decodeCertificate? body == some certificate }

def planForBody (body : List Nat) (request : RuleRequest Bound) : Plan Bound :=
  match decodeCertificate? body, request.inputs, request.writes with
  | some _, [], [target] =>
      { outcome :=
          .success
            [{ node := target, fact := .window7468_7469, payload := payload 0 }]
            [] { arithmeticWork := 8, estimatedProofNodes := 16 }
        drafts :=
          [{ label := payload 0, role := .fact, schema := 1, body }] }
  | _, _, _ => { outcome := .failed 1, drafts := [] }

def integrationPlan : RuleRequest Bound → Plan Bound :=
  planForBody certificateBody

def integrationPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[integralOperation]
    handlers :=
      #[Handler.statelessPlanned integrationRule integrationPlan #[factFormat]] }

def packages : Array (Package Bound) := #[integrationPackage]

def engineLimits : Propagator.Limits :=
  { maxOperations := 1
    maxNodes := 1
    maxRules := 1
    maxRegistryEntries := 4
    maxReplayFormats := 2
    maxArity := 1
    maxScopeNodes := 1
    maxApplications := 1
    maxQueueEntries := 4
    maxActions := 2
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 1
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 16
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 1
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 4, maxTraversal := 16, maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 2
    maxBodyCells := 16
    maxDrafts := 1
    maxDraftCells := 16
    maxAtom := 1400000
    maxSchema := 1
    maxUses := 2 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages #[.all] limits

end Hex.Interval.Experiment.IntegralCanary
