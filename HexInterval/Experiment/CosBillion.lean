/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.SinTenInterval
public import HexInterval.Experiment.SinTen

@[expose] public section

/-!
# Huge-argument cosine sign certificate

This Mathlib-free experiment records the fixed reduction of `10^10` by
`3183098861 * pi`.  The quotient and residual endpoints are untrusted replay
data.  The scheduler knows only a finite endpoint table; real-number and
trigonometric semantics live in the Mathlib companion.
-/

namespace Hex.Interval.Experiment.CosBillion

open Propagator PayloadArena
open Hex.Interval.Experiment.SinTen

abbrev Rat := Rational.Raw

structure Interval where
  lower : Rat
  upper : Rat
  lowerOpen : Bool
  upperOpen : Bool
  deriving DecidableEq, Repr

inductive Bound where
  | all
  | interval (value : Interval)
  deriving DecidableEq, Repr

def rat (numerator denominator : Int) : Rat :=
  { num := numerator, den := denominator }

def openInterval (lower upper : Rat) : Bound :=
  .interval { lower, upper, lowerOpen := true, upperOpen := true }

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    if current == proposed then .noChange
    else match current, proposed with
      | _, .all => .noChange
      | .all, proposed => .improved proposed
      | _, _ => .malformed 1

def quotient : Nat := 3183098861

def finePiCandidate : ConstantCandidate :=
  { lowerNumerator := 314159265358979323846
    lowerDenominator := 100000000000000000000
    upperNumerator := 314159265358979323847
    upperDenominator := 100000000000000000000 }

def finePiFact : Bound :=
  openInterval
    (rat finePiCandidate.lowerNumerator finePiCandidate.lowerDenominator)
    (rat finePiCandidate.upperNumerator finePiCandidate.upperDenominator)

def residualFact : Bound := openInterval (rat 13 5) (rat 27 10)
def negativeFact : Bound :=
  .interval
    { lower := rat (-1) 1, upper := rat 0 1
      lowerOpen := false, upperOpen := true }
def positiveFact : Bound :=
  .interval
    { lower := rat 0 1, upper := rat 1 1
      lowerOpen := true, upperOpen := false }

structure ReductionCertificate where
  quotient : Nat
  lowerNumerator : Nat
  lowerDenominator : Nat
  upperNumerator : Nat
  upperDenominator : Nat
  deriving DecidableEq, Repr

def reductionCertificate : ReductionCertificate :=
  { quotient
    lowerNumerator := 13
    lowerDenominator := 5
    upperNumerator := 27
    upperDenominator := 10 }

def ReductionCertificate.valid (certificate : ReductionCertificate) : Bool :=
  certificate.lowerDenominator != 0 && certificate.upperDenominator != 0

def reductionBody (certificate : ReductionCertificate) : List Nat :=
  [2, certificate.quotient, certificate.lowerNumerator,
    certificate.lowerDenominator, certificate.upperNumerator,
    certificate.upperDenominator]

def decodeReduction? : List Nat → Option ReductionCertificate
  | [2, q, lowerNumerator, lowerDenominator, upperNumerator, upperDenominator] =>
      let certificate :=
        { quotient := q, lowerNumerator, lowerDenominator,
          upperNumerator, upperDenominator }
      if certificate.valid then some certificate else none
  | _ => none

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "cos-billion.source" }
def cosineKey : OpKey := { name := "cos-billion.cosine" }
def piKey : OpKey := { name := "cos-billion.pi" }
def residualKey : OpKey := { name := "cos-billion.reduce" }
def negationKey : OpKey := { name := "cos-billion.negation" }

def constantRuleKey : RuleKey := { name := "cos-billion.constant" }
def reductionRuleKey : RuleKey := { name := "cos-billion.reduction" }
def localRuleKey : RuleKey := { name := "cos-billion.local-cosine" }
def negationRuleKey : RuleKey := { name := "cos-billion.negation" }
def identityRuleKey : RuleKey := { name := "cos-billion.identity" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def cosineOperation : Operation :=
  { key := cosineKey, inputs := [real], output := real }
def piOperation : Operation := { key := piKey, inputs := [], output := real }
def residualOperation : Operation :=
  { key := residualKey, inputs := [real, real], output := real }
def negationOperation : Operation :=
  { key := negationKey, inputs := [real], output := real }

def operations : Array Operation :=
  #[sourceOperation, cosineOperation, piOperation, residualOperation,
    negationOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }
def targetInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }
def piInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [] }
def residualInstruction : Node :=
  { domain := real, op := { index := 3 }, args := [node 0, node 2] }
def localInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 3] }
def negatedInstruction : Node :=
  { domain := real, op := { index := 4 }, args := [node 4] }

def program : Program :=
  { operations
    nodes := #[sourceInstruction, targetInstruction, piInstruction,
      residualInstruction, localInstruction, negatedInstruction] }

def checkerInput : SemanticReplay.CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all, .all, .all, .all, .all, .all]
    target := { node := node 1, fact := positiveFact } }

def constantRule : Registration :=
  { key := constantRuleKey, head := piKey, kind := .forward,
    watches := [], writes := [.result] }
def reductionRule : Registration :=
  { key := reductionRuleKey, head := residualKey, kind := .forward,
    watches := [.argument 0, .argument 1], writes := [.result] }
def localRule : Registration :=
  { key := localRuleKey, head := cosineKey, kind := .forward,
    watches := [.argument 0], writes := [.result] }
def negationRule : Registration :=
  { key := negationRuleKey, head := negationKey, kind := .forward,
    watches := [.argument 0], writes := [.result] }
def identityRule : Registration :=
  { key := identityRuleKey, head := residualKey, kind := .instantiate,
    watches := [.result], writes := [] }

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1
    validateBody := fun body =>
      body == [1] || (decodeReduction? body).isSome ||
        body == [3] || body == [4] }
def instanceFormat : ReplayFormat :=
  { role := .instance, schema := 1
    validateBody := fun body => body == [quotient] }
def equalityFormat : ReplayFormat :=
  { role := .equality, schema := 1
    validateBody := fun body => body == [quotient] }

def constantPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.writes with
  | [target] =>
      { outcome := .success
          [{ node := target, fact := finePiFact, payload := payload 10 }] [] {}
        drafts :=
          [{ label := payload 10, role := .fact, schema := 1, body := [1] }] }
  | _ => { outcome := .failed 1, drafts := [] }

def reductionPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [_source, pi], [target] =>
      if pi.fact == finePiFact then
        { outcome := .success
            [{ node := target, fact := residualFact, payload := payload 11 }] [] {}
          drafts :=
            [{ label := payload 11, role := .fact, schema := 1,
               body := reductionBody reductionCertificate }] }
      else { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 2, drafts := [] }

def localPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      if input.fact == residualFact then
        { outcome := .success
            [{ node := target, fact := negativeFact, payload := payload 12 }] [] {}
          drafts :=
            [{ label := payload 12, role := .fact, schema := 1, body := [3] }] }
      else { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 3, drafts := [] }

def negationPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      if input.fact == negativeFact then
        { outcome := .success
            [{ node := target, fact := positiveFact, payload := payload 13 }] [] {}
          drafts :=
            [{ label := payload 13, role := .fact, schema := 1, body := [4] }] }
      else { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 4, drafts := [] }

def identityPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs with
  | [input] =>
      if input.node != node 3 || input.fact != residualFact then
        { outcome := .noChange {}, drafts := [] }
      else
        match request.program.node? (node 1), request.program.node? (node 5) with
        | some target, some negated =>
            if target != targetInstruction || negated != negatedInstruction then
              { outcome := .noChange {}, drafts := [] }
            else
              { outcome := .success []
                  [.instantiate
                    { key := quotient
                      nodes := []
                      equalities :=
                        [{ left := .existing (node 1), right := .existing (node 5),
                           payload := payload 15 }]
                      payload := payload 14 }] {}
                drafts :=
                  [{ label := payload 14, role := .instance, schema := 1,
                     body := [quotient] },
                   { label := payload 15, role := .equality, schema := 1,
                     body := [quotient] }] }
        | _, _ => { outcome := .noChange {}, drafts := [] }
  | _ => { outcome := .failed 5, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }
def constantPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[piOperation]
    handlers := #[Handler.statelessPlanned constantRule constantPlan #[factFormat]] }
def reductionPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[residualOperation]
    requiredOperations := #[cosineOperation, negationOperation]
    handlers := #[Handler.statelessPlanned reductionRule reductionPlan #[factFormat],
      Handler.statelessPlanned identityRule identityPlan
        #[instanceFormat, equalityFormat]] }
def localPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[cosineOperation]
    handlers := #[Handler.statelessPlanned localRule localPlan #[factFormat]] }
def negationPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[negationOperation]
    handlers := #[Handler.statelessPlanned negationRule negationPlan #[factFormat]] }

def packages : Array (Package Bound) :=
  #[sourcePackage, localPackage, constantPackage, reductionPackage, negationPackage]

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 5, maxNodes := 6, maxRules := 5, maxRegistryEntries := 24,
    maxReplayFormats := 8, maxArity := 2, maxScopeNodes := 1,
    maxApplications := 12, maxQueueEntries := 96, maxActions := 80,
    maxMatcherVisits := 16, matcherBatchSize := 8, maxAcceptedFacts := 12,
    maxRetainedSuggestions := 2, maxEffort := 1, maxObservationValue := 24,
    maxDiagnosticValue := 300, maxOutcomeCandidates := 1,
    maxOutcomeSuggestions := 1, maxProposalItems := 3, maxInstances := 1,
    maxGeneration := 1, maxNodeDepth := 3, maxEqualities := 1,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 4 } }
def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 96, maxTraversal := 768, maxLiveOffers := 64 }
def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 24, maxBodyCells := 64, maxDrafts := 12,
    maxDraftCells := 16, maxAtom := 1000000000000000000000,
    maxSchema := 1, maxUses := 12 }
def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.CosBillion

end
