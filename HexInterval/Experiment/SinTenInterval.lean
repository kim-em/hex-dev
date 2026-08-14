/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.SemanticReplay
public import HexInterval.Experiment.PolicySession
public import HexInterval.Experiment.Rational

@[expose] public section

/-!
# Endpoint facts through the generic chronology

This experiment uses explicit rational interval endpoints. It intentionally
supports only top-to-interval refinement and repeated identical facts; general
interval intersection remains outside this canary.
-/

namespace Hex.Interval.Experiment.SinTenInterval

open Propagator PayloadArena

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

def piFact : Bound := openInterval (rat 3 1) (rat 16 5)
def residualFact : Bound := openInterval (rat 2 5) (rat 1 1)
def positiveFact : Bound :=
  .interval
    { lower := rat 0 1
      upper := rat 1 1
      lowerOpen := true
      upperOpen := false }
def negativeFact : Bound :=
  .interval
    { lower := rat (-1) 1
      upper := rat 0 1
      lowerOpen := false
      upperOpen := true }

namespace Bound

/-- Every explicit endpoint must carry a genuine rational denominator. -/
def valid : Bound → Bool
  | .all => true
  | .interval value => value.lower.valid && value.upper.valid

def code? : Bound → Option Nat
  | .all => some 0
  | fact =>
      if !fact.valid then none
      else if fact == piFact then some 1
      else if fact == residualFact then some 2
      else if fact == positiveFact then some 3
      else if fact == negativeFact then some 4
      else none

def ofCode? : Nat → Option Bound
  | 0 => some .all
  | 1 => some piFact
  | 2 => some residualFact
  | 3 => some positiveFact
  | 4 => some negativeFact
  | _ => none

end Bound

/-- A deliberately partial intersection boundary. Unknown combinations are
malformed rather than silently treated as disjoint. -/
def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    if current == proposed then .noChange
    else match current, proposed with
      | _, .all => .noChange
      | .all, proposed => .improved proposed
      | _, _ => .malformed 1

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "sin-ten-interval.source" }
def sineKey : OpKey := { name := "sin-ten-interval.sine" }
def piKey : OpKey := { name := "sin-ten-interval.pi" }
def residualKey : OpKey := { name := "sin-ten-interval.reduce" }
def negationKey : OpKey := { name := "sin-ten-interval.negation" }

def constantRuleKey : RuleKey := { name := "sin-ten-interval.constant" }
def reductionRuleKey : RuleKey := { name := "sin-ten-interval.reduction" }
def localRuleKey : RuleKey := { name := "sin-ten-interval.local-sine" }
def negationRuleKey : RuleKey := { name := "sin-ten-interval.negation" }
def identityRuleKey : RuleKey := { name := "sin-ten-interval.identity" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def sineOperation : Operation := { key := sineKey, inputs := [real], output := real }
def piOperation : Operation := { key := piKey, inputs := [], output := real }
def residualOperation : Operation :=
  { key := residualKey, inputs := [real, real], output := real }
def negationOperation : Operation :=
  { key := negationKey, inputs := [real], output := real }

def operations : Array Operation :=
  #[sourceOperation, sineOperation, piOperation, residualOperation, negationOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }
def targetSineInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }
def piInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [] }
def residualInstruction : Node :=
  { domain := real, op := { index := 3 }, args := [node 0, node 2] }
def localSineInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 3] }
def negatedLocalSineInstruction : Node :=
  { domain := real, op := { index := 4 }, args := [node 4] }

def baseProgram : Program :=
  { operations
    nodes := #[sourceInstruction, targetSineInstruction, piInstruction,
      residualInstruction, localSineInstruction] }

def extendedProgram : Program :=
  { operations
    nodes := baseProgram.nodes ++ #[negatedLocalSineInstruction] }

def checkerInput : SemanticReplay.CheckerInput Bound :=
  { baseProgram
    initialFacts := #[.all, .all, .all, .all, .all]
    target := { node := node 1, fact := negativeFact } }

def constantRule : Registration :=
  { key := constantRuleKey, head := piKey, kind := .forward,
    watches := [], writes := [.result] }
def reductionRule : Registration :=
  { key := reductionRuleKey, head := residualKey, kind := .forward,
    watches := [.argument 0, .argument 1], writes := [.result] }
def localRule : Registration :=
  { key := localRuleKey, head := sineKey, kind := .forward,
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
      match body with
      | [code] => (Bound.ofCode? code).isSome
      | _ => false }
def instanceFormat : ReplayFormat :=
  { role := .instance, schema := 1, validateBody := fun body => body == [1] }
def equalityFormat : ReplayFormat :=
  { role := .equality, schema := 1, validateBody := fun body => body == [1] }

def factPlan (fact : Bound) (label : PayloadId) (request : RuleRequest Bound) :
    Plan Bound :=
  match fact.code?, request.writes with
  | some code, [target] =>
      { outcome := .success [{ node := target, fact, payload := label }] [] {}
        drafts := [{ label, role := .fact, schema := 1, body := [code] }] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def constantPlan (request : RuleRequest Bound) : Plan Bound :=
  factPlan piFact (payload 10) request

def reductionPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs with
  | [_source, pi] =>
      if pi.fact == piFact then factPlan residualFact (payload 11) request
      else { outcome := .noChange {}, drafts := [] }
  | _ => { outcome := .failed 2, drafts := [] }

def localPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs with
  | [input] =>
      if input.fact == residualFact then factPlan positiveFact (payload 12) request
      else { outcome := .noChange {}, drafts := [] }
  | _ => { outcome := .failed 3, drafts := [] }

def negationPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs with
  | [input] =>
      if input.fact == positiveFact then factPlan negativeFact (payload 13) request
      else { outcome := .noChange {}, drafts := [] }
  | _ => { outcome := .failed 4, drafts := [] }

def identityPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs with
  | [input] =>
      if input.node != node 3 || input.fact != residualFact then
        { outcome := .noChange {}, drafts := [] }
      else
        match request.program.findOp? sineKey, request.program.findOp? negationKey,
            request.program.findOp? residualKey, request.program.findOp? piKey,
            request.program.node? (node 1), request.program.node? (node 2),
            request.program.node? (node 3), request.program.node? (node 4) with
        | some (sineId, _), some (negationId, _), some (residualId, _), some (piId, _),
            some target, some pi, some residual, some localSine =>
            if target != { domain := real, op := sineId, args := [node 0] } ||
                pi != { domain := real, op := piId, args := [] } ||
                residual !=
                  { domain := real, op := residualId, args := [node 0, node 2] } ||
                localSine != { domain := real, op := sineId, args := [node 3] } then
              { outcome := .noChange {}, drafts := [] }
            else
              let proposal : InstantiationRequest :=
                { key := 1
                  nodes :=
                    [{ domain := real, op := negationId, args := [.existing (node 4)] }]
                  equalities :=
                    [{ left := .existing (node 1)
                       right := .proposed 0
                       payload := payload 15 }]
                  payload := payload 14 }
              { outcome := .success [] [.instantiate proposal] {}
                drafts :=
                  [{ label := payload 14, role := .instance, schema := 1, body := [1] },
                   { label := payload 15, role := .equality, schema := 1, body := [1] }] }
        | _, _, _, _, _, _, _, _ => { outcome := .noChange {}, drafts := [] }
  | _ => { outcome := .failed 5, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }
def constantPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[piOperation],
    handlers := #[Handler.statelessPlanned constantRule constantPlan #[factFormat]] }
def reductionPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[residualOperation],
    requiredOperations := #[sineOperation, negationOperation],
    handlers := #[Handler.statelessPlanned reductionRule reductionPlan #[factFormat],
      Handler.statelessPlanned identityRule identityPlan #[instanceFormat, equalityFormat]] }
def localPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sineOperation],
    handlers := #[Handler.statelessPlanned localRule localPlan #[factFormat]] }
def negationPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[negationOperation],
    handlers := #[Handler.statelessPlanned negationRule negationPlan #[factFormat]] }

def packages : Array (Package Bound) :=
  #[sourcePackage, localPackage, constantPackage, reductionPackage, negationPackage]

def engineLimits : Propagator.Limits :=
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
  { maxEntries := 24, maxBodyCells := 48, maxDrafts := 12,
    maxDraftCells := 12, maxAtom := 32, maxSchema := 1, maxUses := 12 }
def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.SinTenInterval

end
