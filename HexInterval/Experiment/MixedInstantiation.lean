/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.MixedFunctions
public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# A mixed-function instantiation canary

This experiment starts from `exp (sin (-x))`. Direct sine propagation is
disabled when the sine input is a negation node. A structural matcher instead
adds `sin x` and `-(sin x)`, then records the oddness equality. Independent
sine and negation propagators establish the shared unit-range fact, equality
transport returns it to `sin (-x)`, and exponential propagation consumes it.
-/

namespace Hex.Interval.Experiment.MixedInstantiation

open Propagator PayloadArena

abbrev Bound := MixedFunctions.Bound

def factDomain : FactDomain Bound := MixedFunctions.factDomain

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "mixed-instantiation.source" }
def negationKey : OpKey := { name := "mixed-instantiation.negation" }
def sineKey : OpKey := { name := "mixed-instantiation.sine" }
def expKey : OpKey := { name := "mixed-instantiation.exp" }

def negationRuleKey : RuleKey := { name := "mixed-instantiation.negation.unit" }
def sineRuleKey : RuleKey := { name := "mixed-instantiation.sine.unit" }
def oddnessRuleKey : RuleKey := { name := "mixed-instantiation.sine.oddness" }
def expRuleKey : RuleKey := { name := "mixed-instantiation.exp.at-most-three" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def negationOperation : Operation :=
  { key := negationKey, inputs := [real], output := real }

def sineOperation : Operation :=
  { key := sineKey, inputs := [real], output := real }

def expOperation : Operation :=
  { key := expKey, inputs := [real], output := real }

def operations : Array Operation :=
  #[sourceOperation, negationOperation, sineOperation, expOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }

def negatedSourceInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

def sineNegatedSourceInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 1] }

def expSineInstruction : Node :=
  { domain := real, op := { index := 3 }, args := [node 2] }

def baseProgram : Program :=
  { operations
    nodes :=
      #[sourceInstruction, negatedSourceInstruction,
        sineNegatedSourceInstruction, expSineInstruction] }

/-- The caller-visible graph and target before structural instantiation. -/
def checkerInput : SemanticReplay.CheckerInput Bound :=
  { baseProgram
    initialFacts := #[.all, .all, .all, .all]
    target := { node := node 3, fact := .atMostThree } }

def sineSourceInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 0] }

def negatedSineInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 4] }

def extendedProgram : Program :=
  { operations
    nodes := baseProgram.nodes ++ #[sineSourceInstruction, negatedSineInstruction] }

def negationRule : Registration :=
  { key := negationRuleKey
    head := negationKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def sineRule : Registration :=
  { key := sineRuleKey
    head := sineKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def oddnessRule : Registration :=
  { key := oddnessRuleKey
    head := sineKey
    kind := .instantiate
    watches := []
    writes := []
    binding := .global
    watchesProgram := true
    matchWatch := .network }

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
      | [code] => (MixedFunctions.Bound.ofCode? code).isSome
      | _ => false }

def instanceFormat : ReplayFormat :=
  { role := .instance
    schema := 1
    validateBody := fun body => body == [1] }

def equalityFormat : ReplayFormat :=
  { role := .equality
    schema := 1
    validateBody := fun body => body == [1] }

def factPlan (fact : Bound) (label : PayloadId)
    (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [_], [target] =>
      { outcome :=
          .success [{ node := target, fact, payload := label }] [] {}
        drafts :=
          [{ label, role := .fact, schema := 1,
             body := [MixedFunctions.Bound.code fact] }] }
  | _, _ => { outcome := .failed 1, drafts := [] }

/-- Unit range is preserved by negation. -/
def negationPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs with
  | [input] =>
      if input.fact == .unit then factPlan .unit (payload 20) request
      else { outcome := .noChange {}, drafts := [] }
  | _ => { outcome := .failed 2, drafts := [] }

/-- Sine proves its unit range except at the deliberately blocked `sin (-_)`
shape. The matcher must expose the equivalent positive-shape expression. -/
def sinePlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs with
  | [input] =>
      if request.program.operationKey? input.node == some negationKey then
        { outcome := .noChange {}, drafts := [] }
      else
        factPlan .unit (payload 21) request
  | _ => { outcome := .failed 3, drafts := [] }

def expPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs with
  | [input] =>
      if input.fact == .unit then factPlan .atMostThree (payload 24) request
      else { outcome := .noChange {}, drafts := [] }
  | _ => { outcome := .failed 4, drafts := [] }

def oddness? (view : ProgramView) (input : StructuralInput) :
    Option InstantiationRequest := do
  let .node anchor := input.key | none
  if view.operationKey? anchor != some sineKey then none else pure ()
  let expression ← view.node? anchor
  let [negated] := expression.args | none
  if view.operationKey? negated != some negationKey then none else pure ()
  let negation ← view.node? negated
  let [argument] := negation.args | none
  let (sineId, _) ← view.findOp? sineKey
  let (negationId, _) ← view.findOp? negationKey
  pure
    { key := 1
      nodes :=
        [{ domain := real, op := sineId, args := [.existing argument] },
          { domain := real, op := negationId, args := [.proposed 0] }]
      equalities :=
        [{ left := .existing anchor
           right := .proposed 1
           payload := payload 23 }]
      payload := payload 22 }

def oddnessPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.action.structuralInputs.findSome? (oddness? request.program) with
  | none => { outcome := .noChange {}, drafts := [] }
  | some proposal =>
      { outcome := .success [] [.instantiate proposal] {}
        drafts :=
          [{ label := payload 22, role := .instance, schema := 1, body := [1] },
           { label := payload 23, role := .equality, schema := 1, body := [1] }] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }

def negationPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[negationOperation]
    handlers := #[Handler.statelessPlanned negationRule negationPlan #[factFormat]] }

def sinePackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[sineOperation]
    requiredOperations := #[negationOperation]
    handlers :=
      #[Handler.statelessPlanned sineRule sinePlan #[factFormat],
        Handler.statelessPlanned oddnessRule oddnessPlan
          #[instanceFormat, equalityFormat]] }

def expPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[expOperation]
    handlers := #[Handler.statelessPlanned expRule expPlan #[factFormat]] }

def packages : Array (Package Bound) :=
  #[sourcePackage, negationPackage, sinePackage, expPackage]

def engineLimits : Propagator.Limits :=
  { maxOperations := 4
    maxNodes := 6
    maxRules := 4
    maxRegistryEntries := 20
    maxReplayFormats := 6
    maxArity := 1
    maxScopeNodes := 1
    maxApplications := 10
    maxQueueEntries := 32
    maxActions := 24
    maxMatcherVisits := 16
    matcherBatchSize := 8
    maxAcceptedFacts := 12
    maxRetainedSuggestions := 2
    maxEffort := 1
    maxObservationValue := 20
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
  { maxDecisions := 32, maxTraversal := 384, maxLiveOffers := 32 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 20
    maxBodyCells := 40
    maxDrafts := 10
    maxDraftCells := 10
    maxAtom := 32
    maxSchema := 1
    maxUses := 10 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.MixedInstantiation
