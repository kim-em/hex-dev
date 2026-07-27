/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Policy

/-!
Conformance canaries for engine-owned policy offers.

The fixture uses opaque `f` and `g` operations over a synthetic rank domain.
It checks two deliberately different valid schedules, exact observations, and
revalidation of selections at the engine boundary.  No policy test depends on
arithmetic semantics.
-/

namespace Hex.Interval.PolicyConformance

open Experiment.Propagator
open Experiment.Propagator.Policy

abbrev Rank := Nat

/-- Larger ranks are strictly stronger synthetic facts. -/
def rankDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def real : DomainId := { index := 0 }

def sourceOp : OpKey := { name := "policy.source" }
def fOp : OpKey := { name := "policy.f" }
def gOp : OpKey := { name := "policy.g" }

def fKey : RuleKey := { name := "policy.f.contract" }
def gKey : RuleKey := { name := "policy.g.contract" }

def node (index : Nat) : NodeId := { index }
def application (index : Nat) : ApplicationId := { index }
def equality (index : Nat) : EqualityId := { index }
def suggestion (index : Nat) : SuggestionId := { index }

def sourceNode : Node := { domain := real, op := { index := 0 }, args := [] }

def unaryNode (op : Nat) (input : Nat) : Node :=
  { domain := real, op := { index := op }, args := [node input] }

def operations : Array Operation :=
  #[{ key := sourceOp, inputs := [], output := real },
    { key := fOp, inputs := [real], output := real },
    { key := gOp, inputs := [real], output := real }]

def program : Program :=
  { operations, nodes := #[sourceNode, unaryNode 1 0] }

def fRule : Registration :=
  { key := fKey
    head := fOp
    kind := .improve
    watches := [.argument 0]
    writes := [.result] }

def gRule : Registration :=
  { key := gKey
    head := gOp
    kind := .improve
    watches := [.argument 0]
    writes := [.result] }

def engineLimits : Experiment.Propagator.Limits :=
  { maxOperations := 8
    maxNodes := 8
    maxRules := 8
    maxArity := 4
    maxApplications := 16
    maxQueueEntries := 64
    maxActions := 32
    maxAcceptedFacts := 32
    maxRetainedSuggestions := 16
    maxEffort := 4
    maxObservationValue := 64
    maxOutcomeCandidates := 8
    maxOutcomeSuggestions := 8
    maxProposalItems := 8
    maxInstances := 8
    maxGeneration := 4
    maxEqualities := 8
    splitEndpointLimit :=
      { maxEndpointHeight := 32, maxAlignmentShift := 16 } }

def policyLimits : Experiment.Propagator.Policy.Limits :=
  { maxDecisions := 32
    maxTraversal := 512
    maxLiveOffers := 32 }

def initialWith? (limits : Experiment.Propagator.Policy.Limits) : Option (State Rank) := do
  let engine <- match Engine.start rankDomain program #[fRule, gRule] #[0, 0] engineLimits with
    | .ok engine => some engine
    | .error _ => none
  some (State.start engine limits)

def initial? : Option (State Rank) := initialWith? policyLimits

def selectOffer (state : State Rank) (id : OfferId) : SelectResult Rank :=
  match state.offer? id with
  | none => state.reject .missingOffer
  | some offer =>
      state.select
        { scope := state.scope
          serial := state.serial
          programVersion := state.engine.programVersion
          id
          expected := offer.key }

def candidate (request : RuleRequest Rank) (rank : Rank) : Candidate Rank :=
  { node := request.action.node
    fact := rank
    payload := { index := request.action.serial } }

def proposedG : ProposedNode :=
  { domain := real, op := { index := 2 }, args := [.existing (node 0)] }

def instantiateG (request : RuleRequest Rank) : InstantiationRequest :=
  { key := 31
    triggers := [request.action.node]
    claimedGeneration := 1
    nodes := [proposedG]
    equalities :=
      [{ left := .existing request.action.node
         right := .proposed 0
         payload := { index := 37 } }]
    payload := { index := 41 } }

def fSuggestions (request : RuleRequest Rank) : List Suggestion :=
  [.retry 1,
    .instantiate (instantiateG request),
    .split { node := node 0, point := 0, reason := .midpoint }]

def invoke (request : RuleRequest Rank) : Outcome Rank :=
  if request.action.key == fKey then
    if request.action.effort == 0 then
      .success [candidate request 1] (fSuggestions request)
        { arithmeticWork := 3, visitedEntries := 5, estimatedProofNodes := 7 }
    else
      .success [candidate request 4] []
        { arithmeticWork := 11, visitedEntries := 13, estimatedProofNodes := 17 }
  else if request.action.key == gKey then
    .success [candidate request 4] []
      { arithmeticWork := 19, visitedEntries := 23, estimatedProofNodes := 29 }
  else
    .failed 43

def submitInvoke (state : State Rank) (request : RuleRequest Rank) : SubmitResult Rank :=
  state.submit (request.action.reply (invoke request))

def request? (state : State Rank) (id : OfferId) :
    Option (RuleRequest Rank × State Rank) :=
  match selectOffer state id with
  | .request request next => some (request, next)
  | _ => none

def submit? (state : State Rank) (request : RuleRequest Rank) :
    Option (RuleObservation Rank × State Rank) :=
  match submitInvoke state request with
  | .accepted observation next => some (observation, next)
  | _ => none

def instantiate? (state : State Rank) (id : SuggestionId) : Option (State Rank) :=
  match selectOffer state (.suggestion id) with
  | .completed (.instanceAdmitted [fresh]) next =>
      if fresh == node 2 then some next else none
  | _ => none

def contract? (state : State Rank) (id : EqualityId) :
    Option (EqualityObservation Rank × State Rank) :=
  match selectOffer state (.equality id) with
  | .equality observation next => some (observation, next)
  | _ => none

def split? (state : State Rank) (id : SuggestionId) :
    Option (SplitPlan Rank × State Rank) :=
  match selectOffer state (.suggestion id) with
  | .split plan next => some (plan, next)
  | _ => none

def oneChange (changes : Array (FactDelta Rank)) (changed : NodeId)
    (before after beforeVersion afterVersion : Nat) : Bool :=
  match changes.toList with
  | [delta] =>
      delta.node == changed && delta.before == before && delta.after == after &&
        delta.beforeVersion == beforeVersion && delta.afterVersion == afterVersion
  | _ => false

def noChanges (changes : Array (FactDelta Rank)) : Bool := changes.isEmpty

def exactCost (cost : CostObservation) (arithmetic visited proof : Nat) : Bool :=
  cost.arithmeticWork == arithmetic && cost.visitedEntries == visited &&
    cost.estimatedProofNodes == proof

def exactInitialObservation (observation : RuleObservation Rank) : Bool :=
  observation.invocation.rule == fKey && observation.invocation.effort == 0 &&
    observation.invocation.inputs == [{ node := node 0, version := 0 }] &&
    observation.outcome == .success && oneChange observation.changes (node 1) 0 1 0 1 &&
    !observation.contradiction && exactCost observation.cost 3 5 7 &&
    observation.emittedSuggestions.toList ==
      [.suggestion (suggestion 0), .suggestion (suggestion 1), .suggestion (suggestion 2)]

def exactRetryObservation (observation : RuleObservation Rank) (changed : Bool) : Bool :=
  observation.invocation.rule == fKey && observation.invocation.effort == 1 &&
    observation.outcome == .success &&
    (if changed then oneChange observation.changes (node 1) 1 4 1 2
      else noChanges observation.changes) &&
    !observation.contradiction && exactCost observation.cost 11 13 17 &&
    observation.emittedSuggestions.isEmpty

def exactGObservation (observation : RuleObservation Rank) (before : Nat) : Bool :=
  observation.invocation.rule == gKey && observation.invocation.effort == 0 &&
    observation.outcome == .success &&
    (if before < 4 then oneChange observation.changes (node 2) before 4
        (if before == 0 then 0 else 1) (if before == 0 then 1 else 2)
      else noChanges observation.changes) &&
    !observation.contradiction && exactCost observation.cost 19 23 29 &&
    observation.emittedSuggestions.isEmpty

def exactEqualityObservation (observation : EqualityObservation Rank)
    (outcome : EqualityOutcome) (changed : Option (NodeId × Nat × Nat × Nat × Nat)) : Bool :=
  observation.key.equality == equality 0 && observation.outcome == outcome &&
    observation.narrowCalls == 2 &&
    match changed with
    | none => noChanges observation.changes
    | some (changed, before, after, beforeVersion, afterVersion) =>
        oneChange observation.changes changed before after beforeVersion afterVersion

def exactSplit (plan : SplitPlan Rank) : Bool :=
  plan.scope == { index := 0 } && plan.suggestion == suggestion 2 &&
    plan.origin.key == fKey && plan.origin.effort == 0 &&
    plan.node == node 0 && plan.version == 0 &&
    plan.fact == 0 && plan.point == 0 && plan.reason == .midpoint &&
    plan.source.rule == fKey && plan.source.effort == 0 &&
    plan.source.inputs == [{ node := node 0, version := 0 }]

structure ScheduleResult where
  state : State Rank
  calls : List (String × Nat)
  observationsExact : Bool

/-! ## Retry-first schedule -/

def retryFirst? : Option ScheduleResult := do
  let state <- initial?
  let (f0Request, state) <- request? state (.application (application 0))
  let (f0Observation, state) <- submit? state f0Request
  let (retryRequest, state) <- request? state (.suggestion (suggestion 0))
  let (retryObservation, state) <- submit? state retryRequest
  let state <- instantiate? state (suggestion 1)
  let (firstEquality, state) <- contract? state (equality 0)
  let (gRequest, state) <- request? state (.application (application 1))
  let (gObservation, state) <- submit? state gRequest
  let (lastEquality, state) <- contract? state (equality 0)
  let (splitPlan, state) <- split? state (suggestion 2)
  some
    { state
      calls :=
        [(f0Request.action.key.name, f0Request.action.effort),
          (retryRequest.action.key.name, retryRequest.action.effort),
          (gRequest.action.key.name, gRequest.action.effort)]
      observationsExact :=
        exactInitialObservation f0Observation &&
          exactRetryObservation retryObservation true &&
          exactEqualityObservation firstEquality .improved
            (some (node 2, 0, 4, 0, 1)) &&
          exactGObservation gObservation 4 &&
          exactEqualityObservation lastEquality .noChange none &&
          exactSplit splitPlan }

#guard
  match retryFirst? with
  | some result =>
      result.state.engine.facts.toList == [0, 4, 4] &&
        result.calls == [(fKey.name, 0), (fKey.name, 1), (gKey.name, 0)] &&
        result.observationsExact && result.state.engine.pending.isNone &&
        result.state.engine.metrics.requests == 3 &&
        result.state.engine.metrics.improvements == 3 &&
        result.state.engine.metrics.equalityRuns == 2 &&
        result.state.engine.metrics.equalityImprovements == 1 &&
        result.state.engine.metrics.admittedInstances == 1 &&
        result.state.metrics.decisions == 7 &&
        result.state.metrics.selectedInvocations == 2 &&
        result.state.metrics.selectedRetries == 1 &&
        result.state.metrics.selectedInstances == 1 &&
        result.state.metrics.selectedEqualities == 2 &&
        result.state.metrics.selectedSplits == 1 &&
        (result.state.offers).toOption.any (fun pair => pair.1.isEmpty)
  | none => false

/-! ## Instantiation-first schedule -/

def instantiateFirst? : Option ScheduleResult := do
  let state <- initial?
  let (f0Request, state) <- request? state (.application (application 0))
  let (f0Observation, state) <- submit? state f0Request
  let state <- instantiate? state (suggestion 1)
  let (gRequest, state) <- request? state (.application (application 1))
  let (gObservation, state) <- submit? state gRequest
  let (firstEquality, state) <- contract? state (equality 0)
  let (lastEquality, state) <- contract? state (equality 0)
  let retryOffer <- state.offer? (.suggestion (suggestion 0))
  let state <- match state.dismiss
      { scope := state.scope
        serial := state.serial
        programVersion := state.engine.programVersion
        id := .suggestion (suggestion 0)
        expected := retryOffer.key } with
    | .completed .dismissed next => some next
    | _ => none
  let (splitPlan, state) <- split? state (suggestion 2)
  some
    { state
      calls :=
        [(f0Request.action.key.name, f0Request.action.effort),
          (gRequest.action.key.name, gRequest.action.effort)]
      observationsExact :=
        exactInitialObservation f0Observation &&
          exactGObservation gObservation 0 &&
          exactEqualityObservation firstEquality .improved
            (some (node 1, 1, 4, 1, 2)) &&
          exactEqualityObservation lastEquality .noChange none &&
          exactSplit splitPlan }

#guard
  match instantiateFirst? with
  | some result =>
      result.state.engine.facts.toList == [0, 4, 4] &&
        result.calls == [(fKey.name, 0), (gKey.name, 0)] &&
        result.observationsExact && result.state.engine.pending.isNone &&
        result.state.engine.metrics.requests == 2 &&
        result.state.engine.metrics.improvements == 3 &&
        result.state.engine.metrics.equalityRuns == 2 &&
        result.state.engine.metrics.equalityImprovements == 1 &&
        result.state.metrics.decisions == 7 &&
        result.state.metrics.selectedInvocations == 2 &&
        result.state.metrics.selectedRetries == 0 &&
        result.state.metrics.selectedInstances == 1 &&
        result.state.metrics.selectedEqualities == 2 &&
        result.state.metrics.selectedSplits == 1 &&
        result.state.metrics.dismissals == 1 &&
        (result.state.offers).toOption.any (fun pair => pair.1.isEmpty)
  | none => false

/-! ## Boundary revalidation and policy resources -/

def afterInitial? : Option (State Rank) := do
  let state <- initial?
  let (request, state) <- request? state (.application (application 0))
  let (_, state) <- submit? state request
  some state

-- A policy cannot turn an engine-advertised effort-one retry into effort two.
#guard
  match afterInitial? with
  | none => false
  | some state =>
      match state.offer? (.suggestion (suggestion 0)) with
      | some { key := .retry source 1, .. } =>
          let fabricated : Selection :=
            { scope := state.scope
              serial := state.serial
              programVersion := state.engine.programVersion
              id := .suggestion (suggestion 0)
              expected := .retry source 2 }
          match state.select fabricated with
          | .rejected .wrongKey next =>
              next.metrics.decisions == state.metrics.decisions + 1 &&
                next.metrics.rejected == state.metrics.rejected + 1 &&
                (next.offer? (.suggestion (suggestion 0))).isSome
          | _ => false
      | _ => false

def staleEqualityResult? : Option (SelectResult Rank) := do
  let state <- afterInitial?
  let state <- instantiate? state (suggestion 1)
  let oldOffer <- state.offer? (.equality (equality 0))
  let (gRequest, state) <- request? state (.application (application 1))
  let (_, state) <- submit? state gRequest
  some <| state.select
    { scope := state.scope
      serial := state.serial
      programVersion := state.engine.programVersion
      id := .equality (equality 0)
      expected := oldOffer.key }

-- A still-dirty equality is rejected when either endpoint version has moved.
#guard
  match staleEqualityResult? with
  | some (.rejected .wrongKey state) =>
      state.metrics.rejected == 1 && state.engine.equalityQueued[0]? == some true
  | _ => false

def oneDecisionState? : Option (State Rank) :=
  initialWith? { policyLimits with maxDecisions := 1 }

-- The decision budget is independent of the engine action budget and does not
-- charge a rejected over-budget selection a second time.
#guard
  match oneDecisionState? with
  | none => false
  | some state =>
      match request? state (.application (application 0)) with
      | none => false
      | some (request, selected) =>
          match submit? selected request with
          | none => false
          | some (_, submitted) =>
              match selectOffer submitted (.suggestion (suggestion 0)) with
              | .rejected .decisionLimit rejected =>
                  rejected.metrics.decisions == 1 && rejected.metrics.rejected == 0 &&
                    match rejected.view with
                    | .error .decisionLimit => true
                    | _ => false
              | _ => false

end Hex.Interval.PolicyConformance
