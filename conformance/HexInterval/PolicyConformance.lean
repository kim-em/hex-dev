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

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 8
    maxNodes := 8
    maxRules := 8
    maxRegistryEntries := 24
    maxReplayFormats := 0
    maxArity := 4
    maxApplications := 16
    maxQueueEntries := 64
    maxActions := 32
    maxAcceptedFacts := 32
    maxRetainedSuggestions := 16
    maxEffort := 4
    maxObservationValue := 64
    maxDiagnosticValue := 128
    maxOutcomeCandidates := 8
    maxOutcomeSuggestions := 8
    maxProposalItems := 8
    maxInstances := 8
    maxGeneration := 4
    maxNodeDepth := 16
    maxEqualities := 8
    splitEndpointLimit :=
      { maxEndpointHeight := 32, maxAlignmentShift := 16 } }

def policyLimits : Experiment.Propagator.Policy.Limits :=
  { maxDecisions := 32
    maxTraversal := 512
    maxLiveOffers := 32 }

def initialWithLimits? (engineLimit : Hex.Interval.State.Limits)
    (policyLimit : Experiment.Propagator.Policy.Limits) : Option (State Rank) := do
  let engine <- match Engine.start rankDomain program #[fRule, gRule] #[0, 0] engineLimit with
    | .ok engine => some engine
    | .error _ => none
  some (State.start engine policyLimit)

def initialWith? (limits : Experiment.Propagator.Policy.Limits) : Option (State Rank) :=
  initialWithLimits? engineLimits limits

def initial? : Option (State Rank) := initialWith? policyLimits

def pendingAdoption? : Option (State Rank) := do
  let engine <- match Engine.start rankDomain program #[fRule, gRule] #[0, 0]
      engineLimits with
    | .ok engine => some engine
    | .error _ => none
  match engine.poll with
  | .request _ awaiting => some (State.start awaiting policyLimits)
  | .equality _ _ | .awaitingReply _ | .saturated _ | .contradiction _
  | .resourceLimit _ _ | .invalidState _ => none

def selectOffer (state : State Rank) (id : OfferId) : SelectResult Rank :=
  match state.offer? id with
  | none => .rejected .missingOffer state
  | some offer =>
      state.select
        { scope := state.scope
          serial := state.serial
          programVersion := state.engine.programVersion
          id
          expected := offer.key }

def dismissOffer (state : State Rank) (id : OfferId) : Option (State Rank) := do
  let offer <- state.offer? id
  match state.dismiss
      { scope := state.scope
        serial := state.serial
        programVersion := state.engine.programVersion
        id
        expected := offer.key } with
  | .completed .dismissed next => some next
  | _ => none

def candidate (request : RuleRequest Rank) (rank : Rank) : Candidate Rank :=
  { node := request.action.node
    fact := rank
    payload := { index := request.action.serial } }

def proposedG : ProposedNode :=
  { domain := real, op := { index := 2 }, args := [.existing (node 0)] }

def instantiateG (request : RuleRequest Rank) : InstantiationRequest :=
  { key := 31
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
    observation.suggestionPlan.kept.length == 3 &&
    observation.suggestionPlan.dropped.isEmpty &&
    observation.emittedSuggestions.toList ==
      [.suggestion (suggestion 0), .suggestion (suggestion 1), .suggestion (suggestion 2)]

def exactRetryObservation (observation : RuleObservation Rank) (changed : Bool) : Bool :=
  observation.invocation.rule == fKey && observation.invocation.effort == 1 &&
    observation.outcome == .success &&
    (if changed then oneChange observation.changes (node 1) 1 4 1 2
      else noChanges observation.changes) &&
    !observation.contradiction && exactCost observation.cost 11 13 17 &&
    observation.suggestionPlan.kept.isEmpty &&
    observation.suggestionPlan.dropped.isEmpty &&
    observation.emittedSuggestions.isEmpty

def exactGObservation (observation : RuleObservation Rank) (before : Nat) : Bool :=
  observation.invocation.rule == gKey && observation.invocation.effort == 0 &&
    observation.outcome == .success &&
    (if before < 4 then oneChange observation.changes (node 2) before 4
        (if before == 0 then 0 else 1) (if before == 0 then 1 else 2)
      else noChanges observation.changes) &&
    !observation.contradiction && exactCost observation.cost 19 23 29 &&
    observation.suggestionPlan.kept.isEmpty &&
    observation.suggestionPlan.dropped.isEmpty &&
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

/-! # Retry-first schedule -/

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
        result.state.epoch == result.state.metrics.decisions &&
        (result.state.view).toOption.any (fun pair => pair.1.offers.isEmpty)
  | none => false

/-! # Instantiation-first schedule -/

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
        result.state.epoch == result.state.metrics.decisions &&
        (result.state.view).toOption.any (fun pair => pair.1.offers.isEmpty)
  | none => false

/-! # Boundary revalidation and policy resources -/

def afterInitial? : Option (State Rank) := do
  let state <- initial?
  let (request, state) <- request? state (.application (application 0))
  let (_, state) <- submit? state request
  some state

def afterReplyWith? (engineLimit : Hex.Interval.State.Limits)
    (reply : RuleRequest Rank -> Outcome Rank) : Option (State Rank) := do
  let state <- initialWithLimits? engineLimit policyLimits
  let (request, state) <- request? state (.application (application 0))
  match state.submit (request.action.reply (reply request)) with
  | .accepted _ next => some next
  | _ => none

def observedWith? (engineLimit : Hex.Interval.State.Limits)
    (reply : RuleRequest Rank -> Outcome Rank) :
    Option (RuleObservation Rank × State Rank) := do
  let state <- initialWithLimits? engineLimit policyLimits
  let (request, state) <- request? state (.application (application 0))
  match state.submit (request.action.reply (reply request)) with
  | .accepted observation next => some (observation, next)
  | _ => none

def afterInitialWith? (engineLimit : Hex.Interval.State.Limits) : Option (State Rank) :=
  afterReplyWith? engineLimit invoke

-- Adopting a snapshot with an open reply latch cannot reconstruct the selected
-- application as a fresh offer. It therefore records incompleteness before an
-- empty frontier could be mistaken for a fixed point.
#guard
  match pendingAdoption? with
  | some state =>
      state.incomplete && state.engine.pending.isSome &&
        (state.view).toOption.any fun pair =>
          pair.1.offers.isEmpty && pair.1.incomplete
  | none => false

-- A structurally invalid reply clears the pending latch and consumes the
-- selected application.  The wrapper must remember that the resulting empty
-- frontier is incomplete.
#guard
  match initial? with
  | none => false
  | some state =>
      match request? state (.application (application 0)) with
      | none => false
      | some (request, awaiting) =>
          match awaiting.submit (request.action.reply
              (.success [] [.retry (engineLimits.maxEffort + 1)] {})) with
          | .invalid .oversizedEffort next =>
              next.incomplete && next.engine.pending.isNone &&
                (next.view).toOption.any fun pair =>
                  pair.1.offers.isEmpty && pair.1.incomplete
          | _ => false

-- Retry selection follows a different dirty-bit path from an initial
-- invocation. A rejected retry reply still clears its pending latch and is
-- therefore completeness-relevant.
#guard
  match afterInitial? with
  | none => false
  | some state =>
      match request? state (.suggestion (suggestion 0)) with
      | none => false
      | some (request, awaiting) =>
          match awaiting.submit (request.action.reply
              (.success [] [.retry (engineLimits.maxEffort + 1)] {})) with
          | .invalid .oversizedEffort next =>
              next.incomplete && next.engine.pending.isNone
          | _ => false

-- A mismatched action leaves the exact pending request intact.  Correcting
-- and resubmitting it remains complete, so the retryable mismatch must not
-- poison the state.
#guard
  match initial? with
  | none => false
  | some state =>
      match request? state (.application (application 0)) with
      | none => false
      | some (request, awaiting) =>
          let mismatched : Reply Rank :=
            { serial := request.action.serial + 1
              programVersion := request.action.programVersion
              application := request.action.application
              outcome := .inapplicable }
          match awaiting.submit mismatched with
          | .invalid .mismatchedAction retryable =>
              !retryable.incomplete && retryable.engine.pending.isSome &&
                match retryable.submit (request.action.reply (invoke request)) with
                | .accepted observation resumed =>
                    exactInitialObservation observation && !resumed.incomplete &&
                      resumed.engine.pending.isNone
                | _ => false
          | _ => false

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
                next.epoch == next.metrics.decisions &&
                match next.offer? (.suggestion (suggestion 0)) with
                | some retry => retry.age == 1
                | none => false
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
-- charge a rejected over-budget selection a second time.  A post-decision
-- view remains available under its separate traversal budget, so a driver can
-- distinguish saturation from live work it no longer has permission to run.
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
                    | .ok (view, _) => !view.offers.isEmpty
                    | _ => false
              | _ => false

/-! # Resource preservation and exact equality observations -/

def retainedEngineWith? (limits : Hex.Interval.State.Limits) : Option (Engine Rank) := do
  let engine <- match Engine.start rankDomain program #[fRule, gRule] #[0, 0] limits with
    | .ok engine => some engine
    | .error _ => none
  match engine.poll with
  | .request request awaiting =>
      match awaiting.submit (request.action.reply (invoke request)) with
      | .accepted _ next => some next
      | _ => none
  | _ => none

def equalityReadyWith? (limits : Hex.Interval.State.Limits)
    (domain : FactDomain Rank) : Option (State Rank) := do
  let engine <- retainedEngineWith? limits
  let state := State.start { engine with factDomain := domain } policyLimits
  instantiate? state (suggestion 1)

def rightResourceDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .resourceLimit 77 else .noChange

def leftMalformedDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if candidate < current then .malformed 91 else .noChange

-- An engine resource failure during reply admission rolls back candidate
-- effects, but the selected application is no longer live.
#guard
  match initialWithLimits?
      { engineLimits with maxAcceptedFacts := 0 } policyLimits with
  | none => false
  | some state =>
      match request? state (.application (application 0)) with
      | none => false
      | some (request, awaiting) =>
          match awaiting.submit (request.action.reply (invoke request)) with
          | .engineResource .acceptedFacts next =>
              next.incomplete && next.engine.pending.isNone &&
                next.engine.history.isEmpty &&
                (next.view).toOption.any fun pair =>
                  pair.1.offers.isEmpty && pair.1.incomplete
          | _ => false

-- A fact-domain resource failure has the same consumed-obligation boundary
-- while retaining its exact domain budget.
#guard
  match Engine.start rightResourceDomain program #[fRule, gRule] #[0, 0]
      engineLimits with
  | .error _ => false
  | .ok engine =>
      let state := State.start engine policyLimits
      match request? state (.application (application 0)) with
      | none => false
      | some (request, awaiting) =>
          match awaiting.submit (request.action.reply (invoke request)) with
          | .factResource 77 next =>
              next.incomplete && next.engine.pending.isNone &&
                next.engine.history.isEmpty &&
                (next.view).toOption.any fun pair =>
                  pair.1.offers.isEmpty && pair.1.incomplete
          | _ => false

-- Exhausting the accepted-fact budget reports a typed equality observation,
-- charges no engine action, and leaves the equality live for a later run.
#guard
  match equalityReadyWith? { engineLimits with maxAcceptedFacts := 1 } rankDomain with
  | none => false
  | some state =>
      let beforePops := state.engine.metrics.queuePops
      let beforeRuns := state.engine.metrics.equalityRuns
      match selectOffer state (.equality (equality 0)) with
      | .equality observation next =>
          observation.outcome == .engineResource .acceptedFacts &&
            observation.narrowCalls == 2 && observation.changes.isEmpty &&
            next.engine.metrics.queuePops == beforePops &&
            next.engine.metrics.equalityRuns == beforeRuns &&
            next.engine.equalityQueued[0]? == some true &&
            (next.offer? (.equality (equality 0))).isSome
      | _ => false

-- A fact-domain resource stop after the second endpoint call is likewise
-- observed exactly and does not destroy the live contractor.
#guard
  match equalityReadyWith? engineLimits rightResourceDomain with
  | none => false
  | some state =>
      match selectOffer state (.equality (equality 0)) with
      | .equality observation next =>
          observation.outcome == .factResource 77 && observation.narrowCalls == 2 &&
            observation.changes.isEmpty && next.engine.equalityQueued[0]? == some true &&
            (next.offer? (.equality (equality 0))).isSome
      | _ => false

-- Malformation on the first endpoint records one actual call rather than a
-- fabricated zero or two.
#guard
  match equalityReadyWith? engineLimits leftMalformedDomain with
  | none => false
  | some state =>
      match selectOffer state (.equality (equality 0)) with
      | .equality observation next =>
          observation.outcome == .invalid (.malformedFact 91) &&
            observation.narrowCalls == 1 && observation.changes.isEmpty &&
            next.engine.equalityQueued[0]? == some true
      | _ => false

/-! # Proposal lifetime and program extension -/

def proposedGAt (input : NodeId) : ProposedNode :=
  { domain := real, op := { index := 2 }, args := [.existing input] }

def instantiateAt (family : Nat) (input : NodeId) : InstantiationRequest :=
  { key := family
    nodes := [proposedGAt input]
    equalities := []
    payload := { index := family } }

def twoInstances (request : RuleRequest Rank) : Outcome Rank :=
  .success [candidate request 1]
    [.instantiate (instantiateAt 101 (node 0)),
      .instantiate (instantiateAt 102 (node 1))]
    {}

def twoInstancesFinal? : Option (State Rank) := do
  let state <- afterReplyWith? engineLimits twoInstances
  let first <- match selectOffer state (.suggestion (suggestion 0)) with
    | .completed (.instanceAdmitted [fresh]) next =>
        if fresh == node 2 then some next else none
    | _ => none
  let secondOffer <- first.offer? (.suggestion (suggestion 1))
  match secondOffer.key with
  | .instantiate _ semantic =>
      if semantic.generation != 1 then none else pure ()
  | _ => none
  match selectOffer first (.suggestion (suggestion 1)) with
  | .completed (.instanceAdmitted [fresh]) next =>
      if fresh == node 3 then some next else none
  | _ => none

-- Admitting one append-only extension does not tombstone an independent
-- retained instantiation from the same still-fresh source invocation.
#guard
  match twoInstancesFinal? with
  | some state =>
      state.engine.programVersion == 2 && state.engine.program.nodes.size == 4 &&
        state.engine.instanceHistory.size == 2 && state.metrics.selectedInstances == 2
  | none => false

def emptyInstance (request : RuleRequest Rank) : Outcome Rank :=
  .success [candidate request 1]
    [.instantiate
      { key := 107
        nodes := []
        equalities := []
        payload := { index := 109 } }]
    {}

-- A structurally valid instantiation with no new node or equality is a
-- duplicate: it consumes no instance slot and does not bump programVersion.
#guard
  match afterReplyWith?
      { engineLimits with maxInstances := 0, maxGeneration := 0 } emptyInstance with
  | none => false
  | some state =>
      match selectOffer state (.suggestion (suggestion 0)) with
      | .completed .instanceDuplicate next =>
          next.engine.programVersion == 0 && next.engine.instances.isEmpty &&
            next.engine.instanceHistory.isEmpty &&
            next.engine.metrics.duplicateInstances == 1
      | _ => false

def selfEqualityRequest (_request : RuleRequest Rank) : InstantiationRequest :=
  { key := 127
    nodes := []
    equalities :=
      [{ left := .existing (node 0)
         right := .existing (node 0)
         payload := { index := 131 } }]
    payload := { index := 137 } }

def selfEqualityInstance (request : RuleRequest Rank) : Outcome Rank :=
  .success [candidate request 3]
    [.instantiate (selfEqualityRequest request)] {}

def selfEqualityResult? : Option (SubmitResult Rank) := do
  let state <- initialWithLimits? engineLimits policyLimits
  let (request, state) <- request? state (.application (application 0))
  some (state.submit (request.action.reply (selfEqualityInstance request)))

def weakRetry (_ : RuleRequest Rank) : Outcome Rank :=
  .success [] [.retry 0] {}

def overflowRetry (_ : RuleRequest Rank) : Outcome Rank :=
  .success []
    [.split { node := node 0, point := 0, reason := .midpoint }, .retry 1] {}

def overflowInstance (request : RuleRequest Rank) : Outcome Rank :=
  .success []
    [.split { node := node 0, point := 0, reason := .midpoint },
      .instantiate (instantiateG request)] {}

def overflowSplit (_ : RuleRequest Rank) : Outcome Rank :=
  .success []
    [.split { node := node 0, point := 0, reason := .midpoint }] {}

def overdepthG (request : RuleRequest Rank) : InstantiationRequest :=
  { key := 139
    nodes :=
      [{ domain := real
         op := { index := 2 }
         args := [.existing request.action.node] }]
    equalities := []
    payload := { index := 149 } }

def mixedDepth (request : RuleRequest Rank) : Outcome Rank :=
  .success [candidate request 2]
    [.instantiate (instantiateG request),
      .instantiate (overdepthG request),
      .retry 1] {}

def depthThenRetry (request : RuleRequest Rank) : Outcome Rank :=
  .success [candidate request 2]
    [.instantiate (overdepthG request), .retry 1] {}

def malformedSuffix (request : RuleRequest Rank) : Outcome Rank :=
  .success [candidate request 2]
    [.split { node := node 0, point := 0, reason := .midpoint },
      .instantiate (selfEqualityRequest request)] {}

def overdepthMalformed (request : RuleRequest Rank) : Outcome Rank :=
  .success [candidate request 3]
    [.instantiate
      { overdepthG request with
        equalities :=
          [{ left := .existing (node 0)
             right := .existing (node 0)
             payload := { index := 151 } }] }]
    {}

def overdepthMalformedResult? : Option (SubmitResult Rank) := do
  let limits := { engineLimits with maxNodeDepth := 1 }
  let state <- initialWithLimits? limits policyLimits
  let (request, state) <- request? state (.application (application 0))
  some (state.submit (request.action.reply (overdepthMalformed request)))

def startWithWeakRetry? : Option (State Rank) := do
  let engine <- match Engine.start rankDomain program #[fRule, gRule] #[0, 0] engineLimits with
    | .ok engine => some engine
    | .error _ => none
  match engine.poll with
  | .request request awaiting =>
      match awaiting.submit (request.action.reply (weakRetry request)) with
      | .accepted _ next => some (State.start next policyLimits)
      | _ => none
  | _ => none

-- The policy key exposes the engine-computed theorem-instantiation generation.
#guard
  match afterInitial? with
  | some state =>
      match state.offer? (.suggestion (suggestion 1)) with
      | some { key := .instantiate _ semantic, .. } => semantic.generation == 1
      | _ => false
  | none => false

-- Malformed structural work is rejected by reply admission and never enters
-- retained policy state.
#guard
  match selfEqualityResult? with
  | some (.invalid .malformedProposal state) =>
      state.incomplete && state.engine.facts.toList == [0, 0] &&
        state.engine.history.isEmpty && state.engine.suggestions.isEmpty
  | _ => false

-- Structural validation outranks recoverable depth filtering: a bad equality
-- after an over-depth draft still invalidates the whole reply atomically.
#guard
  match overdepthMalformedResult? with
  | some (.invalid .malformedProposal state) =>
      state.incomplete && state.engine.facts.toList == [0, 0] &&
        state.engine.history.isEmpty && state.engine.suggestions.isEmpty &&
        state.engine.metrics.droppedSuggestions == 0 &&
        state.engine.metrics.capacityDrops == 0 && state.engine.metrics.depthDrops == 0
  | _ => false

-- A depth-limited instantiation is a recoverable loss local to that
-- suggestion. The useful candidate commits, the valid instantiation and later
-- retry keep their source order, the dropped proposal is counted, and policy
-- cannot report a false fixed point.
#guard
  match observedWith? { engineLimits with maxNodeDepth := 1 } mixedDepth with
  | some (observation, state) =>
      observation.outcome == .success &&
        oneChange observation.changes (node 1) 0 2 0 1 &&
        observation.emittedSuggestions.toList ==
          [.suggestion (suggestion 0), .suggestion (suggestion 1)] &&
        state.engine.facts.toList == [0, 2] &&
        state.engine.history.size == 1 &&
        state.engine.metrics.candidates == 1 &&
        state.engine.metrics.droppedSuggestions == 1 &&
        state.engine.metrics.capacityDrops == 0 &&
        state.engine.metrics.depthDrops == 1 &&
        state.engine.suggestions.size == 2 && state.incomplete &&
        (match observation.suggestionPlan.kept, observation.suggestionPlan.dropped with
        | [.instantiate kept, .retry effort], [.depth (.instantiate dropped)] =>
            kept.key == 31 && dropped.key == 139 && effort == 1
        | _, _ => false) &&
        match state.engine.suggestions[0]?, state.engine.suggestions[1]? with
        | some first, some second =>
            match first.suggestion, second.suggestion with
            | .instantiate request, .retry effort => request.key == 31 && effort == 1
            | _, _ => false
        | _, _ => false
  | none => false

-- Depth filtering does not consume the sole retained-suggestion slot. The
-- later retry is kept, and the exact engine plan reaches the policy
-- observation without structural revalidation.
#guard
  match observedWith?
      { engineLimits with maxNodeDepth := 1, maxRetainedSuggestions := 1 }
      depthThenRetry with
  | some (observation, state) =>
      observation.outcome == .success &&
        oneChange observation.changes (node 1) 0 2 0 1 &&
        observation.emittedSuggestions.toList == [.suggestion (suggestion 0)] &&
        state.engine.facts.toList == [0, 2] &&
        state.engine.metrics.droppedSuggestions == 1 &&
        state.engine.metrics.capacityDrops == 0 &&
        state.engine.metrics.depthDrops == 1 &&
        state.engine.suggestions.size == 1 && state.incomplete &&
        match observation.suggestionPlan.kept, observation.suggestionPlan.dropped with
        | [.retry effort], [.depth (.instantiate dropped)] =>
            effort == 1 && dropped.key == 139
        | _, _ => false
  | none => false

-- Suggestions beyond exact capacity never become retained work and therefore
-- are not structurally validated. This malformed suffix is classified as a
-- capacity loss, its useful sibling candidate commits, and losing the
-- instantiation marks policy incomplete instead of invalidating the reply.
#guard
  match observedWith?
      { engineLimits with maxRetainedSuggestions := 1 } malformedSuffix with
  | some (observation, state) =>
      observation.outcome == .success &&
        oneChange observation.changes (node 1) 0 2 0 1 &&
        observation.emittedSuggestions.toList == [.suggestion (suggestion 0)] &&
        state.engine.facts.toList == [0, 2] &&
        state.engine.metrics.droppedSuggestions == 1 &&
        state.engine.metrics.capacityDrops == 1 &&
        state.engine.metrics.depthDrops == 0 &&
        state.engine.suggestions.size == 1 && state.incomplete &&
        match observation.suggestionPlan.kept, observation.suggestionPlan.dropped with
        | [.split _], [.capacity (.instantiate dropped)] => dropped.key == 127
        | _, _ => false
  | none => false

-- A retry which fails its variant-specific freshness guard is tombstoned, but
-- its disappearance cannot be mistaken for successful propagation.
#guard
  match afterReplyWith? engineLimits weakRetry with
  | some state =>
      state.engine.suggestions.size == 1 && state.incomplete &&
        (state.offer? (.suggestion (suggestion 0))).isNone &&
        (state.view).toOption.any fun pair =>
          pair.1.offers.isEmpty && pair.1.incomplete
  | none => false

-- The same accounting occurs when policy control adopts an engine snapshot
-- which already contains the unusable retained retry.
#guard
  match startWithWeakRetry? with
  | some state =>
      state.incomplete &&
        (state.offer? (.suggestion (suggestion 0))).isNone &&
        (state.view).toOption.any fun pair =>
          pair.1.offers.isEmpty && pair.1.incomplete
  | none => false

-- Retained-suggestion overflow is inspected before the engine discards its
-- suffix. Here the split is retained, but the dropped retry still makes
-- fixed-point completeness unavailable.
#guard
  match observedWith?
      { engineLimits with maxRetainedSuggestions := 1 } overflowRetry with
  | some (observation, state) =>
      observation.outcome == .success &&
        observation.emittedSuggestions.toList == [.suggestion (suggestion 0)] &&
        state.engine.suggestions.size == 1 &&
        state.engine.metrics.droppedSuggestions == 1 &&
        state.engine.metrics.capacityDrops == 1 &&
        state.engine.metrics.depthDrops == 0 && state.incomplete &&
        match state.engine.suggestions[0]? with
        | some retained =>
            match retained.suggestion with
            | .split _ => true
            | .retry _ | .instantiate _ => false
        | none => false
  | none => false

-- A dropped instantiation has the same closure consequence as a dropped
-- retry, even though neither proposal survives in the retained prefix.
#guard
  match observedWith?
      { engineLimits with maxRetainedSuggestions := 1 } overflowInstance with
  | some (observation, state) =>
      observation.outcome == .success &&
        observation.emittedSuggestions.toList == [.suggestion (suggestion 0)] &&
        state.engine.suggestions.size == 1 &&
        state.engine.metrics.droppedSuggestions == 1 &&
        state.engine.metrics.capacityDrops == 1 &&
        state.engine.metrics.depthDrops == 0 && state.incomplete
  | none => false

-- Dropping only optional split advice does not make propagation incomplete.
#guard
  match observedWith?
      { engineLimits with maxRetainedSuggestions := 0 } overflowSplit with
  | some (observation, state) =>
      observation.outcome == .success && observation.emittedSuggestions.isEmpty &&
        state.engine.suggestions.isEmpty &&
        state.engine.metrics.droppedSuggestions == 1 &&
        state.engine.metrics.capacityDrops == 1 &&
        state.engine.metrics.depthDrops == 0 && !state.incomplete &&
        (state.view).toOption.any fun pair =>
          pair.1.offers.isEmpty && !pair.1.incomplete
  | none => false

-- Dismissal uses the same closure classification as tombstoning and bounded
-- retention. Removing the retry and instantiation makes an eventually empty
-- frontier incomplete; removing the split does not erase or invent that fact.
#guard
  match afterInitial? with
  | none => false
  | some state =>
      match dismissOffer state (.suggestion (suggestion 0)) with
      | none => false
      | some state =>
          match dismissOffer state (.suggestion (suggestion 1)) with
          | none => false
          | some state =>
              match dismissOffer state (.suggestion (suggestion 2)) with
              | some state =>
                  state.incomplete && state.metrics.dismissals == 3 &&
                    (state.view).toOption.any fun pair =>
                      pair.1.offers.isEmpty && pair.1.incomplete
              | none => false

-- A split-only frontier remains propagation-complete when its optional search
-- advice is dismissed.
#guard
  match afterReplyWith? engineLimits overflowSplit with
  | none => false
  | some state =>
      match dismissOffer state (.suggestion (suggestion 0)) with
      | some next =>
          !next.incomplete &&
            (next.view).toOption.any fun pair =>
              pair.1.offers.isEmpty && !pair.1.incomplete
      | none => false

def splitChangedTarget (request : RuleRequest Rank) : Outcome Rank :=
  .success [candidate request 1]
    [.split { node := request.action.node, point := 0, reason := .midpoint }]
    {}

-- The split guard is captured before candidates from the same reply commit.
-- Starting or advancing policy control cannot launder version zero into the
-- improved target's version one.
#guard
  match afterReplyWith? engineLimits splitChangedTarget with
  | some state =>
      match state.engine.suggestions[0]? with
      | some retained =>
          !state.incomplete && retained.splitVersion == some 0 &&
            state.engine.versions[1]? == some 1 &&
            (state.offer? (.suggestion (suggestion 0))).isNone
      | none => false
  | none => false

/-! # Rejections, completeness, clocks, and policy-visible budgets -/

-- An action-limit rejection cannot consume the retry it failed to prepare.
#guard
  match afterInitialWith? { engineLimits with maxActions := 1 } with
  | some state =>
      match selectOffer state (.suggestion (suggestion 0)) with
      | .rejected .actionLimit next =>
          (next.offer? (.suggestion (suggestion 0))).isSome &&
            next.metrics.selectedRetries == 0 && next.metrics.rejected == 1
      | _ => false
  | none => false

-- A resource stop while admitting an instantiation is not a verdict on the
-- proposal, so the offer remains available.
#guard
  match afterInitialWith? { engineLimits with maxInstances := 0 } with
  | some state =>
      match selectOffer state (.suggestion (suggestion 1)) with
      | .engineResource .instances next =>
          (next.offer? (.suggestion (suggestion 1))).isSome &&
            next.metrics.selectedInstances == 1
      | _ => false
  | none => false

-- Dismissing required propagation is visible in the bounded view; an empty
-- frontier cannot then be mistaken for a proved fixed point.
#guard
  match initial? with
  | some state =>
      match state.offer? (.application (application 0)) with
      | some offer =>
          match state.dismiss
              { scope := state.scope
                serial := state.serial
                programVersion := state.engine.programVersion
                id := offer.id
                expected := offer.key } with
          | .completed .dismissed next =>
              match next.view with
              | .ok (view, _) => view.offers.isEmpty && view.incomplete
              | _ => false
          | _ => false
      | none => false
  | none => false

-- The policy sees every structural budget that can reject its next
-- instantiation, not only facts and node counts.
#guard
  match afterInitial? with
  | some state =>
      match state.view with
      | .ok (view, _) =>
          view.remaining.actions == 31 && view.remaining.acceptedFacts == 31 &&
            view.remaining.nodes == 6 && view.remaining.applications == 15 &&
            view.remaining.equalities == 8 && view.remaining.retainedSuggestions == 13 &&
            view.remaining.instances == 8 && view.remaining.queueEntries == 63 &&
            view.remaining.generation == 4
      | _ => false
  | none => false

#guard
  match initialWith? { policyLimits with maxTraversal := 0 } with
  | some state =>
      match state.view with
      | .error .traversalLimit => true
      | _ => false
  | none => false

#guard
  match initialWith? { policyLimits with maxLiveOffers := 0 } with
  | some state =>
      match state.view with
      | .error .liveOfferLimit => true
      | _ => false
  | none => false

end Hex.Interval.PolicyConformance
