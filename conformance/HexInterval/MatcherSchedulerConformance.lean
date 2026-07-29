/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Policy
import HexInterval.Experiment.PackageRegistry

/-!
# Engine-owned structural matcher conformance

This canary exercises a registration-wide matcher through the ordinary
request/reply scheduler.  The package receives bounded structural batches but
never owns the cursor.  A sine-shaped match introduces expressions, an
equality, and an arbitrary-scope contractor.  A later batch triggered by the
new equality/application demonstrates that non-node structural causes
contribute to theorem-instantiation generation.
-/

namespace Hex.Interval.MatcherSchedulerConformance

open Experiment.Propagator

abbrev Rank := Nat

def rankDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "matcher-scheduler.source" }
def negKey : OpKey := { name := "matcher-scheduler.neg" }
def sinKey : OpKey := { name := "matcher-scheduler.sin" }
def markerKey : OpKey := { name := "matcher-scheduler.marker" }

def matcherKey : RuleKey := { name := "matcher-scheduler.sin-shapes" }
def contractKey : RuleKey := { name := "matcher-scheduler.sin-contract" }

def operations : Array Operation :=
  #[{ key := sourceKey, inputs := [], output := real },
    { key := negKey, inputs := [real], output := real },
    { key := sinKey, inputs := [real], output := real },
    { key := markerKey, inputs := [], output := real }]

def node (index : Nat) : NodeId := { index }

def program : Program :=
  { operations
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 1 }, args := [node 0] },
        { domain := real, op := { index := 2 }, args := [node 1] }] }

def matcherRule : Registration :=
  { key := matcherKey
    head := sinKey
    kind := .instantiate
    watches := []
    writes := []
    binding := .global
    watchesProgram := true
    matchWatch := .network }

def contractRule : Registration :=
  { key := contractKey
    head := sinKey
    kind := .improve
    watches := []
    writes := []
    binding := .scoped }

def limits : Limits :=
  { maxOperations := 4
    maxNodes := 8
    maxRules := 2
    maxArity := 2
    maxScopeNodes := 2
    maxApplications := 4
    maxQueueEntries := 16
    maxActions := 16
    maxMatcherVisits := 16
    matcherBatchSize := 2
    maxAcceptedFacts := 4
    maxRetainedSuggestions := 4
    maxEffort := 2
    maxObservationValue := 16
    maxDiagnosticValue := 16
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 2
    maxProposalItems := 4
    maxInstances := 4
    maxGeneration := 4
    maxNodeDepth := 8
    maxEqualities := 2
    splitEndpointLimit :=
      { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def started? : Option (Engine Rank) :=
  match Engine.start rankDomain program #[matcherRule, contractRule]
      #[0, 0, 0] limits with
  | .ok state => some state
  | .error _ => none

#guard program.check
#guard registrationsCheck program #[matcherRule, contractRule]

-- A whole-network matcher is compiled once for the registration, even though
-- its declared head can occur many times after instantiation.
#guard
  match started? with
  | some state =>
      state.applications.size == 1 && state.matcherCursors.size == 1 &&
        match state.applications[0]?, state.matcherCursors[0]? with
        | some application, some (some cursor) =>
            application.node == node 2 && application.rule.index == 0 &&
              cursor.offset == 0 && cursor.limit.nodes == 3 &&
              cursor.limit.applications == 1
        | _, _ => false
  | none => false

-- Zero batch size is rejected when a network matcher is registered.
#guard
  match Engine.start rankDomain program #[matcherRule, contractRule]
      #[0, 0, 0] { limits with matcherBatchSize := 0 } with
  | .error .invalidRegistrations => true
  | _ => false

def firstRequest? : Option (RuleRequest Rank × Engine Rank) := do
  let state <- started?
  let .request request awaiting := state.poll | none
  pure (request, awaiting)

-- Polling exposes a batch but does not commit cursor progress or visit cost.
#guard
  match firstRequest? with
  | some (request, awaiting) =>
      request.action.structuralInputs.map (fun input => input.key) ==
          [.node (node 0), .node (node 1)] &&
        request.action.matcherEpoch == some 0 &&
        awaiting.metrics.matcherVisits == 0 &&
        match awaiting.matcherCursors[0]?, awaiting.pendingMatcher with
        | some (some stored), some prepared =>
            stored.offset == 0 && prepared.offset == 2
        | _, _ => false
  | none => false

-- A mismatched reply leaves both the pending action and stored cursor intact.
#guard
  match firstRequest? with
  | some (request, awaiting) =>
      let wrong : Reply Rank :=
        { serial := request.action.serial + 1
          programVersion := request.action.programVersion
          application := request.action.application
          outcome := .noChange {} }
      match awaiting.submit wrong with
      | .invalid .mismatchedAction after =>
          after.pending.isSome && after.metrics.matcherVisits == 0 &&
            match after.matcherCursors[0]? with
            | some (some cursor) => cursor.offset == 0
            | _ => false
      | _ => false
  | none => false

def afterFirst? : Option (Engine Rank) := do
  let (request, awaiting) <- firstRequest?
  let .accepted _ state :=
    awaiting.submit (request.action.reply (.noChange {})) | none
  pure state

-- Accepting the reply commits exactly the issued batch and requeues the same
-- matcher because its frozen epoch still has two unseen inputs.
#guard
  match afterFirst? with
  | some state =>
      state.metrics.matcherVisits == 2 && state.queueHead == 1 &&
        state.queue.size == 2 && state.queued[0]? == some true &&
        match state.matcherCursors[0]? with
        | some (some cursor) => cursor.offset == 2 && !cursor.exhausted
        | _ => false
  | none => false

def oddnessRequest : InstantiationRequest :=
  { key := 41
    nodes :=
      [{ domain := real, op := { index := 2 }, args := [.existing (node 0)] },
        { domain := real, op := { index := 1 }, args := [.proposed 0] }]
    equalities :=
      [{ left := .existing (node 2)
         right := .proposed 1
         payload := { index := 43 } }]
    scopes :=
      [{ rule := contractKey
         anchor := .proposed 0
         watches := [.existing (node 0)]
         writes := [.proposed 0] }]
    payload := { index := 47 } }

def retainedOddness? : Option (Engine Rank) := do
  let state <- afterFirst?
  let .request request awaiting := state.poll | none
  if request.action.structuralInputs.map (fun input => input.key) !=
      [.node (node 2), .application { index := 0 }] then
    none
  else
    let .accepted plan retained :=
      awaiting.submit
        (request.action.reply (.success [] [.instantiate oddnessRequest] {})) | none
    if plan.kept.length == 1 then some retained else none

-- The second accepted batch exhausts the epoch and therefore does not requeue.
#guard
  match retainedOddness? with
  | some state =>
      state.metrics.matcherVisits == 4 && state.queueHead == 2 &&
        state.queue.size == 2 && state.queued[0]? == some false &&
        match state.matcherCursors[0]? with
        | some (some cursor) => cursor.exhausted && cursor.visits == 4
        | _ => false
  | none => false

def afterOddness? : Option (Engine Rank) := do
  let state <- retainedOddness?
  let .admitted [sinX, negSinX] state :=
    state.admitInstantiation { index := 0 } | none
  if sinX == node 3 && negSinX == node 4 then some state else none

-- One atomic admission creates the two expressions, equality, and scoped
-- contractor, but no second global matcher application.  The old matcher is
-- woken once for the appended network delta.
#guard
  match afterOddness? with
  | some state =>
      state.programVersion == 1 && state.program.nodes.size == 5 &&
        state.equalities.size == 1 && state.applications.size == 2 &&
        state.matcherCursors.size == 2 && state.queueHead == 2 &&
        state.queue.size == 5 && state.queued[0]? == some true &&
        state.generations[3]? == some 1 && state.generations[4]? == some 1 &&
        match state.matcherCursors[0]?, state.matcherCursors[1]? with
        | some (some old), some none =>
            old.limit.nodes == 3 && old.limit.equalities == 0 &&
              old.limit.applications == 1
        | _, _ => false
  | none => false

def afterInternalWork? : Option (Engine Rank) := do
  let state <- afterOddness?
  let .equality equality state := state.poll | none
  let .advanced _ state := state.contractEquality equality | none
  let .request request awaiting := state.poll | none
  if request.action.key != contractKey then none else pure ()
  let .accepted _ state :=
    awaiting.submit (request.action.reply (.noChange {})) | none
  pure state

def firstDelta? : Option (Engine Rank) := do
  let state <- afterInternalWork?
  let .request request awaiting := state.poll | none
  if request.action.key != matcherKey ||
      request.action.structuralInputs.map (fun input => input.key) !=
        [.node (node 3), .node (node 4)] ||
      request.action.matcherEpoch != some 1 then
    none
  else
    let .accepted _ state :=
      awaiting.submit (request.action.reply (.noChange {})) | none
    pure state

-- Renewal scans exactly the structural suffix, in bounded batches.
#guard
  match firstDelta? with
  | some state =>
      state.metrics.matcherVisits == 6 && state.queued[0]? == some true &&
        match state.matcherCursors[0]? with
        | some (some cursor) =>
            cursor.epoch == 1 && cursor.base.nodes == 3 &&
              cursor.limit.nodes == 5 && cursor.offset == 2
        | _ => false
  | none => false

def markerRequest : InstantiationRequest :=
  { key := 53
    nodes := [{ domain := real, op := { index := 3 }, args := [] }]
    equalities := []
    payload := { index := 59 } }

def retainedMarker? : Option (Engine Rank) := do
  let state <- firstDelta?
  let .request request awaiting := state.poll | none
  if request.action.structuralInputs !=
      [{ key := .equality { index := 0 }, generation := 1 },
        { key := .application { index := 1 }, generation := 1 }] then
    none
  else
    let .accepted plan state :=
      awaiting.submit
        (request.action.reply (.success [] [.instantiate markerRequest] {})) | none
    if plan.kept.length == 1 then some state else none

-- Equality and application matches are causal inputs: although the marker is
-- nullary and the global matcher's anchor has generation zero, its theorem
-- instance is generation two.
#guard
  match retainedMarker? with
  | some state =>
      match state.suggestions[1]? with
      | some suggestion =>
          state.instantiationGeneration? suggestion == some 2 &&
            match state.admitInstantiation { index := 1 } with
            | .admitted [marker] after =>
                marker == node 5 && after.generations[5]? == some 2 &&
                  after.applications.size == 2
            | _ => false
      | none => false
  | none => false

/-! ## An arbitrary function package receives the same bounded batch -/

def packageMatcher (cache : Nat) (request : RuleRequest Rank) :
    Outcome Rank × Nat :=
  if request.action.structuralInputs.map (fun input => input.key) ==
      [.node (node 0), .node (node 1)] then
    (.noChange {}, cache + request.action.structuralInputs.length)
  else
    (.failed 7, cache)

def packageContract (_ : Rank) (_ : RuleRequest Rank) : Outcome Rank × Rank :=
  (.noChange {}, 0)

def package : Package Rank :=
  { Cache := Nat
    cache := 0
    operations
    handlers :=
      #[Handler.bareDroppingDrafts matcherRule packageMatcher,
        { Handler.bareDroppingDrafts contractRule packageContract with
          acceptsScope := fun _ binding => binding.rule == contractKey }] }

def packageLimits : Limits :=
  { limits with maxDiagnosticValue := 300 }

def registry? : Option (Registry Rank) :=
  match Registry.buildWithin packageLimits #[package] with
  | .ok registry => some registry
  | .error _ => none

def registryStarted? : Option (Registry Rank × Engine Rank) := do
  let registry <- registry?
  if !registry.acceptsProgram program ||
      !registry.acceptsLimits program packageLimits then
    none
  else
    match Engine.start rankDomain program registry.registrations #[0, 0, 0]
        packageLimits #[] (registry.acceptsBinding) with
    | .ok state => some (registry, state)
    | .error _ => none

#guard
  match registryStarted? with
  | some (registry, state) =>
      match state.poll with
      | .request request awaiting =>
          let (plan, registry) := registry.invokePlanned request
          match awaiting.submit (request.action.reply plan.outcome) with
          | .accepted _ next =>
              next.metrics.matcherVisits == 2 &&
                registry.packages[0]?.any (fun package => package.invocations == 1)
          | _ => false
      | _ => false
  | none => false

/-! ## The replaceable policy sees and selects the same engine-owned batch -/

def policyLimits : Policy.Limits :=
  { maxDecisions := 8
    maxTraversal := 32
    maxLiveOffers := 8 }

def policyView? : Option (Policy.View Rank × Policy.State Rank) := do
  let engine <- started?
  match (Policy.State.start engine policyLimits).view with
  | .ok pair => some pair
  | .error _ => none

#guard
  match policyView? with
  | some (view, _) =>
      view.offers.size == 1 && view.remaining.matcherVisits == 16 &&
        match view.offers[0]?.map (fun offer => offer.key) with
        | some (Policy.OfferKey.invoke invocation) =>
            invocation.structuralInputs.map (fun input => input.key) ==
                [.node (node 0), .node (node 1)] &&
              invocation.matcherEpoch == some 0 && !invocation.matcherBlocked
        | _ => false
  | none => false

def policySelected? :
    Option (RuleRequest Rank × Policy.State Rank × Policy.InvocationKey) := do
  let (view, state) <- policyView?
  let offer <- view.offers[0]?
  let Policy.OfferKey.invoke invocation := offer.key | none
  let selection : Policy.Selection :=
    { scope := view.scope
      serial := view.serial
      programVersion := view.programVersion
      id := offer.id
      expected := offer.key }
  let .request request state := state.select selection | none
  pure (request, state, invocation)

-- The policy echoes a semantic batch key; selection reconstructs the same
-- engine request and still keeps the prepared cursor outside that request.
#guard
  match policySelected? with
  | some (request, state, invocation) =>
      request.action.structuralInputs == invocation.structuralInputs &&
        request.action.matcherEpoch == invocation.matcherEpoch &&
        state.engine.pendingMatcher.isSome &&
        match request.action.reply (.noChange {}) |> state.submit with
        | .accepted observation next =>
            observation.invocation.structuralInputs == invocation.structuralInputs &&
              next.engine.metrics.matcherVisits == 2 &&
              next.engine.queued[0]? == some true &&
              match next.engine.matcherCursors[0]? with
              | some (some cursor) => cursor.offset == 2
              | _ => false
        | _ => false
  | none => false

def blockedPolicy? : Option (Policy.View Rank × Policy.State Rank) := do
  let .ok engine :=
    Engine.start rankDomain program #[matcherRule, contractRule] #[0, 0, 0]
      { limits with maxMatcherVisits := 0 } | none
  match (Policy.State.start engine policyLimits).view with
  | .ok pair => some pair
  | .error _ => none

-- Exhausted matcher visits remain a visible live offer. Selecting it reports
-- the exact engine resource instead of silently manufacturing saturation.
#guard
  match blockedPolicy? with
  | some (view, state) =>
      match view.offers[0]? with
      | some offer =>
          match offer.key with
          | Policy.OfferKey.invoke invocation =>
              invocation.matcherBlocked &&
                match state.select
                    { scope := view.scope
                      serial := view.serial
                      programVersion := view.programVersion
                      id := offer.id
                      expected := offer.key } with
                | .engineResource .matcherVisits _ => true
                | _ => false
          | _ => false
      | none => false
  | none => false

end Hex.Interval.MatcherSchedulerConformance
